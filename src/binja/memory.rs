use std::ops::Range;

use binaryninja::binary_view::BinaryView;
use binaryninja::types::{Type, TypeClass};

/// Qualify the bytes read, including annotations nested inside aggregate types.
pub(crate) fn readonly(view: &BinaryView, range: &Range<u64>) -> bool {
    if range.is_empty() || range.end - range.start > 1_048_576 {
        return false;
    }
    if !view.segment_at(range.start).is_some_and(|segment| {
        segment.readable() && !segment.writable() && range.end <= segment.address_range().end
    }) {
        return false;
    }
    for address in range.clone() {
        // Overlapping sections can report both writable and read-only semantics.
        if view.offset_has_writable_semantics(address) {
            return false;
        }
    }
    let mut budget = 1024;
    let mut address = range.start;
    while address < range.end {
        // Qualify each contiguous annotation once, retaining every nested byte boundary.
        let variable = view.data_variable_at_address(address);
        let identity = variable
            .as_ref()
            .map(|var| (var.address, var.ty.contents.handle));
        let mut end = address + 1;
        while end < range.end
            && view
                .data_variable_at_address(end)
                .as_ref()
                .map(|var| (var.address, var.ty.contents.handle))
                == identity
        {
            end += 1;
        }
        if let Some(variable) = variable {
            let Some(start) = address.checked_sub(variable.address) else {
                return false;
            };
            let Some(end) = end.checked_sub(variable.address) else {
                return false;
            };
            if !stable(view, &variable.ty.contents, &(start..end), 0, &mut budget) {
                return false;
            }
        }
        address = end;
    }
    true
}

fn stable(
    view: &BinaryView,
    ty: &Type,
    range: &Range<u64>,
    depth: usize,
    budget: &mut usize,
) -> bool {
    if range.is_empty() {
        return true;
    }
    if depth >= 32 || *budget == 0 || ty.is_volatile().contents {
        return false;
    }
    *budget -= 1;
    match ty.type_class() {
        TypeClass::NamedTypeReferenceClass => ty
            .get_named_type_reference()
            .and_then(|name| view.type_by_id(&name.id()))
            .is_some_and(|target| stable(view, &target, range, depth + 1, budget)),
        TypeClass::ArrayTypeClass => {
            let Some(element) = ty.element_type() else {
                return false;
            };
            let width = element.contents.deref_named_type_reference(view).width();
            if width == 0 {
                return false;
            }
            let first = range.start / width;
            let last = (range.end - 1) / width;
            let start = range.start % width;
            let end = (range.end - 1) % width + 1;
            if first == last {
                stable(view, &element.contents, &(start..end), depth + 1, budget)
            } else {
                stable(view, &element.contents, &(start..width), depth + 1, budget)
                    && (last == first + 1
                        || stable(view, &element.contents, &(0..width), depth + 1, budget))
                    && stable(view, &element.contents, &(0..end), depth + 1, budget)
            }
        }
        TypeClass::StructureTypeClass => {
            let Some(structure) = ty.get_structure() else {
                return false;
            };
            let members = structure.members();
            let bases = structure.base_structures();
            let Some(left) = budget.checked_sub(members.len() + bases.len()) else {
                return false;
            };
            *budget = left;
            for member in members {
                let width = member.ty.contents.deref_named_type_reference(view).width();
                let Some(end) = member.offset.checked_add(width) else {
                    return false;
                };
                if range.start < end && member.offset < range.end {
                    let part = range.start.max(member.offset) - member.offset
                        ..range.end.min(end) - member.offset;
                    if !stable(view, &member.ty.contents, &part, depth + 1, budget) {
                        return false;
                    }
                }
            }
            for base in bases {
                let Some(end) = base.offset.checked_add(base.width) else {
                    return false;
                };
                if range.start < end && base.offset < range.end {
                    let part = range.start.max(base.offset) - base.offset
                        ..range.end.min(end) - base.offset;
                    if !view
                        .type_by_id(&base.ty.id())
                        .is_some_and(|ty| stable(view, &ty, &part, depth + 1, budget))
                    {
                        return false;
                    }
                }
            }
            true
        }
        TypeClass::FragmentTypeClass => false,
        // Volatile pointees do not make the stored pointer itself volatile.
        _ => true,
    }
}
