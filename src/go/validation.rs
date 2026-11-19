//! Bounds and layout checks around the reused best-effort metadata reader.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use unstrip::types::{KindData, KindName, Type};
use unstrip::{GoBinary, ModuleData, buildinfo::BuildInfo};

fn word(binary: &GoBinary, address: u64) -> Option<u64> {
    let bytes = binary.read_at_addr(address, binary.pointer_size())?;
    Some(if binary.little_endian {
        bytes
            .iter()
            .rev()
            .fold(0, |value, byte| (value << 8) | u64::from(*byte))
    } else {
        bytes
            .iter()
            .fold(0, |value, byte| (value << 8) | u64::from(*byte))
    })
}

pub fn in_region(binary: &GoBinary, module: &ModuleData, address: u64) -> bool {
    let header = (4 * binary.pointer_size() + 16) as u64;
    address >= module.types
        && address % binary.pointer_size() as u64 == 0
        && address
            .checked_add(header)
            .is_some_and(|end| end <= module.etypes)
}

/// Some(false) is a plain offset; Some(true) packs offset and embedded bit.
pub fn offset_encoding(binary: &GoBinary, module: &ModuleData) -> Option<bool> {
    let ps = binary.pointer_size() as u64;
    // The validated 1.20+ module prefix includes the two coverage words.
    // Do not let one damaged field choose the encoding of every other type.
    if module.typedesclen != 0
        || (word(binary, module.addr + 37 * ps) == Some(module.types)
            && word(binary, module.addr + 35 * ps) != Some(module.types))
    {
        return Some(false);
    }
    let bytes = binary
        .read_at_addr(module.pc_header_addr, 4)?
        .try_into()
        .ok()?;
    let magic = if binary.little_endian {
        u32::from_le_bytes(bytes)
    } else {
        u32::from_be_bytes(bytes)
    };
    match magic {
        unstrip::pclntab::MAGIC_1_20 => Some(false),
        unstrip::pclntab::MAGIC_1_16 => Some(true),
        unstrip::pclntab::MAGIC_1_18 => {
            let version = BuildInfo::parse(binary).ok()?.go_version;
            let minor: u32 = version
                .strip_prefix("go1.")?
                .split(|c: char| !c.is_ascii_digit())
                .next()?
                .parse()
                .ok()?;
            Some(minor <= 18)
        }
        _ => None,
    }
}

pub fn children(data: &KindData) -> Vec<u64> {
    match data {
        KindData::Pointer { elem }
        | KindData::Slice { elem }
        | KindData::Array { elem, .. }
        | KindData::Chan { elem, .. } => vec![*elem],
        KindData::Map { key, elem, bucket } => {
            let mut result = vec![*key, *elem];
            result.extend(bucket.iter().copied().filter(|address| *address != 0));
            result
        }
        KindData::Struct { fields } => fields.iter().map(|f| f.typ).collect(),
        KindData::Interface { methods } => methods.iter().map(|m| m.typ).collect(),
        KindData::Func {
            in_types,
            out_types,
            ..
        } => in_types.iter().chain(out_types).copied().collect(),
        _ => Vec::new(),
    }
}

pub fn prepare(binary: &GoBinary, offsets: Option<bool>, mut ty: Type) -> Result<Type, String> {
    if ty.size > u64::MAX / 8 {
        return Err("type exceeds native bit-offset representation".into());
    }
    if ty.name.contains('\0')
        || match &ty.kind_data {
            KindData::Struct { fields } => fields.iter().any(|field| field.name.contains('\0')),
            KindData::Interface { methods } => {
                methods.iter().any(|method| method.name.contains('\0'))
            }
            _ => false,
        }
    {
        return Err("metadata name contains NUL".into());
    }
    let ps = binary.pointer_size() as u64;
    let layout = binary
        .read_at_addr(ty.addr + 2 * ps + 5, 2)
        .ok_or("unmapped alignment fields")?;
    if layout.iter().any(|a| !matches!(a, 1 | 2 | 4 | 8)) || ty.size % layout[0] as u64 != 0 {
        return Err("invalid type alignment or aligned size".into());
    }
    if ty.ptr_bytes > ty.size || ty.ptr_bytes % ps != 0 {
        return Err("invalid pointer-bearing prefix".into());
    }
    let width = match ty.kind {
        KindName::Bool | KindName::Int8 | KindName::Uint8 => Some(1),
        KindName::Int16 | KindName::Uint16 => Some(2),
        KindName::Int32 | KindName::Uint32 | KindName::Float32 => Some(4),
        KindName::Int64 | KindName::Uint64 | KindName::Float64 | KindName::Complex64 => Some(8),
        KindName::Complex128 => Some(16),
        KindName::Int
        | KindName::Uint
        | KindName::Uintptr
        | KindName::Pointer
        | KindName::UnsafePointer
        | KindName::Map
        | KindName::Chan
        | KindName::Func => Some(ps),
        KindName::String | KindName::Interface => Some(2 * ps),
        KindName::Slice => Some(3 * ps),
        KindName::Invalid | KindName::Unknown(_) => return Err("invalid type kind".into()),
        _ => None,
    };
    if width.is_some_and(|width| width != ty.size) {
        return Err("kind and value width disagree".into());
    }
    if matches!(
        ty.kind,
        KindName::Pointer
            | KindName::Slice
            | KindName::Array
            | KindName::Map
            | KindName::Chan
            | KindName::Func
            | KindName::Interface
            | KindName::Struct
    ) && matches!(ty.kind_data, KindData::None)
    {
        return Err("missing kind-specific layout".into());
    }
    if let KindData::Func {
        in_count,
        out_count,
        in_types,
        out_types,
        variadic,
    } = &ty.kind_data
    {
        if *in_count as usize != in_types.len()
            || *out_count as usize != out_types.len()
            || (*variadic && in_types.is_empty())
        {
            return Err("incomplete function type parameter lists".into());
        }
    }
    if let KindData::Chan { dir, .. } = ty.kind_data {
        if !matches!(dir, 1 | 2 | 3) {
            return Err("invalid channel direction".into());
        }
    }
    if let KindData::Struct { fields } = &mut ty.kind_data {
        let old = offsets.ok_or("ambiguous struct-field encoding")?;
        let extra = ty.addr + (4 * ps + 16);
        let array = word(binary, extra + ps).ok_or("unmapped field array")?;
        let count = word(binary, extra + 2 * ps).ok_or("unmapped field count")?;
        let capacity = word(binary, extra + 3 * ps).ok_or("unmapped field capacity")?;
        if count != fields.len() as u64 || capacity < count {
            return Err("inconsistent field slice".into());
        }
        for (i, field) in fields.iter_mut().enumerate() {
            let address = array
                .checked_add(i as u64 * 3 * ps)
                .ok_or("field address overflow")?;
            let raw = word(binary, address + 2 * ps).ok_or("unmapped field offset")?;
            field.offset = if old { raw >> 1 } else { raw };
            field.embedded = if old {
                raw & 1 != 0
            } else {
                word(binary, address)
                    .and_then(|name| binary.read_at_addr(name, 1))
                    .is_some_and(|b| b[0] & 8 != 0)
            };
        }
    }
    Ok(ty)
}

fn layout_problem(binary: &GoBinary, ty: &Type, nodes: &BTreeMap<u64, Type>) -> Option<String> {
    for child in children(&ty.kind_data) {
        if !nodes.contains_key(&child) {
            return Some(format!("missing or rejected child 0x{child:x}"));
        }
    }
    if let KindData::Array { elem, len } = ty.kind_data {
        if nodes[&elem].size.checked_mul(len) != Some(ty.size) {
            return Some("array extent disagrees with element size".into());
        }
    }
    if let KindData::Struct { fields } = &ty.kind_data {
        let mut end = 0;
        for field in fields {
            let child = &nodes[&field.typ];
            let Some(bytes) =
                binary.read_at_addr(child.addr + (2 * binary.pointer_size() + 6) as u64, 1)
            else {
                return Some("unmapped child alignment".into());
            };
            let alignment = bytes[0] as u64;
            if alignment == 0 {
                return Some("invalid child alignment".into());
            }
            let next = field.offset.checked_add(child.size);
            if field.offset < end
                || field.offset % alignment != 0
                || next.is_none_or(|next| next > ty.size)
            {
                return Some(
                    "field overlap, alignment or extent disagrees with its structure".into(),
                );
            }
            end = next.unwrap();
        }
    }
    None
}

fn value_cycles(nodes: &BTreeMap<u64, Type>) -> BTreeSet<u64> {
    let mut colors = BTreeMap::new();
    let mut cycles = BTreeSet::new();
    for &root in nodes.keys() {
        let mut stack = vec![(root, false)];
        while let Some((address, leaving)) = stack.pop() {
            if leaving {
                colors.insert(address, 2);
                continue;
            }
            match colors.get(&address) {
                Some(1) => {
                    cycles.insert(address);
                    continue;
                }
                Some(2) => continue,
                _ => {}
            }
            colors.insert(address, 1);
            stack.push((address, true));
            // Only by-value edges require a finite type layout. Pointer,
            // slice, interface and function recursion is legitimate.
            let children = match &nodes[&address].kind_data {
                KindData::Struct { fields } => fields.iter().map(|f| f.typ).collect(),
                KindData::Array { elem, .. } => vec![*elem],
                _ => Vec::new(),
            };
            stack.extend(
                children
                    .into_iter()
                    .filter(|a| nodes.contains_key(a))
                    .map(|a| (a, false)),
            );
        }
    }
    cycles
}

/// Retain valid components; propagate rejection through reverse dependencies.
pub fn quarantine(binary: &GoBinary, nodes: &mut BTreeMap<u64, Type>) -> BTreeMap<u64, String> {
    let mut reverse: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut rejected: BTreeMap<_, _> = value_cycles(nodes)
        .into_iter()
        .map(|address| (address, "recursive by-value type layout".to_string()))
        .collect();
    for (&address, ty) in nodes.iter() {
        for child in children(&ty.kind_data) {
            reverse.entry(child).or_default().push(address);
        }
        if let Some(reason) = layout_problem(binary, ty, nodes) {
            rejected.insert(address, reason);
        }
    }
    let mut queue: VecDeque<_> = rejected.keys().copied().collect();
    while let Some(child) = queue.pop_front() {
        for parent in reverse.get(&child).into_iter().flatten() {
            if !rejected.contains_key(parent) {
                rejected.insert(*parent, format!("depends on rejected type 0x{child:x}"));
                queue.push_back(*parent);
            }
        }
    }
    nodes.retain(|address, _| !rejected.contains_key(address));
    rejected
}
