use binaryninja::function::Function;
use binaryninja::types::{Type, TypeClass, ValueLocation};
use binaryninja::variable::{Variable, VariableSourceType};
use binaryninjacore_sys::*;

use crate::binja::FunctionHandle;
use crate::rust::layout::{Contract, Location, Slot};

fn location(value: &ValueLocation) -> Option<Location> {
    if value.components.is_empty() {
        return None;
    }
    Some(Location {
        pieces: value
            .components
            .iter()
            .map(|piece| (piece.variable.to_identifier(), piece.offset, piece.size))
            .collect(),
        indirect: value.indirect,
        returned_pointer: value
            .returned_pointer
            .map(|variable| variable.to_identifier()),
    })
}

fn integer(ty: &Type) -> Option<bool> {
    (ty.type_class() == TypeClass::IntegerTypeClass).then(|| ty.is_signed().contents)
}

/// The Rust setter supports complete locations; the effective getter is core-only.
fn result(function: &Function) -> Option<Slot> {
    let handle = FunctionHandle::new(function)?;
    let mut value = unsafe { BNGetFunctionReturnValueLocation(handle.as_ptr()) };
    let raw = &value.location;
    let location = if raw.count > 512 || (raw.count != 0 && raw.components.is_null()) {
        None
    } else {
        let pieces = if raw.count == 0 {
            Vec::new()
        } else {
            unsafe { std::slice::from_raw_parts(raw.components, raw.count) }
                .iter()
                .map(|piece| {
                    (
                        Variable::from(&piece.variable).to_identifier(),
                        piece.offset,
                        piece.sizeValid.then_some(piece.size),
                    )
                })
                .collect()
        };
        Some((!pieces.is_empty()).then(|| {
            Location {
                pieces,
                indirect: raw.indirect,
                returned_pointer: raw
                    .returnedPointerValid
                    .then(|| Variable::from(&raw.returnedPointer).to_identifier()),
            }
        }))
    };
    unsafe { BNFreeValueLocation(&mut value.location) };
    Some(Slot {
        width: function.return_type().contents.width(),
        location: location?,
        integer: integer(&function.return_type().contents),
    })
}

pub(in crate::rust) fn capture(function: &Function) -> Option<Contract> {
    let variables = function.parameter_variables().contents;
    let locations = function.parameter_locations().contents;
    let declarations = function.function_type().parameters().unwrap_or_default();
    if variables.len() != locations.len()
        || declarations.len() != locations.len()
        || locations.len() > 256
        || locations
            .iter()
            .any(|location| location.components.len() > 512)
    {
        return None;
    }
    Some(Contract {
        convention: function
            .calling_convention()
            .map(|value| value.contents.name().to_string()),
        parameters: declarations
            .iter()
            .zip(&locations)
            .map(|(parameter, value)| Slot {
                width: parameter
                    .ty
                    .contents
                    .deref_named_type_reference(&function.view())
                    .width(),
                location: location(value),
                integer: integer(&parameter.ty.contents),
            })
            .collect(),
        result: result(function)?,
        stack_adjustment: function.stack_adjustment().contents,
        can_return: function.function_type().can_return().contents,
        pure: function.function_type().pure().contents,
        variadic: function.function_type().has_variable_arguments().contents,
    })
}

/// Only a complete, direct native word can serve as a physical pointer origin.
pub(in crate::rust) fn word_register(slot: &Slot, width: usize) -> Option<u32> {
    let location = slot.location.as_ref()?;
    if slot.width != width as u64 || location.indirect || location.returned_pointer.is_some() {
        return None;
    }
    let [(identifier, offset, size)] = location.pieces.as_slice() else {
        return None;
    };
    if *offset != 0 || size.is_some_and(|size| size != width as u64) {
        return None;
    }
    let variable = Variable::from_identifier(*identifier);
    (variable.ty == VariableSourceType::RegisterVariableSourceType)
        .then(|| u32::try_from(variable.storage).ok())
        .flatten()
}
