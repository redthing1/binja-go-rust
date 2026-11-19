use std::collections::BTreeMap;

use binaryninja::architecture::CoreArchitecture;
use binaryninja::confidence::Conf;
use binaryninja::rc::Ref;
use binaryninja::types::{FunctionParameter, Type, TypeBuilder, ValueLocationSource};
use serde::{Deserialize, Serialize};
use unstrip::Pclntab;

use super::{convention, runtime};

const REGISTERS: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Serialize)]
pub(crate) enum Operand {
    Register(u8),
    Constant(u8),
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Serialize)]
pub(crate) struct Bounds {
    pub code: u8,
    pub signed: bool,
    pub x: Operand,
    pub y: Operand,
}

pub(crate) fn decode(value: i32) -> Option<Bounds> {
    let value = u32::try_from(value).ok()?;
    let code = (value % 9) as u8;
    let mut bits = value / 9;
    let x_register = bits & 1 != 0;
    let y_register = bits & 2 != 0;
    bits >>= 2;
    let signed = x_register && bits & 1 != 0;
    if x_register {
        bits >>= 1;
    }
    let mut operand = |register| {
        let width = if register { 4 } else { 5 };
        let value = (bits & ((1 << width) - 1)) as u8;
        bits >>= width;
        if register {
            Operand::Register(value)
        } else {
            Operand::Constant(value)
        }
    };
    let x = operand(x_register);
    let y = operand(y_register);
    (bits == 0).then_some(Bounds { code, signed, x, y })
}

#[derive(Deserialize, Serialize)]
pub(crate) struct Span {
    pub start: u64,
    pub end: u64,
    pub bounds: Bounds,
}

fn varint(bytes: &mut &[u8]) -> Option<u32> {
    let mut result = 0;
    for shift in (0..35).step_by(7) {
        let (&byte, rest) = bytes.split_first()?;
        *bytes = rest;
        if shift == 28 && byte > 15 {
            return None;
        }
        result |= u32::from(byte & 127) << shift;
        if byte & 128 == 0 {
            return Some(result);
        }
    }
    None
}

fn runs(mut bytes: &[u8], size: u64, budget: &mut usize) -> Option<Vec<(u64, u64, i32)>> {
    let mut result = Vec::new();
    let (mut pc, mut value) = (0u64, -1i32);
    for step in 0..65_536 {
        *budget = budget.checked_sub(1)?;
        let delta = varint(&mut bytes)?;
        if delta == 0 && step != 0 {
            return Some(result);
        }
        value = value.checked_add(((delta >> 1) as i32) ^ -((delta & 1) as i32))?;
        let end = pc.checked_add(u64::from(varint(&mut bytes)?))?;
        if end > size {
            return None;
        }
        if end > pc {
            result.push((pc, end, value));
        }
        pc = end;
        if pc == size {
            return Some(result);
        }
    }
    None
}

/// Modern amd64 _func headers and PCDATA_PanicBounds (Go 1.26–1.27).
pub(crate) fn read(table: &Pclntab<'_>) -> BTreeMap<u64, Vec<Span>> {
    let mut result = BTreeMap::new();
    let mut budget = 100_000;
    if !table.magic_is_official() || table.quantum() != 1 || !table.little_endian() {
        return result;
    }
    for function in table.functions_with_offsets().unwrap_or_default() {
        if budget == 0 {
            break;
        }
        if !table
            .func_fields(&function)
            .is_some_and(|fields| fields.npcdata > 4)
        {
            continue;
        }
        let spans = (|| {
            let offset = table
                .funcdata_off()
                .checked_add(function.func_off)?
                .checked_add(44 + 4 * 4)?;
            let offset = u32::from_le_bytes(
                table
                    .data()
                    .get(offset..offset.checked_add(4)?)?
                    .try_into()
                    .ok()?,
            );
            if offset == 0 {
                return None;
            }
            let bytes = table
                .data()
                .get(table.pctab_off().checked_add(offset as usize)?..)?;
            let decoded = runs(bytes, function.size, &mut budget)?;
            Some(
                decoded
                    .into_iter()
                    .filter_map(|(start, end, value)| {
                        Some(Span {
                            start: function.address.checked_add(start)?,
                            end: function.address.checked_add(end)?,
                            bounds: decode(value)?,
                        })
                    })
                    .collect::<Vec<_>>(),
            )
        })();
        if let Some(spans) = spans.filter(|spans| !spans.is_empty()) {
            result.insert(function.address, spans);
        }
    }
    result
}

pub(crate) fn signature(arch: CoreArchitecture, bounds: Bounds) -> Option<Ref<Type>> {
    let mut parameters = Vec::new();
    for (operand, name, signed) in [
        (bounds.x, "index", bounds.signed),
        (bounds.y, "limit", true),
    ] {
        let Operand::Register(index) = operand else {
            continue;
        };
        let register = *REGISTERS.get(index as usize)?;
        if matches!(register, "rsp" | "r14") {
            return None;
        }
        parameters.push(FunctionParameter {
            ty: Type::int(8, signed).into(),
            name: name.into(),
            location: ValueLocationSource::Custom(runtime::location(arch, register, 8)?),
        });
    }
    let ty = Type::function_with_opts(
        Type::void().as_ref(),
        &parameters,
        false,
        convention::amd64()?.clone(),
        Conf::new(0, 255),
    );
    let builder = TypeBuilder::new(&ty);
    builder.set_can_return(false);
    Some(builder.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_reserved_encodings_and_truncated_pcdata() {
        assert_eq!(decode(-1), None);
        assert_eq!(decode(36_864), None);
        assert_eq!(
            decode(3663),
            Some(Bounds {
                code: 0,
                signed: true,
                x: Operand::Register(2),
                y: Operand::Register(3)
            })
        );
        assert!(runs(&[2], 8, &mut 10).is_none());
        assert!(runs(&[2, 9], 8, &mut 10).is_none());
        assert!(runs(&[2, 8], 8, &mut 0).is_none());
        assert!(varint(&mut &[255, 255, 255, 255, 16][..]).is_none());
    }

    #[test]
    #[ignore = "requires JSON produced by Go's internal/abi.BoundsDecode"]
    fn official_decoder_oracle() {
        let path =
            std::env::var("GO_BOUNDS_ORACLE").expect("set GO_BOUNDS_ORACLE to the oracle JSON");
        let rows: Vec<Vec<u8>> = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(rows.len(), 36_864);
        for (value, row) in rows.iter().enumerate() {
            let decoded = decode(value as i32);
            assert_eq!(decoded.is_some(), row[0] != 0, "{value}");
            if let Some(bounds) = decoded {
                let operand = |register, value| {
                    if register != 0 {
                        Operand::Register(value)
                    } else {
                        Operand::Constant(value)
                    }
                };
                assert_eq!(
                    bounds,
                    Bounds {
                        code: row[1],
                        signed: row[2] != 0,
                        x: operand(row[3], row[5]),
                        y: operand(row[4], row[6])
                    },
                    "{value}"
                );
            }
        }
    }
}
