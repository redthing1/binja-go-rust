//! amd64 ABIInternal allocation. Offsets are relative to callee-entry RSP.

#[derive(Clone, Debug)]
pub(crate) struct Shape {
    pub size: u64,
    pub alignment: u64,
    pub kind: Kind,
}

#[derive(Clone, Debug)]
pub(crate) enum Kind {
    Integer,
    Float,
    Fields(Vec<(u64, Shape)>),
    Array { element: Box<Shape>, count: u64 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Storage {
    Integer(u8),
    Float(u8),
    Stack(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Part {
    pub offset: u64,
    pub size: u64,
    pub storage: Storage,
}

pub(crate) struct Layout {
    pub parameters: Vec<Vec<Part>>,
    pub results: Vec<Vec<Part>>,
    pub spills: Vec<(usize, u64)>,
    pub stack_size: u64,
}

#[derive(Default)]
struct Allocator {
    integers: u8,
    floats: u8,
    stack: u64,
    abi0: bool,
}

fn align(value: u64, alignment: u64) -> Result<u64, String> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return Err("invalid ABI alignment".into());
    }
    value
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
        .ok_or_else(|| "ABI stack overflow".into())
}

impl Allocator {
    /// None means this value must be passed on the stack; assignment rolls back both banks.
    fn flatten(&mut self, shape: &Shape, offset: u64, parts: &mut Vec<Part>) -> Option<()> {
        match &shape.kind {
            Kind::Integer => {
                if shape.size > 16 {
                    return None;
                }
                for start in (0..shape.size).step_by(8) {
                    if self.abi0 || self.integers == 9 {
                        return None;
                    }
                    parts.push(Part {
                        offset: offset + start,
                        size: (shape.size - start).min(8),
                        storage: Storage::Integer(self.integers),
                    });
                    self.integers += 1;
                }
            }
            Kind::Float => {
                if self.abi0 || self.floats == 15 || !matches!(shape.size, 4 | 8) {
                    return None;
                }
                parts.push(Part {
                    offset,
                    size: shape.size,
                    storage: Storage::Float(self.floats),
                });
                self.floats += 1;
            }
            Kind::Fields(fields) => {
                for (field_offset, field) in fields {
                    self.flatten(field, offset + field_offset, parts)?;
                }
            }
            Kind::Array { element, count } => match count {
                0 => (),
                1 => self.flatten(element, offset, parts)?,
                _ => return None,
            },
        }
        Some(())
    }

    fn assign(&mut self, shape: &Shape) -> Result<Vec<Part>, String> {
        let saved = (self.integers, self.floats);
        let mut parts = Vec::new();
        if shape.size != 0 && self.flatten(shape, 0, &mut parts).is_some() {
            return Ok(parts);
        }
        (self.integers, self.floats) = saved;
        self.stack = align(self.stack, shape.alignment)?;
        let storage = Storage::Stack(self.stack.checked_add(8).ok_or("ABI stack overflow")?);
        self.stack = self
            .stack
            .checked_add(shape.size)
            .ok_or("ABI stack overflow")?;
        Ok(vec![Part {
            offset: 0,
            size: shape.size,
            storage,
        }])
    }
}

pub(crate) fn layout(
    parameters: &[Shape],
    results: &[Shape],
    abi0: bool,
) -> Result<Layout, String> {
    let mut allocator = Allocator {
        abi0,
        ..Allocator::default()
    };
    let arguments = parameters
        .iter()
        .map(|shape| allocator.assign(shape))
        .collect::<Result<Vec<_>, _>>()?;
    allocator.stack = align(allocator.stack, 8)?;
    allocator.integers = 0;
    allocator.floats = 0;
    let results = results
        .iter()
        .map(|shape| allocator.assign(shape))
        .collect::<Result<_, _>>()?;
    allocator.stack = align(allocator.stack, 8)?;
    let mut spills = Vec::new();
    for (index, (shape, parts)) in parameters.iter().zip(&arguments).enumerate() {
        if !parts.is_empty()
            && parts
                .iter()
                .all(|part| !matches!(part.storage, Storage::Stack(_)))
        {
            allocator.stack = align(allocator.stack, shape.alignment)?;
            spills.push((
                index,
                allocator.stack.checked_add(8).ok_or("ABI spill overflow")?,
            ));
            allocator.stack = allocator
                .stack
                .checked_add(shape.size)
                .ok_or("ABI spill overflow")?;
        }
    }
    Ok(Layout {
        parameters: arguments,
        results,
        spills,
        stack_size: align(allocator.stack, 8)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn word() -> Shape {
        Shape {
            size: 8,
            alignment: 8,
            kind: Kind::Integer,
        }
    }

    #[test]
    fn aggregate_exhaustion_rolls_back_both_register_banks() {
        let float = Shape {
            kind: Kind::Float,
            ..word()
        };
        let pair = Shape {
            size: 24,
            alignment: 8,
            kind: Kind::Fields(vec![(0, float.clone()), (8, word()), (16, word())]),
        };
        let mut parameters = vec![word(); 8];
        parameters.extend([pair, word(), float]);
        let result = layout(&parameters, &[], false).unwrap();
        assert_eq!(result.parameters[8][0].storage, Storage::Stack(8));
        assert_eq!(result.parameters[9][0].storage, Storage::Integer(8));
        assert_eq!(result.parameters[10][0].storage, Storage::Float(0));
    }

    #[test]
    fn results_reset_registers_and_follow_stack_arguments_before_spills() {
        let array = Shape {
            size: 16,
            alignment: 8,
            kind: Kind::Array {
                element: Box::new(word()),
                count: 2,
            },
        };
        let result = layout(&[word(), array.clone()], &[word(), array], false).unwrap();
        assert_eq!(result.parameters[0][0].storage, Storage::Integer(0));
        assert_eq!(result.results[0][0].storage, Storage::Integer(0));
        assert_eq!(result.results[1][0].storage, Storage::Stack(24));
        assert_eq!(result.spills, vec![(0, 40)]);
        assert_eq!(result.stack_size, 40);
    }

    #[test]
    fn abi0_and_zero_size_values_use_the_stack() {
        let zero = Shape {
            size: 0,
            alignment: 8,
            kind: Kind::Fields(Vec::new()),
        };
        let result = layout(&[zero, word()], &[word()], true).unwrap();
        assert_eq!(result.parameters[0][0].size, 0);
        assert_eq!(result.parameters[1][0].storage, Storage::Stack(8));
        assert_eq!(result.results[0][0].storage, Storage::Stack(16));
        assert!(result.spills.is_empty());
    }
}
