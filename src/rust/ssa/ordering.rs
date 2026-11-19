use super::{
    Op,
    control::{Condition, Value},
};
use crate::rust::layout::Guard;

/// Convert a bounded side of an integer ordering to the existing finite guard.
#[derive(Clone, Copy)]
pub(super) struct Order {
    signed: bool,
    lower: bool,
    inclusive: bool,
}

impl Order {
    pub fn from_op(op: &Op) -> Option<Self> {
        let (signed, lower, inclusive) = match op {
            Op::CmpUlt(_) => (false, true, false),
            Op::CmpUle(_) => (false, true, true),
            Op::CmpUgt(_) => (false, false, false),
            Op::CmpUge(_) => (false, false, true),
            Op::CmpSlt(_) => (true, true, false),
            Op::CmpSle(_) => (true, true, true),
            Op::CmpSgt(_) => (true, false, false),
            Op::CmpSge(_) => (true, false, true),
            _ => return None,
        };
        Some(Self {
            signed,
            lower,
            inclusive,
        })
    }

    pub fn reversed(self) -> Self {
        Self {
            lower: !self.lower,
            ..self
        }
    }

    fn integer(&self, value: u64, width: usize) -> i128 {
        let domain = 1i128 << (width * 8);
        let value = i128::from(value) & (domain - 1);
        if self.signed && value >= domain / 2 {
            value - domain
        } else {
            value
        }
    }

    pub fn evaluate(&self, left: u64, right: u64, width: usize) -> bool {
        let left = self.integer(left, width);
        let right = self.integer(right, width);
        if self.lower {
            if self.inclusive {
                left <= right
            } else {
                left < right
            }
        } else if self.inclusive {
            left >= right
        } else {
            left > right
        }
    }

    pub fn condition(
        &self,
        value: Value,
        constant: u64,
        width: usize,
        taken: bool,
    ) -> Option<Condition> {
        if ![1, 2, 4, 8].contains(&width)
            || value.selector.width == 0
            || value.selector.width > width
        {
            return None;
        }
        let domain = 1i128 << (value.selector.width * 8);
        let comparison_domain = 1i128 << (width * 8);
        let threshold = self.integer(constant, width) + i128::from(self.inclusive == self.lower);
        let split = if self.signed {
            comparison_domain / 2
        } else {
            comparison_domain
        };
        let mut lower = Vec::new();
        let mut upper = Vec::new();
        for (start, end, offset) in [
            (0, domain.min(split), 0),
            (split, domain, comparison_domain),
        ] {
            if start >= end {
                continue;
            }
            let cut = (threshold + offset).clamp(start, end);
            lower.push(start..cut);
            upper.push(cut..end);
        }
        let lower_count: i128 = lower.iter().map(|range| range.end - range.start).sum();
        if lower_count == 0 || lower_count == domain {
            return None;
        }
        let selected_lower = lower_count <= domain - lower_count;
        if lower_count.min(domain - lower_count) > 256 {
            return None;
        }
        let values = if selected_lower { lower } else { upper };
        Some(Condition {
            guard: Guard {
                selector: value.selector,
                values: values
                    .into_iter()
                    .flatten()
                    .map(|value| value as u64)
                    .collect(),
                is_in: (self.lower == selected_lower) == taken,
            },
            memory: value.memory,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rust::layout::{Place, Selector};
    use std::collections::BTreeSet;

    fn value(width: usize) -> Value {
        Value {
            selector: Selector {
                place: Place::parameter(0),
                width,
                loaded: false,
            },
            memory: None,
        }
    }

    #[test]
    fn finite_guards_match_every_byte_ordering() {
        for signed in [false, true] {
            for lower in [false, true] {
                for inclusive in [false, true] {
                    let order = Order {
                        signed,
                        lower,
                        inclusive,
                    };
                    for constant in 0..=255u64 {
                        let expected: Vec<_> = (0..=255u64)
                            .map(|input| {
                                let (a, b) = if signed {
                                    (input as u8 as i8 as i128, constant as u8 as i8 as i128)
                                } else {
                                    (i128::from(input), i128::from(constant))
                                };
                                match (lower, inclusive) {
                                    (true, false) => a < b,
                                    (true, true) => a <= b,
                                    (false, false) => a > b,
                                    (false, true) => a >= b,
                                }
                            })
                            .collect();
                        for taken in [false, true] {
                            let condition = order.condition(value(1), constant, 1, taken);
                            if expected.iter().all(|answer| *answer == expected[0]) {
                                assert!(condition.is_none());
                            } else {
                                let guard = condition.unwrap().guard;
                                for (input, answer) in expected.iter().enumerate() {
                                    assert_eq!(
                                        guard.values.contains(&(input as u64)) == guard.is_in,
                                        *answer == taken
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn zero_extension_keeps_the_comparison_signedness_at_its_operand_width() {
        let order = Order {
            signed: true,
            lower: true,
            inclusive: false,
        };
        assert!(order.condition(value(1), 0, 8, true).is_none());
        let guard = order.condition(value(1), 253, 8, true).unwrap().guard;
        for input in 0..=255u64 {
            assert_eq!(guard.values.contains(&input) == guard.is_in, input < 253);
        }
        let reversed = order
            .reversed()
            .condition(value(1), 253, 8, true)
            .unwrap()
            .guard;
        for input in 0..=255u64 {
            assert_eq!(
                reversed.values.contains(&input) == reversed.is_in,
                253 < input
            );
        }
    }

    #[test]
    fn word_ranges_are_bounded_without_truncating_large_or_signed_domains() {
        let unsigned = Order {
            signed: false,
            lower: true,
            inclusive: false,
        };
        assert_eq!(
            unsigned
                .condition(value(8), 256, 8, true)
                .unwrap()
                .guard
                .values
                .len(),
            256
        );
        assert!(unsigned.condition(value(8), 257, 8, true).is_none());
        assert!(unsigned.condition(value(8), 3, 4, true).is_none());
        let signed = Order {
            signed: true,
            ..unsigned
        };
        assert!(signed.condition(value(8), 0, 8, true).is_none());
        let first = i64::MIN as u64;
        assert_eq!(
            signed
                .condition(value(8), first + 3, 8, true)
                .unwrap()
                .guard
                .values,
            BTreeSet::from([first, first + 1, first + 2])
        );
    }
}
