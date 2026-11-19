use super::control::Control;
use super::*;

struct Origin {
    place: Place,
    guards: Vec<Guard>,
    uncertain: bool,
    fresh: bool,
}

struct Reader<'a, 'b> {
    origins: &'a Origins<'b>,
    control: &'a Control,
    at: &'a binaryninja::medium_level_il::MediumLevelILInstruction,
    budget: &'a mut Budget,
}

impl Reader<'_, '_> {
    fn spend(&mut self, depth: usize) -> Result<bool, Status> {
        self.budget.expressions = self
            .budget
            .expressions
            .checked_sub(1)
            .ok_or(Status::Limit)?;
        Ok(depth < 32)
    }

    fn unique(&self, place: Place, fresh: bool) -> Vec<Origin> {
        vec![Origin {
            place,
            guards: Vec::new(),
            uncertain: false,
            fresh,
        }]
    }

    fn variable(
        &mut self,
        variable: SSAVariable,
        depth: usize,
    ) -> Result<Option<Vec<Origin>>, Status> {
        if !self.spend(depth)? {
            return Ok(None);
        }
        let memory = self.at.ssa_memory_version() as u64;
        if let Some(place) = self.origins.variable(variable, 0, None) {
            return Ok(Some(self.unique(
                place,
                self.origins.variable(variable, 0, Some(memory)).is_some(),
            )));
        }
        match self.origins.definitions.get(&variable) {
            Some(Definition::Assign(index)) => self.expression(*index, depth + 1),
            Some(Definition::Merge(sources)) => {
                let Some(phi) = self.origins.il.ssa_variable_definition(&variable) else {
                    return Ok(None);
                };
                let Some(block) = phi.basic_block() else {
                    return Ok(None);
                };
                let edges = block.incoming_edges();
                if edges.is_empty() || edges.len() > 256 {
                    return Ok(None);
                }
                let mut result = Vec::new();
                for edge in edges.iter() {
                    let Some(last) = edge.source.end_index().0.checked_sub(1).and_then(|index| {
                        self.origins
                            .il
                            .instruction_from_index(InstructionIndex(index))
                    }) else {
                        return Ok(None);
                    };
                    // Query the edge's actual version; operand order is not predecessor order.
                    let incoming = last.ssa_variable_version_after(variable.variable);
                    if !sources.contains(&incoming) {
                        return Ok(None);
                    }
                    let Some(mut choices) = self.variable(incoming, depth + 1)? else {
                        return Ok(None);
                    };
                    let guards = self.control.at(&last);
                    let fresh = self.control.memory.epoch(last.ssa_memory_version() as u64)
                        == self.control.memory.epoch(memory);
                    for choice in &mut choices {
                        choice.uncertain |= self.control.uncertain(&last)
                            || (!fresh && guards.iter().any(|guard| guard.selector.loaded));
                        choice.guards.extend(
                            guards
                                .iter()
                                .filter(|guard| fresh || !guard.selector.loaded)
                                .cloned(),
                        );
                    }
                    result.extend(choices);
                    if result.len() > 256 {
                        return Err(Status::Limit);
                    }
                }
                // An unqualified choice cannot establish a global pointee role.
                if result.iter().any(|choice| choice.guards.is_empty()) {
                    for choice in &mut result {
                        choice.uncertain = true;
                    }
                }
                Ok(Some(result))
            }
            _ => Ok(None),
        }
    }

    fn expression(&mut self, index: Index, depth: usize) -> Result<Option<Vec<Origin>>, Status> {
        if !self.spend(depth)? {
            return Ok(None);
        }
        let memory = self.at.ssa_memory_version() as u64;
        if let Some(place) = self.origins.place(index, 0) {
            return Ok(Some(self.unique(
                place,
                self.origins.place_in(index, 0, Some(memory)).is_some(),
            )));
        }
        let Some(instruction) = self.origins.il.instruction_from_expr_index(index) else {
            return Ok(None);
        };
        let (source, offset, load) = match instruction.kind {
            Op::VarSsa(op) if instruction.size == self.origins.pointer_width => {
                return self.variable(op.src, depth + 1);
            }
            Op::LoadSsa(op) if instruction.size == self.origins.pointer_width => {
                (op.src, 0, Some(op.src_memory))
            }
            Op::LoadStructSsa(op) if instruction.size == self.origins.pointer_width => {
                let Ok(offset) = i64::try_from(op.offset) else {
                    return Ok(None);
                };
                (op.src, offset, Some(op.src_memory))
            }
            Op::Add(op) | Op::Sub(op) => {
                let Some(right) = self.origins.il.instruction_from_expr_index(op.right) else {
                    return Ok(None);
                };
                let Op::Const(value) = right.kind else {
                    return Ok(None);
                };
                let offset = match instruction.size {
                    4 => i64::from(value.constant as u32 as i32),
                    8 => value.constant as i64,
                    _ => return Ok(None),
                };
                let offset = if matches!(instruction.kind, Op::Sub(_)) {
                    let Some(offset) = offset.checked_neg() else {
                        return Ok(None);
                    };
                    offset
                } else {
                    offset
                };
                (op.left, offset, None)
            }
            _ => return Ok(None),
        };
        let Some(mut choices) = self.expression(source, depth + 1)? else {
            return Ok(None);
        };
        for choice in &mut choices {
            let Some(place) = choice.place.shift(offset).and_then(|place| {
                if load.is_some() {
                    place.load()
                } else {
                    Some(place)
                }
            }) else {
                return Ok(None);
            };
            choice.place = place;
            choice.fresh &= load.is_none_or(|version| {
                self.control.memory.epoch(version) == self.control.memory.epoch(memory)
            });
        }
        Ok(Some(choices))
    }
}

/// Observe each qualified incoming address when a compiler merges pointer/scalar loads.
pub(super) fn accesses(
    origins: &Origins<'_>,
    control: &Control,
    instruction: &binaryninja::medium_level_il::MediumLevelILInstruction,
    index: Index,
    offset: u64,
    budget: &mut Budget,
) -> Result<Vec<Access>, Status> {
    let mut reader = Reader {
        origins,
        control,
        at: instruction,
        budget,
    };
    let Some(choices) = reader.expression(index, 0)? else {
        return Ok(Vec::new());
    };
    let mut result = BTreeSet::new();
    for mut choice in choices {
        choice.guards.extend(control.at(instruction));
        let stale = !choice.fresh && choice.guards.iter().any(|guard| guard.selector.loaded);
        if !choice.fresh {
            choice.guards.retain(|guard| !guard.selector.loaded);
        }
        let Some(guards) = crate::rust::layout::guards(choice.guards)? else {
            continue;
        };
        result.insert(Access {
            place: choice
                .place
                .shift(i64::try_from(offset).map_err(|_| Status::Limit)?)
                .ok_or(Status::Limit)?,
            width: instruction.size,
            guards,
            uncertain: choice.uncertain || stale || control.uncertain(instruction),
        });
    }
    Ok(result.into_iter().collect())
}
