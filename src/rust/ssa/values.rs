use super::control::{Condition, Value};
use super::ordering::Order;
use super::*;
use crate::rust::layout::{self, MAX_GUARDS, Root, Selector};

/// Observed words and finite encodings, qualified by the consumed return width.
#[derive(Clone, Eq, PartialEq)]
enum Term {
    Constant(u64),
    Value(Value),
    Bits(Condition, u64, u64),
}

impl Term {
    fn bits(condition: Condition, yes: u64, no: u64) -> Self {
        match (yes, no) {
            _ if yes == no => Self::Constant(yes),
            (0, 1) => Self::Bits(condition.invert(), 1, 0),
            _ => Self::Bits(condition, yes, no),
        }
    }

    fn outcome(&self, candidate: &Condition, taken: bool, context: &[Condition]) -> Option<u64> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Bits(condition, yes, no) => {
                let selected = if condition == candidate {
                    Some(taken)
                } else if *condition == candidate.invert() {
                    Some(!taken)
                } else if context.iter().any(|known| {
                    known.memory == condition.memory
                        && condition
                            .guard
                            .implied_by(std::slice::from_ref(&known.guard))
                }) {
                    Some(true)
                } else if context.iter().any(|known| {
                    known.memory == condition.memory
                        && condition
                            .invert()
                            .guard
                            .implied_by(std::slice::from_ref(&known.guard))
                }) {
                    Some(false)
                } else {
                    None
                }?;
                Some(if selected { *yes } else { *no })
            }
            _ => None,
        }
    }

    fn independent(&self) -> bool {
        let (selector, memory) = match self {
            Self::Constant(_) => return true,
            Self::Value(value) => (&value.selector, value.memory),
            Self::Bits(condition, _, _) => (&condition.guard.selector, condition.memory),
        };
        memory.is_none()
            && !selector.loaded
            && selector.place.path == [0]
            && matches!(selector.place.root, Root::Parameter(_))
    }

    fn binary(left: Self, right: Self, apply: impl Fn(u64, u64) -> u64) -> Option<Self> {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            return Some(Self::Constant(apply(*left, *right)));
        }
        let candidate = match (&left, &right) {
            (Self::Bits(condition, _, _), _) | (_, Self::Bits(condition, _, _)) => condition,
            _ => return None,
        };
        Some(Self::bits(
            candidate.clone(),
            apply(
                left.outcome(candidate, true, &[])?,
                right.outcome(candidate, true, &[])?,
            ),
            apply(
                left.outcome(candidate, false, &[])?,
                right.outcome(candidate, false, &[])?,
            ),
        ))
    }
}

fn join(choices: &[(Term, Vec<Condition>)]) -> Option<Term> {
    let first = choices.first()?.0.clone();
    if choices.iter().all(|(value, _)| *value == first) {
        return Some(first);
    }
    let mut candidates = BTreeSet::new();
    for (value, context) in choices {
        if let Term::Bits(condition, _, _) = value {
            candidates.insert(condition.clone());
        }
        candidates.extend(context.iter().cloned());
    }
    'candidate: for candidate in candidates {
        let mut outcomes = Vec::new();
        for taken in [true, false] {
            let mut values = BTreeSet::new();
            for (value, context) in choices {
                let selected = if taken {
                    candidate.clone()
                } else {
                    candidate.invert()
                };
                if context.iter().any(|known| {
                    known.memory == selected.memory && known.guard.contradicts(&selected.guard)
                }) {
                    continue;
                }
                let Some(value) = value.outcome(&candidate, taken, context) else {
                    continue 'candidate;
                };
                values.insert(value);
            }
            if values.len() != 1 {
                continue 'candidate;
            }
            outcomes.push(*values.first()?);
        }
        return Some(Term::bits(candidate, outcomes[0], outcomes[1]));
    }
    None
}

pub(super) struct Facts<'a> {
    sources: &'a BTreeMap<Key, Source>,
    writes: &'a BTreeMap<Key, bool>,
    summaries: BTreeMap<(Key, usize), Term>,
    active: BTreeSet<(Key, usize)>,
    budget: &'a mut Budget,
    cancelled: &'a dyn Fn() -> bool,
    status: Option<Status>,
}

impl Facts<'_> {
    fn spend(&mut self, amount: usize) -> bool {
        if self.status.is_some() {
            return false;
        }
        if (self.cancelled)() {
            self.status = Some(Status::Cancelled);
            return false;
        }
        let Some(remaining) = self.budget.expressions.checked_sub(amount) else {
            self.status = Some(Status::Limit);
            return false;
        };
        self.budget.expressions = remaining;
        true
    }

    fn checked<T>(&mut self, result: Result<T, Status>) -> Option<T> {
        match result {
            Ok(value) => Some(value),
            Err(status) => {
                self.status = Some(status);
                None
            }
        }
    }

    pub fn check(&self) -> Result<(), Status> {
        self.status.map_or(Ok(()), Err)
    }

    pub fn dependencies(
        &mut self,
        source: &Source,
        index: InstructionIndex,
    ) -> Vec<(InstructionIndex, bool)> {
        if !self.spend(1) {
            return Vec::new();
        }
        let result = source.ssa.dependencies(index, self.budget);
        self.checked(result).unwrap_or_default()
    }

    fn context(
        &mut self,
        source: &Source,
        index: InstructionIndex,
        depth: usize,
    ) -> Vec<Condition> {
        if depth >= 32 {
            return Vec::new();
        }
        let mut result = Vec::new();
        for (index, taken) in self.dependencies(source, index) {
            if let Some(instruction) = source.ssa.il.instruction_from_index(index)
                && let Op::If(op) = instruction.kind
                && let Some(condition) = self.condition(source, op.condition, taken, depth + 1)
            {
                result.push(condition);
            }
        }
        result.sort();
        result.dedup();
        if result.len() > MAX_GUARDS {
            self.status = Some(Status::Limit);
            result.clear();
        }
        result
    }

    pub fn condition(
        &mut self,
        source: &Source,
        index: Index,
        taken: bool,
        depth: usize,
    ) -> Option<Condition> {
        match self.value(source, index, None, depth + 1)? {
            Term::Bits(condition, yes, no) if (yes != 0) != (no != 0) => {
                Some(if (yes != 0) == taken {
                    condition
                } else {
                    condition.invert()
                })
            }
            Term::Value(value) => Some(Condition {
                guard: Guard {
                    selector: value.selector,
                    values: BTreeSet::from([0]),
                    is_in: !taken,
                },
                memory: value.memory,
            }),
            _ => None,
        }
    }

    fn summary(&mut self, source: &Source, width: usize) -> Option<Term> {
        let key = (source.input.key.clone(), width);
        if let Some(summary) = self.summaries.get(&key) {
            return Some(summary.clone());
        }
        if self.active.len() >= 32 || !self.active.insert(key.clone()) {
            return None;
        }
        // A callee's summary is independent of the caller's local SSA traversal depth.
        let result = (|| {
            let mut choices = Vec::new();
            for index in 0..source.ssa.il.instruction_count() {
                if !self.spend(1) {
                    return None;
                }
                let instruction = source
                    .ssa
                    .il
                    .instruction_from_index(InstructionIndex(index))?;
                match instruction.kind {
                    Op::Ret(_) => {
                        let result = source.ssa.expressions(instruction.expr_index, 0);
                        let values = self.checked(result)?;
                        if !self.spend(values.len()) {
                            return None;
                        }
                        let [value] = values.as_slice() else {
                            return None;
                        };
                        if source.ssa.il.instruction_from_expr_index(*value)?.size < width {
                            return None;
                        }
                        let value = self.value(source, *value, Some(width), 0)?;
                        let memory = source
                            .origins
                            .memory
                            .epoch(instruction.ssa_memory_version() as u64);
                        let mut context = self.context(source, instruction.instr_index, 0);
                        context.retain(|condition| condition.memory.is_none_or(|m| m == memory));
                        choices.push((value, context));
                        if choices.len() > 256 {
                            self.status = Some(Status::Limit);
                            return None;
                        }
                    }
                    Op::TailcallSsa(_) => {
                        let value = self.call(source, &instruction, width, 0)?;
                        choices.push((value, self.context(source, instruction.instr_index, 0)));
                    }
                    Op::TailcallUntypedSsa(_) => return None,
                    _ => (),
                }
            }
            let result = join(&choices)?;
            if self.writes[&source.input.key] && !result.independent() {
                return None;
            }
            Some(result)
        })();
        self.active.remove(&key);
        if let Some(value) = &result {
            self.summaries.insert(key, value.clone());
        }
        result
    }

    fn bind(
        &mut self,
        source: &Source,
        call: &Call,
        instruction: &binaryninja::medium_level_il::MediumLevelILInstruction,
        value: Value,
        depth: usize,
    ) -> Option<Term> {
        let Root::Parameter(parameter) = value.selector.place.root else {
            return None;
        };
        let op = match instruction.kind {
            Op::CallSsa(op) | Op::TailcallSsa(op) => op,
            _ => return None,
        };
        let result = source.ssa.expressions(instruction.expr_index, 2);
        let arguments = self.checked(result)?;
        let count = if call.parameter_order.is_empty() {
            call.parameters.len()
        } else {
            call.parameter_order.len()
        };
        if arguments.len() != count || !self.spend(arguments.len()) {
            return None;
        }
        let parameter = if call.parameter_order.is_empty() {
            parameter
        } else {
            call.parameter_order
                .iter()
                .position(|original| *original == parameter)?
        };
        let argument = *arguments.get(parameter)?;
        let selector = &value.selector;
        if !selector.loaded {
            if selector.place.path != [0] {
                return None;
            }
            return self.value(source, argument, Some(selector.width), depth + 1);
        }
        let place = source.origins.place_in(argument, 0, Some(op.src_memory))?;
        let place = selector.place.through(&place).ok()?;
        let mut value = value;
        value.selector.place = place;
        value.memory = Some(source.origins.memory.epoch(op.src_memory));
        Some(Term::Value(value))
    }

    fn call(
        &mut self,
        source: &Source,
        instruction: &binaryninja::medium_level_il::MediumLevelILInstruction,
        width: usize,
        depth: usize,
    ) -> Option<Term> {
        let mut calls = source
            .input
            .calls
            .iter()
            .filter(|call| call.address == instruction.address);
        let call = calls.next()?;
        if call.adjusted || calls.next().is_some() {
            return None;
        }
        let callee = self.sources.get(call.target.as_ref()?)?;
        if (callee.input.parameters.len(), callee.input.pointer_width)
            != (call.parameters.len(), source.input.pointer_width)
        {
            return None;
        }
        if matches!(instruction.kind, Op::TailcallSsa(_)) && !tail_compatible(source, callee, width)
        {
            return None;
        }
        match self.summary(callee, width)? {
            Term::Constant(value) => Some(Term::Constant(value)),
            Term::Value(value) => self.bind(source, call, instruction, value, depth + 1),
            Term::Bits(condition, yes, no) => {
                if !self.spend(condition.guard.values.len()) {
                    return None;
                }
                let value = Value {
                    selector: condition.guard.selector.clone(),
                    memory: condition.memory,
                };
                let mapped = self.bind(source, call, instruction, value, depth + 1)?;
                match self.membership(mapped, &condition.guard.values, condition.guard.is_in)? {
                    Term::Constant(value) => {
                        Some(Term::Constant(if value != 0 { yes } else { no }))
                    }
                    Term::Bits(condition, a, b) => Some(Term::bits(
                        condition,
                        if a != 0 { yes } else { no },
                        if b != 0 { yes } else { no },
                    )),
                    _ => None,
                }
            }
        }
    }

    fn variable(
        &mut self,
        source: &Source,
        variable: SSAVariable,
        width: usize,
        depth: usize,
    ) -> Option<Term> {
        self.variable_field(source, variable, 0, width, depth)
    }

    fn value_field(
        &mut self,
        source: &Source,
        index: Index,
        offset: u64,
        width: usize,
        depth: usize,
    ) -> Option<Term> {
        if offset == 0 {
            return self.value(source, index, Some(width), depth);
        }
        if depth >= 32 || !source.input.little_endian || !self.spend(1) {
            return None;
        }
        let instruction = source.ssa.il.instruction_from_expr_index(index)?;
        if offset.checked_add(width as u64)? > instruction.size as u64 {
            return None;
        }
        match instruction.kind {
            Op::VarSsa(op) => self.variable_field(source, op.src, offset, width, depth + 1),
            Op::VarSsaField(op) => self.variable_field(
                source,
                op.src,
                op.offset.checked_add(offset)?,
                width,
                depth + 1,
            ),
            Op::Const(op) if offset.checked_add(width as u64)? <= 8 => Some(Term::Constant(
                (op.constant >> (offset * 8)) & (u64::MAX >> (64 - width * 8)),
            )),
            _ => None,
        }
    }

    fn variable_field(
        &mut self,
        source: &Source,
        variable: SSAVariable,
        offset: u64,
        width: usize,
        depth: usize,
    ) -> Option<Term> {
        if depth >= 32 || !self.spend(1) {
            return None;
        }
        if variable.version == 0 {
            if offset != 0 {
                return None;
            }
            return Some(Term::Value(Value {
                selector: Selector {
                    place: Place::parameter(*source.origins.parameters.get(&variable.variable)?),
                    width,
                    loaded: false,
                },
                memory: None,
            }));
        }
        let instruction = source.ssa.il.ssa_variable_definition(&variable)?;
        match instruction.kind {
            Op::Undef => self.variable_field(
                source,
                source.ssa.forced_source(instruction.expr_index, variable)?,
                offset,
                width,
                depth + 1,
            ),
            Op::SetVarSsa(op) if instruction.size as u64 >= offset.checked_add(width as u64)? => {
                self.value_field(source, op.src, offset, width, depth + 1)
            }
            Op::SetVarSsaField(op)
                if source.input.little_endian
                    && op.offset <= offset
                    && offset.checked_add(width as u64)?
                        <= op.offset.checked_add(instruction.size as u64)? =>
            {
                self.value_field(source, op.src, offset - op.offset, width, depth + 1)
            }
            Op::SetVarSsaField(op)
                if source.input.little_endian
                    && (op.offset >= offset.checked_add(width as u64)?
                        || op.offset.checked_add(instruction.size as u64)? <= offset) =>
            {
                self.variable_field(source, op.prev, offset, width, depth + 1)
            }
            Op::CallSsa(_) if offset == 0 => {
                source.input.calls.iter().find(|call| {
                    call.address == instruction.address
                        && call.output == Some(variable.variable.to_identifier())
                })?;
                self.call(source, &instruction, width, depth + 1)
            }
            Op::VarPhi(op) => {
                let Definition::Merge(sources) = source.origins.definitions.get(&op.dest)? else {
                    return None;
                };
                let block = instruction.basic_block()?;
                let edges = block.incoming_edges();
                if edges.len() > 256 {
                    self.status = Some(Status::Limit);
                    return None;
                }
                let mut choices = Vec::new();
                for edge in edges.iter() {
                    if !self.spend(1) {
                        return None;
                    }
                    let last = source.ssa.il.instruction_from_index(InstructionIndex(
                        edge.source.end_index().0.checked_sub(1)?,
                    ))?;
                    let incoming = last.ssa_variable_version_after(op.dest.variable);
                    if !sources.contains(&incoming) {
                        return None;
                    }
                    let value = self.variable_field(source, incoming, offset, width, depth + 1)?;
                    choices.push((value, self.context(source, last.instr_index, depth + 1)));
                }
                join(&choices)
            }
            _ => None,
        }
    }

    fn test(&self, term: Term, constant: u64, equal: bool) -> Option<Term> {
        self.membership(term, &BTreeSet::from([constant]), equal)
    }

    fn membership(&self, term: Term, values: &BTreeSet<u64>, is_in: bool) -> Option<Term> {
        match term {
            Term::Constant(value) => {
                Some(Term::Constant(u64::from(values.contains(&value) == is_in)))
            }
            Term::Value(value)
                if value.selector.width <= 8
                    && (value.selector.width == 8
                        || values
                            .iter()
                            .all(|constant| *constant < 1u64 << (value.selector.width * 8))) =>
            {
                Some(Term::Bits(
                    Condition {
                        guard: Guard {
                            selector: value.selector,
                            values: values.clone(),
                            is_in,
                        },
                        memory: value.memory,
                    },
                    1,
                    0,
                ))
            }
            Term::Bits(condition, yes, no) => Some(Term::bits(
                condition,
                u64::from(values.contains(&yes) == is_in),
                u64::from(values.contains(&no) == is_in),
            )),
            _ => None,
        }
    }

    fn bit(&mut self, source: &Source, index: Index, depth: usize) -> Option<Term> {
        if depth >= 32 || !self.spend(1) {
            return None;
        }
        let instruction = source.ssa.il.instruction_from_expr_index(index)?;
        let value = if instruction.size == 0 {
            match instruction.kind {
                Op::Const(op) if op.constant <= 1 => Term::Constant(op.constant),
                Op::VarSsa(op) => {
                    let definition = source.ssa.il.ssa_variable_definition(&op.src)?;
                    let Op::SetVarSsa(op) = definition.kind else {
                        return None;
                    };
                    return self.bit(source, op.src, depth + 1);
                }
                _ => return None,
            }
        } else {
            self.value(source, index, None, depth + 1)?
        };
        matches!(value, Term::Constant(0 | 1) | Term::Bits(_, 1, 0)).then_some(value)
    }

    fn value(
        &mut self,
        source: &Source,
        index: Index,
        width: Option<usize>,
        depth: usize,
    ) -> Option<Term> {
        if depth >= 32 || !self.spend(1) {
            return None;
        }
        let instruction = source.ssa.il.instruction_from_expr_index(index)?;
        let width = width.map_or(instruction.size, |width| width.min(instruction.size));
        if ![1, 2, 4, 8].contains(&width) {
            return None;
        }
        // Partial storage lanes need target evidence; comparison results are 0/1.
        if width < instruction.size
            && !source.input.little_endian
            && !matches!(
                instruction.kind,
                Op::CmpE(_)
                    | Op::CmpNe(_)
                    | Op::CmpUlt(_)
                    | Op::CmpUge(_)
                    | Op::CmpUgt(_)
                    | Op::CmpUle(_)
                    | Op::CmpSlt(_)
                    | Op::CmpSge(_)
                    | Op::CmpSgt(_)
                    | Op::CmpSle(_)
            )
        {
            return None;
        }
        let mask = u64::MAX >> (64 - width * 8);
        match instruction.kind {
            Op::Const(op) | Op::ConstPtr(op) => Some(Term::Constant(op.constant & mask)),
            Op::VarSsa(op) => self.variable(source, op.src, width, depth + 1),
            Op::VarSsaField(op) if source.input.little_endian => {
                self.variable_field(source, op.src, op.offset, width, depth + 1)
            }
            Op::Zx(op) | Op::BoolToInt(op) => self.value(source, op.src, Some(width), depth + 1),
            Op::LowPart(op) if source.input.little_endian => {
                self.value(source, op.src, Some(width), depth + 1)
            }
            Op::LoadSsa(_) | Op::LoadStructSsa(_) => {
                let (index, offset, memory) = match instruction.kind {
                    Op::LoadSsa(op) => (op.src, 0, op.src_memory),
                    Op::LoadStructSsa(op) => (op.src, op.offset, op.src_memory),
                    _ => unreachable!(),
                };
                if width < instruction.size && !source.input.little_endian {
                    return None;
                }
                let place = source
                    .origins
                    .place_in(index, 0, Some(memory))?
                    .shift(i64::try_from(offset).ok()?)?;
                Some(Term::Value(Value {
                    selector: Selector {
                        place,
                        width,
                        loaded: true,
                    },
                    memory: Some(source.origins.memory.epoch(memory)),
                }))
            }
            Op::CmpE(op) | Op::CmpNe(op) => {
                let left = self.value(source, op.left, None, depth + 1)?;
                let right = self.value(source, op.right, None, depth + 1)?;
                let (term, constant) = match (left, right) {
                    (term, Term::Constant(constant)) | (Term::Constant(constant), term) => {
                        (term, constant)
                    }
                    _ => return None,
                };
                self.test(term, constant, matches!(instruction.kind, Op::CmpE(_)))
            }
            Op::CmpUlt(op)
            | Op::CmpUge(op)
            | Op::CmpUgt(op)
            | Op::CmpUle(op)
            | Op::CmpSlt(op)
            | Op::CmpSge(op)
            | Op::CmpSgt(op)
            | Op::CmpSle(op) => {
                let left = self.value(source, op.left, None, depth + 1)?;
                let right = self.value(source, op.right, None, depth + 1)?;
                let order = Order::from_op(&instruction.kind)?;
                let operand_width = source.ssa.il.instruction_from_expr_index(op.left)?.size;
                let condition =
                    match (&left, &right) {
                        (Term::Value(value), Term::Constant(constant)) => {
                            order.condition(value.clone(), *constant, operand_width, true)
                        }
                        (Term::Constant(constant), Term::Value(value)) => order
                            .reversed()
                            .condition(value.clone(), *constant, operand_width, true),
                        _ => None,
                    };
                if let Some(condition) = condition {
                    if !self.spend(condition.guard.values.len()) {
                        return None;
                    }
                    return Some(Term::bits(condition, 1, 0));
                }
                Term::binary(left, right, |left, right| {
                    u64::from(order.evaluate(left, right, operand_width))
                })
            }
            Op::And(op) | Op::Or(op) | Op::Xor(op) | Op::Add(op) | Op::Sub(op) => {
                let mut consumed = width;
                if matches!(instruction.kind, Op::And(_)) && source.input.little_endian {
                    for index in [op.left, op.right] {
                        if let Some(value) = source.ssa.il.instruction_from_expr_index(index)
                            && let Op::Const(constant) = value.kind
                        {
                            consumed = consumed.min(match constant.constant {
                                0..=0xff => 1,
                                0..=0xffff => 2,
                                0..=0xffff_ffff => 4,
                                _ => 8,
                            });
                        }
                    }
                }
                let left = self.value(source, op.left, Some(consumed), depth + 1)?;
                let right = self.value(source, op.right, Some(consumed), depth + 1)?;
                Term::binary(left, right, |left, right| {
                    let result = match instruction.kind {
                        Op::And(_) => left & right,
                        Op::Or(_) => left | right,
                        Op::Xor(_) => left ^ right,
                        Op::Add(_) => left.wrapping_add(right),
                        _ => left.wrapping_sub(right),
                    };
                    result & mask
                })
            }
            Op::Sbb(op) | Op::Adc(op) => {
                let Term::Constant(left) = self.value(source, op.left, Some(width), depth + 1)?
                else {
                    return None;
                };
                let Term::Constant(right) = self.value(source, op.right, Some(width), depth + 1)?
                else {
                    return None;
                };
                let carry = self.bit(source, op.carry, depth + 1)?;
                Term::binary(carry, Term::Constant(0), |carry, _| {
                    let result = if matches!(instruction.kind, Op::Sbb(_)) {
                        left.wrapping_sub(right).wrapping_sub(carry)
                    } else {
                        left.wrapping_add(right).wrapping_add(carry)
                    };
                    result & mask
                })
            }
            _ => None,
        }
    }
}

fn tail_compatible(source: &Source, callee: &Source, width: usize) -> bool {
    let caller = source.ssa.il.function();
    let target = callee.ssa.il.function();
    if caller.arch() != target.arch() {
        return false;
    }
    let (Some(a), Some(b)) = (caller.calling_convention(), target.calling_convention()) else {
        return false;
    };
    if a.contents != b.contents {
        return false;
    }
    for function in [&caller, &target] {
        let size = function.return_type().contents.width() as usize;
        if size < width || size > source.input.pointer_width {
            return false;
        }
    }
    let a = caller.return_value().location.map(|value| value.contents);
    let b = target.return_value().location.map(|value| value.contents);
    if a != b
        || a.as_ref().is_some_and(|location| {
            location.indirect
                || location.returned_pointer.is_some()
                || location.components.len() != 1
        })
    {
        return false;
    }
    let a = caller.return_registers();
    let b = target.return_registers();
    !a.contents.is_empty() && a.contents.iter().eq(b.contents.iter())
}

fn memory(
    source: &Source,
    writes: &BTreeMap<Key, bool>,
    budget: &mut Budget,
) -> Result<Memory, Status> {
    let readonly_call = |address| {
        source.input.calls.iter().any(|call| {
            call.address == address
                && !call.adjusted
                && call.target.as_ref().and_then(|key| writes.get(key)) == Some(&false)
        })
    };
    let mut result = Memory {
        readonly: !writes[&source.input.key],
        epochs: BTreeMap::new(),
    };
    if result.readonly
        || !source
            .input
            .calls
            .iter()
            .any(|call| readonly_call(call.address))
    {
        return Ok(result);
    }
    fn epoch(
        source: &Source,
        version: u64,
        depth: usize,
        readonly_call: &impl Fn(u64) -> bool,
        cache: &mut BTreeMap<u64, u64>,
        budget: &mut Budget,
    ) -> Result<u64, Status> {
        if let Some(value) = cache.get(&version) {
            return Ok(*value);
        }
        budget.expressions = budget.expressions.checked_sub(1).ok_or(Status::Limit)?;
        cache.insert(version, version);
        if version == 0 || depth >= 32 {
            return Ok(version);
        }
        let Some(instruction) = usize::try_from(version)
            .ok()
            .and_then(|v| source.ssa.il.ssa_memory_definition(v))
        else {
            return Ok(version);
        };
        let value = match instruction.kind {
            Op::CallSsa(op) if readonly_call(instruction.address) => epoch(
                source,
                op.src_memory,
                depth + 1,
                readonly_call,
                cache,
                budget,
            )?,
            Op::MemPhi(_) => {
                let versions = source.ssa.operands(instruction.expr_index, 1)?;
                let mut values = BTreeSet::new();
                for version in versions {
                    values.insert(epoch(
                        source,
                        version,
                        depth + 1,
                        readonly_call,
                        cache,
                        budget,
                    )?);
                }
                if values.len() == 1 {
                    *values.first().unwrap()
                } else {
                    version
                }
            }
            _ => version,
        };
        cache.insert(version, value);
        Ok(value)
    }
    for index in 0..source.ssa.il.instruction_count() {
        let instruction = source
            .ssa
            .il
            .instruction_from_index(InstructionIndex(index))
            .ok_or(Status::Unavailable)?;
        epoch(
            source,
            instruction.ssa_memory_version() as u64,
            0,
            &readonly_call,
            &mut result.epochs,
            budget,
        )?;
    }
    Ok(result)
}

pub(in crate::rust) fn refine(
    sources: Vec<Source>,
    budget: &mut Budget,
    cancelled: impl Fn() -> bool,
) -> Result<Vec<Input>, Status> {
    let writes = layout::effects(sources.iter().map(|source| &source.input), &cancelled)?;
    let mut sources: BTreeMap<_, _> = sources
        .into_iter()
        .map(|source| (source.input.key.clone(), source))
        .collect();
    for source in sources.values_mut() {
        source.origins.memory = memory(source, &writes, budget)?;
    }
    let mut facts = Facts {
        sources: &sources,
        writes: &writes,
        summaries: BTreeMap::new(),
        active: BTreeSet::new(),
        budget,
        cancelled: &cancelled,
        status: None,
    };
    let mut controls = BTreeMap::new();
    for (key, source) in &sources {
        controls.insert(key.clone(), source.control.refine(source, &mut facts)?);
    }
    facts.check()?;
    let mut result = Vec::new();
    for (key, mut source) in sources {
        if cancelled() {
            return Err(Status::Cancelled);
        }
        let control = &controls[&key];
        source.input.fields.clear();
        for (index, origin, offset) in source.accesses {
            budget.expressions = budget.expressions.checked_sub(1).ok_or(Status::Limit)?;
            let instruction = source
                .ssa
                .il
                .instruction_from_expr_index(index)
                .ok_or(Status::Unavailable)?;
            source.input.fields.extend(places::accesses(
                &source.origins,
                control,
                &instruction,
                origin,
                offset,
                budget,
            )?);
            if source.input.fields.len() > MAX_FIELDS {
                return Err(Status::Limit);
            }
        }
        for (call, index) in source.input.calls.iter_mut().zip(source.call_sites) {
            let instruction = source
                .ssa
                .il
                .instruction_from_expr_index(index)
                .ok_or(Status::Unavailable)?;
            call.guards = control.at(&instruction);
            call.uncertain = control.uncertain(&instruction);
        }
        source.input.sites = control.sites(&source.ssa, &source.origins, budget, &cancelled)?;
        let function = source.ssa.il.function();
        if function.is_update_needed()
            || !current(&function.view(), &source.input)
            || !source.ssa.current(&function)
        {
            return Err(Status::Unavailable);
        }
        result.push(source.input);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merged_outcomes_need_evidence_on_every_edge() {
        let condition = Condition {
            guard: Guard {
                selector: Selector {
                    place: Place::parameter(0),
                    width: 8,
                    loaded: false,
                },
                values: BTreeSet::from([0]),
                is_in: true,
            },
            memory: None,
        };
        let yes = Term::Constant(1);
        let no = Term::Constant(0);
        assert!(join(&[(yes.clone(), vec![]), (no.clone(), vec![])]).is_none());
        assert!(join(&[(yes.clone(), vec![condition.clone()]), (no.clone(), vec![])]).is_none());
        let encoded = join(&[
            (Term::Constant(2), vec![condition.clone()]),
            (Term::Constant(3), vec![condition.invert()]),
        ])
        .unwrap();
        assert_eq!(encoded.outcome(&condition, true, &[]), Some(2));
        assert_eq!(encoded.outcome(&condition, false, &[]), Some(3));
        assert!(
            Term::binary(encoded, Term::Constant(0), |value, zero| u64::from(
                value != zero
            )) == Some(Term::Constant(1))
        );
        assert!(
            join(&[
                (yes.clone(), vec![condition.clone()]),
                (no, vec![condition.invert()])
            ]) == Some(Term::Bits(condition, 1, 0))
        );
        assert!(join(&[(yes.clone(), vec![]), (yes, vec![])]) == Some(Term::Constant(1)));
    }

    #[test]
    fn niche_return_join_uses_disjoint_tag_evidence() {
        let selector = Selector {
            place: Place::parameter(0),
            width: 1,
            loaded: false,
        };
        let none = Condition {
            guard: Guard {
                selector: selector.clone(),
                values: BTreeSet::from([0]),
                is_in: true,
            },
            memory: None,
        };
        let high = Condition {
            guard: Guard {
                selector,
                values: BTreeSet::from([253, 254, 255]),
                is_in: true,
            },
            memory: None,
        };
        let result = join(&[
            (Term::Constant(0), vec![none.clone()]),
            (Term::bits(high.clone(), 1, 0), vec![none.invert()]),
        ]);
        assert!(result == Some(Term::bits(high, 1, 0)));
    }
}
