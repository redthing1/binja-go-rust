mod frame;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use binaryninja::binary_view::BinaryView;
use binaryninja::low_level_il::expression::{
    ExpressionHandler, LowLevelILExpression, LowLevelILExpressionKind as Expr, ValueExpr,
};
use binaryninja::low_level_il::function::{Finalized, SSA};
use binaryninja::low_level_il::instruction::{
    InstructionHandler, LowLevelILInstruction, LowLevelILInstructionKind as Instruction,
    LowLevelInstructionIndex,
};
use binaryninja::variable::RegisterValueType;
use serde::{Deserialize, Serialize};

use super::effects::Analysis;
use crate::binja::llil::Ssa;

pub(super) type Expression<'a> = LowLevelILExpression<'a, Finalized, SSA, ValueExpr>;
pub(super) type Site<'a> = LowLevelILInstruction<'a, Finalized, SSA>;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(crate) enum Location {
    Register(u32),
    Stack(i64),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Value {
    pub number: u64,
    dictionary_address: bool,
    pub slot: Option<u64>,
    region: Option<Region>,
}

/// A bounded pointer into a known object or write-barrier buffer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Region {
    size: u64,
    offset: i64,
}

impl Value {
    pub(super) fn constant(number: u64) -> Self {
        Self {
            number,
            dictionary_address: false,
            slot: None,
            region: None,
        }
    }

    pub(super) fn region(size: u64) -> Self {
        Self {
            region: Some(Region { size, offset: 0 }),
            ..Self::constant(0)
        }
    }

    pub(super) fn concrete(self) -> Option<Self> {
        self.region.is_none().then_some(self)
    }

    pub(super) fn contains(self, width: usize) -> bool {
        self.region.is_some_and(|region| {
            region.offset >= 0
                && (region.offset as u64)
                    .checked_add(width as u64)
                    .is_some_and(|end| end <= region.size)
        })
    }

    pub(super) fn returned(mut self) -> Self {
        self.dictionary_address = false;
        self.slot = None;
        self
    }
}

#[derive(Deserialize, Serialize)]
pub(crate) struct Read {
    pub offset: u64,
    pub value: u64,
    pub uses: BTreeSet<Role>,
}

#[derive(Clone, Copy, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(crate) enum Role {
    #[serde(rename = "call target")]
    CallTarget,
    #[serde(rename = "allocation type")]
    AllocationType,
    #[serde(rename = "subdictionary")]
    Subdictionary,
}

impl Role {
    pub fn label(self) -> &'static str {
        match self {
            Self::CallTarget => "call target",
            Self::AllocationType => "allocation type",
            Self::Subdictionary => "subdictionary",
        }
    }
}

pub(crate) fn readonly(view: &BinaryView, code: &[Range<u64>], address: u64, size: usize) -> bool {
    let Some(end) = address.checked_add(size as u64) else {
        return false;
    };
    crate::binja::memory::readonly(view, &(address..end))
        && !code
            .iter()
            .any(|range| address < range.end && range.start < end)
}

#[derive(Deserialize, Eq, PartialEq, Serialize)]
pub(crate) struct Watch {
    address: u64,
    width: usize,
    value: Option<u64>,
}

impl Watch {
    fn capture(view: &BinaryView, code: &[Range<u64>], address: u64, width: usize) -> Self {
        let value = if (1..=8).contains(&width) && readonly(view, code, address, width) {
            let bytes = view.read_vec(address, width);
            (bytes.len() == width).then(|| {
                bytes
                    .iter()
                    .rev()
                    .fold(0, |word, byte| word << 8 | u64::from(*byte))
            })
        } else {
            None
        };
        Self {
            address,
            width,
            value,
        }
    }

    pub fn current(&self, view: &BinaryView, code: &[Range<u64>]) -> bool {
        *self == Self::capture(view, code, self.address, self.width)
    }
}

/// Retain failed qualifications too, so restoring a type or mapping enables a new read.
#[derive(Default)]
pub(crate) struct Watches {
    entries: BTreeMap<(u64, usize), Watch>,
    pub limited: bool,
}

impl Watches {
    fn insert(&mut self, watch: Watch) -> Option<u64> {
        let key = (watch.address, watch.width);
        if let Some(previous) = self.entries.get(&key) {
            if *previous != watch {
                self.limited = true;
                return None;
            }
        } else if self.entries.len() >= 16_384 {
            self.limited = true;
            return None;
        }
        let value = watch.value;
        self.entries.insert(key, watch);
        value
    }

    pub fn word(
        &mut self,
        view: &BinaryView,
        code: &[Range<u64>],
        address: u64,
        width: usize,
    ) -> Option<u64> {
        self.insert(Watch::capture(view, code, address, width))
    }

    pub fn merge(&mut self, other: Self) {
        self.limited |= other.limited;
        for watch in other.entries.into_values() {
            self.insert(watch);
        }
    }

    pub fn finish(self) -> Vec<Watch> {
        self.entries.into_values().collect()
    }
}

/// Bounded physical copies and immutable words, with explicit entry storage.
pub(crate) struct Reader<'a> {
    pub reads: BTreeMap<u64, Read>,
    pub watched: Watches,
    pub limited: bool,
    pub(super) view: &'a BinaryView,
    pub(super) ssa: &'a Ssa,
    pub(super) binding: Option<(Location, u64)>,
    code: &'a [Range<u64>],
    effects: Option<&'a Analysis<'a>>,
    budget: usize,
    registers: BTreeMap<(usize, u32), Value>,
    rejected: BTreeMap<(usize, u32), usize>,
    active: BTreeSet<(usize, u32)>,
    stack_values: BTreeMap<(i64, usize, usize), Value>,
    stack_rejected: BTreeMap<(i64, usize, usize), usize>,
    stack_active: BTreeSet<(i64, usize, usize)>,
    reachable: BTreeMap<usize, bool>,
    active_blocks: BTreeSet<usize>,
    expressions: BTreeMap<(usize, usize), Value>,
}

impl<'a> Reader<'a> {
    pub fn new(
        view: &'a BinaryView,
        ssa: &'a Ssa,
        binding: Option<(Location, u64)>,
        code: &'a [Range<u64>],
    ) -> Self {
        Self {
            view,
            ssa,
            binding,
            code,
            effects: None,
            reads: BTreeMap::new(),
            watched: Watches::default(),
            limited: false,
            budget: 16_384,
            registers: BTreeMap::new(),
            rejected: BTreeMap::new(),
            active: BTreeSet::new(),
            stack_values: BTreeMap::new(),
            stack_rejected: BTreeMap::new(),
            stack_active: BTreeSet::new(),
            reachable: BTreeMap::new(),
            active_blocks: BTreeSet::new(),
            expressions: BTreeMap::new(),
        }
    }

    pub(super) fn with_effects(mut self, effects: &'a Analysis<'a>) -> Self {
        self.effects = Some(effects);
        self
    }

    fn spend(&mut self, depth: usize) -> Option<()> {
        if self.budget == 0 || depth >= 64 || self.effects.is_some_and(|effects| !effects.spend()) {
            self.limited = true;
            return None;
        }
        self.budget -= 1;
        Some(())
    }

    fn entry(&self, location: Location) -> Option<Value> {
        let (source, number) = self.binding?;
        (source == location).then_some(Value {
            number,
            dictionary_address: true,
            slot: None,
            region: None,
        })
    }

    pub fn evaluate(&mut self, expression: Expression<'_>) -> Option<Value> {
        let position = self.ssa.position(expression.index.0)?;
        self.visit(expression, position, 0, &mut BTreeSet::new())?
            .concrete()
    }

    fn visit(
        &mut self,
        expression: Expression<'_>,
        position: usize,
        depth: usize,
        seen: &mut BTreeSet<usize>,
    ) -> Option<Value> {
        self.spend(depth)?;
        let key = (expression.index.0, position);
        if let Some(value) = self.expressions.get(&key) {
            return Some(*value);
        }
        if !seen.insert(expression.index.0) {
            return None;
        }
        let result = self
            .expression(expression, position, depth + 1, seen)
            .map(|mut value| {
                if value.region.is_none()
                    && let Some(mask) = expression.kind().size().and_then(mask)
                {
                    value.number &= mask;
                }
                value
            });
        seen.remove(&expression.index.0);
        if let Some(value) = result {
            self.expressions.insert(key, value);
        }
        result
    }

    fn expression(
        &mut self,
        expression: Expression<'_>,
        position: usize,
        depth: usize,
        seen: &mut BTreeSet<usize>,
    ) -> Option<Value> {
        match expression.kind() {
            Expr::Const(op) | Expr::ConstPtr(op) => Some(Value::constant(op.value())),
            Expr::RegSsa(op) => {
                self.before(position, op.source_reg().physical_reg().id().0, depth + 1)
            }
            Expr::Add(op) | Expr::Sub(op) => {
                let left = self.visit(op.left(), position, depth + 1, seen)?;
                let right = self.visit(op.right(), position, depth + 1, seen)?;
                let add = matches!(expression.kind(), Expr::Add(_));
                if let Some(mut region) = left.region {
                    let right = right.concrete()?;
                    region.offset = if add {
                        region.offset.checked_add(right.number as i64)?
                    } else {
                        region.offset.checked_sub(right.number as i64)?
                    };
                    return (op.size() == 8).then_some(Value {
                        region: Some(region),
                        ..left
                    });
                }
                if let Some(mut region) = right.region {
                    region.offset = region.offset.checked_add(left.number as i64)?;
                    return (add && op.size() == 8).then_some(Value {
                        region: Some(region),
                        ..right
                    });
                }
                let number = if add {
                    left.number.wrapping_add(right.number)
                } else {
                    left.number.wrapping_sub(right.number)
                };
                Some(Value {
                    number: number & mask(op.size())?,
                    dictionary_address: (left.dictionary_address && !right.dictionary_address)
                        || (add && right.dictionary_address && !left.dictionary_address),
                    slot: None,
                    region: None,
                })
            }
            Expr::Zx(op) | Expr::LowPart(op) => {
                let mut value = self.visit(op.operand(), position, depth + 1, seen)?;
                if value.region.is_some() {
                    return (op.size() == 8).then_some(value);
                }
                value.number &= mask(op.size())?;
                Some(value)
            }
            Expr::LoadSsa(op) if (1..=8).contains(&op.size()) => {
                let address = op.source_expr();
                let value = address.value();
                if value.state == RegisterValueType::StackFrameOffset {
                    return self.stack(
                        value.value,
                        op.size(),
                        op.source_memory_version() as usize,
                        depth + 1,
                    );
                }
                let address = self.visit(address, position, depth + 1, seen)?;
                let address = address.concrete()?;
                let number = self
                    .watched
                    .word(self.view, self.code, address.number, op.size())?;
                let slot = if address.dictionary_address {
                    let offset = address.number.checked_sub(self.binding?.1)?;
                    if op.size() != 8 || offset % 8 != 0 {
                        return None;
                    }
                    self.reads.entry(offset).or_insert(Read {
                        offset,
                        value: number,
                        uses: BTreeSet::new(),
                    });
                    Some(offset)
                } else {
                    None
                };
                Some(Value {
                    number,
                    dictionary_address: false,
                    slot,
                    region: None,
                })
            }
            Expr::CmpE(op) | Expr::CmpNe(op) => {
                let left = self
                    .visit(op.left(), position, depth + 1, seen)?
                    .concrete()?;
                let right = self
                    .visit(op.right(), position, depth + 1, seen)?
                    .concrete()?;
                Some(Value::constant(u64::from(
                    (left.number == right.number) == matches!(expression.kind(), Expr::CmpE(_)),
                )))
            }
            _ => None,
        }
    }

    pub(super) fn before(&mut self, position: usize, register: u32, depth: usize) -> Option<Value> {
        self.spend(depth)?;
        let key = (position, register);
        if let Some(value) = self.registers.get(&key) {
            return Some(*value);
        }
        if self
            .rejected
            .get(&key)
            .is_some_and(|remaining| *remaining >= 64 - depth)
            || !self.active.insert(key)
        {
            return None;
        }
        let result = (|| {
            let block = self
                .ssa
                .il
                .basic_block_containing_index(LowLevelInstructionIndex(position))?;
            self.reaching(
                block.start_index().0,
                position,
                register,
                depth + 1,
                &mut BTreeSet::new(),
            )
        })();
        self.active.remove(&key);
        if let Some(value) = result {
            self.registers.insert(key, value);
        } else if self.budget != 0 {
            self.rejected.insert(key, 64 - depth);
        }
        result
    }

    fn reaching(
        &mut self,
        mut start: usize,
        mut end: usize,
        register: u32,
        depth: usize,
        seen: &mut BTreeSet<(usize, usize, u32)>,
    ) -> Option<Value> {
        let mut trail = Vec::new();
        let result = (|| loop {
            self.spend(depth)?;
            let key = (start, end, register);
            if !seen.insert(key) {
                return None;
            }
            trail.push(key);
            for index in (start..end).rev() {
                self.spend(depth)?;
                let instruction = self
                    .ssa
                    .il
                    .instruction_from_index(LowLevelInstructionIndex(index))?;
                match instruction.kind() {
                    Instruction::SetRegSsa(op)
                        if op.dest_reg().physical_reg().id().0 == register =>
                    {
                        return self.visit(
                            op.source_expr(),
                            index,
                            depth + 1,
                            &mut BTreeSet::new(),
                        );
                    }
                    Instruction::SetRegPartialSsa(op)
                        if op.dest_reg().physical_reg().id().0 == register =>
                    {
                        return None;
                    }
                    Instruction::RegPhi(op) if op.dest_reg().physical_reg().id().0 == register => {
                        break;
                    }
                    Instruction::SetRegSplitSsa(op) => {
                        for destination in [op.dest_expr_high(), op.dest_expr_low()] {
                            if self.ssa.split_destination(destination.index.0)? == register {
                                return None;
                            }
                        }
                    }
                    Instruction::CallSsa(_) => {
                        return self.effects?.call_value(self, instruction, register);
                    }
                    Instruction::Nop(_)
                    | Instruction::SetRegSsa(_)
                    | Instruction::SetRegPartialSsa(_)
                    | Instruction::SetFlagSsa(_)
                    | Instruction::StoreSsa(_)
                    | Instruction::RegPhi(_)
                    | Instruction::FlagPhi(_)
                    | Instruction::MemPhi(_)
                    | Instruction::If(_)
                    | Instruction::Goto(_)
                    | Instruction::Jump(_)
                    | Instruction::JumpTo(_) => (),
                    _ if matches!(instruction.kind(), Instruction::Value(expression) if matches!(expression.kind(), Expr::And(_))) => {
                        ()
                    }
                    _ => return None,
                }
            }
            let block = self
                .ssa
                .il
                .basic_block_containing_index(LowLevelInstructionIndex(start))?;
            let edges = block.incoming_edges();
            if edges.is_empty() {
                return self.entry(Location::Register(register));
            }
            let mut incoming = Vec::new();
            for edge in edges.iter() {
                if !self.block_possible(edge.source.start_index().0)
                    || !self.edge_possible(&edge.source, edge.branch)
                {
                    continue;
                }
                incoming.push((edge.source.start_index().0, edge.source.end_index().0));
            }
            if let [(previous_start, previous_end)] = incoming.as_slice() {
                start = *previous_start;
                end = *previous_end;
                continue;
            }
            let mut result = None;
            for (start, end) in incoming {
                let value = self.reaching(start, end, register, depth + 1, seen)?;
                if result.is_some_and(|previous| previous != value) {
                    return None;
                }
                result = Some(value);
            }
            return result;
        })();
        for key in trail {
            seen.remove(&key);
        }
        result
    }

    pub(super) fn stack(
        &mut self,
        offset: i64,
        width: usize,
        memory: usize,
        depth: usize,
    ) -> Option<Value> {
        self.spend(depth)?;
        let key = (offset, width, memory);
        if let Some(value) = self.stack_values.get(&key) {
            return Some(*value);
        }
        if self
            .stack_rejected
            .get(&key)
            .is_some_and(|remaining| *remaining >= 64 - depth)
        {
            return None;
        }
        if !self.stack_active.insert(key) {
            return None;
        }
        let value = self.stack_definition(offset, width, memory, depth + 1);
        self.stack_active.remove(&key);
        if let Some(value) = value {
            self.stack_values.insert(key, value);
        } else if self.budget != 0 {
            self.stack_rejected.insert(key, 64 - depth);
        }
        value
    }

    fn stack_definition(
        &mut self,
        offset: i64,
        width: usize,
        mut memory: usize,
        depth: usize,
    ) -> Option<Value> {
        let mut trail = BTreeSet::new();
        let value = (|| loop {
            self.spend(depth)?;
            if !trail.insert(memory) {
                return None;
            }
            if let Some(value) = self.stack_values.get(&(offset, width, memory)) {
                return Some(*value);
            }
            if memory == 0 {
                return (width == 8)
                    .then(|| self.entry(Location::Stack(offset)))
                    .flatten();
            }
            let index = self.ssa.memory_definition(memory)?;
            let site = self.ssa.il.instruction_from_index(index)?;
            match site.kind() {
                Instruction::StoreSsa(op) => {
                    let destination = op.dest_expr().value();
                    if destination.state == RegisterValueType::StackFrameOffset
                        && destination.value == offset
                        && op.size() == width
                    {
                        return self.visit(
                            op.source_expr(),
                            index.0,
                            depth + 1,
                            &mut BTreeSet::new(),
                        );
                    }
                    if !self.disjoint_store(site, offset, width, false) {
                        return None;
                    }
                    memory = op.source_memory_version() as usize;
                }
                Instruction::MemPhi(op) => {
                    let mut result = None;
                    for memory in op.source_memory_versions() {
                        let value = self.stack(offset, width, memory, depth + 1)?;
                        if result.is_some_and(|previous| previous != value) {
                            return None;
                        }
                        result = Some(value);
                    }
                    return result;
                }
                Instruction::CallSsa(_) => {
                    let (_, previous) = self.ssa.call_stack(index.0)?;
                    let value = self.stack(offset, width, previous, depth + 1)?;
                    return self
                        .effects?
                        .preserves(self, site, offset, width, self.nonstack(value))
                        .then_some(value);
                }
                _ => return None,
            }
        })();
        if let Some(value) = value {
            for memory in trail {
                self.stack_values.insert((offset, width, memory), value);
            }
        }
        value
    }

    pub fn argument(&mut self, site: Site<'_>, location: Location) -> Option<Value> {
        if !matches!(
            site.kind(),
            Instruction::CallSsa(_) | Instruction::TailCallSsa(_)
        ) {
            return None;
        }
        (match location {
            Location::Register(register) => self.before(site.index.0, register, 0),
            Location::Stack(offset) => {
                let (entry, memory) = self.ssa.call_stack(site.index.0)?;
                self.stack(entry.checked_add(offset)?, 8, memory, 0)
            }
        })?
        .concrete()
    }

    pub fn used(&mut self, value: Value, role: Role) {
        if let Some(offset) = value.slot
            && let Some(read) = self.reads.get_mut(&offset)
        {
            read.uses.insert(role);
        }
    }

    pub(super) fn nonstack(&self, value: Value) -> bool {
        value.contains(0)
            || readonly(self.view, self.code, value.number, 1)
            || self.code.iter().any(|range| range.contains(&value.number))
    }

    fn edge_possible(
        &mut self,
        block: &binaryninja::basic_block::BasicBlock<
            binaryninja::low_level_il::block::LowLevelILBlock<'_, Finalized, SSA>,
        >,
        branch: binaryninja::architecture::BranchType,
    ) -> bool {
        use binaryninja::architecture::BranchType;
        let Some(index) = block.end_index().0.checked_sub(1) else {
            return true;
        };
        let Some(site) = self.ssa.il.instruction_from_index(index.into()) else {
            return true;
        };
        let Instruction::If(op) = site.kind() else {
            return true;
        };
        let Some(condition) = self.evaluate(op.condition()) else {
            return true;
        };
        match branch {
            BranchType::TrueBranch => condition.number != 0,
            BranchType::FalseBranch => condition.number == 0,
            _ => true,
        }
    }

    fn block_possible(&mut self, start: usize) -> bool {
        if let Some(possible) = self.reachable.get(&start) {
            return *possible;
        }
        if self.spend(0).is_none()
            || self.active_blocks.len() >= 64
            || !self.active_blocks.insert(start)
        {
            return true;
        }
        let possible = self
            .ssa
            .il
            .basic_block_containing_index(start.into())
            .is_none_or(|block| {
                let edges = block.incoming_edges();
                edges.is_empty()
                    || edges.iter().any(|edge| {
                        self.block_possible(edge.source.start_index().0)
                            && self.edge_possible(&edge.source, edge.branch)
                    })
            });
        self.active_blocks.remove(&start);
        self.reachable.insert(start, possible);
        possible
    }
}

fn mask(size: usize) -> Option<u64> {
    match size {
        1..=7 => Some((1u64 << (8 * size)) - 1),
        8 => Some(u64::MAX),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{Region, Value};

    #[test]
    fn region_writes_must_fit_the_known_object() {
        for (offset, width, expected) in [
            (0, 8, true),
            (7, 1, true),
            (8, 1, false),
            (-1, 1, false),
            (1, 8, false),
            (i64::MAX, 8, false),
        ] {
            let value = Value {
                region: Some(Region { size: 8, offset }),
                ..Value::constant(0)
            };
            assert_eq!(value.contains(width), expected, "{offset:+} / {width}");
            assert!(value.concrete().is_none());
        }
        assert!(!Value::constant(0).contains(1));
    }
}
