use std::collections::{BTreeMap, BTreeSet};

use binaryninja::medium_level_il::{
    MediumLevelILInstruction as Instruction, MediumLevelInstructionIndex,
};

use super::ordering::Order;
use super::*;
use crate::rust::layout::{MAX_GUARDS, Selector};

#[derive(Clone, Eq, PartialEq)]
pub(super) struct Value {
    pub selector: Selector,
    pub memory: Option<u64>,
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Condition {
    pub guard: Guard,
    pub memory: Option<u64>,
}

impl Condition {
    pub fn invert(&self) -> Self {
        let mut result = self.clone();
        result.guard.is_in = !result.guard.is_in;
        result
    }
}

struct Region {
    switch: usize,
    block: usize,
    condition: Condition,
}

struct Table {
    address: u64,
    width: usize,
    relative: bool,
    selector: Value,
}

#[derive(Clone)]
struct Block {
    end: usize,
    conditions: Vec<Condition>,
    unresolved: bool,
    unresolved_switch: bool,
}

#[derive(Clone)]
pub(super) struct Control {
    blocks: BTreeMap<usize, Block>,
    pub(super) memory: Memory,
}

impl Origins<'_> {
    fn peel(
        &self,
        mut index: Index,
    ) -> Option<binaryninja::medium_level_il::MediumLevelILInstruction> {
        for _ in 0..32 {
            let instruction = self.il.instruction_from_expr_index(index)?;
            if let Op::VarSsa(op) = instruction.kind
                && let Some(Definition::Assign(next)) = self.definitions.get(&op.src)
            {
                index = *next;
                continue;
            }
            return Some(instruction);
        }
        None
    }

    fn scalar_variable(&self, variable: SSAVariable, width: usize, depth: usize) -> Option<Value> {
        if depth >= 32 {
            return None;
        }
        if variable.version == 0 {
            return Some(Value {
                selector: Selector {
                    place: Place::parameter(*self.parameters.get(&variable.variable)?),
                    width,
                    loaded: false,
                },
                memory: None,
            });
        }
        match self.definitions.get(&variable)? {
            Definition::Assign(index) => {
                if self.il.instruction_from_expr_index(*index)?.size != width {
                    return None;
                }
                self.value(*index, depth + 1)
            }
            Definition::Call(address) if width == self.pointer_width => Some(Value {
                selector: Selector {
                    place: Place::call(*address),
                    width,
                    loaded: false,
                },
                memory: None,
            }),
            Definition::Merge(sources) => {
                let mut selected = None;
                for source in sources {
                    let value = self.scalar_variable(*source, width, depth + 1)?;
                    if selected.as_ref().is_some_and(|previous| *previous != value) {
                        return None;
                    }
                    selected = Some(value);
                }
                selected
            }
            _ => None,
        }
    }

    fn value(&self, index: Index, depth: usize) -> Option<Value> {
        if depth >= 32 {
            return None;
        }
        let instruction = self.il.instruction_from_expr_index(index)?;
        if ![1, 2, 4, 8, 16].contains(&instruction.size) {
            return None;
        }
        let (place, memory) = match instruction.kind {
            Op::Zx(op) => return self.value(op.src, depth + 1),
            Op::VarSsa(op) => return self.scalar_variable(op.src, instruction.size, depth + 1),
            Op::LoadSsa(op) => (
                self.place_in(op.src, 0, Some(op.src_memory))?,
                op.src_memory,
            ),
            Op::LoadStructSsa(op) => (
                self.place_in(op.src, 0, Some(op.src_memory))?
                    .shift(i64::try_from(op.offset).ok()?)?,
                op.src_memory,
            ),
            _ => return None,
        };
        Some(Value {
            selector: Selector {
                place,
                width: instruction.size,
                loaded: true,
            },
            memory: Some(memory),
        })
    }

    fn comparison(&self, index: Index, taken: bool) -> Option<Condition> {
        let instruction = self.peel(index)?;
        let op = match instruction.kind {
            Op::CmpE(op)
            | Op::CmpNe(op)
            | Op::CmpUlt(op)
            | Op::CmpUle(op)
            | Op::CmpUgt(op)
            | Op::CmpUge(op)
            | Op::CmpSlt(op)
            | Op::CmpSle(op)
            | Op::CmpSgt(op)
            | Op::CmpSge(op) => op,
            _ => return None,
        };
        let (expression, constant, reversed) = match self.peel(op.right)?.kind {
            Op::Const(c) | Op::ConstPtr(c) => (op.left, c.constant, false),
            _ => match self.peel(op.left)?.kind {
                Op::Const(c) | Op::ConstPtr(c) => (op.right, c.constant, true),
                _ => return None,
            },
        };
        let value = self.value(expression, 0)?;
        if let Some(mut order) = Order::from_op(&instruction.kind) {
            if reversed {
                order = order.reversed();
            }
            return order.condition(
                value,
                constant,
                self.il.instruction_from_expr_index(expression)?.size,
                taken,
            );
        }
        if value.selector.width > 8
            || (value.selector.width < 8 && constant >= 1u64 << (value.selector.width * 8))
        {
            return None;
        }
        Some(Condition {
            guard: Guard {
                selector: value.selector,
                values: BTreeSet::from([constant]),
                is_in: matches!(instruction.kind, Op::CmpE(_)) == taken,
            },
            memory: value.memory,
        })
    }

    fn indexed_load(&self, index: Index, relative: bool) -> Option<Table> {
        let instruction = self.peel(index)?;
        let Op::LoadSsa(load) = instruction.kind else {
            return None;
        };
        let width = if relative { 4 } else { self.pointer_width };
        if instruction.size != width {
            return None;
        }
        let Op::Add(add) = self.peel(load.src)?.kind else {
            return None;
        };
        for (base, scaled) in [(add.left, add.right), (add.right, add.left)] {
            let base = match self.peel(base)?.kind {
                Op::Const(c) | Op::ConstPtr(c) => c.constant,
                _ => continue,
            };
            let Op::Lsl(shift) = self.peel(scaled)?.kind else {
                continue;
            };
            let Op::Const(count) = self.peel(shift.right)?.kind else {
                continue;
            };
            if count.constant == width.trailing_zeros() as u64 {
                return Some(Table {
                    address: base,
                    width,
                    relative,
                    selector: self.value(shift.left, 0)?,
                });
            }
        }
        None
    }

    fn table(&self, index: Index) -> Option<Table> {
        if let Some(table) = self.indexed_load(index, false) {
            return Some(table);
        }
        let Op::Add(add) = self.peel(index)?.kind else {
            return None;
        };
        for (base, offset) in [(add.left, add.right), (add.right, add.left)] {
            let base = match self.peel(base)?.kind {
                Op::Const(c) | Op::ConstPtr(c) => c.constant,
                _ => continue,
            };
            let Op::Sx(sx) = self.peel(offset)?.kind else {
                continue;
            };
            let Some(table) = self.indexed_load(sx.src, true) else {
                continue;
            };
            if table.address == base {
                return Some(table);
            }
        }
        None
    }
}

fn byte_table_entries(
    ssa: &Ssa,
    table: &Table,
    targets: &BTreeMap<u64, u64>,
    snapshot: &mut Snapshot,
    budget: &mut Budget,
) -> Result<Option<BTreeMap<u64, BTreeSet<u64>>>, Status> {
    if table.selector.selector.width != 1 {
        return Ok(None);
    }
    let Some(end) = table.address.checked_add(256 * table.width as u64) else {
        return Ok(None);
    };
    let view = ssa.il.function().view();
    if !readonly(&view, &(table.address..end)) {
        return Ok(None);
    }
    let bytes = snapshot.read(&view, table.address..end, true, budget)?;
    let function = ssa.il.function();
    let ranges = function.address_ranges();
    let mut result: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    for (index, bytes) in bytes.chunks_exact(table.width).enumerate() {
        budget.expressions = budget
            .expressions
            .checked_sub(ranges.len() + 1)
            .ok_or(Status::Limit)?;
        let word = if snapshot.little_endian {
            bytes.iter().rev().fold(0u64, |a, b| a << 8 | u64::from(*b))
        } else {
            bytes.iter().fold(0u64, |a, b| a << 8 | u64::from(*b))
        };
        let target = if table.relative {
            table.address.checked_add_signed(word as u32 as i32 as i64)
        } else {
            Some(word)
        };
        if let Some(target) = target {
            if targets.contains_key(&target) {
                result.entry(target).or_default().insert(index as u64);
            } else if ranges
                .iter()
                .any(|range| range.start <= target && target < range.end)
            {
                return Ok(None);
            }
        }
    }
    Ok((!result.is_empty()).then_some(result))
}

fn regions(
    ssa: &Ssa,
    origins: &Origins<'_>,
    snapshot: &mut Snapshot,
    budget: &mut Budget,
    cancelled: &impl Fn() -> bool,
) -> Result<Vec<Region>, Status> {
    let mut result = Vec::new();
    let function = ssa.il.function();
    let view = function.view();
    for index in 0..ssa.il.instruction_count() {
        if index % 256 == 0 && cancelled() {
            return Err(Status::Cancelled);
        }
        let instruction = ssa
            .il
            .instruction_from_index(MediumLevelInstructionIndex(index))
            .ok_or(Status::Unavailable)?;
        let Op::JumpTo(op) = instruction.kind else {
            continue;
        };
        let Some(table) = origins.table(op.dest) else {
            continue;
        };
        let entries = ssa.lookup(op.dest, budget)?;
        let raw_targets = ssa.operands(instruction.expr_index, 1)?;
        budget.expressions = budget
            .expressions
            .checked_sub(raw_targets.len())
            .ok_or(Status::Limit)?;
        if raw_targets.len() % 2 != 0 {
            return Err(Status::Unavailable);
        }
        let targets: BTreeMap<_, _> = raw_targets
            .chunks_exact(2)
            .map(|pair| (pair[0], pair[1]))
            .collect();
        let Some(entries) = (match entries {
            Some(entries) if entries.keys().all(|target| targets.contains_key(target)) => {
                Some(entries)
            }
            _ => byte_table_entries(ssa, &table, &targets, snapshot, budget)?,
        }) else {
            continue;
        };
        let Some(switch) = instruction.basic_block() else {
            continue;
        };
        let mut selected = Vec::new();
        let mut valid = true;
        for (target, values) in entries {
            let Some(target_index) = targets
                .get(&target)
                .and_then(|index| usize::try_from(*index).ok())
            else {
                valid = false;
                break;
            };
            let Some(block) = ssa
                .il
                .basic_block_containing_index(MediumLevelInstructionIndex(target_index))
            else {
                valid = false;
                break;
            };
            for &value in &values {
                if cancelled() {
                    return Err(Status::Cancelled);
                }
                if table.selector.selector.width < 8
                    && value >= 1u64 << (table.selector.selector.width * 8)
                {
                    valid = false;
                    break;
                }
                let Some(address) = value
                    .checked_mul(table.width as u64)
                    .and_then(|offset| table.address.checked_add(offset))
                else {
                    valid = false;
                    break;
                };
                let Some(end) = address.checked_add(table.width as u64) else {
                    valid = false;
                    break;
                };
                let range = address..end;
                if !readonly(&view, &range) {
                    valid = false;
                    break;
                }
                let bytes = snapshot.read(&view, range, true, budget)?;
                let word = if snapshot.little_endian {
                    bytes.iter().rev().fold(0u64, |a, b| a << 8 | u64::from(*b))
                } else {
                    bytes.iter().fold(0u64, |a, b| a << 8 | u64::from(*b))
                };
                let actual = if table.relative {
                    table.address.checked_add_signed(word as u32 as i32 as i64)
                } else {
                    Some(word)
                };
                if actual != Some(target) {
                    valid = false;
                    break;
                }
            }
            let incoming = block.incoming_edges();
            if valid
                && !values.is_empty()
                && incoming.len() == 1
                && incoming
                    .iter()
                    .next()
                    .is_some_and(|edge| edge.source.index() == switch.index())
            {
                selected.push(Region {
                    switch: switch.index(),
                    block: block.index(),
                    condition: Condition {
                        guard: Guard {
                            selector: table.selector.selector.clone(),
                            values,
                            is_in: true,
                        },
                        memory: table.selector.memory,
                    },
                });
            }
        }
        if valid {
            result.extend(selected)
        }
        if result.len() > 256 {
            return Err(Status::Limit);
        }
    }
    Ok(result)
}

/// Join validated case sets when every incoming path has a known switch case.
fn joined_regions(
    ssa: &Ssa,
    regions: &[Region],
    budget: &mut Budget,
    cancelled: &impl Fn() -> bool,
) -> Result<BTreeMap<usize, (Vec<Condition>, bool)>, Status> {
    let blocks = ssa.il.basic_blocks();
    let switches: BTreeSet<_> = blocks
        .iter()
        .filter_map(|block| {
            let last = block.end_index().0.checked_sub(1)?;
            let instruction = ssa
                .il
                .instruction_from_index(MediumLevelInstructionIndex(last))?;
            matches!(instruction.kind, Op::JumpTo(_)).then_some(block.index())
        })
        .collect();
    if switches.is_empty() {
        return Ok(BTreeMap::new());
    }
    let mut predecessors = BTreeMap::new();
    let mut successors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut dominators = BTreeMap::new();
    let mut result = BTreeMap::new();
    for block in blocks.iter() {
        let incoming: Vec<_> = block
            .incoming_edges()
            .iter()
            .map(|edge| edge.source.index())
            .collect();
        let dominating: BTreeSet<_> = block
            .dominators()
            .iter()
            .map(|block| block.index())
            .collect();
        budget.expressions = budget
            .expressions
            .checked_sub(incoming.len() + dominating.len())
            .ok_or(Status::Limit)?;
        for parent in &incoming {
            successors.entry(*parent).or_default().push(block.index());
        }
        let missing: BTreeSet<_> = switches
            .intersection(&dominating)
            .copied()
            .filter(|switch| *switch != block.index())
            .collect();
        result.insert(block.index(), (Vec::new(), missing));
        predecessors.insert(block.index(), incoming);
        dominators.insert(block.index(), dominating);
    }
    let mut groups: BTreeMap<usize, Vec<&Region>> = BTreeMap::new();
    for region in regions {
        groups.entry(region.switch).or_default().push(region);
    }
    for (switch, cases) in groups {
        let mut known: BTreeMap<usize, BTreeSet<u64>> = BTreeMap::new();
        for (block, dominating) in &dominators {
            if let Some(case) = cases
                .iter()
                .find(|case| dominating.contains(&case.switch) && dominating.contains(&case.block))
            {
                budget.expressions = budget
                    .expressions
                    .checked_sub(case.condition.guard.values.len())
                    .ok_or(Status::Limit)?;
                known.insert(*block, case.condition.guard.values.clone());
            }
        }
        let mut queue = std::collections::VecDeque::from_iter(known.keys().copied());
        while let Some(block) = queue.pop_front() {
            if cancelled() {
                return Err(Status::Cancelled);
            }
            for next in successors.get(&block).into_iter().flatten() {
                if known.contains_key(next) || !dominators[next].contains(&switch) {
                    continue;
                }
                let incoming = &predecessors[next];
                budget.expressions = budget
                    .expressions
                    .checked_sub(incoming.len())
                    .ok_or(Status::Limit)?;
                if incoming.is_empty() || incoming.iter().any(|parent| !known.contains_key(parent))
                {
                    continue;
                }
                let mut values = BTreeSet::new();
                for parent in incoming {
                    values.extend(known[parent].iter().copied());
                }
                if values.len() > 256 {
                    return Err(Status::Limit);
                }
                budget.expressions = budget
                    .expressions
                    .checked_sub(values.len())
                    .ok_or(Status::Limit)?;
                known.insert(*next, values);
                queue.push_back(*next);
            }
        }
        for (block, values) in known {
            let mut condition = cases[0].condition.clone();
            condition.guard.values = values;
            let (conditions, missing) = result.get_mut(&block).ok_or(Status::Unavailable)?;
            conditions.push(condition);
            missing.remove(&switch);
        }
    }
    Ok(result
        .into_iter()
        .map(|(block, (conditions, missing))| (block, (conditions, !missing.is_empty())))
        .collect())
}

impl Control {
    /// A copied field used after an aliasing write must remain a copied value.
    pub fn retained_loads(
        ssa: &Ssa,
        origins: &Origins<'_>,
        budget: &mut Budget,
        cancelled: &impl Fn() -> bool,
    ) -> Result<BTreeSet<Selector>, Status> {
        fn changed(
            ssa: &Ssa,
            origins: &Origins<'_>,
            selector: &Selector,
            from: u64,
            to: u64,
            depth: usize,
            budget: &mut Budget,
        ) -> Result<bool, Status> {
            if from == to {
                return Ok(false);
            }
            if depth >= 32 {
                return Ok(true);
            }
            budget.expressions = budget.expressions.checked_sub(1).ok_or(Status::Limit)?;
            let Some(instruction) = usize::try_from(to)
                .ok()
                .and_then(|to| ssa.il.ssa_memory_definition(to))
            else {
                return Ok(true);
            };
            let (destination, offset, memory) = match instruction.kind {
                Op::StoreSsa(op) if op.dest_memory == to => (op.dest, 0, op.src_memory),
                Op::StoreStructSsa(op) if op.dest_memory == to => {
                    (op.dest, op.offset, op.src_memory)
                }
                Op::MemPhi(op) if op.dest_memory == to => {
                    let versions = ssa.operands(instruction.expr_index, 1)?;
                    for version in versions {
                        if changed(ssa, origins, selector, from, version, depth + 1, budget)? {
                            return Ok(true);
                        }
                    }
                    return Ok(false);
                }
                _ => return Ok(true),
            };
            let Some(place) = i64::try_from(offset).ok().and_then(|offset| {
                origins
                    .place_in(destination, 0, Some(memory))?
                    .shift(offset)
            }) else {
                return Ok(true);
            };
            let (Some((&left, prefix)), Some((&right, other_prefix))) =
                (selector.place.path.split_last(), place.path.split_last())
            else {
                return Ok(true);
            };
            if selector.place.root != place.root || prefix != other_prefix {
                return Ok(true);
            }
            if (left as i128) < right as i128 + instruction.size as i128
                && (right as i128) < left as i128 + selector.width as i128
            {
                return Ok(true);
            }
            changed(ssa, origins, selector, from, memory, depth + 1, budget)
        }
        let mut result = BTreeSet::new();
        let mut cache = BTreeMap::new();
        for index in 0..ssa.il.expression_count() {
            if index % 256 == 0 && cancelled() {
                return Err(Status::Cancelled);
            }
            let instruction = ssa
                .il
                .instruction_from_expr_index(Index(index))
                .ok_or(Status::Unavailable)?;
            if instruction.instr_index.0 >= ssa.il.instruction_count() {
                continue;
            }
            let Some(value) = origins.value(Index(index), 0) else {
                continue;
            };
            let Some(memory) = value.memory else { continue };
            let current = instruction.ssa_memory_version() as u64;
            if memory == current {
                continue;
            }
            let key = (value.selector.clone(), memory, current);
            if !cache.contains_key(&key) {
                if cache.len() >= 4096 {
                    return Err(Status::Limit);
                }
                cache.insert(
                    key.clone(),
                    changed(ssa, origins, &value.selector, memory, current, 0, budget)?,
                );
            }
            if cache[&key] {
                result.insert(value.selector);
            }
        }
        Ok(result)
    }

    pub fn collect(
        ssa: &Ssa,
        origins: &Origins<'_>,
        snapshot: &mut Snapshot,
        budget: &mut Budget,
        cancelled: &impl Fn() -> bool,
    ) -> Result<Self, Status> {
        let blocks = ssa.il.basic_blocks();
        if blocks.len() > 4096 {
            return Err(Status::Limit);
        }
        let regions = regions(ssa, origins, snapshot, budget, cancelled)?;
        let region_contexts = joined_regions(ssa, &regions, budget, cancelled)?;
        let mut result = BTreeMap::new();
        for block in blocks.iter() {
            if cancelled() {
                return Err(Status::Cancelled);
            }
            let (mut conditions, unresolved_switch) = region_contexts
                .get(&block.index())
                .cloned()
                .unwrap_or_default();
            let mut unresolved = false;
            for (index, taken) in ssa.dependencies(block.start_index(), budget)? {
                if let Some(instruction) = ssa.il.instruction_from_index(index)
                    && let Op::If(op) = instruction.kind
                {
                    if let Some(condition) = origins.comparison(op.condition, taken) {
                        budget.expressions = budget
                            .expressions
                            .checked_sub(condition.guard.values.len())
                            .ok_or(Status::Limit)?;
                        conditions.push(condition);
                    } else {
                        unresolved = true;
                    }
                }
            }
            if conditions.len() > MAX_GUARDS {
                return Err(Status::Limit);
            }
            result.insert(
                block.start_index().0,
                Block {
                    end: block.end_index().0,
                    conditions,
                    unresolved,
                    unresolved_switch,
                },
            );
        }
        Ok(Self {
            blocks: result,
            memory: origins.memory.clone(),
        })
    }

    pub fn refine(&self, source: &Source, facts: &mut values::Facts<'_>) -> Result<Self, Status> {
        let mut result = self.clone();
        result.memory = source.origins.memory.clone();
        for (start, block) in &mut result.blocks {
            block.unresolved = false;
            for (index, taken) in facts.dependencies(source, InstructionIndex(*start)) {
                if let Some(instruction) = source.ssa.il.instruction_from_index(index)
                    && let Op::If(op) = instruction.kind
                {
                    if let Some(condition) = facts.condition(source, op.condition, taken, 0) {
                        block.conditions.push(condition);
                    } else if source.origins.comparison(op.condition, taken).is_none() {
                        block.unresolved = true;
                    }
                }
            }
            for condition in &mut block.conditions {
                condition.memory = condition.memory.map(|version| result.memory.epoch(version));
            }
            block.conditions.sort();
            block.conditions.dedup();
            if block.conditions.len() > MAX_GUARDS {
                return Err(Status::Limit);
            }
        }
        facts.check()?;
        Ok(result)
    }

    pub fn at(&self, instruction: &Instruction) -> Vec<Guard> {
        let Some((_, block)) = self.blocks.range(..=instruction.instr_index.0).next_back() else {
            return Vec::new();
        };
        if instruction.instr_index.0 >= block.end {
            return Vec::new();
        }
        let memory = self.memory.epoch(instruction.ssa_memory_version() as u64);
        let mut result: Vec<_> = block
            .conditions
            .iter()
            .filter(|condition| condition.memory.is_none_or(|version| version == memory))
            .map(|condition| condition.guard.clone())
            .collect();
        result.sort();
        result.dedup();
        result
    }

    pub fn uncertain(&self, instruction: &Instruction) -> bool {
        let Some((_, block)) = self.blocks.range(..=instruction.instr_index.0).next_back() else {
            return true;
        };
        let memory = self.memory.epoch(instruction.ssa_memory_version() as u64);
        instruction.instr_index.0 >= block.end
            || block.unresolved
            || block.unresolved_switch
            || block
                .conditions
                .iter()
                .any(|condition| condition.memory.is_some_and(|version| version != memory))
    }

    pub fn for_origin(
        &self,
        instruction: &Instruction,
        origins: &Origins<'_>,
        index: Index,
    ) -> Vec<Guard> {
        let mut result = self.at(instruction);
        if origins
            .place_in(index, 0, Some(instruction.ssa_memory_version() as u64))
            .is_none()
        {
            result.retain(|guard| !guard.selector.loaded);
        }
        result
    }

    pub fn sites(
        &self,
        ssa: &Ssa,
        origins: &Origins<'_>,
        budget: &mut Budget,
        cancelled: &impl Fn() -> bool,
    ) -> Result<BTreeMap<u64, Vec<Guard>>, Status> {
        let mut result: BTreeMap<u64, Vec<Guard>> = BTreeMap::new();
        for index in 0..ssa.il.expression_count() {
            if index % 256 == 0 && cancelled() {
                return Err(Status::Cancelled);
            }
            let instruction = ssa
                .il
                .instruction_from_expr_index(Index(index))
                .ok_or(Status::Unavailable)?;
            if instruction.instr_index.0 >= ssa.il.instruction_count() {
                continue;
            }
            if !matches!(instruction.kind, Op::VarSsa(_))
                || origins.place(Index(index), 0).is_none()
            {
                continue;
            }
            budget.expressions = budget.expressions.checked_sub(1).ok_or(Status::Limit)?;
            let context = self.for_origin(&instruction, origins, Index(index));
            result
                .entry(instruction.address)
                .and_modify(|previous| previous.retain(|guard| context.contains(guard)))
                .or_insert(context);
        }
        result.retain(|_, context| !context.is_empty());
        if result.len() > 4096 {
            return Err(Status::Limit);
        }
        Ok(result)
    }
}
