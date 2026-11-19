use std::collections::VecDeque;

use binaryninja::architecture::{Register, RegisterInfo};
use binaryninja::calling_convention::CallingConvention;
use binaryninja::low_level_il::{
    LowLevelILRegisterKind, LowLevelILSSAFunction, LowLevelILSSARegisterKind,
    instruction::LowLevelInstructionIndex,
};
use binaryninja::variable::VariableSourceType;
use serde::{Deserialize, Serialize};

use super::*;
use crate::rust::layout;
use BNLowLevelILOperation::*;

type Bindings = BTreeMap<u32, u64>;

#[derive(Clone, Eq, PartialEq)]
enum Value {
    Constant(u64),
    Entry(u32, i64),
    ReturnAddress,
    Pointer(Place),
    Loaded(Place, usize),
}

impl Value {
    fn constant(self) -> Option<u64> {
        match self {
            Self::Constant(value) => Some(value),
            Self::Entry(_, _) | Self::ReturnAddress | Self::Pointer(_) | Self::Loaded(_, _) => None,
        }
    }

    fn pointer(self) -> Option<Place> {
        match self {
            Self::Pointer(place) | Self::Loaded(place, _) => Some(place),
            Self::Constant(_) | Self::Entry(_, _) | Self::ReturnAddress => None,
        }
    }

    fn add(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => Some(Self::Constant(a.wrapping_add(b))),
            (Self::Entry(register, offset), Self::Constant(value))
            | (Self::Constant(value), Self::Entry(register, offset)) => {
                let offset = offset.checked_add(value as i64)?;
                (offset.unsigned_abs() <= layout::MAX_OFFSET)
                    .then_some(Self::Entry(register, offset))
            }
            (Self::ReturnAddress, Self::Constant(0)) | (Self::Constant(0), Self::ReturnAddress) => {
                Some(Self::ReturnAddress)
            }
            (Self::Pointer(place), Self::Constant(offset))
            | (Self::Constant(offset), Self::Pointer(place)) => {
                place.shift(offset as i64).map(Self::Pointer)
            }
            (Self::Loaded(place, memory), Self::Constant(offset))
            | (Self::Constant(offset), Self::Loaded(place, memory)) => place
                .shift(offset as i64)
                .map(|place| Self::Loaded(place, memory)),
            _ => None,
        }
    }

    fn subtract(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => Some(Self::Constant(a.wrapping_sub(b))),
            (Self::Entry(register, offset), Self::Constant(value)) => {
                let offset = offset.checked_sub(value as i64)?;
                (offset.unsigned_abs() <= layout::MAX_OFFSET)
                    .then_some(Self::Entry(register, offset))
            }
            (Self::ReturnAddress, Self::Constant(0)) => Some(Self::ReturnAddress),
            (Self::Pointer(place), Self::Constant(offset)) => place
                .shift((offset as i64).checked_neg()?)
                .map(Self::Pointer),
            (Self::Loaded(place, memory), Self::Constant(offset)) => place
                .shift((offset as i64).checked_neg()?)
                .map(|place| Self::Loaded(place, memory)),
            _ => None,
        }
    }

    fn sized(self, width: usize, pointer_width: usize) -> Option<Self> {
        match self {
            Self::Constant(value) => mask(value, width).map(Self::Constant),
            Self::Entry(_, _) | Self::ReturnAddress | Self::Pointer(_) | Self::Loaded(_, _)
                if width == pointer_width =>
            {
                Some(self)
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(in crate::rust) struct Target {
    pub address: u64,
    pub target: Option<Key>,
    pub indirect: bool,
    pub registers: Bindings,
    pub parameters: Vec<Option<Place>>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(in crate::rust) struct Context {
    pub function: Key,
    pub registers: Bindings,
    pub calls: Vec<Target>,
}

/// Owned core SSA identity; SDK equality compares the owning function instead.
struct Low {
    il: Ref<LowLevelILSSAFunction>,
    raw: *mut BNLowLevelILFunction,
    calls: BTreeMap<u64, Vec<usize>>,
    returns: Vec<usize>,
}

impl Low {
    fn handle(function: &Function) -> Option<*mut BNLowLevelILFunction> {
        let function = FunctionHandle::new(function)?;
        unsafe {
            let regular = BNGetFunctionLowLevelILIfAvailable(function.as_ptr());
            if regular.is_null() {
                return None;
            }
            let raw = BNGetLowLevelILSSAForm(regular);
            BNFreeLowLevelILFunction(regular);
            (!raw.is_null()).then_some(raw)
        }
    }

    fn new(function: &Function) -> Option<Self> {
        let _regular = function.low_level_il().ok()?;
        let raw = Self::handle(function)?;
        Some(unsafe { Self::from_raw(raw) })
    }

    unsafe fn from_raw(raw: *mut BNLowLevelILFunction) -> Self {
        let il = unsafe { LowLevelILSSAFunction::from_raw(raw) }.to_owned();
        Self {
            il,
            raw,
            calls: BTreeMap::new(),
            returns: Vec::new(),
        }
    }

    fn current(&self, function: &Function) -> bool {
        Self::handle(function).is_some_and(|raw| {
            let same = self.raw == raw;
            unsafe { BNFreeLowLevelILFunction(raw) };
            same
        })
    }

    fn expression(&self, index: usize) -> Option<BNLowLevelILInstruction> {
        (index < self.il.expression_count())
            .then(|| unsafe { BNGetLowLevelILByIndex(self.raw, index) })
    }

    fn instruction(&self, index: usize) -> Option<BNLowLevelILInstruction> {
        (index < self.il.instruction_count())
            .then(|| unsafe { BNGetLowLevelILIndexForInstruction(self.raw, index) })
            .and_then(|index| self.expression(index))
    }

    fn call(&self, address: u64) -> Option<(usize, BNLowLevelILInstruction)> {
        let [index] = self.calls.get(&address)?.as_slice() else {
            return None;
        };
        Some((*index, self.instruction(*index)?))
    }

    fn operands(&self, expression: usize, operand: usize) -> Option<Vec<u64>> {
        let mut count = 0;
        let raw = unsafe { BNLowLevelILGetOperandList(self.raw, expression, operand, &mut count) };
        let result = if count == 0 {
            Some(Vec::new())
        } else if raw.is_null() || count > 512 {
            None
        } else {
            Some(unsafe { std::slice::from_raw_parts(raw, count) }.to_vec())
        };
        if !raw.is_null() {
            unsafe { BNLowLevelILFreeOperandList(raw) };
        }
        result
    }

    fn stack_at_call(&self, call: &BNLowLevelILInstruction) -> Option<(i64, usize)> {
        let arch = self.il.function()?.arch();
        if arch.name() != "x86_64" {
            return None;
        }
        let pointer = arch.stack_pointer_reg()?;
        let stack = self.expression(call.operands[2] as usize)?;
        if stack.operation != LLIL_CALL_STACK_SSA || stack.operands[0] != u64::from(pointer.id().0)
        {
            return None;
        }
        let register = LowLevelILSSARegisterKind::new_full(
            LowLevelILRegisterKind::Arch(pointer),
            u32::try_from(stack.operands[1]).ok()?,
        );
        let value = self.il.get_ssa_register_value(register)?;
        (value.state == BNRegisterValueType::StackFrameOffset)
            .then_some((value.value, stack.operands[2] as usize))
    }
}

impl Drop for Low {
    fn drop(&mut self) {
        unsafe { BNFreeLowLevelILFunction(self.raw) };
    }
}

struct Query {
    value: Option<Value>,
    depth: usize,
    generation: usize,
}

struct Resolver<'a> {
    in_callback: bool,
    inputs: BTreeMap<Key, &'a Input>,
    functions: BTreeMap<Key, Ref<Function>>,
    low: BTreeMap<Key, Low>,
    entries: BTreeMap<Key, Vec<u32>>,
    queries: BTreeMap<(Key, usize, u32, Bindings), Query>,
    generation: usize,
    reads: BTreeMap<Key, BTreeMap<(u64, usize), Vec<u8>>>,
    exits: BTreeMap<Key, BTreeMap<u32, Option<u32>>>,
    verified_exits: BTreeMap<(Key, u32, Bindings), Option<u32>>,
    preserved: BTreeMap<(Key, i64, usize, Bindings), bool>,
    arguments: BTreeMap<Key, Option<BTreeSet<u32>>>,
    frames: BTreeMap<Key, bool>,
    budget: &'a mut Budget,
    cancelled: &'a dyn Fn() -> bool,
    status: Option<Status>,
}

impl Resolver<'_> {
    fn insert_low(&mut self, key: Key, mut low: Low) -> Option<()> {
        // Address lookup can return non-SSA indices even on an SSA handle.
        // Index actual SSA call instructions once, under the shared work budget.
        for index in 0..low.il.instruction_count() {
            self.spend()?;
            let instruction = low.instruction(index)?;
            if matches!(instruction.operation, LLIL_CALL_SSA | LLIL_TAILCALL_SSA) {
                low.calls
                    .entry(instruction.address)
                    .or_default()
                    .push(index);
            }
            if matches!(instruction.operation, LLIL_RET | LLIL_TAILCALL_SSA) {
                low.returns.push(index);
            }
        }
        let arch = self.functions[&key].arch();
        let stack = arch.stack_pointer_reg().map(|register| register.id());
        let registers: Vec<_> = arch
            .registers_full_width()
            .into_iter()
            .filter(|register| {
                register.info().size() == self.inputs[&key].pointer_width
                    && Some(register.id()) != stack
            })
            .collect();
        let mut entries = Vec::new();
        for register in registers {
            self.spend()?;
            let mut count = 0;
            let uses =
                unsafe { BNGetLowLevelILSSARegisterUses(low.raw, register.id().0, 0, &mut count) };
            if !uses.is_null() {
                unsafe { BNFreeILInstructionList(uses) };
            }
            if count != 0 {
                entries.push(register.id().0);
            }
        }
        self.entries.insert(key.clone(), entries);
        self.low.insert(key, low);
        Some(())
    }

    fn prepare(&mut self, key: &Key) -> Option<()> {
        if !self.low.contains_key(key) {
            let function = self.functions.get(key)?;
            let low = unsafe { Low::from_raw(Low::handle(function)?) };
            self.insert_low(key.clone(), low)?;
        }
        Some(())
    }

    fn argument_inputs(&mut self, key: &Key, depth: usize) -> Option<BTreeSet<u32>> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        if let Some(known) = self.arguments.get(key) {
            return known.clone();
        }
        self.arguments.insert(key.clone(), None);
        let result = (|| {
            self.prepare(key)?;
            let convention = self.functions[key].calling_convention()?.contents;
            let bank: BTreeSet<_> = convention
                .int_arg_registers()
                .iter()
                .map(|reg| reg.0)
                .collect();
            let mut preserved: BTreeSet<_> = convention
                .callee_saved_registers()
                .iter()
                .map(|reg| reg.0)
                .collect();
            preserved.insert(self.functions[key].arch().stack_pointer_reg()?.id().0);
            let mut result = BTreeSet::new();
            for index in 0..self.low[key].il.expression_count() {
                self.spend()?;
                let instruction = self.low[key].expression(index)?;
                let count = match instruction.operation {
                    LLIL_REG_SSA | LLIL_REG_SSA_PARTIAL => 1,
                    LLIL_REG_SPLIT_SSA => 2,
                    LLIL_REG_STACK_REL_SSA | LLIL_REG_STACK_ABS_SSA => return None,
                    _ => continue,
                };
                let position =
                    unsafe { BNGetLowLevelILInstructionForExpr(self.low[key].raw, index) };
                let owner = self.low[key].instruction(position)?;
                // Call-parameter scaffolding includes inferred, unused register slots.
                if !matches!(owner.operation, LLIL_CALL_SSA | LLIL_TAILCALL_SSA) {
                    for register in instruction.operands[..count * 2].chunks_exact(2) {
                        if register[1] != 0 {
                            continue;
                        }
                        let register = register[0] as u32;
                        if bank.contains(&register) {
                            result.insert(register);
                        } else if !preserved.contains(&register) {
                            return None;
                        }
                    }
                }
            }
            let calls: Vec<_> = self.low[key].calls.values().flatten().copied().collect();
            for position in calls {
                let call = self.low[key].instruction(position)?;
                let target = Key {
                    address: self.destination(key, call.address, &Bindings::new(), 0)?,
                    platform: key.platform.clone(),
                };
                for register in self.argument_inputs(&target, depth + 1)? {
                    let value = self.before(key, position, register, &Bindings::new(), 0)?;
                    let register = match value {
                        Value::Constant(_) => continue,
                        Value::Entry(register, _) => register,
                        Value::Pointer(place) | Value::Loaded(place, _) => {
                            let layout::Root::Parameter(parameter) = place.root else {
                                return None;
                            };
                            abi::word_register(
                                self.inputs[key].contract.parameters.get(parameter)?,
                                8,
                            )?
                        }
                        Value::ReturnAddress => return None,
                    };
                    if !bank.contains(&register) {
                        return None;
                    }
                    result.insert(register);
                }
            }
            Some(result)
        })();
        if let Some(value) = &result {
            self.arguments.insert(key.clone(), Some(value.clone()));
        } else {
            self.arguments.remove(key);
        }
        result
    }

    fn return_frame(&mut self, key: &Key, depth: usize) -> Option<()> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        if let Some(known) = self.frames.get(key) {
            return known.then_some(());
        }
        self.frames.insert(key.clone(), false);
        let result = (|| {
            self.prepare(key)?;
            let function = self.functions[key].clone();
            if function.arch().name() != "x86_64" || self.inputs[key].informed {
                return None;
            }
            let stack = function.arch().stack_pointer_reg()?.id().0;
            let calls: Vec<_> = self.low[key].calls.values().flatten().copied().collect();
            for position in calls {
                let call = self.low[key].instruction(position)?;
                let target = Key {
                    address: self.destination(key, call.address, &Bindings::new(), 0)?,
                    platform: key.platform.clone(),
                };
                self.return_frame(&target, depth + 1)?;
            }
            let returns = self.low[key].returns.clone();
            if returns.is_empty() {
                return None;
            }
            for position in returns {
                let instruction = self.low[key].instruction(position)?;
                if self.before(key, position, stack, &Bindings::new(), 0)? != Value::Entry(stack, 0)
                {
                    return None;
                }
                let address = if instruction.operation == LLIL_TAILCALL_SSA {
                    let (_, memory) = self.low[key].stack_at_call(&instruction)?;
                    self.stack(key, 0, 8, memory, &Bindings::new(), 0)?
                } else {
                    self.llil(
                        key,
                        instruction.operands[0] as usize,
                        position,
                        &Bindings::new(),
                        0,
                    )?
                };
                if address != Value::ReturnAddress {
                    return None;
                }
            }
            if !self.low[key].current(&function) {
                return None;
            }
            Some(())
        })();
        if result.is_some() {
            self.frames.insert(key.clone(), true);
        } else {
            self.frames.remove(key);
        }
        result
    }

    fn wire(&mut self, key: &Key) -> Option<layout::Wire> {
        let function = self.functions[key].clone();
        let input = self.inputs[key];
        if !crate::rust::library::eligible(&function, &input.contract) || input.informed {
            return None;
        }
        let convention = function.calling_convention()?.contents;
        let output = abi::word_register(&input.contract.result, 8)?;
        if convention.return_int_reg()?.0 != output {
            return None;
        }
        let arguments = self.argument_inputs(key, 0)?;
        if arguments.len() != 1 {
            return None;
        }
        let register = *arguments.first()?;
        if self.return_entry(key, output, &Bindings::new(), 0)? != register {
            return None;
        }
        self.return_frame(key, 0)?;
        for saved in convention.callee_saved_registers() {
            if self.return_entry(key, saved.0, &Bindings::new(), 0)? != saved.0 {
                return None;
            }
        }
        let parameter = input
            .contract
            .parameters
            .iter()
            .position(|slot| abi::word_register(slot, 8) == Some(register))?;
        Some(layout::Wire {
            input: register,
            output,
            parameter,
        })
    }

    fn spend(&mut self) -> Option<()> {
        if (self.cancelled)() {
            self.status = Some(Status::Cancelled);
        }
        if self.status.is_some() {
            return None;
        }
        match self.budget.expressions.checked_sub(1) {
            Some(left) => {
                self.budget.expressions = left;
                Some(())
            }
            None => {
                self.status = Some(Status::Limit);
                None
            }
        }
    }

    fn incoming(&self, key: &Key, register: u32, context: &Bindings) -> Option<Value> {
        if let Some(value) = context.get(&register) {
            return Some(Value::Constant(*value));
        }
        let input = self.inputs[key];
        input
            .contract
            .parameters
            .iter()
            .position(|slot| abi::word_register(slot, input.pointer_width) == Some(register))
            .map(|parameter| Value::Pointer(Place::parameter(parameter)))
            .or(Some(Value::Entry(register, 0)))
    }

    fn word(&mut self, key: &Key, address: u64, width: usize) -> Option<u64> {
        self.spend()?;
        if !(1..=8).contains(&width) {
            return None;
        }
        let input = self.inputs[key];
        let range = address..address.checked_add(width as u64)?;
        let view = self.functions[key].view();
        if !readonly(&view, &range) {
            return None;
        }
        let reads = self.reads.entry(key.clone()).or_default();
        if !reads.contains_key(&(address, width)) {
            let Some(left) = self.budget.bytes.checked_sub(width) else {
                self.status = Some(Status::Limit);
                return None;
            };
            self.budget.bytes = left;
            let raw = view.read_vec(address, width);
            if raw.len() != width {
                return None;
            }
            reads.insert((address, width), raw);
        }
        let bytes = &reads[&(address, width)];
        Some(if input.little_endian {
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

    fn destination(
        &mut self,
        key: &Key,
        address: u64,
        context: &Bindings,
        depth: usize,
    ) -> Option<u64> {
        if adjusted(&self.functions[key], address) {
            return None;
        }
        let (position, call) = self.low.get(key)?.call(address)?;
        self.llil(key, call.operands[1] as usize, position, context, depth + 1)?
            .constant()
    }

    fn exit(
        &mut self,
        caller: &Key,
        target: u64,
        address: u64,
        register: u32,
        incoming: &Bindings,
        depth: usize,
    ) -> Option<u32> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        let key = Key {
            address: target,
            platform: caller.platform.clone(),
        };
        let input = self.inputs.get(&key)?;
        let function = self.functions.get(&key)?.clone();
        if input.informed
            || input.sources.is_empty()
            || function.arch() != self.functions[caller].arch()
            || (self.in_callback && (key == *caller || function.is_update_needed()))
        {
            return None;
        }
        self.prepare(&key)?;
        let mut context = Bindings::new();
        for register in self.entries.get(&key).cloned().unwrap_or_default() {
            if let Some(value) = self
                .at(caller, address, register, incoming, depth + 1)
                .and_then(Value::constant)
            {
                context.insert(register, value);
            }
        }
        self.return_entry(&key, register, &context, depth)
    }

    fn return_entry(
        &mut self,
        key: &Key,
        register: u32,
        context: &Bindings,
        depth: usize,
    ) -> Option<u32> {
        self.spend()?;
        if depth >= 32 || self.inputs[key].informed || self.inputs[key].sources.is_empty() {
            return None;
        }
        self.prepare(key)?;
        let function = self.functions[key].clone();
        let cache = (key.clone(), register, context.clone());
        if let Some(known) = self.verified_exits.get(&cache) {
            return *known;
        }
        self.verified_exits.insert(cache.clone(), None);
        let result = (|| {
            let witness = exit_entry(&function, register);
            let result = function
                .calling_convention()
                .and_then(|convention| convention.contents.return_int_reg())
                .is_some_and(|result| result.0 == register);
            let argument = result
                .then(|| self.arguments.get(key)?.as_ref())
                .flatten()
                .filter(|arguments| arguments.len() == 1)
                .and_then(|arguments| arguments.first().copied());
            // A candidate input still needs the same proof over every machine return.
            let entry = witness.or(argument).unwrap_or(register);
            let expected = self.incoming(key, entry, context)?;
            let returns = self.low[key].returns.clone();
            if returns.is_empty() {
                return None;
            }
            for index in returns {
                let instruction = self.low[key].instruction(index)?;
                let value = if instruction.operation == LLIL_TAILCALL_SSA {
                    let target = self.destination(key, instruction.address, context, depth + 1)?;
                    let entry = self.exit(
                        key,
                        target,
                        instruction.address,
                        register,
                        context,
                        depth + 1,
                    )?;
                    self.at(key, instruction.address, entry, context, depth + 1)?
                } else {
                    self.before(key, index, register, context, depth + 1)?
                };
                if value != expected {
                    return None;
                }
            }
            if !self.low[key].current(&function) {
                return None;
            }
            self.exits
                .entry(key.clone())
                .or_default()
                .insert(register, witness);
            Some(entry)
        })();
        if let Some(entry) = result {
            self.verified_exits.insert(cache, Some(entry));
            self.generation += 1;
        } else {
            // Failure may depend on the remaining depth; retain only proven results.
            self.verified_exits.remove(&cache);
        }
        result
    }

    fn result(&self, key: &Key, address: u64, register: u32, target: Option<u64>) -> Option<Value> {
        let callee = self.inputs.get(&Key {
            address: target?,
            platform: key.platform.clone(),
        })?;
        if abi::word_register(&callee.contract.result, self.inputs[key].pointer_width)
            != Some(register)
        {
            return None;
        }
        let mut calls = self.inputs[key]
            .calls
            .iter()
            .filter(|call| call.address == address);
        let call = calls.next()?;
        if calls.next().is_some() || call.adjusted {
            return None;
        }
        let output = Variable::from_identifier(call.output?);
        (output.ty == VariableSourceType::RegisterVariableSourceType
            && output.storage == i64::from(register))
        .then(|| Value::Pointer(Place::call(address)))
    }

    fn register(
        &mut self,
        key: &Key,
        register: u32,
        version: usize,
        context: &Bindings,
        depth: usize,
    ) -> Option<Value> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        if version == 0 {
            return self.incoming(key, register, context);
        }
        let low = self.low.get(key)?;
        let index = unsafe { BNGetLowLevelILSSARegisterDefinition(low.raw, register, version) };
        let instruction = low.instruction(index)?;
        let operands = instruction.operands;
        match instruction.operation {
            LLIL_SET_REG_SSA => self.llil(key, operands[2] as usize, index, context, depth + 1),
            LLIL_REG_PHI => self.before(key, index, register, context, depth + 1),
            LLIL_CALL_SSA => {
                if adjusted(&self.functions[key], instruction.address) {
                    return None;
                }
                let target = self
                    .llil(key, operands[1] as usize, index, context, depth + 1)
                    .and_then(Value::constant);
                let entry = target.and_then(|target| {
                    self.exit(
                        key,
                        target,
                        instruction.address,
                        register,
                        context,
                        depth + 1,
                    )
                });
                match entry {
                    Some(entry) => self.at(key, instruction.address, entry, context, depth + 1),
                    None => self.result(key, instruction.address, register, target),
                }
            }
            _ => None,
        }
    }

    fn llil(
        &mut self,
        key: &Key,
        index: usize,
        position: usize,
        context: &Bindings,
        depth: usize,
    ) -> Option<Value> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        let low = self.low.get(key)?;
        let instruction = low.expression(index)?;
        let operands = instruction.operands;
        let result = match instruction.operation {
            LLIL_CONST | LLIL_CONST_PTR => Some(Value::Constant(operands[0])),
            LLIL_REG_SSA => self.before(key, position, operands[0] as u32, context, depth),
            LLIL_ADD => self
                .llil(key, operands[0] as usize, position, context, depth + 1)?
                .add(self.llil(key, operands[1] as usize, position, context, depth + 1)?),
            LLIL_SUB => self
                .llil(key, operands[0] as usize, position, context, depth + 1)?
                .subtract(self.llil(key, operands[1] as usize, position, context, depth + 1)?),
            LLIL_ZX | LLIL_LOW_PART => {
                self.llil(key, operands[0] as usize, position, context, depth + 1)
            }
            LLIL_LOAD_SSA => {
                let address = unsafe { BNGetLowLevelILExprValue(low.raw, operands[0] as usize) };
                if address.state == BNRegisterValueType::StackFrameOffset {
                    self.stack(
                        key,
                        address.value,
                        instruction.size,
                        operands[1] as usize,
                        context,
                        depth + 1,
                    )
                } else {
                    let memory = operands[1] as usize;
                    match self.llil(key, operands[0] as usize, position, context, depth + 1)? {
                        Value::Constant(address) => self
                            .word(key, address, instruction.size)
                            .map(Value::Constant),
                        Value::Pointer(place) => Some(Value::Loaded(place.load()?, memory)),
                        Value::Loaded(place, previous) if previous == memory => {
                            Some(Value::Loaded(place.load()?, memory))
                        }
                        _ => None,
                    }
                }
            }
            _ => None,
        }?;
        result.sized(instruction.size, self.inputs[key].pointer_width)
    }

    /// Follow exact stores; calls require a checked callee and a protected caller slot.
    fn stack(
        &mut self,
        key: &Key,
        offset: i64,
        width: usize,
        memory: usize,
        context: &Bindings,
        depth: usize,
    ) -> Option<Value> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        if memory == 0 {
            return (offset == 0 && width == 8 && self.functions[key].arch().name() == "x86_64")
                .then_some(Value::ReturnAddress);
        }
        let low = self.low.get(key)?;
        let index = unsafe { BNGetLowLevelILSSAMemoryDefinition(low.raw, memory) };
        let instruction = low.instruction(index)?;
        let operands = instruction.operands;
        match instruction.operation {
            LLIL_STORE_SSA => {
                let destination =
                    unsafe { BNGetLowLevelILExprValue(low.raw, operands[0] as usize) };
                if destination.state != BNRegisterValueType::StackFrameOffset {
                    return None;
                }
                if destination.value == offset && instruction.size == width {
                    self.llil(key, operands[3] as usize, index, context, depth + 1)
                } else if offset.checked_add(width as i64)? <= destination.value
                    || destination
                        .value
                        .checked_add(i64::try_from(instruction.size).ok()?)?
                        <= offset
                {
                    self.stack(key, offset, width, operands[2] as usize, context, depth + 1)
                } else {
                    None
                }
            }
            LLIL_MEM_PHI => {
                let expression = unsafe { BNGetLowLevelILIndexForInstruction(low.raw, index) };
                let versions = low.operands(expression, 1)?;
                let mut values = Vec::new();
                for version in versions {
                    values.push(self.stack(
                        key,
                        offset,
                        width,
                        version as usize,
                        context,
                        depth + 1,
                    )?);
                }
                agree(values)
            }
            LLIL_CALL_SSA => {
                let memory =
                    self.preserve_call(key, &instruction, offset, width, context, depth + 1)?;
                self.stack(key, offset, width, memory, context, depth + 1)
            }
            _ => None,
        }
    }

    fn preserve_call(
        &mut self,
        key: &Key,
        call: &BNLowLevelILInstruction,
        offset: i64,
        width: usize,
        context: &Bindings,
        depth: usize,
    ) -> Option<usize> {
        self.spend()?;
        if depth >= 32 || adjusted(&self.functions[key], call.address) {
            return None;
        }
        let (stack, memory) = self.low.get(key)?.stack_at_call(call)?;
        let entry = if call.operation == LLIL_TAILCALL_SSA {
            stack
        } else {
            stack.checked_sub(8)?
        };
        // Include the callee's incoming return slot, even for tail transfers.
        if offset < entry.checked_add(8)? {
            return None;
        }
        let target = self.destination(key, call.address, context, depth + 1)?;
        let target = Key {
            address: target,
            platform: key.platform.clone(),
        };
        self.prepare(&target)?;
        let mut child = Bindings::new();
        for register in self.entries.get(&target).cloned().unwrap_or_default() {
            if let Some(value) = self
                .at(key, call.address, register, context, depth + 1)
                .and_then(Value::constant)
            {
                child.insert(register, value);
            }
        }
        self.preserves(
            &target,
            offset.checked_sub(entry)?,
            width,
            &child,
            depth + 1,
        )?;
        Some(memory)
    }

    /// Prove that machine stores and nested calls cannot overlap this caller slot.
    fn preserves(
        &mut self,
        key: &Key,
        offset: i64,
        width: usize,
        context: &Bindings,
        depth: usize,
    ) -> Option<()> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        let cache = (key.clone(), offset, width, context.clone());
        if let Some(known) = self.preserved.get(&cache) {
            return known.then_some(());
        }
        self.preserved.insert(cache.clone(), false);
        let result = (|| {
            let input = self.inputs.get(key)?;
            let function = self.functions.get(key)?.clone();
            if input.informed || input.sources.is_empty() || function.is_update_needed() {
                return None;
            }
            self.prepare(key)?;
            let count = self.low[key].il.expression_count();
            for index in 0..count {
                self.spend()?;
                let instruction = self.low[key].expression(index)?;
                match instruction.operation {
                    LLIL_STORE_SSA => {
                        let destination = unsafe {
                            BNGetLowLevelILExprValue(
                                self.low[key].raw,
                                instruction.operands[0] as usize,
                            )
                        };
                        if destination.state != BNRegisterValueType::StackFrameOffset {
                            return None;
                        }
                        if !(offset.checked_add(i64::try_from(width).ok()?)? <= destination.value
                            || destination
                                .value
                                .checked_add(i64::try_from(instruction.size).ok()?)?
                                <= offset)
                        {
                            return None;
                        }
                    }
                    LLIL_CALL_SSA | LLIL_TAILCALL_SSA => {
                        self.preserve_call(key, &instruction, offset, width, context, depth + 1)?;
                    }
                    LLIL_NOP
                    | LLIL_SET_REG_SSA
                    | LLIL_SET_REG_SSA_PARTIAL
                    | LLIL_SET_FLAG_SSA
                    | LLIL_REG_SSA
                    | LLIL_FLAG_SSA
                    | LLIL_REG_PHI
                    | LLIL_FLAG_PHI
                    | LLIL_MEM_PHI
                    | LLIL_CONST
                    | LLIL_CONST_PTR
                    | LLIL_LOAD_SSA
                    | LLIL_RET
                    | LLIL_IF
                    | LLIL_GOTO
                    | LLIL_ADD
                    | LLIL_SUB
                    | LLIL_MUL
                    | LLIL_AND
                    | LLIL_OR
                    | LLIL_XOR
                    | LLIL_NOT
                    | LLIL_NEG
                    | LLIL_ZX
                    | LLIL_SX
                    | LLIL_LOW_PART
                    | LLIL_LSL
                    | LLIL_LSR
                    | LLIL_ASR
                    | LLIL_CMP_E
                    | LLIL_CMP_NE
                    | LLIL_CMP_ULT
                    | LLIL_CMP_ULE
                    | LLIL_CMP_UGT
                    | LLIL_CMP_UGE
                    | LLIL_CMP_SLT
                    | LLIL_CMP_SLE
                    | LLIL_CMP_SGT
                    | LLIL_CMP_SGE
                    | LLIL_CALL_OUTPUT_SSA
                    | LLIL_CALL_STACK_SSA
                    | LLIL_CALL_PARAM
                    | LLIL_SEPARATE_PARAM_LIST_SSA
                    | LLIL_SHARED_PARAM_SLOT_SSA => (),
                    _ => return None,
                }
            }
            if !self.low[key].current(&function) {
                return None;
            }
            Some(())
        })();
        if result.is_some() {
            self.preserved.insert(cache, true);
            self.generation += 1;
        } else {
            self.preserved.remove(&cache);
        }
        result
    }

    fn reaching(
        &mut self,
        key: &Key,
        start: usize,
        end: usize,
        register: u32,
        seen: &mut BTreeSet<(usize, usize)>,
        context: &Bindings,
        depth: usize,
    ) -> Option<Vec<(u32, usize)>> {
        self.spend()?;
        if depth >= 32 || seen.len() >= 32 || !seen.insert((start, end)) {
            return None;
        }
        for index in (start..end).rev() {
            self.spend()?;
            let instruction = self.low.get(key)?.instruction(index)?;
            let operands = instruction.operands;
            match instruction.operation {
                LLIL_SET_REG_SSA | LLIL_SET_REG_SSA_PARTIAL | LLIL_REG_PHI => {
                    if operands[0] == u64::from(register) {
                        return Some(vec![(register, operands[1] as usize)]);
                    }
                }
                LLIL_CALL_SSA | LLIL_TAILCALL_SSA => {
                    if adjusted(&self.functions[key], instruction.address) {
                        return None;
                    }
                    let low = self.low.get(key)?;
                    let output = low.expression(operands[0] as usize)?;
                    if output.operation != LLIL_CALL_OUTPUT_SSA {
                        return None;
                    }
                    let registers = low.operands(operands[0] as usize, 1)?;
                    for pair in registers.chunks_exact(2) {
                        if pair[0] == u64::from(register) {
                            return Some(vec![(register, pair[1] as usize)]);
                        }
                    }
                    let target = self
                        .llil(key, operands[1] as usize, index, context, depth + 1)?
                        .constant()?;
                    if self.exit(
                        key,
                        target,
                        instruction.address,
                        register,
                        context,
                        depth + 1,
                    )? != register
                    {
                        return None;
                    }
                }
                LLIL_NOP | LLIL_STORE_SSA | LLIL_SET_FLAG_SSA | LLIL_IF | LLIL_GOTO
                | LLIL_MEM_PHI => (),
                _ => return None,
            }
        }
        let block = self
            .low
            .get(key)?
            .il
            .basic_block_containing_index(LowLevelInstructionIndex(start))?;
        let incoming: Vec<_> = block
            .incoming_edges()
            .iter()
            .map(|edge| (edge.source.start_index().0, edge.source.end_index().0))
            .collect();
        drop(block);
        if incoming.is_empty() {
            return Some(vec![(register, 0)]);
        }
        let mut result = Vec::new();
        for (start, end) in incoming {
            result.extend(self.reaching(
                key,
                start,
                end,
                register,
                &mut seen.clone(),
                context,
                depth + 1,
            )?);
            if result.len() > 256 {
                self.status = Some(Status::Limit);
                return None;
            }
        }
        Some(result)
    }

    fn before(
        &mut self,
        key: &Key,
        index: usize,
        register: u32,
        context: &Bindings,
        depth: usize,
    ) -> Option<Value> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        let cache = (key.clone(), index, register, context.clone());
        if let Some(query) = self.queries.get(&cache)
            && (query.value.is_some()
                || (query.depth <= depth && query.generation == self.generation))
        {
            return query.value.clone();
        }
        let value = (|| {
            let start = self
                .low
                .get(key)?
                .il
                .basic_block_containing_index(LowLevelInstructionIndex(index))?
                .start_index()
                .0;
            let definitions = self.reaching(
                key,
                start,
                index,
                register,
                &mut BTreeSet::new(),
                context,
                depth,
            )?;
            let mut values = Vec::new();
            for (register, version) in definitions {
                values.push(self.register(key, register, version, context, depth + 1)?);
            }
            agree(values)
        })();
        self.queries.insert(
            cache,
            Query {
                value: value.clone(),
                depth,
                generation: self.generation,
            },
        );
        value
    }

    fn at(
        &mut self,
        key: &Key,
        address: u64,
        register: u32,
        context: &Bindings,
        depth: usize,
    ) -> Option<Value> {
        self.spend()?;
        if depth >= 32 {
            return None;
        }
        let low = self.low.get(key)?;
        let sites = low.calls.get(&address)?;
        if sites.len() > 256 {
            self.status = Some(Status::Limit);
            return None;
        }
        let mut calls = sites.iter().filter_map(|index| {
            low.instruction(*index)
                .filter(|i| matches!(i.operation, LLIL_CALL_SSA | LLIL_TAILCALL_SSA))
                .map(|_| *index)
        });
        let index = calls.next()?;
        if calls.next().is_some() {
            return None;
        }
        let call = low.instruction(index)?;
        let stack = low.expression(call.operands[2] as usize)?;
        if stack.operation != LLIL_CALL_STACK_SSA {
            return None;
        }
        let memory = stack.operands[2] as usize;
        let value = self.before(key, index, register, context, depth)?;
        match value {
            Value::Loaded(_, epoch) if epoch != memory => None,
            _ => Some(value),
        }
    }
}

fn agree<T: PartialEq>(values: Vec<T>) -> Option<T> {
    let mut values = values.into_iter();
    let first = values.next()?;
    values.all(|value| value == first).then_some(first)
}

fn mask(value: u64, width: usize) -> Option<u64> {
    (1..=8)
        .contains(&width)
        .then(|| value & (u64::MAX >> (64 - 8 * width)))
}

/// Bound contexts share the ordinary layout solver, but never replace global types.
pub(in crate::rust) fn layouts(
    inputs: &[Input],
    contexts: &[Context],
    cancelled: impl Fn() -> bool,
) -> Result<Vec<layout::Layout>, Status> {
    let by_key: BTreeMap<_, _> = inputs
        .iter()
        .enumerate()
        .map(|(index, input)| (&input.key, index))
        .collect();
    let mut variants = layout::variants(inputs);
    let mut indices = BTreeMap::new();
    for context in contexts {
        let Some(&input) = by_key.get(&context.function) else {
            return Err(Status::Unavailable);
        };
        let index = if context.registers.is_empty() {
            input
        } else {
            let index = variants.len();
            variants.push(layout::Variant {
                input,
                calls: Vec::new(),
            });
            index
        };
        if indices
            .insert((&context.function, &context.registers), index)
            .is_some()
        {
            return Err(Status::Unavailable);
        }
    }
    for context in contexts {
        if cancelled() {
            return Err(Status::Cancelled);
        }
        let index = indices[&(&context.function, &context.registers)];
        let input = &inputs[variants[index].input];
        let mut calls = Vec::new();
        for edge in &context.calls {
            let Some(target) = &edge.target else { continue };
            let Some(&callee) = indices.get(&(target, &edge.registers)) else {
                continue;
            };
            let mut sites = input
                .calls
                .iter()
                .filter(|call| call.address == edge.address);
            let Some(call) = sites.next().filter(|call| !call.adjusted) else {
                continue;
            };
            if sites.next().is_some() {
                continue;
            }
            let mut call = call.clone();
            call.target = Some(target.clone());
            call.parameters = edge.parameters.clone();
            calls.push((callee, call));
        }
        variants[index].calls = calls;
    }
    let mut result = layout::solve_variants(inputs, &variants, cancelled)?;
    result.truncate(inputs.len());
    Ok(result)
}

/// Recompute local targets from the current, original workflow LLIL.
/// The model may provide dependencies, never the destination expression being proved.
pub(in crate::rust) unsafe fn local(
    view: &BinaryView,
    context: *mut BNAnalysisContext,
    key: &Key,
    inputs: &[Input],
    candidates: &BTreeMap<u64, u64>,
) -> Result<BTreeMap<u64, u64>, Status> {
    let functions: BTreeMap<_, _> = inputs
        .iter()
        .filter_map(|input| {
            view.function_at(&*Platform::by_name(&input.key.platform)?, input.key.address)
                .map(|function| (input.key.clone(), function))
        })
        .collect();
    if functions.len() != inputs.len() {
        return Err(Status::Unavailable);
    }
    let regular = unsafe { BNAnalysisContextGetLowLevelILFunction(context) };
    if regular.is_null() {
        return Err(Status::Unavailable);
    }
    let raw = unsafe { BNGetLowLevelILSSAForm(regular) };
    unsafe { BNFreeLowLevelILFunction(regular) };
    if raw.is_null() {
        return Err(Status::Unavailable);
    }
    let low = unsafe { Low::from_raw(raw) };
    let mut budget = Budget {
        expressions: 100_000,
        bytes: 1_048_576,
    };
    let mut resolver = Resolver {
        in_callback: true,
        inputs: inputs
            .iter()
            .map(|input| (input.key.clone(), input))
            .collect(),
        functions,
        low: BTreeMap::new(),
        entries: BTreeMap::new(),
        queries: BTreeMap::new(),
        generation: 0,
        reads: BTreeMap::new(),
        exits: BTreeMap::new(),
        verified_exits: BTreeMap::new(),
        preserved: BTreeMap::new(),
        arguments: BTreeMap::new(),
        frames: BTreeMap::new(),
        budget: &mut budget,
        cancelled: &|| false,
        status: None,
    };
    resolver
        .insert_low(key.clone(), low)
        .ok_or(resolver.status.unwrap_or(Status::Unavailable))?;
    let mut found = BTreeMap::new();
    for (&address, &expected) in candidates {
        if adjusted(&resolver.functions[key], address) {
            continue;
        }
        if resolver.destination(key, address, &Bindings::new(), 0) == Some(expected) {
            found.insert(address, expected);
        }
    }
    if let Some(status) = resolver.status {
        return Err(status);
    }
    for (key, reads) in &resolver.reads {
        let input = resolver.inputs[key];
        for (&(address, width), bytes) in reads {
            let end = address
                .checked_add(width as u64)
                .ok_or(Status::Unavailable)?;
            if !input
                .readonly
                .iter()
                .any(|range| range.start <= address && end <= range.end)
                || view.read_vec(address, width) != *bytes
            {
                return Err(Status::Unavailable);
            }
        }
    }
    for (key, registers) in &resolver.exits {
        if registers.iter().any(|(register, entry)| {
            resolver.inputs[key].register_exits.get(register) != Some(entry)
        }) {
            return Err(Status::Unavailable);
        }
    }
    Ok(found)
}

pub(in crate::rust) fn collect(
    sources: &mut Vec<Source>,
    roots: &[Key],
    budget: &mut Budget,
    cancelled: &dyn Fn() -> bool,
) -> Result<Vec<Context>, Status> {
    let requested: BTreeSet<_> = sources
        .iter()
        .filter(|source| {
            crate::rust::library::probe(&source.ssa.il.function(), &source.input.contract)
        })
        .map(|source| source.input.key.clone())
        .collect();
    if requested.is_empty()
        && !sources.iter().any(|source| {
            source.input.calls.iter().any(|call| {
                (call.target.is_none()
                    || source.input.overlaid.contains_key(&call.address)
                    || call.parameters.iter().any(Option::is_none))
                    && !call.adjusted
            })
        })
    {
        return Ok(Vec::new());
    }
    let mut owned: BTreeMap<_, _> = std::mem::take(sources)
        .into_iter()
        .map(|s| (s.input.key.clone(), s))
        .collect();
    let mut resolver = Resolver {
        in_callback: false,
        inputs: owned
            .iter()
            .map(|(key, source)| (key.clone(), &source.input))
            .collect(),
        functions: owned
            .iter()
            .map(|(key, source)| (key.clone(), source.ssa.il.function()))
            .collect(),
        low: BTreeMap::new(),
        entries: BTreeMap::new(),
        queries: BTreeMap::new(),
        generation: 0,
        reads: BTreeMap::new(),
        exits: BTreeMap::new(),
        verified_exits: BTreeMap::new(),
        preserved: BTreeMap::new(),
        arguments: BTreeMap::new(),
        frames: BTreeMap::new(),
        budget,
        cancelled,
        status: None,
    };
    for (key, source) in &owned {
        let function = source.ssa.il.function();
        let Some(low) = Low::new(&function) else {
            continue;
        };
        resolver
            .insert_low(key.clone(), low)
            .ok_or(resolver.status.unwrap_or(Status::Unavailable))?;
    }
    let mut wires = BTreeMap::new();
    for key in requested {
        if let Some(wire) = resolver.wire(&key) {
            wires.insert(key, wire);
        }
    }
    let mut queue: VecDeque<_> = roots
        .iter()
        .cloned()
        .map(|key| (key, Bindings::new()))
        .collect();
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    while let Some((key, registers)) = queue.pop_front() {
        if !seen.insert((key.clone(), registers.clone())) {
            continue;
        }
        if seen.len() > 256 {
            return Err(Status::Limit);
        }
        resolver.spend();
        let Some(source) = owned.get(&key).filter(|s| !s.input.informed) else {
            continue;
        };
        let function = source.ssa.il.function();
        let mut calls = Vec::new();
        for (&index, call) in source.call_sites.iter().zip(&source.input.calls) {
            let instruction = source
                .ssa
                .il
                .instruction_from_expr_index(index)
                .ok_or(Status::Unavailable)?;
            if !matches!(instruction.kind, Op::CallSsa(_) | Op::TailcallSsa(_)) {
                continue;
            }
            let target = (!call.adjusted)
                .then(|| resolver.destination(&key, call.address, &registers, 0))
                .flatten()
                .filter(|address| function.view().offset_executable(*address))
                .map(|address| Key {
                    address,
                    platform: key.platform.clone(),
                });
            let mut child = Bindings::new();
            let mut parameters = Vec::new();
            if let Some(target) = &target {
                for register in resolver.entries.get(target).cloned().unwrap_or_default() {
                    if let Some(value) = resolver
                        .at(&key, call.address, register, &registers, 0)
                        .and_then(Value::constant)
                    {
                        child.insert(register, value);
                    }
                }
                if let Some(callee) = owned.get(target) {
                    for slot in &callee.input.contract.parameters {
                        let value = abi::word_register(slot, callee.input.pointer_width).and_then(
                            |register| {
                                resolver
                                    .at(&key, call.address, register, &registers, 0)
                                    .and_then(Value::pointer)
                            },
                        );
                        parameters.push(value);
                    }
                }
                queue.push_back((target.clone(), child.clone()));
            }
            calls.push(Target {
                address: call.address,
                target,
                indirect: call.target.is_none()
                    || source.input.overlaid.contains_key(&call.address),
                registers: child,
                parameters,
            });
        }
        result.push(Context {
            function: key,
            registers,
            calls,
        });
    }
    if let Some(status) = resolver.status {
        return Err(status);
    }
    for (key, low) in &resolver.low {
        if !low.current(&owned[key].ssa.il.function()) {
            return Err(Status::Unavailable);
        }
    }
    let reads = std::mem::take(&mut resolver.reads);
    let exits = std::mem::take(&mut resolver.exits);
    drop(resolver);
    for (key, wire) in wires {
        owned.get_mut(&key).unwrap().input.wire = Some(wire);
    }
    for (key, registers) in exits {
        owned
            .get_mut(&key)
            .unwrap()
            .input
            .register_exits
            .extend(registers);
    }
    for (key, reads) in reads {
        let source = owned.get_mut(&key).unwrap();
        let view = source.ssa.il.function().view();
        for ((address, width), expected) in reads {
            let range = address..address + width as u64;
            if source.snapshot.readonly.contains(&range) {
                if !readonly(&view, &range) || view.read_vec(address, width) != expected {
                    return Err(Status::Unavailable);
                }
                continue;
            }
            let actual = source.snapshot.read(&view, range, true, budget)?;
            if actual != expected {
                return Err(Status::Unavailable);
            }
        }
        source.input.sources = source.snapshot.sources.clone();
        source.input.readonly = source.snapshot.readonly.clone();
        source.input.digest = format!("{:x}", source.snapshot.hash.clone().finalize());
    }
    *sources = owned.into_values().collect();
    Ok(result)
}
