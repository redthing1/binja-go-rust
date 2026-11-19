use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ffi::CStr;
use std::ops::Range;

use binaryninja::architecture::Architecture;
use binaryninja::binary_view::{BinaryView, BinaryViewBase};
use binaryninja::function::Function;
use binaryninja::medium_level_il::{
    MediumLevelExpressionIndex as Index, MediumLevelILFunction, MediumLevelILInstructionKind as Op,
    MediumLevelInstructionIndex as InstructionIndex,
};
use binaryninja::platform::Platform;
use binaryninja::rc::Ref;
use binaryninja::types::{Type, TypeClass};
use binaryninja::variable::{SSAVariable, Variable};
use binaryninjacore_sys::*;
use sha2::{Digest, Sha256};

use super::layout::{Access, Call, Guard, Input, Key, MAX_FIELDS, Place, Status};
use crate::binja::FunctionHandle;

pub(in crate::rust) mod abi;
mod control;
pub(super) mod dispatch;
mod ordering;
mod places;
mod values;

use crate::binja::memory::readonly;

#[derive(Clone, Default)]
struct Memory {
    readonly: bool,
    epochs: BTreeMap<u64, u64>,
}

impl Memory {
    fn epoch(&self, version: u64) -> u64 {
        if self.readonly {
            0
        } else {
            self.epochs.get(&version).copied().unwrap_or(version)
        }
    }
}

pub(super) struct Source {
    pub input: Input,
    ssa: Ssa,
    origins: Origins<'static>,
    control: control::Control,
    accesses: Vec<(Index, Index, u64)>,
    call_sites: Vec<Index>,
    snapshot: Snapshot,
}

pub(super) use values::refine;

pub(super) struct Budget {
    pub expressions: usize,
    pub bytes: usize,
}

pub(super) const OBSERVED_TYPE: &CStr = c"go-rust.observed-layout";
pub(super) const OVERLAID: &str = "go-rust.rust.call-overlays.v1";

pub(super) fn overlaid(function: &Function) -> BTreeMap<u64, u64> {
    function
        .query_metadata(OVERLAID)
        .and_then(|value| value.get_string())
        .and_then(|value| serde_json::from_slice(value.to_bytes()).ok())
        .unwrap_or_default()
}

pub(super) fn key(function: &Function) -> Key {
    Key {
        address: function.start(),
        platform: function.platform().name(),
    }
}

/// Keep existing declarations; this pass's observed records are recomputed separately.
pub(super) fn declared_word(ty: &Type, width: usize) -> bool {
    ty.width() as usize == width
        && (ty.type_class() == TypeClass::NamedTypeReferenceClass
            || (ty.type_class() == TypeClass::PointerTypeClass
                && ty.target().is_some_and(|target| {
                    if target.contents.type_class() == TypeClass::VoidTypeClass {
                        return false;
                    }
                    let attribute = unsafe {
                        BNGetTypeAttributeByName(target.contents.handle, OBSERVED_TYPE.as_ptr())
                    };
                    let observed = !attribute.is_null();
                    if observed {
                        unsafe { BNFreeString(attribute) };
                    }
                    !observed
                })))
}

pub(super) fn named_word(ty: &Type, width: usize) -> bool {
    declared_word(ty, width)
        && (ty.type_class() == TypeClass::NamedTypeReferenceClass
            || ty.target().is_some_and(|target| {
                target.contents.type_class() == TypeClass::NamedTypeReferenceClass
                    || target.contents.registered_name().is_some()
            }))
}

fn declarations(function: &Function, width: usize) -> Vec<String> {
    let ty = function.return_type().contents;
    let mut result = vec![if declared_word(&ty, width) {
        ty.to_string()
    } else {
        String::new()
    }];
    result.extend(
        function
            .parameter_variables()
            .contents
            .iter()
            .map(|variable| {
                function
                    .variable_type(variable)
                    .filter(|ty| declared_word(&ty.contents, width))
                    .map(|ty| ty.contents.to_string())
                    .unwrap_or_default()
            }),
    );
    result
}

pub(super) fn digest(view: &BinaryView, code: &[Range<u64>]) -> Option<String> {
    let mut hash = Sha256::new();
    for range in code {
        let size = usize::try_from(range.end.checked_sub(range.start)?).ok()?;
        let bytes = view.read_vec(range.start, size);
        if bytes.len() != size {
            return None;
        }
        hash.update(range.start.to_le_bytes());
        hash.update(range.end.to_le_bytes());
        hash.update(bytes);
    }
    Some(format!("{:x}", hash.finalize()))
}

pub(super) fn current(view: &BinaryView, input: &Input) -> bool {
    current_with(view, input, true)
}

/// Current-call proof does not consume this function's inferred signature or exits.
/// The core temporarily clears those while regenerating its pre-MLIL context.
pub(super) fn current_call_evidence(view: &BinaryView, input: &Input) -> bool {
    current_with(view, input, false)
}

fn current_with(view: &BinaryView, input: &Input, signature: bool) -> bool {
    input.little_endian == (view.default_endianness() == binaryninja::Endianness::LittleEndian)
        && input.readonly.iter().all(|range| readonly(view, range))
        && digest(view, &input.sources).as_ref() == Some(&input.digest)
        && Platform::by_name(&input.key.platform)
            .and_then(|platform| view.function_at(&platform, input.key.address))
            .is_some_and(|function| {
                informed(&function) == input.informed
                    && (input.wire.is_none()
                        || crate::rust::library::eligible(&function, &input.contract))
                    && input
                        .calls
                        .iter()
                        .all(|call| adjusted(&function, call.address) == call.adjusted)
                    && (!signature
                        || (function
                            .parameter_variables()
                            .contents
                            .iter()
                            .map(|variable| variable.to_identifier())
                            .eq(input.parameters.iter().copied())
                            && abi::capture(&function).as_ref() == Some(&input.contract)
                            && input.register_exits.iter().all(|(&register, &entry)| {
                                exit_entry(&function, register) == entry
                            })))
            })
}

fn adjusted(function: &Function, address: u64) -> bool {
    if function.call_type_adjustment(address, None).is_some()
        && crate::rust::library::owned(function, address).is_none()
    {
        return true;
    }
    let Some(handle) = FunctionHandle::new(function) else {
        return true;
    };
    let mut count = 0;
    unsafe {
        let raw = BNGetIndirectBranchesAt(
            handle.as_ptr(),
            BNGetFunctionArchitecture(handle.as_ptr()),
            address,
            &mut count,
        );
        let user = if count == 0 {
            false
        } else if raw.is_null() || count > 256 {
            true
        } else {
            std::slice::from_raw_parts(raw, count)
                .iter()
                .any(|branch| !branch.autoDefined)
        };
        if !raw.is_null() {
            BNFreeIndirectBranchList(raw);
        }
        user
    }
}

fn informed(function: &Function) -> bool {
    crate::binja::llil::Ssa::has_user_values(function)
}

fn exit_entry(function: &Function, register: u32) -> Option<u32> {
    let value = function.register_value_at_exit(register);
    (value.confidence != 0
        && value.contents.state == BNRegisterValueType::EntryValue
        && value.contents.offset == 0)
        .then(|| u32::try_from(value.contents.value).ok())
        .flatten()
}

struct Snapshot {
    sources: Vec<Range<u64>>,
    readonly: Vec<Range<u64>>,
    hash: Sha256,
    little_endian: bool,
}

impl Snapshot {
    fn new(view: &BinaryView) -> Self {
        Self {
            sources: Vec::new(),
            readonly: Vec::new(),
            hash: Sha256::new(),
            little_endian: view.default_endianness() == binaryninja::Endianness::LittleEndian,
        }
    }

    fn read(
        &mut self,
        view: &BinaryView,
        range: Range<u64>,
        required_readonly: bool,
        budget: &mut Budget,
    ) -> Result<Vec<u8>, Status> {
        let size = usize::try_from(
            range
                .end
                .checked_sub(range.start)
                .ok_or(Status::Unavailable)?,
        )
        .map_err(|_| Status::Limit)?;
        budget.bytes = budget.bytes.checked_sub(size).ok_or(Status::Limit)?;
        if required_readonly && !readonly(view, &range) {
            return Err(Status::Unavailable);
        }
        let bytes = view.read_vec(range.start, size);
        if bytes.len() != size {
            return Err(Status::Unavailable);
        }
        self.hash.update(range.start.to_le_bytes());
        self.hash.update(range.end.to_le_bytes());
        self.hash.update(&bytes);
        if required_readonly {
            self.readonly.push(range.clone());
        }
        self.sources.push(range);
        Ok(bytes)
    }
}

// Obtain call operands without the SDK's recursive eager expression-tree lift.
// This handle is used only on committed IL, outside function workflow callbacks.
struct Ssa {
    il: Ref<MediumLevelILFunction>,
    raw: RawSsa,
}

struct RawSsa(*mut BNMediumLevelILFunction);

impl RawSsa {
    fn new(function: &Function) -> Option<Self> {
        let handle = FunctionHandle::new(function)?;
        let raw = unsafe {
            let regular = BNGetFunctionMediumLevelILIfAvailable(handle.as_ptr());
            if regular.is_null() {
                return None;
            }
            let raw = BNGetMediumLevelILSSAForm(regular);
            BNFreeMediumLevelILFunction(regular);
            raw
        };
        if raw.is_null() { None } else { Some(Self(raw)) }
    }
}

impl Drop for RawSsa {
    fn drop(&mut self) {
        unsafe { BNFreeMediumLevelILFunction(self.0) };
    }
}

impl Ssa {
    /// The pinned SDK reports FORCE_VER_SSA as Undef; only core partial-access copies qualify.
    fn forced_source(&self, index: Index, destination: SSAVariable) -> Option<SSAVariable> {
        // PartialAccessAnalysisForceVersionReason is absent from the pinned bindings.
        const PARTIAL_ACCESS: u64 = 1;
        let raw = unsafe { BNGetMediumLevelILByIndex(self.raw.0, index.0) };
        (raw.operation == BNMediumLevelILOperation::MLIL_FORCE_VER_SSA
            && raw.operands[0] == destination.variable.to_identifier()
            && raw.operands[1] == destination.version as u64
            && raw.operands[4] == PARTIAL_ACCESS)
            .then(|| {
                Some(SSAVariable {
                    variable: Variable::from_identifier(raw.operands[2]),
                    version: usize::try_from(raw.operands[3]).ok()?,
                })
            })
            .flatten()
    }
    /// Both core APIs use distinct index domains; the pinned SDK confuses them.
    fn dependencies(
        &self,
        index: InstructionIndex,
        budget: &mut Budget,
    ) -> Result<Vec<(InstructionIndex, bool)>, Status> {
        let mut count = 0;
        let raw = unsafe { BNGetAllMediumLevelILBranchDependence(self.raw.0, index.0, &mut count) };
        let result = if count > 256 {
            Err(Status::Limit)
        } else if count == 0 {
            Ok(Vec::new())
        } else if raw.is_null() {
            Err(Status::Unavailable)
        } else if let Some(remaining) = budget.expressions.checked_sub(count) {
            budget.expressions = remaining;
            Ok(unsafe { std::slice::from_raw_parts(raw, count) }
                .iter()
                .filter_map(|dep| {
                    let taken = match dep.dependence {
                        BNILBranchDependence::TrueBranchDependent => true,
                        BNILBranchDependence::FalseBranchDependent => false,
                        _ => return None,
                    };
                    Some((InstructionIndex(dep.branch), taken))
                })
                .collect())
        } else {
            Err(Status::Limit)
        };
        if !raw.is_null() {
            unsafe { BNFreeILBranchDependenceList(raw) };
        }
        result
    }

    fn lookup(
        &self,
        index: Index,
        budget: &mut Budget,
    ) -> Result<Option<BTreeMap<u64, BTreeSet<u64>>>, Status> {
        struct Values(BNPossibleValueSet);
        impl Drop for Values {
            fn drop(&mut self) {
                unsafe { BNFreePossibleValueSet(&mut self.0) };
            }
        }
        let values = Values(unsafe {
            BNGetMediumLevelILPossibleExprValues(self.raw.0, index.0, std::ptr::null_mut(), 0)
        });
        let raw = &values.0;
        if raw.state != BNRegisterValueType::LookupTableValue {
            return Ok(None);
        }
        if raw.count > 256 {
            return Err(Status::Limit);
        }
        if raw.count == 0 {
            return Ok(None);
        }
        if raw.table.is_null() {
            return Err(Status::Unavailable);
        }
        let mut result: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
        let mut total = 0usize;
        for entry in unsafe { std::slice::from_raw_parts(raw.table, raw.count) } {
            total = total.checked_add(entry.fromCount).ok_or(Status::Limit)?;
            if total > 256 {
                return Err(Status::Limit);
            }
            budget.expressions = budget
                .expressions
                .checked_sub(entry.fromCount)
                .ok_or(Status::Limit)?;
            if entry.fromCount == 0 {
                continue;
            }
            if entry.fromValues.is_null() {
                return Err(Status::Unavailable);
            }
            for value in unsafe { std::slice::from_raw_parts(entry.fromValues, entry.fromCount) } {
                let Ok(value) = u64::try_from(*value) else {
                    return Ok(None);
                };
                result
                    .entry(entry.toValue as u64)
                    .or_default()
                    .insert(value);
            }
        }
        Ok(Some(result))
    }

    fn new(function: &Function) -> Option<Self> {
        if function.is_update_needed() {
            return None;
        }
        function.medium_level_il().ok()?;
        let raw = RawSsa::new(function)?;
        let il = function.medium_level_il().ok()?.ssa_form();
        let result = Self { il, raw };
        (result.current(function)
            && unsafe { BNGetMediumLevelILExprCount(result.raw.0) } == result.il.expression_count())
        .then_some(result)
    }

    fn current(&self, function: &Function) -> bool {
        // SDK MLIL equality compares owner functions, not IL generations.
        RawSsa::new(function).is_some_and(|current| current.0 == self.raw.0)
    }

    fn operands(&self, index: Index, operand: usize) -> Result<Vec<u64>, Status> {
        let mut count = 0;
        let raw =
            unsafe { BNMediumLevelILGetOperandList(self.raw.0, index.0, operand, &mut count) };
        let result = if count == 0 {
            Ok(Vec::new())
        } else if raw.is_null() {
            Err(Status::Unavailable)
        } else if count > 512 {
            Err(Status::Limit)
        } else {
            Ok(unsafe { std::slice::from_raw_parts(raw, count) }.to_vec())
        };
        if !raw.is_null() {
            unsafe { BNMediumLevelILFreeOperandList(raw) };
        }
        result
    }

    fn expressions(&self, index: Index, operand: usize) -> Result<Vec<Index>, Status> {
        let operands = self.operands(index, operand)?;
        if operands.len() > 256 {
            return Err(Status::Limit);
        }
        operands
            .into_iter()
            .map(|index| {
                usize::try_from(index)
                    .map(Index)
                    .map_err(|_| Status::Unavailable)
            })
            .collect()
    }
}

enum Definition {
    Assign(Index),
    Merge(Vec<SSAVariable>),
    Call(u64),
}

pub(super) struct Origins<'a> {
    il: Ref<MediumLevelILFunction>,
    parameters: HashMap<Variable, usize>,
    definitions: HashMap<SSAVariable, Definition>,
    pointer_width: usize,
    calls: &'a [Call],
    memory: Memory,
}

impl<'a> Origins<'a> {
    /// Rebind current SSA expressions without using previously committed IL.
    pub fn in_context(
        il: &'a MediumLevelILFunction,
        parameters: &[Variable],
        input: &'a Input,
    ) -> Result<Self, Status> {
        let mut result = Self {
            il: il.to_owned(),
            parameters: parameters
                .iter()
                .enumerate()
                .map(|(index, var)| (*var, index))
                .collect(),
            definitions: HashMap::new(),
            pointer_width: input.pointer_width,
            calls: &input.calls,
            memory: Memory::default(),
        };
        let mut budget = 100_000usize;
        budget = budget
            .checked_sub(il.expression_count())
            .ok_or(Status::Limit)?;
        for index in 0..il.expression_count() {
            let instruction = il
                .instruction_from_expr_index(Index(index))
                .ok_or(Status::Unavailable)?;
            if instruction.instr_index.0 >= il.instruction_count() {
                continue;
            }
            match instruction.kind {
                Op::SetVarSsa(op) => {
                    result
                        .definitions
                        .insert(op.dest, Definition::Assign(op.src));
                }
                Op::VarPhi(op) => {
                    budget = budget.checked_sub(op.num_operands).ok_or(Status::Limit)?;
                    if op.num_operands > 256 {
                        return Err(Status::Limit);
                    }
                    // Lifting a phi only reads its bounded variable list, not expression trees.
                    if let binaryninja::medium_level_il::MediumLevelILLiftedInstructionKind::VarPhi(op) = instruction.lift().kind {
                        result.definitions.insert(op.dest, Definition::Merge(op.src));
                    }
                }
                _ => (),
            }
        }
        Ok(result)
    }
}

impl Origins<'_> {
    fn variable(&self, variable: SSAVariable, depth: usize, memory: Option<u64>) -> Option<Place> {
        if depth >= 32 {
            return None;
        }
        if variable.version == 0 {
            return self
                .parameters
                .get(&variable.variable)
                .copied()
                .map(Place::parameter);
        }
        let definition = self.definitions.get(&variable);
        if definition.is_none() {
            let instruction = self.il.ssa_variable_definition(&variable)?;
            if matches!(instruction.kind, Op::CallSsa(_))
                && self.calls.iter().any(|call| {
                    call.address == instruction.address
                        && call.output == Some(variable.variable.to_identifier())
                })
            {
                return Some(Place::call(instruction.address));
            }
        }
        match definition? {
            Definition::Assign(index) => self.place_in(*index, depth + 1, memory),
            Definition::Call(address) => Some(Place::call(*address)),
            Definition::Merge(sources) => {
                let mut result = None;
                for source in sources {
                    let place = self.variable(*source, depth + 1, memory)?;
                    if result.as_ref().is_some_and(|previous| *previous != place) {
                        return None;
                    }
                    result = Some(place);
                }
                result
            }
        }
    }

    pub fn place(&self, index: Index, depth: usize) -> Option<Place> {
        self.place_in(index, depth, None)
    }

    fn place_in(&self, index: Index, depth: usize, memory: Option<u64>) -> Option<Place> {
        if depth >= 32 {
            return None;
        }
        let instruction = self.il.instruction_from_expr_index(index)?;
        match instruction.kind {
            Op::VarSsa(op) if instruction.size == self.pointer_width => {
                self.variable(op.src, depth + 1, memory)
            }
            Op::LoadSsa(op)
                if instruction.size == self.pointer_width
                    && memory.is_none_or(|m| {
                        self.memory.epoch(m) == self.memory.epoch(op.src_memory)
                    }) =>
            {
                self.place_in(op.src, depth + 1, memory)?.load()
            }
            Op::LoadStructSsa(op)
                if instruction.size == self.pointer_width
                    && memory.is_none_or(|m| {
                        self.memory.epoch(m) == self.memory.epoch(op.src_memory)
                    }) =>
            {
                self.place_in(op.src, depth + 1, memory)?
                    .shift(i64::try_from(op.offset).ok()?)?
                    .load()
            }
            Op::Add(op) | Op::Sub(op) => {
                let right = self.il.instruction_from_expr_index(op.right)?;
                let Op::Const(constant) = right.kind else {
                    return None;
                };
                let delta = match instruction.size {
                    4 => i64::from(constant.constant as u32 as i32),
                    8 => constant.constant as i64,
                    _ => return None,
                };
                let delta = if matches!(instruction.kind, Op::Sub(_)) {
                    delta.checked_neg()?
                } else {
                    delta
                };
                self.place_in(op.left, depth + 1, memory)?.shift(delta)
            }
            _ => None,
        }
    }
}

pub(super) fn extract(
    function: &Function,
    budget: &mut Budget,
    cancelled: impl Fn() -> bool,
    inherited: Option<&Input>,
) -> Result<Source, Status> {
    let mut code: Vec<_> = function
        .basic_blocks()
        .iter()
        .map(|block| block.start()..block.end())
        .collect();
    code.sort_by_key(|range| range.start);
    if code.len() > 4096 {
        return Err(Status::Limit);
    }
    let view = function.view();
    let mut snapshot = Snapshot::new(&view);
    for range in &code {
        snapshot.read(&view, range.clone(), false, budget)?;
    }
    if let Some(previous) = inherited {
        for range in &previous.readonly {
            snapshot.read(&view, range.clone(), true, budget)?;
        }
    }
    let ssa = Ssa::new(function).ok_or(Status::Unavailable)?;
    let count = ssa.il.expression_count();
    budget.expressions = budget.expressions.checked_sub(count).ok_or(Status::Limit)?;
    let parameters = function.parameter_variables().contents;
    if parameters.len() > 256 {
        return Err(Status::Limit);
    }
    let mut origins = Origins {
        il: ssa.il.clone(),
        parameters: parameters
            .iter()
            .enumerate()
            .map(|(index, var)| (*var, index))
            .collect(),
        definitions: HashMap::new(),
        pointer_width: function.arch().address_size(),
        calls: &[],
        memory: Memory::default(),
    };
    let mut outputs = HashMap::new();
    let mut call_addresses: HashMap<u64, usize> = HashMap::new();
    for index in 0..count {
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
        match instruction.kind {
            Op::SetVarSsa(op) => {
                origins
                    .definitions
                    .insert(op.dest, Definition::Assign(op.src));
            }
            Op::VarPhi(op) => {
                let operands = ssa.operands(Index(index), 2)?;
                if operands.len() % 2 != 0 {
                    return Err(Status::Unavailable);
                }
                budget.expressions = budget
                    .expressions
                    .checked_sub(operands.len())
                    .ok_or(Status::Limit)?;
                let variables = operands
                    .chunks_exact(2)
                    .map(|pair| {
                        Ok(SSAVariable::new(
                            Variable::from_identifier(pair[0]),
                            usize::try_from(pair[1]).map_err(|_| Status::Limit)?,
                        ))
                    })
                    .collect::<Result<_, Status>>()?;
                origins
                    .definitions
                    .insert(op.dest, Definition::Merge(variables));
            }
            Op::CallSsa(op) | Op::TailcallSsa(op) => {
                *call_addresses.entry(instruction.address).or_default() += 1;
                if let Some(output) = ssa.il.instruction_from_expr_index(op.output)
                    && matches!(output.kind, Op::CallOutputSsa(_))
                {
                    let values = ssa.expressions(op.output, 1)?;
                    budget.expressions = budget
                        .expressions
                        .checked_sub(values.len())
                        .ok_or(Status::Limit)?;
                    if let [value] = values.as_slice()
                        && let Some(value) = ssa.il.instruction_from_expr_index(*value)
                        && let Op::VarOutputSsa(var) = value.kind
                    {
                        // Output declarations have size zero; address uses enforce word width.
                        origins
                            .definitions
                            .insert(var.dest, Definition::Call(instruction.address));
                        outputs.insert(index, var.dest.variable.to_identifier());
                    }
                }
            }
            _ => (),
        }
    }
    origins.definitions.retain(|_, definition| !matches!(definition, Definition::Call(address) if call_addresses[address] != 1));
    let control = control::Control::collect(&ssa, &origins, &mut snapshot, budget, &cancelled)?;
    let mut fields = BTreeSet::new();
    let mut accesses = Vec::new();
    let mut calls = Vec::new();
    let mut call_sites = Vec::new();
    let mut returns = Vec::new();
    let mut opaque_memory = false;
    let function_key = key(function);
    for index in 0..count {
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
        let memory = match instruction.kind {
            Op::LoadSsa(op) => Some((op.src, 0)),
            Op::LoadStructSsa(op) => Some((op.src, op.offset)),
            Op::StoreSsa(op) => {
                opaque_memory = true;
                Some((op.dest, 0))
            }
            Op::StoreStructSsa(op) => {
                opaque_memory = true;
                Some((op.dest, op.offset))
            }
            Op::CallSsa(op) | Op::TailcallSsa(op) => {
                if calls.len() >= 256 {
                    return Err(Status::Limit);
                }
                let target = ssa
                    .il
                    .instruction_from_expr_index(op.dest)
                    .and_then(|instruction| match instruction.kind {
                        Op::ConstPtr(target) => Some(Key {
                            address: target.constant,
                            platform: function_key.platform.clone(),
                        }),
                        _ => None,
                    });
                let arguments = ssa.expressions(Index(index), 2)?;
                budget.expressions = budget
                    .expressions
                    .checked_sub(arguments.len())
                    .ok_or(Status::Limit)?;
                let mut parameters: Vec<_> =
                    arguments.iter().map(|arg| origins.place(*arg, 0)).collect();
                let mut parameter_order = Vec::new();
                if let Some(hint) = crate::rust::library::owned(function, instruction.address)
                    && target.as_ref() == Some(&hint.target)
                    && arguments.len() == 1
                    && let Some(callee) =
                        view.function_at(&function.platform(), hint.target.address)
                    && let Some(contract) = abi::capture(&callee)
                    && let Some(parameter) = contract.parameters.iter().position(|slot| {
                        abi::word_register(slot, origins.pointer_width) == Some(hint.wire.input)
                    })
                {
                    let value = parameters.pop().flatten();
                    parameters = vec![None; contract.parameters.len()];
                    parameters[parameter] = value;
                    parameter_order.push(parameter);
                }
                calls.push(Call {
                    uncertain: control.uncertain(&instruction),
                    guards: control.at(&instruction),
                    address: instruction.address,
                    declarations: target
                        .as_ref()
                        .and_then(|target| {
                            function
                                .view()
                                .function_at(&function.platform(), target.address)
                        })
                        .map(|callee| declarations(&callee, origins.pointer_width))
                        .unwrap_or_default(),
                    target,
                    adjusted: adjusted(function, instruction.address),
                    parameters,
                    parameter_order,
                    output: (call_addresses[&instruction.address] == 1)
                        .then(|| outputs.get(&index).copied())
                        .flatten(),
                });
                call_sites.push(instruction.expr_index);
                if matches!(instruction.kind, Op::TailcallSsa(_)) {
                    returns.push(
                        (function.return_type().contents.width() as usize == origins.pointer_width
                            && call_addresses[&instruction.address] == 1)
                            .then(|| Place::call(instruction.address)),
                    );
                }
                None
            }
            Op::Ret(_) => {
                let values = ssa.expressions(Index(index), 0)?;
                budget.expressions = budget
                    .expressions
                    .checked_sub(values.len())
                    .ok_or(Status::Limit)?;
                returns.push(match values.as_slice() {
                    [value]
                        if ssa
                            .il
                            .instruction_from_expr_index(*value)
                            .is_some_and(|value| value.size == origins.pointer_width) =>
                    {
                        origins.place(*value, 0)
                    }
                    _ => None,
                });
                None
            }
            Op::SetVarAliased(_)
            | Op::SetVarAliasedField(_)
            | Op::MemoryIntrinsicSsa(_)
            | Op::IntrinsicSsa(_)
            | Op::SyscallSsa(_)
            | Op::SyscallUntypedSsa(_)
            | Op::CallUntypedSsa(_)
            | Op::TailcallUntypedSsa(_)
            | Op::Unimpl
            | Op::UnimplMem(_) => {
                opaque_memory = true;
                None
            }
            _ => None,
        };
        if let Some((index, offset)) = memory {
            let observed =
                places::accesses(&origins, &control, &instruction, index, offset, budget)?;
            if !observed.is_empty() {
                accesses.push((instruction.expr_index, index, offset));
                fields.extend(observed);
                if fields.len() > MAX_FIELDS {
                    return Err(Status::Limit);
                }
            }
        }
    }
    let retained_loads = control::Control::retained_loads(&ssa, &origins, budget, &cancelled)?;
    let sites = control.sites(&ssa, &origins, budget, &cancelled)?;
    let input = Input {
        key: function_key,
        parameters: parameters.iter().map(Variable::to_identifier).collect(),
        contract: abi::capture(function).ok_or(Status::Unavailable)?,
        wire: None,
        informed: informed(function),
        register_exits: inherited
            .map(|input| input.register_exits.clone())
            .unwrap_or_default(),
        overlaid: overlaid(function),
        pointer_width: function.arch().address_size(),
        fields,
        calls,
        returns,
        opaque_memory,
        sources: snapshot.sources.clone(),
        readonly: snapshot.readonly.clone(),
        little_endian: snapshot.little_endian,
        sites,
        retained_loads,
        digest: format!("{:x}", snapshot.hash.clone().finalize()),
    };
    // Reject mixed code/data/IL generations when edits race with extraction.
    if function.is_update_needed() || !current(&view, &input) || !ssa.current(function) {
        return Err(Status::Unavailable);
    }
    Ok(Source {
        input,
        ssa,
        origins,
        control,
        accesses,
        call_sites,
        snapshot,
    })
}
