use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ffi::c_void;
use std::fmt::Write;

use binaryninja::architecture::Architecture;
use binaryninja::background_task::BackgroundTask;
use binaryninja::binary_view::{BinaryView, BinaryViewBase, MetadataStoreFlags};
use binaryninja::command::FunctionCommand;
use binaryninja::function::{Function, FunctionUpdateType};
use binaryninja::medium_level_il::{MediumLevelExpressionIndex, MediumLevelILInstructionKind};
use binaryninja::platform::Platform;
use binaryninja::rc::Ref;
use binaryninja::types::{MemberAccess, MemberScope, StructureBuilder, Type};
use binaryninja::workflow::activity::{Config, Eligibility};
use binaryninja::workflow::{Activity, AnalysisContext, Workflow};
use binaryninjacore_sys::{
    BNActivity, BNAnalysisContext, BNAnalysisContextGetFunction, BNCreateTypeBuilderFromType,
    BNFinalizeTypeBuilder, BNFreeTypeBuilder, BNSetTypeBuilderAttribute,
};
use serde::{Deserialize, Serialize};

use crate::binja::workflow;

use super::layout::{Access, Field, Input, Key, Layout, Place, Root, Status};
use super::library;
use super::ssa::{self, Budget};

const ROOT: &str = "go-rust.rust.layout-root.v1";
const MEMBER: &str = "go-rust.rust.layout-member.v1";
const ACTIVE: &str = "go-rust.rust.layouts-active.v1";
const STARTED: &str = "go-rust.rust.layouts-started.v1";
const RESULT: &str = "go-rust.rust.layouts.v1";
const STOPPED: &str = "go-rust.rust.layouts-stopped.v1";
const ATTEMPTS: &str = "go-rust.rust.layouts-attempts.v1";
const PENDING: &str = "go-rust.rust.layouts-pending.v1";

#[derive(Deserialize, Eq, PartialEq, Serialize)]
struct Model {
    roots: Vec<Key>,
    inputs: Vec<Input>,
    layouts: Vec<Layout>,
    contexts: Vec<ssa::dispatch::Context>,
    status: Status,
}

impl Model {
    fn withhold(&mut self, status: Status) {
        self.status = status;
        self.layouts.clear();
        self.contexts.clear();
    }
}

fn flag(function: &Function, key: &str) -> bool {
    function
        .query_metadata(key)
        .and_then(|value| value.get_boolean())
        == Some(true)
}

fn model(view: &BinaryView) -> Option<Model> {
    serde_json::from_str(&view.get_metadata::<String>(RESULT)?).ok()
}

fn local_targets(model: &Model, key: &Key) -> BTreeMap<u64, u64> {
    let mut candidates = BTreeMap::new();
    for call in model
        .contexts
        .iter()
        .filter(|context| context.function == *key && context.registers.is_empty())
        .flat_map(|context| &context.calls)
        .filter(|call| call.indirect)
    {
        let target = call.target.as_ref().map(|key| key.address);
        candidates
            .entry(call.address)
            .and_modify(|previous| {
                if *previous != target {
                    *previous = None;
                }
            })
            .or_insert(target);
    }
    candidates
        .into_iter()
        .filter_map(|(address, target)| Some((address, target?)))
        .collect()
}

fn word_calls(model: &Model, key: &Key) -> BTreeMap<u64, library::Hint> {
    let Some(input) = model.inputs.iter().find(|input| input.key == *key) else {
        return BTreeMap::new();
    };
    input
        .calls
        .iter()
        .filter(|call| !call.adjusted)
        .filter_map(|call| {
            let target = model
                .inputs
                .iter()
                .find(|input| Some(&input.key) == call.target.as_ref())?;
            let wire = target.wire.as_ref()?;
            // Already accurate interfaces retain their current parameter names/types.
            (target.parameters.len() > 1).then(|| {
                (
                    call.address,
                    library::Hint {
                        target: target.key.clone(),
                        wire: wire.clone(),
                    },
                )
            })
        })
        .collect()
}

fn word_dependencies<'a>(model: &'a Model, key: &Key) -> Vec<(u64, &'a Input)> {
    word_calls(model, key)
        .into_iter()
        .filter_map(|(address, hint)| {
            Some((
                address,
                model.inputs.iter().find(|input| input.key == hint.target)?,
            ))
        })
        .collect()
}

fn find(view: &BinaryView, key: &Key) -> Option<Ref<Function>> {
    view.function_at(&*Platform::by_name(&key.platform)?, key.address)
}

fn roots(view: &BinaryView) -> Vec<Key> {
    let mut roots: Vec<_> = view
        .functions()
        .iter()
        .filter(|function| flag(function, ROOT))
        .map(|function| ssa::key(&function))
        .collect();
    roots.sort();
    roots
}

fn withdraw(view: &BinaryView) {
    view.remove_metadata(RESULT);
    for function in view
        .functions()
        .iter()
        .filter(|function| flag(function, MEMBER))
    {
        function.remove_metadata(MEMBER);
        function.reanalyze(FunctionUpdateType::FullAutoFunctionUpdate);
    }
}

fn current(view: &BinaryView, model: &Model) -> bool {
    current_in(view, model, None)
}

fn current_in(view: &BinaryView, model: &Model, analysing: Option<&Key>) -> bool {
    model
        .roots
        .iter()
        .all(|key| find(view, key).is_some_and(|function| flag(&function, ROOT)))
        && model.inputs.iter().all(|input| {
            if analysing == Some(&input.key) {
                ssa::current_call_evidence(view, input)
            } else {
                ssa::current(view, input)
            }
        })
        && model
            .contexts
            .iter()
            .flat_map(|context| &context.calls)
            .filter_map(|call| call.target.as_ref())
            .all(|target| view.offset_executable(target.address))
}

fn guarded(context: &AnalysisContext, action: fn(&AnalysisContext)) {
    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| action(context))).is_err() {
        let view = context.view();
        withdraw(&view);
        view.store_metadata(STOPPED, true, MetadataStoreFlags::EPHEMERAL);
        tracing::error!("Rust layout activity panicked; annotations withdrawn");
    }
}

fn prepare(context: &AnalysisContext) {
    guarded(context, prepare_inner);
}

fn prepare_inner(context: &AnalysisContext) {
    let view = context.view();
    if view.get_metadata::<bool>(ACTIVE) != Some(true) {
        return;
    }
    let first = view.get_metadata::<bool>(STARTED) != Some(true);
    view.store_metadata(PENDING, true, MetadataStoreFlags::EPHEMERAL);
    view.store_metadata(STARTED, true, MetadataStoreFlags::EPHEMERAL);
    if first || model(&view).is_some_and(|model| !current(&view, &model)) {
        withdraw(&view);
        view.remove_metadata(ATTEMPTS);
    }
}

fn collect(view: &BinaryView, roots: Vec<Key>, cancelled: impl Fn() -> bool) -> Model {
    let inherited = model(view).filter(|previous| {
        previous.status == Status::Complete
            && previous.roots == roots
            && current(view, previous)
            && previous.inputs.iter().any(|input| {
                find(view, &input.key).is_some_and(|function| !ssa::overlaid(&function).is_empty())
            })
    });
    let mut result = Model {
        roots: roots.clone(),
        inputs: Vec::new(),
        layouts: Vec::new(),
        contexts: Vec::new(),
        status: Status::Complete,
    };
    if roots.len() > 64 {
        result.status = Status::Limit;
        return result;
    }
    let mut queue = VecDeque::from(roots);
    if let Some(previous) = &inherited {
        // Overlay-only IL no longer contains every helper or data dependency.
        queue.extend(previous.inputs.iter().map(|input| input.key.clone()));
    }
    let mut seen = BTreeSet::new();
    let mut sources = Vec::new();
    let mut budget = Budget {
        expressions: 100_000,
        bytes: 1_048_576,
    };
    loop {
        while let Some(key) = queue.pop_front() {
            if cancelled() {
                result.status = Status::Cancelled;
                break;
            }
            if !seen.insert(key.clone()) {
                continue;
            }
            if seen.len() > 64 {
                result.status = Status::Limit;
                break;
            }
            let Some(function) = find(view, &key) else {
                continue;
            };
            let previous = inherited
                .as_ref()
                .and_then(|previous| previous.inputs.iter().find(|input| input.key == key));
            match ssa::extract(&function, &mut budget, &cancelled, previous) {
                Ok(source) => {
                    queue.extend(
                        source
                            .input
                            .calls
                            .iter()
                            .filter_map(|call| call.target.clone()),
                    );
                    sources.push(source);
                }
                Err(status) => {
                    result.status = status;
                    break;
                }
            }
        }
        if result.status != Status::Complete {
            break;
        }
        match ssa::dispatch::collect(&mut sources, &result.roots, &mut budget, &cancelled) {
            Ok(contexts) => result.contexts = contexts,
            Err(status) => {
                result.status = status;
                break;
            }
        }
        queue.extend(
            result
                .contexts
                .iter()
                .flat_map(|context| &context.calls)
                .filter_map(|call| call.target.clone())
                .filter(|key| !seen.contains(key)),
        );
        if queue.is_empty() {
            break;
        }
    }
    result.inputs = sources.iter().map(|source| source.input.clone()).collect();
    if result.status == Status::Complete {
        match ssa::refine(sources, &mut budget, &cancelled) {
            Ok(inputs) => result.inputs = inputs,
            Err(status) => result.status = status,
        }
    }
    result
        .inputs
        .sort_by(|left, right| left.key.cmp(&right.key));
    if result.status == Status::Complete {
        match ssa::dispatch::layouts(&result.inputs, &result.contexts, cancelled) {
            Ok(layouts) => result.layouts = layouts,
            Err(status) => result.status = status,
        }
    }
    if result.status != Status::Complete {
        result.withhold(result.status);
    }
    result
}

fn refresh(view: &BinaryView) {
    if view.get_metadata::<bool>(ACTIVE) != Some(true)
        || view.get_metadata::<bool>(STOPPED) == Some(true)
    {
        return;
    }
    view.store_metadata(PENDING, false, MetadataStoreFlags::EPHEMERAL);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let selected = roots(&view);
        if selected.is_empty() {
            withdraw(&view);
            view.store_metadata(ACTIVE, false, MetadataStoreFlags::PERSISTENT);
            return;
        }
        let task = BackgroundTask::new("Inferring Rust layouts", true).enter();
        let mut next = collect(&view, selected, || task.is_cancelled());
        if next.status == Status::Complete
            && (!current(&view, &next)
                || next.inputs.iter().any(|input| {
                    find(&view, &input.key).is_none_or(|function| function.is_update_needed())
                }))
        {
            next.withhold(Status::Unavailable);
        }
        let previous = model(&view);
        if previous.as_ref() == Some(&next) {
            view.remove_metadata(ATTEMPTS);
            return;
        }
        let attempts = view.get_metadata::<u64>(ATTEMPTS).unwrap_or(0) + 1;
        if attempts > 8 {
            next.withhold(Status::Unstable);
        }
        view.store_metadata(ATTEMPTS, attempts, MetadataStoreFlags::EPHEMERAL);
        if matches!(next.status, Status::Cancelled | Status::Unstable) {
            view.store_metadata(STOPPED, true, MetadataStoreFlags::EPHEMERAL);
        }
        // Commands may change the selected roots while a cancellable pass runs.
        if view.get_metadata::<bool>(ACTIVE) != Some(true) || next.roots != roots(&view) {
            view.store_metadata(PENDING, true, MetadataStoreFlags::EPHEMERAL);
            return;
        }
        let serialized = match serde_json::to_string(&next) {
            Ok(value) => value,
            Err(_) => {
                withdraw(&view);
                return;
            }
        };
        let mut affected: BTreeSet<_> = next
            .layouts
            .iter()
            .filter(|layout| !layout.fields.is_empty())
            .map(|layout| layout.function.clone())
            .collect();
        affected.extend(
            next.contexts
                .iter()
                .filter(|context| {
                    context.registers.is_empty()
                        && context
                            .calls
                            .iter()
                            .any(|call| call.indirect && call.target.is_some())
                })
                .map(|context| context.function.clone()),
        );
        affected.extend(
            next.inputs
                .iter()
                .filter(|input| !word_calls(&next, &input.key).is_empty())
                .map(|input| input.key.clone()),
        );
        if let Some(previous) = &previous {
            affected.extend(
                previous
                    .inputs
                    .iter()
                    .filter(|input| !word_calls(previous, &input.key).is_empty())
                    .map(|input| input.key.clone()),
            );
            affected.extend(
                previous
                    .contexts
                    .iter()
                    .filter(|context| {
                        context.registers.is_empty()
                            && context
                                .calls
                                .iter()
                                .any(|call| call.indirect && call.target.is_some())
                    })
                    .map(|context| context.function.clone()),
            );
            affected.extend(
                previous
                    .layouts
                    .iter()
                    .filter(|layout| !layout.fields.is_empty())
                    .map(|layout| layout.function.clone()),
            );
        }
        if let Some(previous) = &previous {
            affected.retain(|key| {
                previous.status != next.status
                    || previous.inputs.iter().find(|input| input.key == *key)
                        != next.inputs.iter().find(|input| input.key == *key)
                    || previous
                        .layouts
                        .iter()
                        .find(|layout| layout.function == *key)
                        != next.layouts.iter().find(|layout| layout.function == *key)
                    || local_targets(previous, key) != local_targets(&next, key)
                    || word_dependencies(previous, key) != word_dependencies(&next, key)
            });
        }
        view.store_metadata(RESULT, serialized, MetadataStoreFlags::EPHEMERAL);
        for key in &affected {
            if let Some(function) = find(&view, key) {
                function.store_metadata(MEMBER, true, MetadataStoreFlags::PERSISTENT);
                function.reanalyze(FunctionUpdateType::FullAutoFunctionUpdate);
            }
        }
        view.store_metadata(PENDING, true, MetadataStoreFlags::EPHEMERAL);
    }));
    if outcome.is_err() {
        withdraw(&view);
        view.store_metadata(STOPPED, true, MetadataStoreFlags::EPHEMERAL);
        tracing::error!("Rust layout inference panicked; annotations withdrawn");
    }
}

unsafe extern "C" fn apply_calls(_: *mut c_void, context: *mut BNAnalysisContext) {
    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        apply_calls_inner(context)
    }))
    .is_err()
    {
        if let Some(view) = unsafe { workflow::view(context) } {
            withdraw(&view);
            view.store_metadata(STOPPED, true, MetadataStoreFlags::EPHEMERAL);
            tracing::error!("Rust call activity panicked; annotations withdrawn");
        }
    }
}

unsafe fn apply_calls_inner(raw: *mut BNAnalysisContext) {
    use binaryninja::low_level_il::instruction::{InstructionHandler, LowLevelILInstructionKind};

    let function = unsafe { BNAnalysisContextGetFunction(raw) };
    if function.is_null() {
        return;
    }
    let function = unsafe { Function::ref_from_raw(function) };
    let view = function.view();
    let key = ssa::key(&function);
    let applicable = flag(&function, MEMBER)
        .then(|| model(&view))
        .flatten()
        .filter(|model| model.status == Status::Complete && current_in(&view, model, Some(&key)));
    // Validate ownership while the previous automatic annotations are still present.
    library::clear_calls(&function);
    if function.query_metadata(ssa::OVERLAID).is_some() {
        function.remove_metadata(ssa::OVERLAID);
    }
    let Some(model) = applicable else {
        return;
    };
    library::apply_calls(&function, word_calls(&model, &key));
    let candidates = local_targets(&model, &key);
    if candidates.is_empty() {
        return;
    }
    let Ok(targets) =
        (unsafe { ssa::dispatch::local(&view, raw, &key, &model.inputs, &candidates) })
    else {
        return;
    };
    if targets.is_empty() || !current_in(&view, &model, Some(&key)) {
        return;
    }
    let Some(context) = (unsafe { workflow::FunctionContext::from_raw(raw) }) else {
        return;
    };
    let mut replacements = Vec::new();
    for block in context.il.basic_blocks().iter() {
        for instruction in block.iter() {
            let Some(&target) = targets.get(&instruction.address()) else {
                continue;
            };
            if let LowLevelILInstructionKind::Call(call)
            | LowLevelILInstructionKind::TailCall(call) = instruction.kind()
            {
                replacements.push((instruction.address(), call.target().index, target));
            }
        }
    }
    let old_address = context.il.current_address();
    let mut applied = BTreeMap::new();
    for (address, expression, target) in replacements {
        context.il.set_current_address(address);
        if unsafe {
            context
                .il
                .replace_expression(expression, context.il.const_ptr(target))
        } {
            applied.insert(address, target);
        }
    }
    context.il.set_current_address(old_address);
    if !applied.is_empty() {
        context.il.generate_ssa_form();
        if let Ok(value) = serde_json::to_string(&applied) {
            function.store_metadata(ssa::OVERLAID, value, MetadataStoreFlags::EPHEMERAL);
        }
    }
}

unsafe extern "C" fn refresh_action(_: *mut c_void, context: *mut BNAnalysisContext) {
    if let Some(view) = unsafe { workflow::view(context) } {
        refresh(&view);
    }
}

unsafe extern "C" fn refresh_eligible(
    _: *mut c_void,
    _: *mut BNActivity,
    context: *mut BNAnalysisContext,
) -> bool {
    let Some(view) = (unsafe { workflow::view(context) }) else {
        return false;
    };
    view.get_metadata::<bool>(ACTIVE) == Some(true)
        && view.get_metadata::<bool>(STOPPED) != Some(true)
        && view.get_metadata::<bool>(PENDING) != Some(false)
}

fn record(fields: &[Field], function: &Function) -> Ref<Type> {
    let mut builder = StructureBuilder::new();
    // No source alignment or complete size is implied by these accessed bytes.
    builder.packed(true);
    for field in fields {
        let ty = if field.children.is_empty() {
            Type::int(field.width, false)
        } else {
            Type::pointer(&function.arch(), &*record(&field.children, function))
        };
        builder.insert(
            &*ty,
            &format!("field_{:x}", field.offset),
            field.offset,
            false,
            MemberAccess::PublicAccess,
            MemberScope::NoScope,
        );
    }
    let ty = Type::structure(&builder.finalize());
    // Type attributes distinguish our transient records from analyst declarations.
    unsafe {
        let builder = BNCreateTypeBuilderFromType(ty.handle);
        assert!(!builder.is_null());
        BNSetTypeBuilderAttribute(builder, ssa::OBSERVED_TYPE.as_ptr(), c"1".as_ptr());
        let result = BNFinalizeTypeBuilder(builder);
        BNFreeTypeBuilder(builder);
        assert!(!result.is_null());
        Type::ref_from_raw(result)
    }
}

fn declared_pointer(
    view: &BinaryView,
    function: &Function,
    input: &Input,
    place: &Place,
) -> Option<Ref<Type>> {
    let (&last, path) = place.path.split_last()?;
    if last != 0 {
        return None;
    }
    let mut ty = match place.root {
        Root::Call(address) => {
            let call = input
                .calls
                .iter()
                .find(|call| call.address == address && !call.adjusted)?;
            let callee = find(view, call.target.as_ref()?)?;
            let ty = callee.return_type().contents;
            if !callee.has_user_type() && !ssa::named_word(&ty, input.pointer_width) {
                return None;
            }
            ty
        }
        Root::Parameter(parameter) => {
            let mut selected = None;
            for call in input.calls.iter().filter(|call| !call.adjusted) {
                let Some(callee) = call.target.as_ref().and_then(|target| find(view, target))
                else {
                    continue;
                };
                let variables = callee.parameter_variables().contents;
                if variables.len() != call.parameters.len() {
                    continue;
                }
                for (argument, variable) in call.parameters.iter().zip(variables) {
                    if argument.as_ref() != Some(&Place::parameter(parameter)) {
                        continue;
                    }
                    let Some(ty) = callee
                        .variable_type(&variable)
                        .map(|ty| ty.contents)
                        .filter(|ty| {
                            ssa::named_word(ty, input.pointer_width)
                                || (callee.is_var_user_defined(&variable)
                                    && ssa::declared_word(ty, input.pointer_width))
                        })
                    else {
                        continue;
                    };
                    if selected.as_ref().is_some_and(|previous| *previous != ty) {
                        return None;
                    }
                    selected = Some(ty);
                }
            }
            selected.or_else(|| {
                function
                    .parameter_variables()
                    .contents
                    .get(parameter)
                    .and_then(|var| function.variable_type(var))
                    .map(|ty| ty.contents)
                    .filter(|ty| ssa::named_word(ty, input.pointer_width))
            })?
        }
    };
    if !ssa::declared_word(&ty, input.pointer_width) {
        return None;
    }
    for offset in path {
        let pointer = ty.deref_named_type_reference(view);
        let target = pointer.target()?.contents.deref_named_type_reference(view);
        let structure = target.get_structure()?;
        let mut selected = None;
        for field in structure
            .members()
            .iter()
            .filter(|field| field.offset == *offset as u64)
        {
            if selected.is_some() {
                return None;
            }
            selected = Some(field.ty.contents.clone());
        }
        ty = selected?;
        if !ssa::declared_word(&ty, input.pointer_width) {
            return None;
        }
    }
    Some(ty)
}

fn apply(context: &AnalysisContext) {
    guarded(context, apply_inner);
}

fn apply_inner(context: &AnalysisContext) {
    let function = context.function();
    if !flag(&function, MEMBER) {
        return;
    }
    let view = context.view();
    let Some(model) = model(&view) else {
        return;
    };
    if model.status != Status::Complete || !current(&view, &model) {
        return;
    }
    let key = ssa::key(&function);
    let Some(input) = model.inputs.iter().find(|input| input.key == key) else {
        return;
    };
    let Some(layout) = model.layouts.iter().find(|layout| layout.function == key) else {
        return;
    };
    let parameters = function.parameter_variables().contents;
    if parameters
        .iter()
        .map(|var| var.to_identifier())
        .collect::<Vec<_>>()
        != input.parameters
    {
        return;
    }
    let Some(il) = context.mlil_function() else {
        return;
    };
    let il = il.ssa_form();
    if il.expression_count() > 100_000 {
        return;
    }
    let Ok(origins) = ssa::Origins::in_context(&il, &parameters, input) else {
        return;
    };
    let mut retained = Vec::new();
    for selector in &input.retained_loads {
        let Ok(place) = layout.resolve(&selector.place) else {
            return;
        };
        let mut selector = selector.clone();
        selector.place = place;
        retained.push(selector);
    }
    let mut untyped_sites = BTreeSet::new();
    if !retained.is_empty() {
        for index in 0..il.expression_count() {
            let Some(instruction) =
                il.instruction_from_expr_index(MediumLevelExpressionIndex(index))
            else {
                continue;
            };
            let (pointer, offset) = match instruction.kind {
                MediumLevelILInstructionKind::LoadSsa(op) => (op.src, 0),
                MediumLevelILInstructionKind::LoadStructSsa(op) => (op.src, op.offset),
                MediumLevelILInstructionKind::StoreSsa(op) => (op.dest, 0),
                MediumLevelILInstructionKind::StoreStructSsa(op) => (op.dest, op.offset),
                _ => continue,
            };
            let Some(place) = i64::try_from(offset)
                .ok()
                .and_then(|offset| origins.place(pointer, 0)?.shift(offset))
                .and_then(|place| layout.resolve(&place).ok())
            else {
                continue;
            };
            let access = Access {
                uncertain: false,
                place,
                width: instruction.size,
                guards: Vec::new(),
            };
            if retained
                .iter()
                .any(|selector| selector.overlaps(&access, input.pointer_width))
            {
                untyped_sites.insert(instruction.address);
            }
        }
    }
    let mut hints = BTreeMap::new();
    for (parameter, variable) in parameters.iter().enumerate() {
        if function.is_var_user_defined(variable) {
            continue;
        }
        let place = Place::parameter(parameter);
        if let Some(ty) = declared_pointer(&view, &function, input, &place) {
            hints.insert((place, Vec::new()), Some(ty));
            continue;
        }
        let Some(fields) =
            layout.fields_in(&place, input.pointer_width, &[], &input.retained_loads)
        else {
            continue;
        };
        let pointer = Type::pointer(&function.arch(), &*record(&fields, &function));
        if !retained
            .iter()
            .any(|selector| selector.place.root == place.root)
        {
            function.create_auto_var(
                variable,
                &*pointer,
                &function.variable_name(variable),
                false,
            );
        }
        hints.insert((place, Vec::new()), Some(pointer));
    }
    for index in 0..il.expression_count() {
        if let Some(instruction) = il.instruction_from_expr_index(MediumLevelExpressionIndex(index))
            && let MediumLevelILInstructionKind::VarSsa(op) = instruction.kind
            && !function.is_var_user_defined(&op.src.variable)
            && instruction.instr_index.0 < il.instruction_count()
            && let Some(place) = origins.place(instruction.expr_index, 0)
        {
            if untyped_sites.contains(&instruction.address) {
                continue;
            }
            match place.root {
                Root::Parameter(parameter)
                    if parameters
                        .get(parameter)
                        .is_none_or(|var| function.is_var_user_defined(var)) =>
                {
                    continue;
                }
                Root::Call(address) if function.call_type_adjustment(address, None).is_some() => {
                    continue;
                }
                _ => (),
            }
            let known = instruction
                .expr_type()
                .map(|ty| ty.contents)
                .filter(|ty| ssa::named_word(ty, input.pointer_width));
            if let Some(ty) = known {
                instruction.set_expr_type(&*ty);
                continue;
            }
            let context = input
                .sites
                .get(&instruction.address)
                .cloned()
                .unwrap_or_default();
            let hint_key = (place.clone(), context.clone());
            if !hints.contains_key(&hint_key) {
                if hints.len() >= 256 {
                    continue;
                }
                let ty = declared_pointer(&view, &function, input, &place).or_else(|| {
                    let fields = layout.fields_in(
                        &place,
                        input.pointer_width,
                        &context,
                        &input.retained_loads,
                    )?;
                    Some(Type::pointer(
                        &function.arch(),
                        &*record(&fields, &function),
                    ))
                });
                hints.insert(hint_key.clone(), ty);
            }
            if let Some(ty) = &hints[&hint_key] {
                instruction.set_expr_type(&**ty);
            }
        }
    }
}

pub(crate) fn register() -> Result<(), ()> {
    workflow::before(
        Config::action(
            "analysis.goRust.localCalls",
            "Rust call targets",
            "Apply independently proven local call targets",
        )
        .eligibility(Eligibility::without_setting().run_once(false)),
        c"core.function.metaAnalysis",
        c"core.function.generateMediumLevelIL",
        apply_calls,
    )?;
    let before = "analysis.goRust.layoutInputs";
    let preparation = Activity::new_with_action(
        Config::action(
            before,
            "Rust layout inputs",
            "Refresh selected Rust layout inputs",
        )
        .eligibility(Eligibility::without_setting().run_once(false)),
        prepare,
    );
    Workflow::cloned("core.module.metaAnalysis")
        .ok_or(())?
        .register_activity(&preparation)?
        .insert("core.module.update", [before])?
        .register()?;
    workflow::after(
        Config::action(
            "analysis.goRust.layouts",
            "Rust layouts",
            "Infer observed Rust field layouts",
        )
        .eligibility(
            Eligibility::without_setting()
                .run_once(false)
                .continuation(true),
        )
        .downstream_dependencies(["core.module.update"]),
        c"core.module.metaAnalysis",
        c"core.module.update",
        refresh_action,
        Some(refresh_eligible),
    )?;
    let name = "analysis.goRust.applyLayouts";
    let activity = Activity::new_with_action(
        Config::action(
            name,
            "Rust field types",
            "Apply current observed Rust field types",
        )
        .eligibility(Eligibility::without_setting().run_once(false)),
        apply,
    );
    Workflow::cloned("core.function.metaAnalysis")
        .ok_or(())?
        .register_activity(&activity)?
        .insert_after("core.function.generateMediumLevelIL", [name])?
        .register()?;
    Ok(())
}

pub(crate) struct Infer;
pub(crate) struct Forget;
pub(crate) struct Inspect;

impl FunctionCommand for Infer {
    fn valid(&self, _: &BinaryView, _: &Function) -> bool {
        true
    }
    fn action(&self, view: &BinaryView, function: &Function) {
        function.store_metadata(ROOT, true, MetadataStoreFlags::PERSISTENT);
        view.store_metadata(ACTIVE, true, MetadataStoreFlags::PERSISTENT);
        view.remove_metadata(STOPPED);
        view.remove_metadata(ATTEMPTS);
        withdraw(view);
        view.update_analysis();
    }
}

impl FunctionCommand for Forget {
    fn valid(&self, _: &BinaryView, function: &Function) -> bool {
        flag(function, ROOT)
    }
    fn action(&self, view: &BinaryView, function: &Function) {
        function.remove_metadata(ROOT);
        let active = view
            .functions()
            .iter()
            .any(|function| flag(&function, ROOT));
        view.store_metadata(ACTIVE, active, MetadataStoreFlags::PERSISTENT);
        view.remove_metadata(STOPPED);
        view.remove_metadata(ATTEMPTS);
        withdraw(view);
        view.update_analysis();
    }
}

impl FunctionCommand for Inspect {
    fn valid(&self, view: &BinaryView, _: &Function) -> bool {
        view.get_metadata::<bool>(ACTIVE) == Some(true)
    }
    fn action(&self, view: &BinaryView, function: &Function) {
        let mut report = String::new();
        if let Some(model) = model(view).filter(|model| {
            (view.get_metadata::<bool>(PENDING) == Some(false)
                || view.get_metadata::<bool>(STOPPED) == Some(true))
                && current(view, model)
                && !function.is_update_needed()
                && model.inputs.iter().all(|input| {
                    find(view, &input.key).is_some_and(|function| !function.is_update_needed())
                })
        }) {
            let _ = writeln!(report, "{}\n", model.status.label());
            for context in model
                .contexts
                .iter()
                .filter(|context| context.function == ssa::key(function))
            {
                let bindings = context
                    .registers
                    .iter()
                    .map(|(&register, value)| {
                        let name = function
                            .arch()
                            .register_from_id(binaryninja::architecture::RegisterId(register))
                            .map(|register| {
                                use binaryninja::architecture::Register;
                                register.name().to_string()
                            })
                            .unwrap_or_else(|| register.to_string());
                        format!("{name}={value:#x}")
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                for call in context.calls.iter().filter(|call| call.indirect) {
                    let target = call
                        .target
                        .as_ref()
                        .map(|key| format!("{:#x}", key.address))
                        .unwrap_or_else(|| "unknown".into());
                    let _ = writeln!(
                        report,
                        "Call {:#x} -> {target} [{}]",
                        call.address, bindings
                    );
                }
            }
            for layout in &model.layouts {
                if layout.function != ssa::key(function) {
                    continue;
                }
                for access in &layout.fields {
                    let _ = writeln!(
                        report,
                        "{}: {}, {} bytes{}",
                        access.place.root,
                        access
                            .place
                            .path
                            .iter()
                            .map(|offset| format!("{offset:+#x}"))
                            .collect::<Vec<_>>()
                            .join(" -> "),
                        access.width,
                        if access.uncertain {
                            " (path condition unavailable)".into()
                        } else if access.guards.is_empty() {
                            String::new()
                        } else {
                            format!(
                                " when {}",
                                access
                                    .guards
                                    .iter()
                                    .map(ToString::to_string)
                                    .collect::<Vec<_>>()
                                    .join(" and ")
                            )
                        }
                    );
                }
                if let Some(input) = model
                    .inputs
                    .iter()
                    .find(|input| input.key == layout.function)
                    && !input.retained_loads.is_empty()
                {
                    report.push_str(
                        "\nCopied values that may outlive writes retain their raw loads.\n",
                    );
                }
                let parameters: BTreeSet<_> = layout
                    .fields
                    .iter()
                    .map(|access| access.place.root)
                    .collect();
                for root in parameters {
                    let place = Place {
                        root,
                        path: vec![0],
                    };
                    if layout.fields_for(&place, view.address_size()).is_none() {
                        let _ = writeln!(
                            report,
                            "{root}: layout withheld; overlapping or unsupported accesses"
                        );
                    }
                }
            }
            report.push_str("\nOffsets describe observed bytes. Source names, complete size and alignment remain unknown.\n");
        } else {
            report.push_str("Current Rust layout analysis is unavailable or pending.\n");
        }
        view.show_plaintext_report("Observed Rust layouts", &report);
    }
}
