use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::Range;

use binaryninja::architecture::{Architecture, ArchitectureExt, Register};
use binaryninja::binary_view::{BinaryView, MetadataStoreFlags};
use binaryninja::command::AddressCommand;
use binaryninja::low_level_il::VisitorAction;
use binaryninja::low_level_il::expression::{ExpressionHandler, LowLevelILExpressionKind as Expr};
use binaryninja::low_level_il::instruction::{
    InstructionHandler, LowLevelILInstructionKind as Instruction,
};
use binaryninja::settings::{QueryOptions, Settings};
use binaryninja::workflow::activity::{Config, Eligibility};
use binaryninja::workflow::{Activity, AnalysisContext, Workflow};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use unstrip::SectionKind;

use crate::binja::llil::Ssa;

use super::{
    calls, convention, effects,
    image::Image,
    metadata::Metadata,
    runtime, types,
    values::{self, Location, Reader, Role},
};

const INPUT: &str = "go-rust.go.context-input.v1";
const RESULT: &str = "go-rust.go.contexts.v1";
const PENDING: &str = "go-rust.go.context-pending.v1";
const ACTIVITY: &str = "analysis.goRust.contexts";
const MAX_CONTEXTS: usize = 4096;

#[derive(Deserialize, Serialize)]
pub(super) struct Model {
    pub functions: BTreeMap<u64, String>,
    pub types: BTreeMap<u64, String>,
    pub itabs: BTreeMap<u64, String>,
    pub code: Vec<Range<u64>>,
    pub lengths: BTreeMap<u64, usize>,
    pub headers: BTreeMap<u64, [u64; 6]>,
    pub runtime: effects::Runtime,
}

#[derive(Clone, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct Origin {
    function: u64,
    call: u64,
    dictionary: Option<u64>,
    location: Option<Location>,
}

#[derive(Deserialize, Serialize)]
struct Call {
    address: u64,
    target: Option<u64>,
    indirect: bool,
    allocation_type: Option<u64>,
    dictionary: Option<u64>,
}

#[derive(Deserialize, Serialize)]
struct Context {
    function: u64,
    dictionary: u64,
    location: Location,
    origins: BTreeSet<Origin>,
    reads: Vec<values::Read>,
    calls: Vec<Call>,
}

#[derive(Default, Deserialize, Serialize)]
struct Results {
    input_digest: String,
    contexts: Vec<Context>,
    watched: Vec<values::Watch>,
    truncated: bool,
    unavailable: usize,
    evidence: Vec<effects::Evidence>,
    runtime_current: bool,
}

pub(crate) fn publish(view: &BinaryView, image: &Image, metadata: &Metadata) -> Result<(), String> {
    if !view
        .default_arch()
        .is_some_and(|arch| arch.name() == "x86_64")
        || image.binary.pointer_size() != 8
        || !runtime::checked_abi(&image.binary)
    {
        clear(view);
        return Ok(());
    }
    let functions = metadata
        .functions
        .iter()
        .filter_map(|function| {
            Some((
                image.loaded_address(function.address)?,
                function.name.clone(),
            ))
        })
        .collect();
    let types = metadata
        .types
        .nodes
        .keys()
        .filter_map(|&address| Some((image.loaded_address(address)?, types::identity(address))))
        .collect();
    let code = image
        .binary
        .sections
        .iter()
        .filter(|section| section.kind == SectionKind::Text)
        .filter_map(|section| {
            Some(
                image.loaded_address(section.addr)?
                    ..image.loaded_address(section.addr.checked_add(section.file_size as u64)?)?,
            )
        })
        .collect();
    let itabs = metadata
        .itabs
        .iter()
        .filter_map(|itab| {
            let bytes = image.binary.read_at_addr(itab.addr, 16)?;
            let interface = u64::from_le_bytes(bytes[..8].try_into().ok()?);
            let concrete = u64::from_le_bytes(bytes[8..].try_into().ok()?);
            let interface = metadata.types.nodes.get(&interface)?;
            let concrete = metadata.types.nodes.get(&concrete)?;
            Some((
                image.loaded_address(itab.addr)?,
                format!("{} -> {}", concrete.name, interface.name),
            ))
        })
        .collect();
    let mut lengths = BTreeMap::new();
    let mut runtime_ranges = Vec::new();
    for function in &metadata.functions {
        let Some(&length) = metadata.extents.get(&function.address) else {
            continue;
        };
        let Some(start) = image.loaded_address(function.address) else {
            continue;
        };
        let Some(end) = function
            .address
            .checked_add(length)
            .and_then(|end| image.loaded_address(end))
        else {
            continue;
        };
        lengths.insert(start, (end - start) as usize);
        if effects::runtime_code(&function.name, function.file.as_deref()) {
            runtime_ranges.push(start..end);
        }
    }
    let runtime_code = effects::Runtime::publish(view, runtime_ranges, &functions);
    let model = Model {
        functions,
        types,
        itabs,
        code,
        lengths,
        headers: metadata
            .types
            .nodes
            .keys()
            .filter_map(|&address| {
                let bytes = image.binary.read_at_addr(address, 48)?;
                let words: Vec<_> = bytes
                    .chunks_exact(8)
                    .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
                    .collect();
                Some((image.loaded_address(address)?, words.try_into().ok()?))
            })
            .collect(),
        runtime: runtime_code,
    };
    view.store_metadata(
        INPUT,
        serde_json::to_string(&model).map_err(|error| error.to_string())?,
        MetadataStoreFlags::EPHEMERAL,
    );
    view.store_metadata(PENDING, true, MetadataStoreFlags::EPHEMERAL);
    Ok(())
}

pub(crate) fn clear(view: &BinaryView) {
    view.remove_metadata(INPUT);
    view.remove_metadata(RESULT);
    view.remove_metadata(PENDING);
}

fn generic(name: &str) -> bool {
    name.contains("[go.shape.") && !name.ends_with(".abi0")
}

fn free_generic(name: &str) -> bool {
    generic(name) && name.ends_with(']')
}

fn locations(view: &BinaryView, name: &str) -> Vec<Location> {
    let Some(arch) = view.default_arch() else {
        return Vec::new();
    };
    let registers = if free_generic(name) {
        &convention::INTEGERS[..1]
    } else {
        &convention::INTEGERS[..]
    };
    let mut result: Vec<_> = registers
        .iter()
        .filter_map(|name| Some(Location::Register(arch.register_by_name(name)?.id().0)))
        .collect();
    if !free_generic(name) {
        result.push(Location::Stack(8));
    }
    result
}

fn dictionary(
    view: &BinaryView,
    model: &Model,
    address: u64,
    watched: &mut values::Watches,
) -> bool {
    address % 8 == 0
        && !model.types.contains_key(&address)
        && !model.itabs.contains_key(&address)
        && watched.word(view, &model.code, address, 8).is_some()
}

type Key = (u64, Location, u64);
type Bindings = BTreeMap<Key, BTreeSet<Origin>>;

struct Link {
    parent: Key,
    call: u64,
    child: Key,
    slot: Option<u64>,
}

fn seeds(
    view: &BinaryView,
    model: &Model,
    watched: &mut values::Watches,
    effects: &effects::Analysis<'_>,
) -> Bindings {
    let mut result = Bindings::new();
    let mut examined = BTreeSet::new();
    for (&callee, name) in &model.functions {
        if !generic(name) {
            continue;
        }
        for site in view.code_refs_to_addr(callee).iter() {
            let Some(function) = site.func.as_ref() else {
                continue;
            };
            let address = function.start();
            if !model.functions.contains_key(&address) || !examined.insert((address, site.address))
            {
                continue;
            }
            let Some(ssa) = Ssa::new(function) else {
                continue;
            };
            if Ssa::has_user_values(function) {
                continue;
            }
            if !effects.track(function, &ssa) {
                watched.limited = true;
                return Bindings::new();
            }
            let mut reader = Reader::new(view, &ssa, None, &model.code);
            // Enumerate actual SSA indices; address convenience queries use regular IL indices.
            for index in 0..ssa.il.instruction_count() {
                let Some(instruction) = ssa.il.instruction_from_index(index.into()) else {
                    continue;
                };
                if instruction.address() != site.address {
                    continue;
                }
                let op = match instruction.kind() {
                    Instruction::CallSsa(op) | Instruction::TailCallSsa(op) => op,
                    _ => continue,
                };
                let Some(target) = reader.evaluate(op.target()) else {
                    continue;
                };
                let Some(name) = model
                    .functions
                    .get(&target.number)
                    .filter(|name| generic(name))
                else {
                    continue;
                };
                for location in locations(view, name) {
                    let Some(argument) = reader.argument(instruction, location) else {
                        continue;
                    };
                    if !dictionary(view, model, argument.number, watched) {
                        continue;
                    }
                    result
                        .entry((target.number, location, argument.number))
                        .or_default()
                        .insert(Origin {
                            function: address,
                            call: site.address,
                            dictionary: None,
                            location: None,
                        });
                    if result.len() > MAX_CONTEXTS {
                        watched.merge(reader.watched);
                        return result;
                    }
                }
            }
            if !ssa.current(function) {
                watched.limited = true;
                return Bindings::new();
            }
            watched.merge(reader.watched);
        }
    }
    result
}

fn collect(view: &BinaryView, model: &Model) -> Results {
    let mut results = Results::default();
    let Some(platform) = view.default_platform() else {
        return results;
    };
    let mut watched = values::Watches::default();
    let effects = effects::Analysis::new(view, model);
    let mut bindings = seeds(view, model, &mut watched, &effects);
    let mut pending: VecDeque<_> = bindings.keys().copied().collect();
    let mut visited = BTreeSet::new();
    let mut links = Vec::new();
    let mut indices = BTreeMap::new();
    let mut limited = BTreeSet::new();
    while let Some(key @ (address, location, binding)) = pending.pop_front() {
        if !visited.insert(key) {
            continue;
        }
        if visited.len() > MAX_CONTEXTS {
            results.truncated = true;
            break;
        }
        let function = view.function_at(&platform, address);
        let ssa = function.as_ref().and_then(|function| Ssa::new(function));
        let (Some(function), Some(ssa)) = (function, ssa) else {
            results.unavailable += 1;
            continue;
        };
        if Ssa::has_user_values(&function) {
            results.unavailable += 1;
            continue;
        }
        if !effects.track(&function, &ssa) {
            results.unavailable += 1;
            continue;
        }
        let mut reader =
            Reader::new(view, &ssa, Some((location, binding)), &model.code).with_effects(&effects);
        let mut calls = Vec::new();
        for index in 0..ssa.il.instruction_count() {
            let Some(instruction) = ssa.il.instruction_from_index(index.into()) else {
                continue;
            };
            match instruction.kind() {
                Instruction::CallSsa(op) | Instruction::TailCallSsa(op) => {
                    let target = reader
                        .evaluate(op.target())
                        .filter(|target| model.functions.contains_key(&target.number));
                    let mut call = Call {
                        address: instruction.address(),
                        target: target.map(|value| value.number),
                        indirect: !matches!(op.target().kind(), Expr::ConstPtr(_) | Expr::Const(_)),
                        allocation_type: None,
                        dictionary: None,
                    };
                    if let Some(target) = target {
                        reader.used(target, Role::CallTarget);
                        if let Some(kind) = calls::allocation(view, target.number)
                            && let Some(register) =
                                function.arch().register_by_name(kind.descriptor_register())
                            && let Some(descriptor) =
                                reader.argument(instruction, Location::Register(register.id().0))
                            && model.types.contains_key(&descriptor.number)
                        {
                            reader.used(descriptor, Role::AllocationType);
                            call.allocation_type = Some(descriptor.number);
                        }
                        let name = &model.functions[&target.number];
                        if generic(name) {
                            for child_location in locations(view, name) {
                                let Some(argument) = reader.argument(instruction, child_location)
                                else {
                                    continue;
                                };
                                if !dictionary(view, model, argument.number, &mut reader.watched) {
                                    continue;
                                }
                                let child = (target.number, child_location, argument.number);
                                let new = !bindings.contains_key(&child);
                                if new && bindings.len() >= MAX_CONTEXTS {
                                    results.truncated = true;
                                    continue;
                                }
                                bindings.entry(child).or_default().insert(Origin {
                                    function: address,
                                    call: call.address,
                                    dictionary: Some(binding),
                                    location: Some(location),
                                });
                                links.push(Link {
                                    parent: key,
                                    call: call.address,
                                    child,
                                    slot: argument.slot,
                                });
                                if new {
                                    pending.push_back(child);
                                }
                            }
                        }
                    }
                    calls.push(call);
                }
                Instruction::SetRegSsa(op) => {
                    op.source_expr().visit_tree(&mut |expression| {
                        if matches!(expression.kind(), Expr::LoadSsa(_)) {
                            reader.evaluate(*expression);
                        }
                        VisitorAction::Descend
                    });
                }
                _ => (),
            }
        }
        if reader.limited {
            limited.insert(key);
        }
        if !ssa.current(&function) {
            results.unavailable += 1;
            continue;
        }
        indices.insert(key, results.contexts.len());
        watched.merge(reader.watched);
        results.contexts.push(Context {
            function: address,
            dictionary: binding,
            location,
            origins: BTreeSet::new(),
            reads: reader.reads.into_values().collect(),
            calls,
        });
    }
    // Receiver candidates require real slot use. A child is a subdictionary only
    // after its own entry storage is established; candidate cycles prove nothing.
    let mut accepted: BTreeSet<_> = indices
        .iter()
        .filter_map(|(&key, &index)| {
            let context = &results.contexts[index];
            (free_generic(&model.functions[&key.0])
                || context.reads.iter().any(|read| !read.uses.is_empty()))
            .then_some(key)
        })
        .collect();
    loop {
        let mut changed = false;
        for link in &links {
            if link.slot.is_some()
                && accepted.contains(&link.child)
                && indices.contains_key(&link.parent)
            {
                changed |= accepted.insert(link.parent);
            }
        }
        if !changed {
            break;
        }
    }
    // A valid child proof still needs a live path from an independently seeded call.
    let mut rooted: BTreeSet<_> = accepted
        .iter()
        .copied()
        .filter(|key| {
            bindings
                .get(key)
                .is_some_and(|origins| origins.iter().any(|origin| origin.dictionary.is_none()))
        })
        .collect();
    loop {
        let mut changed = false;
        for link in &links {
            if rooted.contains(&link.parent) && accepted.contains(&link.child) {
                changed |= rooted.insert(link.child);
            }
        }
        if !changed {
            break;
        }
    }
    accepted.retain(|key| rooted.contains(key));
    results.truncated |= accepted.iter().any(|key| limited.contains(key));
    let mut children = BTreeMap::<(Key, u64), BTreeSet<u64>>::new();
    for link in links {
        if !accepted.contains(&link.parent) || !accepted.contains(&link.child) {
            continue;
        }
        let context = &mut results.contexts[indices[&link.parent]];
        if let Some(slot) = link.slot
            && let Some(read) = context.reads.iter_mut().find(|read| read.offset == slot)
        {
            read.uses.insert(Role::Subdictionary);
        }
        children
            .entry((link.parent, link.call))
            .or_default()
            .insert(link.child.2);
    }
    for ((parent, address), dictionaries) in children {
        if dictionaries.len() == 1
            && let Some(call) = results.contexts[indices[&parent]]
                .calls
                .iter_mut()
                .find(|call| call.address == address)
        {
            call.dictionary = dictionaries.first().copied();
        }
    }
    results.contexts.retain(|context| {
        accepted.contains(&(context.function, context.location, context.dictionary))
    });
    for context in &mut results.contexts {
        context.origins = bindings
            .remove(&(context.function, context.location, context.dictionary))
            .unwrap_or_default();
        context
            .origins
            .retain(|origin| match (origin.location, origin.dictionary) {
                (Some(location), Some(dictionary)) => {
                    accepted.contains(&(origin.function, location, dictionary))
                }
                _ => true,
            });
    }
    if let Some((evidence, runtime_current)) = effects.finish(&mut watched) {
        results.evidence = evidence;
        results.runtime_current = runtime_current;
    } else {
        results.contexts.clear();
        results.unavailable += 1;
    }
    results.truncated |= effects.limited();
    results.truncated |= watched.limited;
    if watched.limited {
        results.contexts.clear();
    }
    results.watched = watched.finish();
    if !results
        .watched
        .iter()
        .all(|watch| watch.current(view, &model.code))
    {
        results.contexts.clear();
        results.unavailable += 1;
    }
    results
}

fn run(view: &BinaryView) -> Result<(), String> {
    if Settings::global()
        .get_string_with_opts("analysis.mode", &mut QueryOptions::new_with_view(view))
        != "full"
    {
        view.remove_metadata(RESULT);
        return Ok(());
    }
    let Some(input) = view.get_metadata::<String>(INPUT) else {
        view.remove_metadata(RESULT);
        return Ok(());
    };
    let model: Model = serde_json::from_str(&input).map_err(|error| error.to_string())?;
    let input_digest = format!("{:x}", Sha256::digest(input.as_bytes()));
    if view.get_metadata::<bool>(PENDING) != Some(true)
        && let Some(cached) = view.get_metadata::<String>(RESULT)
        && let Ok(cached) = serde_json::from_str::<Results>(&cached)
        && !cached.truncated
        && cached.unavailable == 0
        && cached.input_digest == input_digest
        && cached.runtime_current == model.runtime.current(view)
        && cached.evidence.iter().all(|record| record.current(view))
        && cached
            .watched
            .iter()
            .all(|watch| watch.current(view, &model.code))
    {
        return Ok(());
    }
    let mut results = collect(view, &model);
    if view.get_metadata::<String>(INPUT).as_deref() != Some(input.as_str()) {
        view.remove_metadata(RESULT);
        return Ok(());
    }
    results.input_digest = input_digest;
    view.store_metadata(
        RESULT,
        serde_json::to_string(&results).map_err(|error| error.to_string())?,
        MetadataStoreFlags::EPHEMERAL,
    );
    view.store_metadata(PENDING, false, MetadataStoreFlags::EPHEMERAL);
    Ok(())
}

fn changed(context: &AnalysisContext) {
    let view = context.view();
    // Idle callbacks only materialize discarded IL; no analysis inputs changed.
    let state = unsafe { binaryninjacore_sys::BNGetAnalysisState(view.handle) };
    if state != binaryninjacore_sys::BNAnalysisState::IdleState
        && view.query_metadata(INPUT).is_some()
    {
        view.store_metadata(PENDING, true, MetadataStoreFlags::EPHEMERAL);
    }
}

fn analyze(context: &AnalysisContext) {
    let view = context.view();
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&view))) {
        Ok(Ok(())) => (),
        _ => {
            view.remove_metadata(RESULT);
            tracing::warn!("Go dictionary analysis stopped");
        }
    }
}

pub(crate) fn register() -> Result<(), ()> {
    let changes = "analysis.goRust.contextChanges";
    let marker = Activity::new_with_action(
        Config::action(
            changes,
            "Go dictionary inputs",
            "Track changed dictionary analysis inputs",
        )
        .eligibility(Eligibility::without_setting().run_once(false)),
        changed,
    );
    Workflow::cloned("core.function.metaAnalysis")
        .ok_or(())?
        .register_activity(&marker)?
        .insert_after("core.function.commitAnalysisData", [changes])?
        .register()?;
    let activity = Activity::new_with_action(
        Config::action(
            ACTIVITY,
            "Go dictionaries",
            "Recover concrete Go dictionary contexts",
        )
        .eligibility(Eligibility::auto().run_once(false)),
        analyze,
    );
    Workflow::cloned("core.module.metaAnalysis")
        .ok_or(())?
        .register_activity(&activity)?
        .insert_after("core.module.update", [ACTIVITY])?
        .register()?;
    Ok(())
}

pub(crate) struct ShowContexts;

impl AddressCommand for ShowContexts {
    fn valid(&self, view: &BinaryView, _address: u64) -> bool {
        view.query_metadata(RESULT).is_some() && view.get_metadata::<bool>(PENDING) != Some(true)
    }

    fn action(&self, view: &BinaryView, address: u64) {
        match report(view, address) {
            Some(report) => view.show_plaintext_report("Go dictionary contexts", &report),
            None => tracing::info!("No concrete Go dictionary context at {address:#x}"),
        }
    }
}

fn report(view: &BinaryView, address: u64) -> Option<String> {
    if view.get_metadata::<bool>(PENDING) == Some(true) {
        return None;
    }
    let input = view.get_metadata::<String>(INPUT)?;
    let model: Model = serde_json::from_str(&input).ok()?;
    let results: Results = serde_json::from_str(&view.get_metadata::<String>(RESULT)?).ok()?;
    if results.input_digest != format!("{:x}", Sha256::digest(input.as_bytes()))
        || results.runtime_current != model.runtime.current(view)
        || !results.evidence.iter().all(|record| record.current(view))
    {
        return None;
    }
    if !results
        .watched
        .iter()
        .all(|watch| watch.current(view, &model.code))
    {
        return None;
    }
    let owners: BTreeSet<_> = view
        .functions_containing(address)
        .iter()
        .map(|function| function.start())
        .collect();
    let mut report = String::new();
    for context in results.contexts.iter().filter(|context| {
        owners.contains(&context.function)
            || context.origins.iter().any(|origin| origin.call == address)
    }) {
        let storage = match context.location {
            Location::Register(id) => view
                .default_arch()?
                .register_from_id(binaryninja::architecture::RegisterId(id))?
                .name()
                .to_string(),
            Location::Stack(offset) => format!("entry stack {offset:+#x}"),
        };
        report.push_str(&format!(
            "{} — dictionary {:#x} ({storage})\n",
            model.functions.get(&context.function)?,
            context.dictionary
        ));
        for read in &context.reads {
            let value = model
                .types
                .get(&read.value)
                .and_then(|id| view.type_name_by_id(id))
                .map(|name| name.to_string())
                .or_else(|| model.functions.get(&read.value).cloned())
                .or_else(|| model.itabs.get(&read.value).cloned())
                .unwrap_or_else(|| format!("{:#x}", read.value));
            report.push_str(&format!("  +{:#x}: {}", read.offset, value));
            if !read.uses.is_empty() {
                report.push_str(&format!(
                    " ({})",
                    read.uses
                        .iter()
                        .map(|role| role.label())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            report.push('\n');
        }
        for call in &context.calls {
            if let Some(descriptor) = call.allocation_type {
                let name = view.type_name_by_id(model.types.get(&descriptor)?)?;
                report.push_str(&format!("  {:#x}: allocation -> {name}*\n", call.address));
            }
            if (call.indirect || call.dictionary.is_some())
                && let Some(target) = call.target
            {
                report.push_str(&format!(
                    "  {:#x}: call -> {}",
                    call.address,
                    model.functions.get(&target)?
                ));
                if let Some(dictionary) = call.dictionary {
                    report.push_str(&format!(" (dictionary {dictionary:#x})"));
                }
                report.push('\n');
            }
        }
        report.push('\n');
    }
    if report.is_empty() {
        return None;
    }
    if results.truncated {
        report.push_str("Analysis limit reached; some facts were not examined.\n");
    }
    if results.unavailable != 0 {
        report.push_str(&format!(
            "{} contexts lack available analysis.\n",
            results.unavailable
        ));
    }
    Some(report)
}
