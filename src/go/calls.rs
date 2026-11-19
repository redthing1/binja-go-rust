use std::collections::{BTreeMap, BTreeSet, HashMap};

use binaryninja::architecture::{ArchitectureExt, Register};
use binaryninja::binary_view::{BinaryView, MetadataStoreFlags};
use binaryninja::function::FunctionUpdateType;
use binaryninja::low_level_il::instruction::{InstructionHandler, LowLevelILInstructionKind};
use binaryninja::metadata::Metadata as Stored;
use binaryninja::rc::Ref;
use binaryninja::types::{NamedTypeReference, NamedTypeReferenceClass, Type, TypeBuilder};
use binaryninja::variable::{RegisterValue, RegisterValueType};
use binaryninja::workflow::activity::{Config, Eligibility};
use binaryninjacore_sys::BNAnalysisContext;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::ffi::c_void;

use super::{bounds, image::Image, metadata::Metadata, runtime, types};
use crate::binja::workflow::{self, FunctionContext};

const MODEL: &str = "go-rust.go.calls.v1";
const BASELINES: &str = "go-rust.go.helper-bytes.v1";
const SITES: &str = "go-rust.go.call-sites.v1";
const ACTIVITY: &str = "analysis.goRust.calls";

#[derive(Deserialize, Serialize)]
struct Helper {
    kind: Kind,
    start: u64,
    length: usize,
    digest: String,
}

#[derive(Deserialize, Serialize)]
enum Kind {
    Allocation(runtime::Allocation),
    Bounds(Option<bounds::Bounds>),
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Publish a replaceable model using core-owned metadata, with no retained view refs.
pub(crate) fn publish(view: &BinaryView, image: &Image, metadata: &Metadata) -> Result<(), String> {
    let mut helpers = HashMap::<String, String>::new();
    let mut descriptors = HashMap::<String, String>::new();
    let mut bounds = HashMap::<String, String>::new();
    let mut baselines: BTreeMap<String, String> = view
        .get_metadata::<String>(BASELINES)
        .and_then(|value| serde_json::from_str(&value).ok())
        .unwrap_or_default();
    if view
        .default_arch()
        .is_some_and(|arch| arch.name() == "x86_64")
        && image.binary.pointer_size() == 8
        && let Some(version) = runtime::checked_version(&image.binary)
    {
        for function in &metadata.functions {
            let (start, name) = (function.address, function.name.as_str());
            let kind = match (runtime::Allocation::from_name(name), name, version) {
                (Some(kind), _, _) => Kind::Allocation(kind),
                (_, "runtime.panicIndex", 25) => Kind::Bounds(Some(bounds::Bounds {
                    code: 0,
                    signed: true,
                    x: bounds::Operand::Register(0),
                    y: bounds::Operand::Register(1),
                })),
                (_, "runtime.panicBounds", 26 | 27) => Kind::Bounds(None),
                _ => continue,
            };
            let Some(&length) = metadata.extents.get(&start) else {
                continue;
            };
            let length = usize::try_from(length).map_err(|_| "helper size overflow")?;
            if length == 0 || length > 1_048_576 {
                continue;
            }
            let Some(bytes) = image.binary.text_slice_at(start, length) else {
                continue;
            };
            if bytes.len() != length {
                continue;
            }
            let hash = digest(bytes);
            let baseline = baselines
                .entry(format!("{name}:{start:x}"))
                .or_insert_with(|| hash.clone());
            if *baseline != hash {
                continue;
            }
            let Some(start) = image.loaded_address(start) else {
                continue;
            };
            let helper = Helper {
                kind,
                start,
                length,
                digest: hash,
            };
            helpers.insert(
                format!("{start:x}"),
                serde_json::to_string(&helper).map_err(|error| error.to_string())?,
            );
        }
        for &address in metadata.types.nodes.keys() {
            if let Some(loaded) = image.loaded_address(address) {
                descriptors.insert(format!("{loaded:x}"), types::identity(address));
            }
        }
        for (&owner, spans) in &metadata.bounds {
            let spans = spans
                .iter()
                .filter_map(|span| {
                    Some(bounds::Span {
                        start: image.loaded_address(span.start)?,
                        end: image.loaded_address(span.end)?,
                        bounds: span.bounds,
                    })
                })
                .collect::<Vec<_>>();
            if let Some(owner) = image.loaded_address(owner) {
                bounds.insert(
                    format!("{owner:x}"),
                    serde_json::to_string(&spans).map_err(|error| error.to_string())?,
                );
            }
        }
    }
    view.store_metadata(
        BASELINES,
        serde_json::to_string(&baselines).map_err(|error| error.to_string())?,
        MetadataStoreFlags::PERSISTENT,
    );
    let model: HashMap<&str, Ref<Stored>> = HashMap::from([
        ("helpers", helpers.into()),
        ("types", descriptors.into()),
        ("bounds", bounds.into()),
    ]);
    view.store_metadata(MODEL, model, MetadataStoreFlags::EPHEMERAL);
    revisit(view);
    Ok(())
}

fn revisit(view: &BinaryView) {
    for function in view.functions().iter() {
        if function
            .query_metadata(SITES)
            .and_then(|value| value.get_unsigned_integer_list())
            .is_some_and(|sites| !sites.is_empty())
        {
            function.reanalyze(FunctionUpdateType::FullAutoFunctionUpdate);
        }
    }
}

pub(crate) fn clear(view: &BinaryView) {
    view.remove_metadata(MODEL);
    revisit(view);
}

fn constant(value: RegisterValue) -> Option<u64> {
    matches!(
        value.state,
        RegisterValueType::ConstantValue | RegisterValueType::ConstantPointerValue
    )
    .then_some(value.value as u64)
}

fn field(model: &Stored, name: &str) -> Option<Ref<Stored>> {
    model.get(name).ok().flatten()
}

pub(super) fn allocation(view: &BinaryView, target: u64) -> Option<runtime::Allocation> {
    let model = view.query_metadata(MODEL)?;
    let helpers = field(&model, "helpers")?;
    let record = field(&helpers, &format!("{target:x}"))?.get_string()?;
    let helper: Helper = serde_json::from_slice(record.to_bytes()).ok()?;
    let bytes = view.read_vec(helper.start, helper.length);
    if bytes.len() != helper.length || digest(&bytes) != helper.digest {
        return None;
    }
    match helper.kind {
        Kind::Allocation(kind) => Some(kind),
        _ => None,
    }
}

fn call_type(
    context: &FunctionContext,
    view: &BinaryView,
    descriptors: &Stored,
    bounds: &Stored,
    helper: &Helper,
    index: usize,
    address: u64,
) -> Option<Ref<Type>> {
    let bytes = view.read_vec(helper.start, helper.length);
    if bytes.len() != helper.length || digest(&bytes) != helper.digest {
        return None;
    }
    let arch = context.function.arch();
    let kind = match helper.kind {
        Kind::Allocation(kind) => kind,
        Kind::Bounds(known) => {
            let bounds = known.or_else(|| {
                let spans =
                    field(bounds, &format!("{:x}", context.function.start()))?.get_string()?;
                let spans: Vec<bounds::Span> = serde_json::from_slice(spans.to_bytes()).ok()?;
                let pc = address
                    .checked_add(view.instruction_len(&arch, address)? as u64)?
                    .checked_sub(1)?;
                spans
                    .into_iter()
                    .find(|span| span.start <= pc && pc < span.end)
                    .map(|span| span.bounds)
            })?;
            return bounds::signature(arch, bounds);
        }
    };
    let register = arch.register_by_name(kind.descriptor_register())?;
    let address = constant(context.register_at(index, register.id().0))?;
    let id = field(descriptors, &format!("{address:x}"))?.get_string()?;
    let id = id.to_str().ok()?;
    let ty = view.type_by_id(id)?;
    let reference = NamedTypeReference::new_with_id(
        NamedTypeReferenceClass::TypedefNamedTypeClass,
        id,
        view.type_name_by_id(id)?,
    );
    let builder = TypeBuilder::named_type(&reference);
    builder
        .set_width(ty.width() as usize)
        .set_alignment(ty.alignment());
    runtime::signature(arch, kind, &builder.finalize())
}

fn apply(context: &FunctionContext) {
    let function = &context.function;
    let view = function.view();
    let previous = function
        .query_metadata(SITES)
        .and_then(|value| value.get_unsigned_integer_list())
        .unwrap_or_default();
    let model = view.query_metadata(MODEL);
    if previous.is_empty() && model.is_none() {
        return;
    }
    let mut history: BTreeSet<_> = previous.iter().copied().collect();
    let mut applied = BTreeSet::new();
    // The context owns this IL; do not request recursive analysis through Function.
    if let Some(model) = model
        && let (Some(helpers), Some(descriptors), Some(bounds)) = (
            field(&model, "helpers"),
            field(&model, "types"),
            field(&model, "bounds"),
        )
    {
        for site in function.call_sites().iter() {
            for instruction in context.il.instructions_at(site.address) {
                let target = match instruction.kind() {
                    LowLevelILInstructionKind::Call(op)
                    | LowLevelILInstructionKind::TailCall(op) => constant(op.target().value()),
                    _ => None,
                };
                let Some(record) =
                    target.and_then(|target| field(&helpers, &format!("{target:x}")))
                else {
                    continue;
                };
                let Some(helper) = record
                    .get_string()
                    .and_then(|value| serde_json::from_slice::<Helper>(value.to_bytes()).ok())
                else {
                    continue;
                };
                history.insert(site.address);
                let Some(signature) = call_type(
                    context,
                    &view,
                    &descriptors,
                    &bounds,
                    &helper,
                    instruction.index.0,
                    site.address,
                ) else {
                    continue;
                };
                function.set_auto_call_type_adjustment(site.address, signature.as_ref(), None);
                tracing::debug!("Go call applied {:#x}: {signature}", site.address);
                applied.insert(site.address);
            }
        }
    }
    for address in history.difference(&applied) {
        crate::binja::calls::clear(&function, *address);
    }
    if !history.is_empty() {
        function.store_metadata(
            SITES,
            &history.into_iter().collect::<Vec<_>>(),
            MetadataStoreFlags::PERSISTENT,
        );
    }
}

unsafe extern "C" fn analyze(_: *mut c_void, context: *mut BNAnalysisContext) {
    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if let Some(context) = unsafe { FunctionContext::from_raw(context) } {
            apply(&context);
        }
    }))
    .is_err()
    {
        tracing::error!("Go call analysis panicked");
    }
}

pub(crate) fn register() -> Result<(), ()> {
    workflow::after(
        Config::action(ACTIVITY, "Go calls", "Annotate validated Go runtime calls")
            .eligibility(Eligibility::auto().run_once(false)),
        c"core.function.metaAnalysis",
        c"core.function.generateMediumLevelIL",
        analyze,
        None,
    )
}
