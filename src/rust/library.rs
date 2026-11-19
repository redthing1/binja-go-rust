use std::collections::{BTreeMap, BTreeSet};
use std::ffi::CString;
use std::fmt::Write;

use binaryninja::binary_view::{BinaryView, MetadataStoreFlags};
use binaryninja::command::FunctionCommand;
use binaryninja::function::Function;
use binaryninja::rc::Ref;
use binaryninja::types::{Type, TypeClass};
use binaryninjacore_sys::*;
use serde::{Deserialize, Serialize};

use super::layout::{Contract, Key, Wire};
use super::ssa::abi;
use crate::binja::warp;

const PROBE: &str = "go-rust.rust.word-probe.v1";
const CALLS: &str = "go-rust.rust.typed-calls.v1";
const OWNED: &std::ffi::CStr = c"go-rust.word-call";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Hint {
    pub target: Key,
    pub wire: Wire,
}

pub(super) fn eligible(function: &Function, contract: &Contract) -> bool {
    function.arch().name() == "x86_64"
        && contract.convention.as_deref() == Some("sysv")
        && contract.stack_adjustment == 0
        && contract.can_return
        && !contract.variadic
        && contract.result.width == 8
        && contract.result.integer.is_some()
        && !contract.parameters.is_empty()
        && contract.parameters.iter().all(|slot| {
            slot.width == 8 && slot.integer.is_some() && abi::word_register(slot, 8).is_some()
        })
        && !function.has_explicitly_defined_type()
        && function
            .parameter_variables()
            .contents
            .iter()
            .all(|var| !function.is_var_user_defined(var))
}

pub(super) fn probe(function: &Function, contract: &Contract) -> bool {
    if !eligible(function, contract) {
        return false;
    }
    if function
        .query_metadata(PROBE)
        .and_then(|value| value.get_boolean())
        == Some(true)
    {
        return true;
    }
    let Some(evidence) = warp::inspect(function) else {
        return false;
    };
    let proposed = evidence
        .candidates
        .iter()
        .map(|candidate| &candidate.signature)
        .chain(
            evidence
                .recorded
                .iter()
                .filter(|signature| signature.guid == evidence.guid),
        )
        .filter_map(|signature| signature.ty.as_ref())
        .any(|ty| {
            let Some(parameters) = ty.parameters() else {
                return false;
            };
            parameters.len() == 1
                && parameters[0].ty.contents.type_class() == TypeClass::IntegerTypeClass
                && parameters[0].ty.contents.width() == 8
                && ty.return_value().is_some_and(|value| {
                    value.contents.type_class() == TypeClass::IntegerTypeClass
                        && value.contents.width() == 8
                })
        });
    if proposed {
        // Persist the query, not its answer or an assumed source identity.
        function.store_metadata(PROBE, true, MetadataStoreFlags::PERSISTENT);
    }
    proposed
}

fn history(function: &Function) -> BTreeMap<u64, Hint> {
    function
        .query_metadata(CALLS)
        .and_then(|value| value.get_string())
        .and_then(|value| serde_json::from_slice(value.to_bytes()).ok())
        .unwrap_or_default()
}

fn raw_location(register: u32, piece: &mut BNValueLocationComponent) -> BNValueLocation {
    *piece = BNValueLocationComponent {
        variable: BNVariable {
            type_: BNVariableSourceType::RegisterVariableSourceType,
            index: 0,
            storage: i64::from(register),
        },
        offset: 0,
        sizeValid: false,
        size: 0,
    };
    BNValueLocation {
        count: 1,
        components: piece,
        indirect: false,
        returnedPointerValid: false,
        returnedPointer: piece.variable,
    }
}

fn call_type(function: &Function, wire: &Wire) -> Option<Ref<Type>> {
    let original = function.function_type();
    let parameters = original.parameters()?;
    let parameter = parameters.get(wire.parameter)?;
    let name = CString::new(parameter.name.as_str()).ok()?;
    unsafe {
        let builder = BNCreateTypeBuilderFromType(original.handle);
        if builder.is_null() {
            return None;
        }
        let mut input = std::mem::zeroed();
        let mut parameter = BNFunctionParameter {
            name: name.as_ptr().cast_mut(),
            type_: parameter.ty.contents.handle,
            typeConfidence: parameter.ty.confidence,
            locationSource: BNValueLocationSource::CustomLocationSource,
            location: raw_location(wire.input, &mut input),
        };
        BNSetFunctionTypeBuilderParameters(builder, &mut parameter, 1);
        let mut output = std::mem::zeroed();
        let mut location = BNValueLocationWithConfidence {
            location: raw_location(wire.output, &mut output),
            confidence: 255,
        };
        BNTypeBuilderSetIsReturnValueDefaultLocation(builder, false);
        BNTypeBuilderSetReturnValueLocation(builder, &mut location);
        BNSetTypeBuilderAttribute(builder, OWNED.as_ptr(), c"1".as_ptr());
        let result = BNFinalizeTypeBuilder(builder);
        BNFreeTypeBuilder(builder);
        (!result.is_null()).then(|| Type::ref_from_raw(result))
    }
}

pub(super) fn owned(function: &Function, address: u64) -> Option<Hint> {
    let hint = history(function).remove(&address)?;
    let ty = function.call_type_adjustment(address, None)?;
    let attribute = unsafe { BNGetTypeAttributeByName(ty.contents.handle, OWNED.as_ptr()) };
    if attribute.is_null() {
        return None;
    }
    unsafe { BNFreeString(attribute) };
    let platform = binaryninja::platform::Platform::by_name(&hint.target.platform)?;
    let target = function
        .view()
        .function_at(&platform, hint.target.address)?;
    let expected = call_type(&target, &hint.wire)?;
    (ty.contents == expected).then_some(hint)
}

pub(super) fn clear_calls(function: &Function) {
    for address in history(function).keys() {
        crate::binja::calls::clear(function, *address);
    }
    function.remove_metadata(CALLS);
}

pub(super) fn apply_calls(function: &Function, hints: BTreeMap<u64, Hint>) {
    let mut applied = BTreeMap::new();
    let view = function.view();
    for (address, hint) in hints {
        let Some(platform) = binaryninja::platform::Platform::by_name(&hint.target.platform) else {
            continue;
        };
        let Some(target) = view.function_at(&platform, hint.target.address) else {
            continue;
        };
        let Some(contract) = abi::capture(&target) else {
            continue;
        };
        if !eligible(&target, &contract) {
            continue;
        }
        let Some(ty) = call_type(&target, &hint.wire) else {
            continue;
        };
        function.set_auto_call_type_adjustment(address, &*ty, None);
        applied.insert(address, hint);
    }
    if !applied.is_empty() {
        if let Ok(value) = serde_json::to_string(&applied) {
            function.store_metadata(CALLS, value, MetadataStoreFlags::PERSISTENT);
        }
    }
}

pub(crate) struct Inspect;

impl FunctionCommand for Inspect {
    fn valid(&self, _: &BinaryView, _: &Function) -> bool {
        warp::available()
    }

    fn action(&self, view: &BinaryView, function: &Function) {
        let report = match warp::inspect(function) {
            Some(evidence) => report(function, &evidence),
            None => "Current function analysis is unavailable or pending.\n".into(),
        };
        view.show_plaintext_report("Rust library evidence", &report);
    }
}

fn signature(
    report: &mut String,
    signature: &warp::Signature,
    observed: Option<&[warp::Constraint]>,
) {
    let _ = writeln!(report, "{}", signature.name);
    if let Some(ty) = &signature.ty {
        let _ = writeln!(report, "  Type: {ty}");
    }
    let identities: BTreeSet<_> = signature.constraints.iter().map(|c| &c.guid).collect();
    let relative = signature
        .constraints
        .iter()
        .filter(|c| c.offset.is_some())
        .count();
    let _ = writeln!(
        report,
        "  Constraints: {} ({} identities, {} relative)",
        signature.constraints.len(),
        identities.len(),
        relative
    );
    match observed {
        Some(observed) if !signature.constraints.is_empty() => {
            let observed: BTreeSet<_> = observed.iter().collect();
            let expected: BTreeSet<_> = signature.constraints.iter().collect();
            let _ = writeln!(
                report,
                "  Current support: {} of {} constraints",
                expected.intersection(&observed).count(),
                expected.len()
            );
        }
        Some(_) => report.push_str("  Current support: no constraints recorded\n"),
        None => report.push_str("  Current support: unavailable\n"),
    }
}

fn report(function: &Function, evidence: &warp::Evidence) -> String {
    let mut report = format!(
        "{} at {:#x}\nCode GUID: {}\n\n",
        function.symbol().full_name().to_string_lossy(),
        function.start(),
        evidence.guid
    );
    if let Some(recorded) = &evidence.recorded {
        if recorded.guid == evidence.guid {
            report.push_str("Recorded WARP match:\n");
        } else {
            report.push_str("Recorded WARP match differs from the current code:\n");
        }
        signature(&mut report, recorded, evidence.observed.as_deref());
        report.push('\n');
    }
    let _ = writeln!(
        report,
        "Loaded signature candidates: {}",
        evidence.candidates.len()
    );
    for candidate in &evidence.candidates {
        signature(
            &mut report,
            &candidate.signature,
            evidence.observed.as_deref(),
        );
        let _ = writeln!(
            report,
            "  Source: {} / {}\n",
            candidate.container, candidate.source
        );
    }
    if evidence.truncated {
        report.push_str("The evidence limit was reached; these results are incomplete.\n");
    }
    report.push_str("Constraint support covers calls and neighboring functions. Referenced data and unique Rust source identity remain unverified.\n");
    report
}
