use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::rc::Rc;

use binaryninja::architecture::{ArchitectureExt, Register};
use binaryninja::binary_view::{BinaryView, MetadataStoreFlags};
use binaryninja::function::Function;
use binaryninja::low_level_il::instruction::{
    InstructionHandler, LowLevelILInstructionKind as Instruction,
};
use binaryninja::rc::Ref;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::contexts::Model;
use super::values::{Location, Reader, Site, Value, Watches};
use crate::binja::llil::Ssa;

const RUNTIME: &str = "go-rust.go.runtime-code.v1";
const RESTARTS: &str = "go-rust.go.restart-code.v1";

pub(super) fn runtime_code(name: &str, file: Option<&str>) -> bool {
    if ["runtime.", "runtime/", "internal/", "reflect."]
        .iter()
        .any(|prefix| name.starts_with(prefix))
    {
        return true;
    }
    // Local assembly helpers retain their owning source package.
    !name.contains('.')
        && !name.contains('/')
        && file.is_some_and(|file| {
            let file = file.replace('\\', "/");
            file.starts_with("runtime/")
                || file.contains("/runtime/")
                || file.starts_with("internal/")
                || file.contains("/internal/")
        })
}

#[derive(Default, Deserialize, Serialize)]
pub(super) struct Runtime {
    pub ranges: Vec<Range<u64>>,
    pub digest: String,
    helpers: Vec<u64>,
}

pub(super) fn digest(view: &BinaryView, ranges: &[Range<u64>]) -> Option<String> {
    let mut hash = Sha256::new();
    let base = ranges.first()?.start;
    let mut total = 0usize;
    for range in ranges {
        let length = usize::try_from(range.end.checked_sub(range.start)?).ok()?;
        total = total.checked_add(length)?;
        if total > 16_777_216 {
            return None;
        }
        let bytes = view.read_vec(range.start, length);
        if bytes.len() != length {
            return None;
        }
        hash.update(range.start.checked_sub(base)?.to_le_bytes());
        hash.update(range.end.checked_sub(base)?.to_le_bytes());
        hash.update(bytes);
    }
    Some(format!("{:x}", hash.finalize()))
}

impl Runtime {
    pub fn publish(
        view: &BinaryView,
        ranges: Vec<Range<u64>>,
        functions: &BTreeMap<u64, String>,
    ) -> Self {
        let baseline = view
            .get_metadata::<String>(RUNTIME)
            .or_else(|| {
                let baseline = digest(view, &ranges)?;
                view.store_metadata(RUNTIME, baseline.clone(), MetadataStoreFlags::PERSISTENT);
                Some(baseline)
            })
            .unwrap_or_default();
        Self {
            helpers: functions
                .iter()
                .filter_map(|(&address, name)| {
                    (boxing(name).is_some()
                        || barrier(name).is_some()
                        || matches!(
                            name.as_str(),
                            "runtime.newobject"
                                | "reflect.(*rtype).String"
                                | "runtime.morestack"
                                | "runtime.morestack_noctxt"
                                | "runtime.panicdottypeI"
                                | "runtime.panicwrap"
                        ))
                    .then_some(address)
                })
                .collect(),
            ranges,
            digest: baseline,
        }
    }

    pub fn current(&self, view: &BinaryView) -> bool {
        let Some(platform) = view.default_platform() else {
            return false;
        };
        !self.ranges.is_empty()
            && self.helpers.iter().all(|&address| {
                self.ranges.iter().any(|range| range.contains(&address))
                    && view
                        .function_at(&platform, address)
                        .is_some_and(|function| function.stack_adjustment().contents == 0)
            })
            && digest(view, &self.ranges).as_ref() == Some(&self.digest)
    }
}

struct Source {
    function: Ref<Function>,
    ssa: Ssa,
    bytes: Vec<u8>,
}

#[derive(Deserialize, Serialize)]
pub(super) struct Evidence {
    function: u64,
    length: usize,
    digest: String,
    calls: BTreeMap<u64, bool>,
}

impl Evidence {
    pub fn current(&self, view: &BinaryView) -> bool {
        let Some(platform) = view.default_platform() else {
            return false;
        };
        let Some(function) = view.function_at(&platform, self.function) else {
            return false;
        };
        !function.is_update_needed()
            && !Ssa::has_user_values(&function)
            && function.stack_adjustment().contents == 0
            && format!(
                "{:x}",
                Sha256::digest(view.read_vec(self.function, self.length))
            ) == self.digest
            && self
                .calls
                .iter()
                .all(|(&address, &clean)| clean == clean_call(&function, address))
    }
}

fn clean_call(function: &Function, address: u64) -> bool {
    function.call_type_adjustment(address, None).is_none()
        && function.call_stack_adjustment(address, None).contents == 0
}

type Binding = Option<(Location, u64)>;
type ReturnKey = (u64, Binding, u32);
type FrameKey = (u64, Binding, i64, usize, bool);

#[derive(Default)]
struct Cache {
    sources: BTreeMap<u64, Rc<Source>>,
    returns: BTreeMap<ReturnKey, Value>,
    frames: BTreeSet<FrameKey>,
    active_returns: BTreeSet<ReturnKey>,
    active_frames: BTreeSet<FrameKey>,
    watched: Watches,
    restarts: BTreeMap<String, String>,
    calls: BTreeMap<u64, BTreeMap<u64, bool>>,
}

/// Go amd64 call effects, independent of global call-site types and values.
/// Queries retain owned SSA snapshots and publish only while all evidence is current.
pub(super) struct Analysis<'a> {
    view: &'a BinaryView,
    model: &'a Model,
    runtime_current: bool,
    cache: RefCell<Cache>,
    remaining: Cell<usize>,
    limited: Cell<bool>,
}

impl<'a> Analysis<'a> {
    pub fn new(view: &'a BinaryView, model: &'a Model) -> Self {
        let restarts = view
            .get_metadata::<String>(RESTARTS)
            .and_then(|value| serde_json::from_str(&value).ok())
            .unwrap_or_default();
        Self {
            view,
            model,
            runtime_current: model.runtime.current(view),
            remaining: Cell::new(1_048_576),
            limited: Cell::new(false),
            cache: RefCell::new(Cache {
                restarts,
                ..Cache::default()
            }),
        }
    }

    pub fn spend(&self) -> bool {
        let Some(remaining) = self.remaining.get().checked_sub(1) else {
            self.limited.set(true);
            return false;
        };
        self.remaining.set(remaining);
        true
    }

    pub fn limited(&self) -> bool {
        self.limited.get()
    }

    fn source(&self, address: u64) -> Option<Rc<Source>> {
        if let Some(source) = self.cache.borrow().sources.get(&address) {
            return Some(source.clone());
        }
        if self.cache.borrow().sources.len() >= 256 {
            self.limited.set(true);
            return None;
        }
        let length = *self.model.lengths.get(&address)?;
        if length == 0 || length > 1_048_576 {
            return None;
        }
        let platform = self.view.default_platform()?;
        let function = self.view.function_at(&platform, address)?;
        if Ssa::has_user_values(&function) || function.stack_adjustment().contents != 0 {
            return None;
        }
        let ssa = Ssa::new(&function)?;
        let bytes = self.view.read_vec(address, length);
        if bytes.len() != length {
            return None;
        }
        let source = Rc::new(Source {
            function,
            ssa,
            bytes,
        });
        self.cache
            .borrow_mut()
            .sources
            .insert(address, source.clone());
        Some(source)
    }

    fn absorb(&self, reader: Reader<'_>) {
        self.cache.borrow_mut().watched.merge(reader.watched);
    }

    pub fn track(&self, function: &Ref<Function>, ssa: &Ssa) -> bool {
        let Some(&length) = self.model.lengths.get(&function.start()) else {
            return false;
        };
        if length == 0 || length > 1_048_576 {
            return false;
        }
        let bytes = self.view.read_vec(function.start(), length);
        if bytes.len() != length {
            return false;
        }
        self.cache
            .borrow_mut()
            .sources
            .entry(function.start())
            .or_insert_with(|| {
                Rc::new(Source {
                    function: function.clone(),
                    ssa: ssa.clone(),
                    bytes,
                })
            });
        true
    }

    pub fn finish(&self, watched: &mut Watches) -> Option<(Vec<Evidence>, bool)> {
        let valid = self.cache.borrow().sources.values().all(|source| {
            source.ssa.current(&source.function)
                && !Ssa::has_user_values(&source.function)
                && self
                    .view
                    .read_vec(source.function.start(), source.bytes.len())
                    == source.bytes
        }) && self.runtime_current == self.model.runtime.current(self.view);
        let mut cache = self.cache.borrow_mut();
        watched.merge(std::mem::take(&mut cache.watched));
        if let Ok(restarts) = serde_json::to_string(&cache.restarts) {
            self.view
                .store_metadata(RESTARTS, restarts, MetadataStoreFlags::PERSISTENT);
        }
        if !valid {
            return None;
        }
        let evidence: Vec<_> = cache
            .sources
            .iter()
            .map(|(&address, source)| Evidence {
                function: address,
                length: source.bytes.len(),
                digest: format!("{:x}", Sha256::digest(&source.bytes)),
                calls: cache.calls.get(&address).cloned().unwrap_or_default(),
            })
            .collect();
        evidence
            .iter()
            .all(|record| record.current(self.view))
            .then_some((evidence, self.runtime_current))
    }

    fn clean(&self, reader: &Reader<'_>, site: Site<'_>) -> bool {
        reader.ssa.il.function().is_some_and(|function| {
            let clean = clean_call(&function, site.address());
            self.cache
                .borrow_mut()
                .calls
                .entry(function.start())
                .or_default()
                .insert(site.address(), clean);
            !Ssa::has_user_values(&function) && clean
        })
    }

    fn target(&self, reader: &mut Reader<'_>, site: Site<'_>) -> Option<u64> {
        if !self.clean(reader, site) {
            return None;
        }
        let op = match site.kind() {
            Instruction::CallSsa(op) | Instruction::TailCallSsa(op) => op,
            _ => return None,
        };
        Some(reader.evaluate(op.target())?.number)
    }

    fn name(&self, target: u64) -> &str {
        self.model
            .functions
            .get(&target)
            .map(String::as_str)
            .unwrap_or("")
    }

    fn binding(&self, reader: &mut Reader<'_>, site: Site<'_>, target: u64) -> Binding {
        let name = self.name(target);
        // Method dictionaries have receiver-dependent entry storage. They remain
        // context roots; return summaries currently accept free generic bodies.
        if !name.contains("[go.shape.") || !name.ends_with(']') {
            return None;
        }
        let register = reader
            .ssa
            .il
            .function()?
            .arch()
            .register_by_name("rax")?
            .id()
            .0;
        let value = reader.argument(site, Location::Register(register))?.number;
        (value % 8 == 0
            && !self.model.types.contains_key(&value)
            && !self.model.itabs.contains_key(&value)
            && reader
                .watched
                .word(self.view, &self.model.code, value, 8)
                .is_some())
        .then_some((Location::Register(register), value))
    }

    fn type_size(&self, reader: &mut Reader<'_>, descriptor: u64) -> Option<u64> {
        let header = self.model.headers.get(&descriptor)?;
        for (index, expected) in header.iter().enumerate() {
            if reader.watched.word(
                self.view,
                &self.model.code,
                descriptor.checked_add(index as u64 * 8)?,
                8,
            )? != *expected
            {
                return None;
            }
        }
        (header[0] > 0 && header[0] <= 1_048_576).then_some(header[0])
    }

    pub fn call_value(
        &self,
        reader: &mut Reader<'_>,
        site: Site<'_>,
        register: u32,
    ) -> Option<Value> {
        let target = self.target(reader, site)?;
        let arch = reader.ssa.il.function()?.arch();
        let name = self.name(target);
        if let Some(count) = barrier(name) {
            if !self.runtime_current {
                return None;
            }
            if register == arch.register_by_name("r11")?.id().0 {
                return Some(Value::region(count * 8));
            }
            return [
                "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r12", "r13", "r14",
                "r15", "rbp",
            ]
            .iter()
            .filter_map(|name| arch.register_by_name(name))
            .any(|reg| reg.id().0 == register)
            .then(|| reader.before(site.index.0, register, 0))
            .flatten();
        }
        if name == "runtime.newobject" || boxing(name).is_some() {
            if !self.runtime_current || register != arch.register_by_name("rax")?.id().0 {
                return None;
            }
            let size = if let Some(size) = boxing(name) {
                size
            } else {
                let descriptor = reader.argument(site, Location::Register(register))?.number;
                self.type_size(reader, descriptor)?
            };
            return Some(Value::region(size));
        }
        if name.is_empty() || name.starts_with("runtime.") || name.starts_with("reflect.") {
            return None;
        }
        let binding = self.binding(reader, site, target);
        let key = (target, binding, register);
        if let Some(value) = self.cache.borrow().returns.get(&key) {
            return Some(*value);
        }
        {
            let mut cache = self.cache.borrow_mut();
            if cache.active_returns.len() >= 16 || !cache.active_returns.insert(key) {
                return None;
            }
        }
        let result = (|| {
            let source = self.source(target)?;
            let mut reader =
                Reader::new(self.view, &source.ssa, binding, &self.model.code).with_effects(self);
            let result = reader.returned(register);
            self.absorb(reader);
            result
        })();
        let mut cache = self.cache.borrow_mut();
        cache.active_returns.remove(&key);
        if let Some(value) = result {
            cache.returns.insert(key, value);
        }
        result
    }

    pub fn preserves(
        &self,
        reader: &mut Reader<'_>,
        site: Site<'_>,
        offset: i64,
        width: usize,
        nonstack: bool,
    ) -> bool {
        let Some(target) = self.target(reader, site) else {
            return false;
        };
        let Some((entry, _)) = reader.ssa.call_stack(site.index.0) else {
            return false;
        };
        let Some(relative) = offset.checked_sub(entry) else {
            return false;
        };
        let name = self.name(target);
        if name == "runtime.newobject"
            || boxing(name).is_some()
            || name == "reflect.(*rtype).String"
        {
            if !self.runtime_current || relative < 16 {
                return false;
            }
            if name == "runtime.newobject" {
                let Some(register) = reader
                    .ssa
                    .il
                    .function()
                    .and_then(|function| function.arch().register_by_name("rax"))
                else {
                    return false;
                };
                let Some(descriptor) = reader.argument(site, Location::Register(register.id().0))
                else {
                    return false;
                };
                return self.type_size(reader, descriptor.number).is_some();
            }
            return true;
        }
        if barrier(name).is_some() {
            return self.runtime_current && relative >= 8;
        }
        if relative < 8
            || name.is_empty()
            || name.starts_with("runtime.")
            || name.starts_with("reflect.")
        {
            return false;
        }
        let binding = self.binding(reader, site, target);
        let key = (target, binding, relative, width, nonstack);
        if self.cache.borrow().frames.contains(&key) {
            return true;
        }
        {
            let mut cache = self.cache.borrow_mut();
            if cache.active_frames.len() >= 16 || !cache.active_frames.insert(key) {
                return false;
            }
        }
        let valid = self.source(target).is_some_and(|source| {
            let mut reader =
                Reader::new(self.view, &source.ssa, binding, &self.model.code).with_effects(self);
            let valid = reader.preserves_frame(relative, width, nonstack);
            self.absorb(reader);
            valid
        });
        let mut cache = self.cache.borrow_mut();
        cache.active_frames.remove(&key);
        if valid {
            cache.frames.insert(key);
        }
        valid
    }

    pub fn exit_call(&self, reader: &mut Reader<'_>, site: Site<'_>) -> bool {
        self.runtime_current
            && self.target(reader, site).is_some_and(|target| {
                matches!(
                    self.name(target),
                    "runtime.morestack"
                        | "runtime.morestack_noctxt"
                        | "runtime.panicdottypeI"
                        | "runtime.panicwrap"
                )
            })
    }

    pub fn exit(&self, reader: &mut Reader<'_>, site: Site<'_>) -> bool {
        let Some(previous) = site
            .index
            .0
            .checked_sub(1)
            .and_then(|index| reader.ssa.il.instruction_from_index(index.into()))
        else {
            return false;
        };
        if !self.exit_call(reader, previous) {
            return false;
        }
        let Some(target) = self.target(reader, previous) else {
            return false;
        };
        if matches!(
            self.name(target),
            "runtime.panicdottypeI" | "runtime.panicwrap"
        ) {
            return true;
        }
        let Some(function) = reader.ssa.il.function() else {
            return false;
        };
        let Some(length) = self.model.lengths.get(&function.start()) else {
            return false;
        };
        let Some(block) = site.basic_block() else {
            return false;
        };
        let Some(first) = reader.ssa.il.instruction_from_index(block.start_index()) else {
            return false;
        };
        let Some(end) = function.start().checked_add(*length as u64) else {
            return false;
        };
        let ranges = [first.address()..end];
        let Some(current) = digest(self.view, &ranges) else {
            return false;
        };
        let key = format!("{:x}:{end:x}", first.address());
        let mut cache = self.cache.borrow_mut();
        let baseline = cache.restarts.entry(key).or_insert_with(|| current.clone());
        *baseline == current
    }
}

fn barrier(name: &str) -> Option<u64> {
    let suffix = name.strip_prefix("runtime.gcWriteBarrier")?;
    if suffix.len() != 1 {
        return None;
    }
    let count: u64 = suffix.parse().ok()?;
    (1..=8).contains(&count).then_some(count)
}

fn boxing(name: &str) -> Option<u64> {
    match name {
        "runtime.convT32" => Some(4),
        "runtime.convT64" => Some(8),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::runtime_code;

    #[test]
    fn runtime_dependencies_include_local_assembly_and_preserve_user_packages() {
        for (name, file) in [
            ("runtime.gcWriteBarrier1", None),
            ("internal/chacha8rand.block", None),
            ("gcWriteBarrier", Some("runtime/asm_amd64.s")),
            ("cmpbody", Some("internal/bytealg/compare_amd64.s")),
            (
                "gosave_systemstack_switch",
                Some(r"src\runtime\asm_amd64.s"),
            ),
        ] {
            assert!(runtime_code(name, file), "{name}");
        }
        assert!(!runtime_code("main.work", Some("app/runtime/work.go")));
        assert!(!runtime_code(
            "privateHelper",
            Some("app/kernel/asm_amd64.s")
        ));
    }
}
