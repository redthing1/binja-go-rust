//! Optional access to the bundled WARP plugin's public C API.

use std::collections::BTreeMap;
use std::ffi::{c_char, c_void};
use std::sync::OnceLock;

use binaryninja::function::Function;
use binaryninja::rc::Ref;
use binaryninja::settings::Settings;
use binaryninja::string::BnString;
use binaryninja::types::Type;
use binaryninjacore_sys::*;
use libloading::Library;

use super::FunctionHandle;

type Handle = *mut c_void;
type Free = unsafe extern "C" fn(Handle);
type FreeList<T> = unsafe extern "C" fn(*mut T, usize);

#[repr(C)]
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Guid([u8; 16]);

impl std::fmt::Display for Guid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, byte) in self.0.iter().enumerate() {
            if matches!(index, 4 | 6 | 8 | 10) {
                write!(f, "-")?;
            }
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

#[repr(C)]
struct RawConstraint {
    guid: Guid,
    offset: i64,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Constraint {
    pub guid: String,
    pub offset: Option<i64>,
}

pub(crate) struct Signature {
    pub guid: String,
    pub name: String,
    pub ty: Option<Ref<Type>>,
    pub constraints: Vec<Constraint>,
}

pub(crate) struct Candidate {
    pub container: String,
    pub source: String,
    pub signature: Signature,
}

pub(crate) struct Evidence {
    pub guid: String,
    pub observed: Option<Vec<Constraint>>,
    pub recorded: Option<Signature>,
    pub candidates: Vec<Candidate>,
    pub truncated: bool,
}

struct Owned {
    pointer: Handle,
    free: Free,
}
impl Drop for Owned {
    fn drop(&mut self) {
        unsafe { (self.free)(self.pointer) }
    }
}

struct List<T> {
    pointer: *mut T,
    count: usize,
    free: FreeList<T>,
}
impl<T> List<T> {
    unsafe fn read(get: impl FnOnce(*mut usize) -> *mut T, free: FreeList<T>) -> Self {
        let mut count = 0;
        let pointer = get(&mut count);
        Self {
            pointer,
            count,
            free,
        }
    }
    fn items(&self) -> &[T] {
        if self.pointer.is_null() || self.count == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.pointer, self.count) }
        }
    }
}
impl<T> Drop for List<T> {
    fn drop(&mut self) {
        if !self.pointer.is_null() {
            unsafe { (self.free)(self.pointer, self.count) }
        }
    }
}

struct Api {
    _library: Library,
    guid: unsafe extern "C" fn(*mut BNFunction, *mut Guid) -> bool,
    matched: unsafe extern "C" fn(*mut BNFunction) -> Handle,
    function: unsafe extern "C" fn(*mut BNFunction) -> Handle,
    target: unsafe extern "C" fn(*mut BNPlatform) -> Handle,
    containers: unsafe extern "C" fn(*mut usize) -> *mut Handle,
    container_name: unsafe extern "C" fn(Handle) -> *mut c_char,
    sources: unsafe extern "C" fn(Handle, Handle, *const Guid, *mut usize) -> *mut Guid,
    functions:
        unsafe extern "C" fn(Handle, Handle, *const Guid, *const Guid, *mut usize) -> *mut Handle,
    name: unsafe extern "C" fn(Handle) -> *mut c_char,
    signature_guid: unsafe extern "C" fn(Handle) -> Guid,
    ty: unsafe extern "C" fn(Handle) -> Handle,
    analysis_type: unsafe extern "C" fn(*mut BNArchitecture, Handle) -> *mut BNType,
    constraints: unsafe extern "C" fn(Handle, *mut usize) -> *mut RawConstraint,
    free_target: Free,
    free_function: Free,
    free_type: Free,
    free_containers: FreeList<Handle>,
    free_functions: FreeList<Handle>,
    free_guids: FreeList<Guid>,
    free_constraints: FreeList<RawConstraint>,
}

static API: OnceLock<Option<Api>> = OnceLock::new();

impl Api {
    fn load() -> Option<Self> {
        let settings = Settings::global();
        if !settings.contains("corePlugins.warp") || !settings.get_bool("corePlugins.warp") {
            return None;
        }
        let filename = if cfg!(target_os = "windows") {
            "warp_ninja.dll"
        } else if cfg!(target_os = "macos") {
            "libwarp_ninja.dylib"
        } else {
            "libwarp_ninja.so"
        };
        let path = binaryninja::bundled_plugin_directory().ok()?.join(filename);
        // Only the installed first-party module is loaded; missing symbols disable this adapter.
        unsafe {
            let library = Library::new(path).ok()?;
            Some(Self {
                guid: *library.get(b"BNWARPGetAnalysisFunctionGUID\0").ok()?,
                matched: *library.get(b"BNWARPGetMatchedFunction\0").ok()?,
                function: *library.get(b"BNWARPGetFunction\0").ok()?,
                target: *library.get(b"BNWARPGetTarget\0").ok()?,
                containers: *library.get(b"BNWARPGetContainers\0").ok()?,
                container_name: *library.get(b"BNWARPContainerGetName\0").ok()?,
                sources: *library
                    .get(b"BNWARPContainerGetSourcesWithFunctionGUID\0")
                    .ok()?,
                functions: *library.get(b"BNWARPContainerGetFunctionsWithGUID\0").ok()?,
                name: *library.get(b"BNWARPFunctionGetSymbolName\0").ok()?,
                signature_guid: *library.get(b"BNWARPFunctionGetGUID\0").ok()?,
                ty: *library.get(b"BNWARPFunctionGetType\0").ok()?,
                analysis_type: *library.get(b"BNWARPTypeGetAnalysisType\0").ok()?,
                constraints: *library.get(b"BNWARPFunctionGetConstraints\0").ok()?,
                free_target: *library.get(b"BNWARPFreeTargetReference\0").ok()?,
                free_function: *library.get(b"BNWARPFreeFunctionReference\0").ok()?,
                free_type: *library.get(b"BNWARPFreeTypeReference\0").ok()?,
                free_containers: *library.get(b"BNWARPFreeContainerList\0").ok()?,
                free_functions: *library.get(b"BNWARPFreeFunctionList\0").ok()?,
                free_guids: *library.get(b"BNWARPFreeUUIDList\0").ok()?,
                free_constraints: *library.get(b"BNWARPFreeConstraintList\0").ok()?,
                _library: library,
            })
        }
    }

    unsafe fn signature(
        &self,
        pointer: Handle,
        arch: *mut BNArchitecture,
        truncated: &mut bool,
    ) -> Signature {
        let raw_type = Owned {
            pointer: unsafe { (self.ty)(pointer) },
            free: self.free_type,
        };
        let ty = if raw_type.pointer.is_null() {
            None
        } else {
            let handle = unsafe { (self.analysis_type)(arch, raw_type.pointer) };
            (!handle.is_null()).then(|| unsafe { Type::ref_from_raw(handle) })
        };
        Signature {
            guid: unsafe { (self.signature_guid)(pointer) }.to_string(),
            name: unsafe { string((self.name)(pointer)) },
            ty,
            constraints: unsafe { self.constraints(pointer, truncated) },
        }
    }

    unsafe fn constraints(&self, pointer: Handle, truncated: &mut bool) -> Vec<Constraint> {
        let constraints = unsafe {
            List::read(
                |count| (self.constraints)(pointer, count),
                self.free_constraints,
            )
        };
        *truncated |= constraints.items().len() > 4096;
        constraints
            .items()
            .iter()
            .take(4096)
            .map(|c| Constraint {
                guid: c.guid.to_string(),
                offset: (c.offset != i64::MAX).then_some(c.offset),
            })
            .collect()
    }

    fn observed(&self, function: &Function, truncated: &mut bool) -> Option<Vec<Constraint>> {
        let view = function.view();
        let mut related = BTreeMap::new();
        let mut insert = |function: Ref<Function>| {
            related.insert((function.platform().name(), function.start()), function);
            if related.len() > 64 {
                *truncated = true;
                None
            } else {
                Some(())
            }
        };
        insert(function.to_owned())?;
        let sites = function.call_sites();
        let mut work = sites.len();
        for site in &sites {
            let references = view.code_refs_from_addr(site.address, Some(function));
            work = work.checked_add(references.len())?;
            if work > 4096 {
                *truncated = true;
                return None;
            }
            for address in references {
                if let Some(callee) = view.function_at(&function.platform(), address) {
                    insert(callee)?;
                }
            }
        }
        let (mut before, mut after) = (function.start(), function.start());
        for _ in 0..2 {
            before = view.function_start_before(before);
            after = view.function_start_after(after);
            for address in [before, after] {
                for neighbor in &view.functions_at(address) {
                    insert(neighbor.to_owned())?;
                }
            }
        }
        // The bundled collector reads cached GUIDs for callees and two neighbors
        // on either side. Refresh exactly that neighborhood before collecting.
        for related in related.values() {
            if related.is_update_needed() {
                return None;
            }
            let handle = FunctionHandle::new(related)?;
            related.remove_metadata("warp_function_guid");
            let mut guid = Guid::default();
            if !unsafe { (self.guid)(handle.as_ptr(), &mut guid) } {
                return None;
            }
        }
        let handle = FunctionHandle::new(function)?;
        let current = Owned {
            pointer: unsafe { (self.function)(handle.as_ptr()) },
            free: self.free_function,
        };
        if current.pointer.is_null() {
            return None;
        }
        let constraints = unsafe { self.constraints(current.pointer, truncated) };
        related
            .values()
            .all(|function| !function.is_update_needed())
            .then_some(constraints)
    }
}

unsafe fn string(pointer: *mut c_char) -> String {
    if pointer.is_null() {
        String::new()
    } else {
        unsafe { BnString::into_string(pointer) }
    }
}

pub(crate) fn available() -> bool {
    API.get_or_init(Api::load).is_some()
}

/// Query loaded candidates and persisted matches without running WARP's matcher or fetcher.
pub(crate) fn inspect(function: &Function) -> Option<Evidence> {
    let api = API.get_or_init(Api::load).as_ref()?;
    if function.is_update_needed() {
        return None;
    }
    let handle = FunctionHandle::new(function)?;
    unsafe {
        // WARP documents removing this cache entry before regenerating a GUID.
        // Do not discard its recorded match: compare it with the new GUID instead.
        function.remove_metadata("warp_function_guid");
        let mut guid = Guid::default();
        if !(api.guid)(handle.as_ptr(), &mut guid) {
            return None;
        }
        let platform = BNGetFunctionPlatform(handle.as_ptr());
        let target = Owned {
            pointer: (api.target)(platform),
            free: api.free_target,
        };
        BNFreePlatform(platform);
        if target.pointer.is_null() {
            return None;
        }
        let arch = BNGetFunctionArchitecture(handle.as_ptr());
        let mut truncated = false;
        let observed = api.observed(function, &mut truncated);
        let matched = Owned {
            pointer: (api.matched)(handle.as_ptr()),
            free: api.free_function,
        };
        let recorded = (!matched.pointer.is_null())
            .then(|| api.signature(matched.pointer, arch, &mut truncated));
        let containers = List::read(|count| (api.containers)(count), api.free_containers);
        let mut candidates = Vec::new();
        let mut sources_seen = 0;
        'containers: for &container in containers.items() {
            let name = string((api.container_name)(container));
            let sources = List::read(
                |count| (api.sources)(container, target.pointer, &guid, count),
                api.free_guids,
            );
            for source in sources.items() {
                sources_seen += 1;
                if sources_seen > 4096 {
                    truncated = true;
                    break 'containers;
                }
                let functions = List::read(
                    |count| (api.functions)(container, target.pointer, source, &guid, count),
                    api.free_functions,
                );
                for &pointer in functions.items() {
                    if candidates.len() == 256 {
                        truncated = true;
                        break 'containers;
                    }
                    candidates.push(Candidate {
                        container: name.clone(),
                        source: source.to_string(),
                        signature: api.signature(pointer, arch, &mut truncated),
                    });
                }
            }
        }
        candidates.sort_by(|a, b| {
            (&a.container, &a.source, &a.signature.name).cmp(&(
                &b.container,
                &b.source,
                &b.signature.name,
            ))
        });
        if function.is_update_needed() {
            return None;
        }
        Some(Evidence {
            guid: guid.to_string(),
            observed,
            recorded,
            candidates,
            truncated,
        })
    }
}
