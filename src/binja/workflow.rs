use std::ffi::{CStr, CString, c_void};

use binaryninja::binary_view::BinaryView;
use binaryninja::function::Function;
use binaryninja::low_level_il::LowLevelILMutableFunction;
use binaryninja::rc::Ref;
use binaryninja::variable::RegisterValue;
use binaryninja::workflow::activity::{AsConfig, Config};
use binaryninjacore_sys::*;

pub(crate) type EligibilityCallback =
    unsafe extern "C" fn(*mut c_void, *mut BNActivity, *mut BNAnalysisContext) -> bool;

/// An owned view reference scoped to a raw workflow callback.
pub(crate) unsafe fn view(context: *mut BNAnalysisContext) -> Option<Ref<BinaryView>> {
    if context.is_null() {
        return None;
    }
    let raw = unsafe { BNAnalysisContextGetBinaryView(context) };
    if raw.is_null() {
        return None;
    }
    let view = unsafe { BinaryView::from_raw(raw) }.to_owned();
    unsafe { BNFreeBinaryView(raw) };
    Some(view)
}

/// Context-local queries avoid reading the function's previously committed IL.
pub(crate) struct FunctionContext {
    pub function: Ref<Function>,
    pub il: Ref<LowLevelILMutableFunction>,
    handle: *mut BNLowLevelILFunction,
}

impl FunctionContext {
    /// Use only while the core is executing this analysis callback.
    pub unsafe fn from_raw(context: *mut BNAnalysisContext) -> Option<Self> {
        if context.is_null() {
            return None;
        }
        let function = unsafe { BNAnalysisContextGetFunction(context) };
        if function.is_null() {
            return None;
        }
        let function = unsafe { Function::ref_from_raw(function) };
        let handle = unsafe { BNAnalysisContextGetLowLevelILFunction(context) };
        if handle.is_null() {
            return None;
        }
        let il = unsafe { LowLevelILMutableFunction::from_raw(handle) }.to_owned();
        unsafe { BNFreeLowLevelILFunction(handle) };
        Some(Self {
            function,
            il,
            handle,
        })
    }

    pub fn register_at(&self, index: usize, register: u32) -> RegisterValue {
        unsafe { BNGetLowLevelILRegisterValueAtInstruction(self.handle, register, index) }.into()
    }
}

/// Register a stateless callback when an API omitted by the Rust SDK needs its raw context.
pub(crate) fn after(
    config: Config,
    workflow: &CStr,
    anchor: &CStr,
    action: unsafe extern "C" fn(*mut c_void, *mut BNAnalysisContext),
    eligibility: Option<EligibilityCallback>,
) -> Result<(), ()> {
    insert(config, workflow, anchor, action, eligibility, true)
}

pub(crate) fn before(
    config: Config,
    workflow: &CStr,
    anchor: &CStr,
    action: unsafe extern "C" fn(*mut c_void, *mut BNAnalysisContext),
) -> Result<(), ()> {
    insert(config, workflow, anchor, action, None, false)
}

fn insert(
    config: Config,
    workflow: &CStr,
    anchor: &CStr,
    action: unsafe extern "C" fn(*mut c_void, *mut BNAnalysisContext),
    eligibility: Option<EligibilityCallback>,
    after: bool,
) -> Result<(), ()> {
    let name = CString::new(config.name.as_str()).map_err(|_| ())?;
    let config = config.as_config();
    unsafe {
        let source = BNWorkflowGet(workflow.as_ptr());
        if source.is_null() {
            return Err(());
        }
        let target = BNWorkflowClone(source, workflow.as_ptr(), c"".as_ptr());
        BNFreeWorkflow(source);
        if target.is_null() {
            return Err(());
        }
        let activity = if eligibility.is_some() {
            BNCreateActivityWithEligibility(
                config.as_ptr(),
                std::ptr::null_mut(),
                Some(action),
                eligibility,
            )
        } else {
            BNCreateActivity(config.as_ptr(), std::ptr::null_mut(), Some(action))
        };
        let mut success = false;
        if !activity.is_null() {
            let registered = BNWorkflowRegisterActivity(target, activity, std::ptr::null_mut(), 0);
            if !registered.is_null() {
                BNFreeActivity(registered);
                let mut activities = [name.as_ptr()];
                let inserted = if after {
                    BNWorkflowInsertAfter(target, anchor.as_ptr(), activities.as_mut_ptr(), 1)
                } else {
                    BNWorkflowInsert(target, anchor.as_ptr(), activities.as_mut_ptr(), 1)
                };
                success = inserted && BNRegisterWorkflow(target, c"".as_ptr());
            }
            BNFreeActivity(activity);
        }
        BNFreeWorkflow(target);
        success.then_some(()).ok_or(())
    }
}
