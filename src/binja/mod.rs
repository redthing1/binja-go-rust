pub(crate) mod calls;
pub(crate) mod llil;
pub(crate) mod memory;
pub(crate) mod warp;
pub(crate) mod workflow;

use std::ffi::CString;
use std::ptr::NonNull;

use binaryninja::function::Function;
use binaryninjacore_sys::*;

/// An owned core reference acquired without depending on the SDK's private fields.
pub(crate) struct FunctionHandle(NonNull<BNFunction>);

impl FunctionHandle {
    pub fn new(function: &Function) -> Option<Self> {
        let name = CString::new(function.platform().name()).ok()?;
        unsafe {
            let platform = BNGetPlatformByName(name.as_ptr());
            if platform.is_null() {
                return None;
            }
            let view = function.view();
            let handle = BNGetAnalysisFunction(view.handle, platform, function.start());
            BNFreePlatform(platform);
            NonNull::new(handle).map(Self)
        }
    }

    pub fn as_ptr(&self) -> *mut BNFunction {
        self.0.as_ptr()
    }
}

impl Drop for FunctionHandle {
    fn drop(&mut self) {
        unsafe { BNFreeFunction(self.as_ptr()) }
    }
}
