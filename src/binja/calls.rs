use binaryninja::function::Function;
use binaryninjacore_sys::*;

use super::FunctionHandle;

/// The SDK's automatic setter accepts a type, but omits the nullable reset.
pub(crate) fn clear(function: &Function, address: u64) {
    let Some(handle) = FunctionHandle::new(function) else {
        return;
    };
    unsafe {
        BNSetAutoCallTypeAdjustment(
            handle.as_ptr(),
            BNGetFunctionArchitecture(handle.as_ptr()),
            address,
            std::ptr::null_mut(),
        );
    }
}
