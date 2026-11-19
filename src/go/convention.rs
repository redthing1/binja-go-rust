use binaryninja::architecture::CoreArchitecture;
use binaryninja::calling_convention::{ConventionBuilder, CoreCallingConvention};
use binaryninja::rc::Ref;
use std::sync::OnceLock;

pub(crate) const INTEGERS: [&str; 9] =
    ["rax", "rbx", "rcx", "rdi", "rsi", "r8", "r9", "r10", "r11"];
pub(crate) const FLOATS: [&str; 15] = [
    "zmm0", "zmm1", "zmm2", "zmm3", "zmm4", "zmm5", "zmm6", "zmm7", "zmm8", "zmm9", "zmm10",
    "zmm11", "zmm12", "zmm13", "zmm14",
];
static AMD64: OnceLock<Option<Ref<CoreCallingConvention>>> = OnceLock::new();

pub(crate) fn amd64() -> Option<&'static Ref<CoreCallingConvention>> {
    AMD64
        .get_or_init(|| {
            let arch = CoreArchitecture::by_name("x86_64")?;
            let mut volatile = INTEGERS.to_vec();
            volatile.extend(["rdx", "r12", "r13", "r15"]);
            volatile.extend(FLOATS);
            volatile.push("zmm15");
            Some(
                ConventionBuilder::new(&arch)
                    .int_arg_registers(&INTEGERS)
                    .float_arg_registers(&FLOATS)
                    .caller_saved_registers(&volatile)
                    .callee_saved_registers(&["rbp", "r14"])
                    .return_int_reg("rax")
                    .return_hi_int_reg("rbx")
                    .return_float_reg("zmm0")
                    .is_eligible_for_heuristics(false)
                    .register("go-rust.go.amd64"),
            )
        })
        .as_ref()
}
