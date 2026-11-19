use std::hint::black_box;

#[repr(C)]
struct Leaf {
    prefix: u64,
    value: u64,
}

#[repr(C)]
struct Inner {
    prefix: u64,
    leaf: *const Leaf,
}

#[repr(C)]
struct Outer {
    prefix: u64,
    inner: *const Inner,
}

// Opaque callees keep LLVM from eliminating the return-alias controls.
#[unsafe(naked)]
unsafe extern "sysv64" fn alias(_: *const Leaf) -> *const Leaf {
    core::arch::naked_asm!("mov rax, rdi", "ret");
}

#[unsafe(naked)]
unsafe extern "sysv64" fn loaded(_: *const Outer) -> *const Inner {
    core::arch::naked_asm!("mov rax, [rdi + 8]", "ret");
}

#[unsafe(naked)]
unsafe extern "sysv64" fn dirty(_: *mut Outer, _: *const Inner) -> *const Inner {
    core::arch::naked_asm!("mov rax, [rdi + 8]", "mov [rdi + 8], rsi", "ret");
}

#[unsafe(naked)]
unsafe extern "sysv64" fn ambiguous(_: *const Leaf, _: *const Leaf, _: usize) -> *const Leaf {
    core::arch::naked_asm!("test rdx, rdx", "cmovne rdi, rsi", "mov rax, rdi", "ret");
}

#[inline(never)]
unsafe extern "sysv64" fn nested(value: *const Outer) -> u64 {
    unsafe { (*(*(*value).inner).leaf).value }
}

#[inline(never)]
unsafe extern "sysv64" fn from_alias(value: *const Leaf) -> u64 {
    unsafe { (*alias(value)).value }
}

#[inline(never)]
unsafe extern "sysv64" fn from_loaded(value: *const Outer) -> u64 {
    unsafe { (*(*loaded(value)).leaf).value }
}

#[inline(never)]
unsafe extern "sysv64" fn from_dirty(value: *mut Outer, replacement: *const Inner) -> u64 {
    unsafe { (*(*dirty(value, replacement)).leaf).value }
}

#[inline(never)]
unsafe extern "sysv64" fn from_ambiguous(a: *const Leaf, b: *const Leaf, flag: usize) -> u64 {
    unsafe { (*ambiguous(a, b, flag)).value }
}

#[inline(never)]
unsafe extern "sysv64" fn root(
    value: *mut Outer,
    leaf: *const Leaf,
    replacement: *const Inner,
    flag: usize,
) -> u64 {
    unsafe {
        nested(value)
            + from_alias(leaf)
            + from_loaded(value)
            + from_dirty(value, replacement)
            + from_ambiguous(leaf, (*replacement).leaf, flag)
    }
}

fn main() {
    let leaf = Leaf {
        prefix: 7,
        value: 11,
    };
    let inner = Inner {
        prefix: 13,
        leaf: &leaf,
    };
    let mut outer = Outer {
        prefix: 17,
        inner: &inner,
    };
    assert_eq!(
        unsafe {
            root(
                black_box(&mut outer),
                black_box(&leaf),
                black_box(&inner),
                black_box(1),
            )
        },
        55
    );
    println!(
        "{{\"root\":{},\"nested\":{},\"from_alias\":{},\"from_loaded\":{},\"from_dirty\":{},\"from_ambiguous\":{},\"alias\":{},\"offsets\":[{},{},{}]}}",
        root as *const () as usize,
        nested as *const () as usize,
        from_alias as *const () as usize,
        from_loaded as *const () as usize,
        from_dirty as *const () as usize,
        from_ambiguous as *const () as usize,
        alias as *const () as usize,
        std::mem::offset_of!(Outer, inner),
        std::mem::offset_of!(Inner, leaf),
        std::mem::offset_of!(Leaf, value),
    );
}
