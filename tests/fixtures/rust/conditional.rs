use std::hint::black_box;

#[repr(C)]
pub struct Leaf {
    pub prefix: u64,
    pub value: u64,
}

#[repr(C, u8)]
pub enum Choice {
    Empty,
    Wide(u64),
    Narrow(u32),
    Pointer(*const Leaf),
}

#[repr(C)]
pub union Payload {
    pub wide: u64,
    pub narrow: u32,
    pub pointer: *const Leaf,
}

#[repr(C)]
pub struct Raw {
    pub tag: u8,
    pub payload: Payload,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_choice(value: *const Choice) -> u64 {
    match unsafe { &*value } {
        Choice::Empty => 0,
        Choice::Wide(x) => x.wrapping_add(1),
        Choice::Narrow(x) => u64::from(*x).wrapping_add(2),
        Choice::Pointer(x) => unsafe { (**x).value }.wrapping_add(3),
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_raw(value: *const Raw) -> u64 {
    match unsafe { (*value).tag } {
        0 => 0,
        1 => unsafe { (*value).payload.wide }.wrapping_add(1),
        2 => u64::from(unsafe { (*value).payload.narrow }).wrapping_add(2),
        3 => unsafe { (*(*value).payload.pointer).value }.wrapping_add(3),
        _ => 17,
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_word_tag(value: *const Raw) -> u64 {
    if unsafe { (*value).tag } == 3 {
        unsafe { (*(*value).payload.pointer).value }
    } else {
        unsafe { (*value).payload.wide }.wrapping_add(1)
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_option(value: *const Option<&Leaf>) -> u64 {
    unsafe { &*value }.map_or(0, |leaf| leaf.value)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_nullable(value: *const Leaf) -> u64 {
    if value.is_null() {
        0
    } else {
        unsafe { (*value).value }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_dirty(value: *mut Raw) -> u64 {
    let tag = unsafe { (*value).tag };
    unsafe { (*value).tag = 0 };
    if tag == 1 {
        unsafe { (*value).payload.wide }
    } else {
        0
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn conditional_root(
    raw: *mut Raw,
    choice: *const Choice,
    option: *const Option<&Leaf>,
    leaf: *const Leaf,
) -> u64 {
    unsafe {
        read_raw(raw)
            + read_choice(choice)
            + read_option(option)
            + read_nullable(leaf)
            + read_dirty(raw)
            + read_word_tag(raw)
    }
}

fn main() {
    let leaf = Leaf {
        prefix: 7,
        value: 11,
    };
    let choice = Choice::Pointer(&leaf);
    let mut raw = Raw {
        tag: 2,
        payload: Payload { wide: 23 },
    };
    let option = Some(&leaf);
    assert_eq!(
        unsafe {
            conditional_root(
                black_box(&mut raw),
                black_box(&choice),
                black_box(&option),
                black_box(&leaf),
            )
        },
        85
    );
    println!(
        "{{\"root\":{},\"read_choice\":{},\"read_raw\":{},\"read_option\":{},\"read_nullable\":{},\"read_dirty\":{},\"read_word_tag\":{},\"payload_offset\":{},\"leaf_value_offset\":{},\"size\":{}}}",
        conditional_root as *const () as usize,
        read_choice as *const () as usize,
        read_raw as *const () as usize,
        read_option as *const () as usize,
        read_nullable as *const () as usize,
        read_dirty as *const () as usize,
        read_word_tag as *const () as usize,
        std::mem::offset_of!(Raw, payload),
        std::mem::offset_of!(Leaf, value),
        std::mem::size_of::<Choice>()
    );
}
