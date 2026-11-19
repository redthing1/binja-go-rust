use std::{hint::black_box, num::NonZeroU8};

#[repr(C)]
pub struct Leaf {
    prefix: u64,
    value: u64,
}
#[repr(C)]
pub union Payload {
    pointer: *const Leaf,
    word: u64,
}
#[repr(C)]
pub struct Packet {
    tag: u8,
    payload: Payload,
}
#[repr(C)]
pub struct Niche {
    tag: Option<NonZeroU8>,
    payload: Payload,
}
#[repr(C, u8)]
pub enum Choice {
    First(*const Leaf),
    Second(*const Leaf),
    Third(*const Leaf),
    Word(u64),
    Empty,
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn read_choice(value: *const Choice) -> u64 {
    match unsafe { &*value } {
        Choice::First(p) | Choice::Second(p) | Choice::Third(p) => unsafe { (**p).value + 1 },
        Choice::Word(x) => x.wrapping_add(13),
        Choice::Empty => 0,
    }
}
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn read_unsigned(value: *const Packet) -> u64 {
    if unsafe { (*value).tag } < 3 {
        unsafe { (*(*value).payload.pointer).value + 2 }
    } else {
        unsafe { (*value).payload.word }.wrapping_add(17)
    }
}
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn read_signed(value: *const Packet) -> u64 {
    if (unsafe { (*value).tag } as i8) < -126 {
        unsafe { (*(*value).payload.pointer).value + 3 }
    } else {
        unsafe { (*value).payload.word }.wrapping_add(19)
    }
}
#[no_mangle]
#[inline(never)]
pub fn high_tag(tag: u8) -> bool {
    tag >= 253
}
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn read_helper(value: *const Packet) -> u64 {
    if high_tag(unsafe { (*value).tag }) {
        unsafe { (*(*value).payload.pointer).value + 4 }
    } else {
        unsafe { (*value).payload.word }.wrapping_add(23)
    }
}
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn read_niche(value: *const Niche) -> u64 {
    if unsafe { (*value).tag }.is_some_and(|tag| tag.get() >= 253) {
        unsafe { (*(*value).payload.pointer).value + 5 }
    } else {
        unsafe { (*value).payload.word }.wrapping_add(29)
    }
}
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn read_dirty(value: *mut Packet) -> u64 {
    let old = unsafe { (*value).tag };
    unsafe { (*value).tag = 4 };
    if old < 3 {
        unsafe { (*(*value).payload.pointer).value + 6 }
    } else {
        unsafe { (*value).payload.word }.wrapping_add(31)
    }
}
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn range_root(
    a: *const Choice,
    b: *const Packet,
    c: *const Packet,
    d: *const Packet,
    e: *const Niche,
) -> u64 {
    unsafe { read_choice(a) + read_unsigned(b) + read_signed(c) + read_helper(d) + read_niche(e) }
}
fn main() {
    let leaf = Leaf {
        prefix: 7,
        value: 11,
    };
    let choice = Choice::Second(&leaf);
    let packet = |tag| Packet {
        tag,
        payload: Payload { pointer: &leaf },
    };
    let (a, b, c) = (packet(1), packet(128), packet(254));
    let niche = Niche {
        tag: NonZeroU8::new(254),
        payload: Payload { pointer: &leaf },
    };
    assert_eq!(
        unsafe {
            range_root(
                black_box(&choice),
                black_box(&a),
                black_box(&b),
                black_box(&c),
                black_box(&niche),
            )
        },
        70
    );
    assert_eq!(
        unsafe {
            read_unsigned(&Packet {
                tag: 4,
                payload: Payload { word: 7 },
            })
        },
        24
    );
    assert_eq!(
        unsafe {
            read_niche(&Niche {
                tag: None,
                payload: Payload { word: 7 },
            })
        },
        36
    );
    let mut dirty = packet(1);
    assert_eq!(unsafe { read_dirty(black_box(&mut dirty)) }, 17);
    assert_eq!(dirty.tag, 4);
    println!("{{\"root\":{},\"read_choice\":{},\"read_unsigned\":{},\"read_signed\":{},\"read_helper\":{},\"read_niche\":{},\"read_dirty\":{},\"high_tag\":{}}}",
        range_root as *const () as usize, read_choice as *const () as usize,
        read_unsigned as *const () as usize, read_signed as *const () as usize,
        read_helper as *const () as usize, read_niche as *const () as usize,
        read_dirty as *const () as usize, high_tag as *const () as usize);
}
