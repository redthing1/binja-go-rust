#[repr(C)]
pub struct Record {
    pub tag: u64,
    pub value: u64,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn is_zero(value: u64) -> bool {
    value == 0
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn is_nonzero(value: u64) -> bool {
    !is_zero(value)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn is_odd(value: u64) -> bool {
    value & 1 != 0
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn two_or_three(value: u64) -> u64 {
    if is_zero(value) { 2 } else { 3 }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn tag_is_zero(record: *const Record) -> bool {
    unsafe { (*record).tag == 0 }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn load_tag(record: *const Record) -> u64 {
    unsafe { (*record).tag }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn relay_tag(record: *const Record) -> u64 {
    unsafe { load_tag(record) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn write_word(record: *mut Record, value: u64) -> u64 {
    unsafe { (*record).tag = 1 };
    value
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn replace_tag(record: *mut Record) -> bool {
    unsafe {
        let old = (*record).tag;
        (*record).tag = 1;
        old == 0
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_scalar(record: *const Record) -> u64 {
    unsafe {
        if is_zero((*record).tag) {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_inverted(record: *const Record) -> u64 {
    unsafe {
        if is_nonzero((*record).tag) {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_memory(record: *const Record) -> u64 {
    unsafe {
        if tag_is_zero(record) {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_old(record: *mut Record) -> u64 {
    unsafe {
        let old = tag_is_zero(record);
        (*record).tag = 1;
        if old { (*record).value } else { 0 }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_writing(record: *mut Record) -> u64 {
    unsafe {
        if replace_tag(record) {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_masked(record: *const Record) -> u64 {
    unsafe {
        if is_odd((*record).tag) {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_nonboolean(record: *const Record) -> u64 {
    unsafe {
        if two_or_three((*record).tag) == 2 {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_returned(record: *const Record) -> u64 {
    unsafe {
        if relay_tag(record) == 0 {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_copied(record: *mut Record) -> u64 {
    unsafe {
        let old = load_tag(record);
        (*record).tag = 1;
        if old == 0 { (*record).value } else { 0 }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_saved(record: *mut Record) -> u64 {
    unsafe {
        let old = (*record).tag;
        if write_word(record, old) == 0 {
            (*record).value
        } else {
            0
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn read_argument(record: *mut Record, value: u64) -> u64 {
    unsafe {
        if write_word(record, value) == 0 {
            (*record).value
        } else {
            0
        }
    }
}

fn main() {
    let mut record = Record { tag: 0, value: 37 };
    assert!(is_zero(0) && !is_zero(2) && is_nonzero(2));
    assert!(!is_odd(2) && is_odd(3));
    unsafe {
        assert_eq!(read_scalar(&record), 37);
        assert_eq!(read_inverted(&record), 0);
        assert_eq!(read_memory(&record), 37);
        assert_eq!(read_nonboolean(&record), 37);
        assert_eq!(read_returned(&record), 37);
        assert_eq!(read_argument(&mut record, 0), 37);
        record.tag = 0;
        assert_eq!(read_saved(&mut record), 37);
        record.tag = 0;
        assert_eq!(read_copied(&mut record), 37);
        record.tag = 0;
        assert_eq!(read_old(&mut record), 37);
        assert_eq!(record.tag, 1);
        record.tag = 0;
        assert_eq!(read_writing(&mut record), 37);
        assert_eq!(record.tag, 1);
        assert_eq!(read_masked(&record), 37);
    }
    let helpers = [
        ("is_zero", is_zero as usize),
        ("is_nonzero", is_nonzero as usize),
        ("is_odd", is_odd as usize),
        ("two_or_three", two_or_three as usize),
        ("tag_is_zero", tag_is_zero as usize),
        ("replace_tag", replace_tag as usize),
        ("read_memory", read_memory as usize),
        ("read_old", read_old as usize),
        ("read_writing", read_writing as usize),
        ("read_masked", read_masked as usize),
        ("read_nonboolean", read_nonboolean as usize),
        ("load_tag", load_tag as usize),
        ("relay_tag", relay_tag as usize),
        ("write_word", write_word as usize),
        ("read_returned", read_returned as usize),
        ("read_copied", read_copied as usize),
        ("read_saved", read_saved as usize),
        ("read_argument", read_argument as usize),
    ];
    print!(
        "{{\"read_scalar\":{},\"read_inverted\":{},\"helpers\":{{",
        read_scalar as usize, read_inverted as usize
    );
    for (index, (name, address)) in helpers.iter().enumerate() {
        if index != 0 {
            print!(",");
        }
        print!("\"{name}\":{address}");
    }
    println!("}}}}");
}
