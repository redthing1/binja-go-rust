use std::hint::black_box;

struct Record {
    prefix: u8,
    count: u64,
    status: u32,
}

#[inline(never)]
unsafe fn read(record: *const Record) -> u64 {
    unsafe { (*record).count }
}

#[inline(never)]
unsafe fn forward(record: *const Record) -> u64 {
    unsafe { read(record) }.wrapping_add(1)
}

#[inline(never)]
unsafe fn user_variable(record: *const Record) -> u64 {
    unsafe { read(record) }.wrapping_add(3)
}

#[inline(never)]
unsafe fn user_prototype(record: *const Record) -> u64 {
    unsafe { read(record) }.wrapping_add(5)
}

#[inline(never)]
unsafe fn store(record: *mut Record, value: u32) -> u64 {
    unsafe { (*record).status = value };
    u64::from(value)
}

#[inline(never)]
unsafe fn root(record: *mut Record, value: u32) -> u64 {
    unsafe { forward(record) }
        .wrapping_add(unsafe { user_variable(record) })
        .wrapping_add(unsafe { user_prototype(record) })
        .wrapping_add(unsafe { store(record, value) })
}

pub fn oracle() -> String {
    let mut record = Record {
        prefix: 17,
        count: 29,
        status: 31,
    };
    let value = unsafe { root(black_box(&mut record), black_box(37)) };
    assert_eq!(value, 29 * 3 + 1 + 3 + 5 + 37);
    assert_eq!(record.prefix, 17);
    format!(
        "{{\"root\":{},\"read\":{},\"forward\":{},\"store\":{},\"user_variable\":{},\"user_prototype\":{},\"count_offset\":{},\"status_offset\":{}}}",
        root as *const () as usize,
        read as *const () as usize,
        forward as *const () as usize,
        store as *const () as usize,
        user_variable as *const () as usize,
        user_prototype as *const () as usize,
        std::mem::offset_of!(Record, count),
        std::mem::offset_of!(Record, status),
    )
}
