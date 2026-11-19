use std::hint::black_box;

mod layouts;

trait Score {
    fn score(&self) -> u64;
}

struct Counter(u64);
struct OtherCounter {
    prefix: u64,
    value: u64,
}

impl Score for Counter {
    #[inline(never)]
    fn score(&self) -> u64 {
        self.0
    }
}

impl Score for OtherCounter {
    #[inline(never)]
    fn score(&self) -> u64 {
        self.value
    }
}

#[inline(never)]
fn dispatch(value: &dyn Score) -> u64 {
    black_box(value).score()
}

#[inline(never)]
fn counter_score(value: &Counter) -> u64 {
    dispatch(black_box(value as &dyn Score))
}

#[inline(never)]
fn other_score(value: &OtherCounter) -> u64 {
    dispatch(black_box(value as &dyn Score))
}

#[inline(never)]
fn dispatch_root(a: &Counter, b: &OtherCounter) -> u64 {
    counter_score(a) + other_score(b)
}

#[inline(never)]
fn local_score(value: &Counter) -> u64 {
    let object = black_box(value as &dyn Score);
    object.score() + object.score()
}

static COUNTER: Counter = Counter(17);
static OTHER: OtherCounter = OtherCounter {
    prefix: 0,
    value: 23,
};
static SPAN: &[u8] = b"native Rust span";

#[inline(never)]
fn library_control(value: u64) -> u64 {
    let value = value.rotate_left(13) ^ 0xa076_1d64_78bd_642f;
    value.wrapping_mul(0xe703_7ed1_a0b4_28db)
}

fn main() {
    let object: &dyn Score = black_box(&COUNTER);
    // This fixture observes the compiler's trait-object representation.
    let words: [usize; 2] = unsafe { std::mem::transmute(object) };
    let other: [usize; 2] = unsafe { std::mem::transmute(&OTHER as &dyn Score) };
    assert_eq!(dispatch_root(black_box(&COUNTER), black_box(&OTHER)), 40);
    assert_eq!(local_score(black_box(&COUNTER)), 34);
    assert_eq!(OTHER.prefix, 0);
    println!(
        "{{\"vtable\":{},\"span\":{},\"size\":{},\"alignment\":{},\"library\":{},\"layouts\":{},\"dispatch\":{{\"root\":{},\"function\":{},\"local\":{},\"tables\":[{},{}]}}}}",
        words[1],
        &SPAN as *const _ as usize,
        std::mem::size_of::<Counter>(),
        std::mem::align_of::<Counter>(),
        library_control as *const () as usize,
        layouts::oracle(),
        dispatch_root as *const () as usize,
        dispatch as *const () as usize,
        local_score as *const () as usize,
        words[1],
        other[1],
    );
    black_box(library_control(black_box(17)));
    assert_eq!(object.score(), 17);
}
