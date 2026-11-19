pub(crate) mod inference;
mod layout;
pub(crate) mod library;
mod ssa;
mod structures;

use binaryninja::Endianness;
use binaryninja::binary_view::{BinaryView, BinaryViewBase};
use binaryninja::command::AddressCommand;

pub(crate) struct Inspect;

impl AddressCommand for Inspect {
    fn valid(&self, view: &BinaryView, address: u64) -> bool {
        matches!(view.address_size(), 4 | 8) && view.offset_readable(address)
    }

    fn action(&self, view: &BinaryView, address: u64) {
        view.show_plaintext_report("Rust structure evidence", &inspect(view, address));
    }
}

fn inspect(view: &BinaryView, address: u64) -> String {
    let ps = view.address_size();
    if !matches!(ps, 4 | 8) {
        return "Unsupported pointer width.\n".into();
    }
    let bytes = view.read_vec(address, 4 * ps);
    let mut words = Vec::new();
    for bytes in bytes.chunks_exact(ps) {
        words.push(if view.default_endianness() == Endianness::LittleEndian {
            bytes
                .iter()
                .rev()
                .fold(0u64, |word, byte| (word << 8) | u64::from(*byte))
        } else {
            bytes
                .iter()
                .fold(0u64, |word, byte| (word << 8) | u64::from(*byte))
        });
    }
    let mut report = format!("Structure evidence at {address:#x}\n\n");
    if let [data, length, ..] = words.as_slice() {
        if *length > 0
            && *length <= 16_384
            && view.segment_at(*data).is_some_and(|segment| {
                data.checked_add(*length)
                    .is_some_and(|end| end <= segment.address_range().end)
            })
        {
            let value = view.read_vec(*data, *length as usize);
            if value.len() == *length as usize {
                report.push_str(&format!(
                    "Pointer/length pair: data {data:#x}, length {length}\n"
                ));
                if let Some(text) = structures::text(&value) {
                    report.push_str(&format!("UTF-8 bytes: {text:?}\n"));
                }
                report
                    .push_str("The representation does not distinguish str from a byte slice.\n\n");
            }
        }
    }
    if let Ok(words) = <[u64; 4]>::try_from(words.as_slice()) {
        if let Some(header) = structures::vtable(words, |pc| view.offset_executable(pc)) {
            report.push_str(&format!(
                "Vtable header candidate: size {}, alignment {}\n",
                header.size, header.alignment
            ));
            report.push_str(&format!(
                "Drop entry: {}\nFirst method: {:#x}\n",
                header
                    .drop
                    .map(|pc| format!("{pc:#x}"))
                    .unwrap_or_else(|| "null".into()),
                header.first_method
            ));
            report.push_str(
                "Later slots may include supertrait pointers. The method count is unknown.\n\n",
            );
        }
    }
    report
        .push_str("These observations do not establish a Rust source type or compiler version.\n");
    report
}
