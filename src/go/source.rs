use binaryninja::binary_view::BinaryView;
use binaryninja::command::AddressCommand;
use unstrip::{ModuleData, Pclntab};

use super::image::Image;

pub(crate) struct ShowSource;

impl AddressCommand for ShowSource {
    fn valid(&self, view: &BinaryView, _address: u64) -> bool {
        view.default_platform().is_some()
    }

    fn action(&self, view: &BinaryView, address: u64) {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| source(view, address))) {
            Ok(Ok(report)) => view.show_plaintext_report("Go source information", &report),
            Ok(Err(error)) => tracing::warn!(%error, "Go source lookup failed"),
            Err(_) => tracing::error!("Go source reader panicked"),
        }
    }
}

fn source(view: &BinaryView, address: u64) -> Result<String, String> {
    let mut snapshot = Image::read(view)?;
    let address = snapshot
        .original_address(address)
        .ok_or("source address overflow")?;
    let module = ModuleData::locate(&snapshot.binary).map_err(|error| error.to_string())?;
    snapshot.binary.text_addr = module.text;
    let table = Pclntab::parse(&snapshot.binary)
        .map_err(|error| error.to_string())?
        .with_gofunc(module.gofunc);
    let frames = table.lookup_inline(&snapshot.binary, address);
    if frames.is_empty() {
        return Err("no Go source information at this address".into());
    }
    let mut report = String::new();
    for frame in frames {
        report.push_str(if frame.name.is_empty() {
            "(name unavailable)"
        } else {
            &frame.name
        });
        if frame.inlined {
            report.push_str(" (inlined)");
        }
        report.push('\n');
        if let Some(file) = frame.file {
            report.push_str(&file);
            if let Some(line) = frame.line {
                report.push_str(&format!(":{line}"));
            }
            report.push('\n');
        }
    }
    Ok(report)
}
