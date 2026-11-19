mod abi;
mod bounds;
mod calls;
mod contexts;
mod convention;
mod effects;
mod image;
mod metadata;
mod refresh;
mod runtime;
mod signatures;
mod source;
mod symbols;
mod types;
mod validation;
mod values;

use binaryninja::binary_view::BinaryView;
use binaryninja::command::Command;

pub(crate) struct Analyze;
pub(crate) use contexts::ShowContexts;
pub(crate) use refresh::register;
pub(crate) use source::ShowSource;

impl Command for Analyze {
    fn valid(&self, view: &BinaryView) -> bool {
        view.default_platform().is_some()
    }

    fn action(&self, view: &BinaryView) {
        // Keep parser failures and unwinding inside the Rust callback boundary.
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| refresh::run(view, true))) {
            Ok(Ok(count)) => tracing::info!(functions = count, "Go metadata recovered"),
            Ok(Err(error)) => tracing::warn!(%error, "Go metadata recovery stopped"),
            Err(_) => tracing::error!("Go metadata reader panicked; recovery stopped"),
        }
    }
}

fn apply(
    view: &BinaryView,
    snapshot: &image::Image,
    metadata: &metadata::Metadata,
) -> Result<usize, String> {
    let installed = types::install(view, &snapshot.binary, &metadata.types)?;
    tracing::info!(
        "Recovered {} Go types; rejected {} descriptors",
        installed.count,
        metadata.types.rejected.len()
    );
    let functions = symbols::install(view, snapshot, metadata)?;
    let methods = signatures::install(view, snapshot, metadata, &installed)?;
    tracing::info!("Recovered {methods} Go method signatures");
    calls::publish(view, snapshot, metadata)?;
    contexts::publish(view, snapshot, metadata)?;
    Ok(functions)
}
