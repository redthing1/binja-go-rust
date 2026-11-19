mod binja;
mod go;
mod rust;

/// Register the plugin with Binary Ninja.
///
/// # Safety
/// Called by the Binary Ninja plugin loader after core initialization.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn CorePluginInit() -> bool {
    binaryninja::tracing_init!();
    if go::register().is_err() {
        tracing::error!("Could not register the Go metadata workflow");
    }
    if rust::inference::register().is_err() {
        tracing::error!("Could not register the Rust layout workflow");
    }
    binaryninja::command::register_command(
        "Go and Rust\\Analyze Go metadata",
        "Recover Go functions, source information and runtime types",
        go::Analyze,
    );
    binaryninja::command::register_command_for_address(
        "Go and Rust\\Show Go source information",
        "Show the Go source location and inline call chain at this address",
        go::ShowSource,
    );
    binaryninja::command::register_command_for_address(
        "Go and Rust\\Show Go dictionary contexts",
        "Show concrete dictionary slots, allocation types and resolved calls",
        go::ShowContexts,
    );
    binaryninja::command::register_command_for_address(
        "Go and Rust\\Inspect Rust structure",
        "Inspect pointer/length and vtable header evidence at this address",
        rust::Inspect,
    );
    binaryninja::command::register_command_for_function(
        "Go and Rust\\Infer Rust layouts",
        "Infer observed field layouts through bounded direct calls",
        rust::inference::Infer,
    );
    binaryninja::command::register_command_for_function(
        "Go and Rust\\Stop inferring Rust layouts",
        "Remove this inference root and refresh dependent field types",
        rust::inference::Forget,
    );
    binaryninja::command::register_command_for_function(
        "Go and Rust\\Inspect Rust layouts",
        "Show observed field offsets and inference status",
        rust::inference::Inspect,
    );
    binaryninja::command::register_command_for_function(
        "Go and Rust\\Inspect Rust library evidence",
        "Show loaded WARP signature candidates and the recorded function match",
        rust::library::Inspect,
    );
    true
}
