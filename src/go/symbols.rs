use std::collections::{BTreeMap, BTreeSet};

use binaryninja::binary_view::{BinaryView, BinaryViewBase, MetadataStoreFlags};
use binaryninja::symbol::{Symbol, SymbolType};

use super::image::Image;
use super::metadata::Metadata;

const NAMES: &str = "go-rust.go.function-names.v1";

pub(crate) fn clear(view: &BinaryView) {
    let previous: BTreeMap<u64, String> = view
        .get_metadata::<String>(NAMES)
        .and_then(|value| serde_json::from_str(&value).ok())
        .unwrap_or_default();
    let mut protected = BTreeMap::new();
    for (address, name) in previous {
        if view.symbol_by_address(address).is_some_and(|symbol| {
            !symbol.auto_defined() || symbol.raw_name().to_bytes() != name.as_bytes()
        }) {
            protected.insert(address, name.clone());
        }
        for symbol in view
            .symbols_in_range(address..address.saturating_add(1))
            .iter()
        {
            if symbol.auto_defined() && symbol.raw_name().to_bytes() == name.as_bytes() {
                view.undefine_auto_symbol(&symbol);
            }
        }
    }
    if let Ok(value) = serde_json::to_string(&protected) {
        view.store_metadata(NAMES, value, MetadataStoreFlags::PERSISTENT);
    }
}

pub(crate) fn install(
    view: &BinaryView,
    snapshot: &Image,
    metadata: &Metadata,
) -> Result<usize, String> {
    let previous: BTreeMap<u64, String> = view
        .get_metadata::<String>(NAMES)
        .and_then(|value| serde_json::from_str(&value).ok())
        .unwrap_or_default();
    let mut owned = previous.clone();
    let mut accepted = BTreeSet::new();
    let mut count = 0;
    for function in &metadata.functions {
        let Some(address) = snapshot.loaded_address(function.address) else {
            continue;
        };
        if !view.offset_executable(address) {
            continue;
        }
        if view.add_auto_function(address).is_none() {
            continue;
        }
        if function.name.is_empty() {
            continue;
        }
        accepted.insert(address);
        if let Some(symbol) = view.symbol_by_address(address) {
            if !symbol.auto_defined() {
                continue;
            }
            if let Some(last) = previous.get(&address) {
                if symbol.raw_name().to_bytes() != last.as_bytes() {
                    continue;
                }
                if last != &function.name {
                    view.undefine_auto_symbol(&symbol);
                }
            }
        }
        view.define_auto_symbol(
            &Symbol::builder(SymbolType::Function, &function.name, address).create(),
        );
        owned.insert(address, function.name.clone());
        count += 1;
    }
    for (address, name) in previous {
        if accepted.contains(&address) {
            continue;
        }
        if let Some(symbol) = view.symbol_by_address(address) {
            if symbol.auto_defined() && symbol.raw_name().to_bytes() == name.as_bytes() {
                view.undefine_auto_symbol(&symbol);
                owned.remove(&address);
            }
        }
    }
    view.store_metadata(
        NAMES,
        serde_json::to_string(&owned).map_err(|error| error.to_string())?,
        MetadataStoreFlags::PERSISTENT,
    );
    Ok(count)
}
