use std::collections::BTreeSet;
use std::sync::{Mutex, OnceLock};

use binaryninja::binary_view::{BinaryView, MetadataStoreFlags};
use binaryninja::workflow::activity::{Config, Eligibility};
use binaryninja::workflow::{Activity, AnalysisContext, Workflow};

use super::{calls, contexts, image::Image, metadata, symbols, types};

const ACTIVE: &str = "go-rust.go.active.v1";
const INPUT: &str = "go-rust.go.input.v1";
const ACTIVITY: &str = "analysis.goRust.metadata";
static RUNNING: OnceLock<Mutex<BTreeSet<usize>>> = OnceLock::new();

// Keep independent views independent and avoid reentry from analysis notifications.
struct Running(usize);

impl Running {
    fn enter(key: usize) -> Option<Self> {
        RUNNING
            .get_or_init(Mutex::default)
            .lock()
            .ok()?
            .insert(key)
            .then(|| Self(key))
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        if let Ok(mut running) = RUNNING.get().unwrap().lock() {
            running.remove(&self.0);
        }
    }
}

pub(crate) fn run(view: &BinaryView, force: bool) -> Result<usize, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_inner(view, force))) {
        Ok(result) => result,
        Err(_) => {
            let input = view.get_metadata::<String>(INPUT);
            clear(view);
            if let Some(input) = input {
                view.store_metadata(INPUT, input, MetadataStoreFlags::EPHEMERAL);
            }
            Err("Go metadata reader panicked; dependent annotations withdrawn".into())
        }
    }
}

fn run_inner(view: &BinaryView, force: bool) -> Result<usize, String> {
    let Some(_running) = Running::enter(view.handle as usize) else {
        return Ok(0);
    };
    if !force && view.get_metadata::<bool>(ACTIVE) == Some(false) {
        return Ok(0);
    }
    let mut image = match Image::read(view) {
        Ok(image) => image,
        Err(error) => {
            if view.get_metadata::<bool>(ACTIVE) == Some(true) {
                clear(view);
                return Err(error);
            }
            return if force { Err(error) } else { Ok(0) };
        }
    };
    let input = image.fingerprint();
    if !force && view.get_metadata::<String>(INPUT).as_ref() == Some(&input) {
        return Ok(0);
    }
    view.store_metadata(INPUT, input.as_str(), MetadataStoreFlags::EPHEMERAL);
    let metadata = match metadata::read(&mut image.binary) {
        Ok(metadata) => metadata,
        Err(error) => {
            if view.get_metadata::<bool>(ACTIVE) == Some(true) {
                clear(view);
            }
            view.store_metadata(INPUT, input, MetadataStoreFlags::EPHEMERAL);
            return if force || view.get_metadata::<bool>(ACTIVE) == Some(true) {
                Err(error)
            } else {
                Ok(0)
            };
        }
    };
    view.store_metadata(ACTIVE, true, MetadataStoreFlags::PERSISTENT);
    match super::apply(view, &image, &metadata) {
        Ok(count) => Ok(count),
        Err(error) => {
            clear(view);
            view.store_metadata(INPUT, input, MetadataStoreFlags::EPHEMERAL);
            Err(error)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Running;

    #[test]
    fn rejected_reentry_preserves_the_owner_and_other_views_remain_independent() {
        let owner = Running::enter(1).unwrap();
        assert!(Running::enter(1).is_none());
        let other = Running::enter(2).unwrap();
        drop(other);
        assert!(Running::enter(1).is_none());
        drop(owner);
        assert!(Running::enter(1).is_some());
    }
}

fn clear(view: &BinaryView) {
    contexts::clear(view);
    calls::clear(view);
    symbols::clear(view);
    types::clear(view);
    view.remove_metadata(INPUT);
}

fn refresh(context: &AnalysisContext) {
    let view = context.view();
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&view, false))) {
        Ok(Err(error)) => tracing::warn!("Go metadata refresh stopped: {error}"),
        Err(_) => tracing::error!("Go metadata refresh panicked"),
        _ => (),
    }
}

pub(crate) fn register() -> Result<(), ()> {
    calls::register()?;
    contexts::register()?;
    let activity = Activity::new_with_action(
        Config::action(
            ACTIVITY,
            "Go metadata",
            "Recover Go metadata and update dependent annotations",
        )
        .eligibility(Eligibility::auto().run_once(false)),
        refresh,
    );
    Workflow::cloned("core.module.metaAnalysis")
        .ok_or(())?
        .register_activity(&activity)?
        .insert("core.module.update", [ACTIVITY])?
        .register()?;
    Ok(())
}
