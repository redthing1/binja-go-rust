use binaryninja::architecture::{ArchitectureExt, CoreArchitecture};
use binaryninja::confidence::Conf;
use binaryninja::rc::Ref;
use binaryninja::types::{
    FunctionParameter, ReturnValue, Type, ValueLocation, ValueLocationComponent,
    ValueLocationSource,
};
use binaryninja::variable::Variable;
use serde::{Deserialize, Serialize};

use super::convention;

/// These helper contracts have been checked against the compiler and runtime.
pub(crate) fn checked_version(binary: &unstrip::GoBinary) -> Option<u32> {
    let Ok(info) = unstrip::BuildInfo::parse(binary) else {
        return None;
    };
    let Some(minor) = info.go_version.strip_prefix("go1.").and_then(|version| {
        version
            .split(|c: char| !c.is_ascii_digit())
            .next()?
            .parse::<u32>()
            .ok()
    }) else {
        return None;
    };
    ((25..=27).contains(&minor)
        && !info.settings.iter().any(|setting| {
            setting.key == "GOEXPERIMENT"
                && setting
                    .value
                    .split(',')
                    .any(|value| value == "noregabiargs")
        }))
    .then_some(minor)
}

pub(crate) fn checked_abi(binary: &unstrip::GoBinary) -> bool {
    checked_version(binary).is_some()
}

#[derive(Clone, Copy, Deserialize, Serialize)]
pub(crate) enum Allocation {
    Object,
    Slice,
    Malloc,
}

impl Allocation {
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        match name {
            "runtime.newobject" => Some(Self::Object),
            "runtime.makeslice" => Some(Self::Slice),
            "runtime.mallocgc" => Some(Self::Malloc),
            _ => ["SmallNoScan", "SmallScanNoHeader", "Tiny"]
                .iter()
                .any(|kind| {
                    name.strip_prefix(&format!("runtime.mallocgc{kind}SC"))
                        .is_some_and(|suffix| {
                            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                        })
                })
                .then_some(Self::Malloc),
        }
    }

    pub(crate) fn descriptor_register(self) -> &'static str {
        match self {
            Self::Object | Self::Slice => "rax",
            Self::Malloc => "rbx",
        }
    }
}

pub(crate) fn location(arch: CoreArchitecture, register: &str, size: u64) -> Option<ValueLocation> {
    Some(ValueLocation {
        components: vec![ValueLocationComponent {
            variable: Variable::from_register(arch.register_by_name(register)?),
            offset: 0,
            size: Some(size),
        }],
        indirect: false,
        returned_pointer: None,
    })
}

pub(crate) fn signature(
    arch: CoreArchitecture,
    kind: Allocation,
    element: &Type,
) -> Option<Ref<Type>> {
    let descriptor = Type::pointer_of_width(&Type::void(), 8, false, false, None);
    let word = Type::int(8, true);
    let fields = match kind {
        Allocation::Object => vec![(descriptor, "type_descriptor", "rax", 8)],
        Allocation::Slice => vec![
            (descriptor, "element_type", "rax", 8),
            (word.clone(), "length", "rbx", 8),
            (word, "capacity", "rcx", 8),
        ],
        Allocation::Malloc => vec![
            (Type::int(8, false), "size", "rax", 8),
            (descriptor, "type_descriptor", "rbx", 8),
            (Type::bool(), "need_zero", "rcx", 1),
        ],
    };
    let parameters = fields
        .into_iter()
        .map(|(ty, name, register, size)| {
            Some(FunctionParameter {
                ty: ty.into(),
                name: name.into(),
                location: ValueLocationSource::Custom(location(arch, register, size)?),
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(Type::function_with_opts(
        ReturnValue {
            ty: Type::pointer_of_width(element, 8, false, false, None).into(),
            location: Some(location(arch, "rax", 8)?.into()),
        },
        &parameters,
        false,
        convention::amd64()?.clone(),
        Conf::new(0, 255),
    ))
}

#[cfg(test)]
mod tests {
    use super::Allocation;

    #[test]
    fn helper_names_require_the_complete_runtime_contract() {
        assert!(Allocation::from_name("runtime.mallocgcSmallNoScanSC16").is_some());
        for name in [
            "mallocgc",
            "runtime.mallocgc.abi0",
            "runtime.mallocgcTinySC",
            "runtime.mallocgcTinySC8x",
        ] {
            assert!(Allocation::from_name(name).is_none(), "{name}");
        }
    }
}
