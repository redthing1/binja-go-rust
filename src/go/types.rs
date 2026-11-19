use std::collections::BTreeMap;

use binaryninja::binary_view::{BinaryView, MetadataStoreFlags};
use binaryninja::qualified_name::QualifiedName;
use binaryninja::rc::Ref;
use binaryninja::types::{
    MemberAccess, MemberScope, NamedTypeReference, NamedTypeReferenceClass, StructureBuilder, Type,
    TypeBuilder,
};
use unstrip::GoBinary;
use unstrip::types::{KindData, KindName};

use super::metadata::TypeGraph;

const NAMES: &str = "go-rust.go.type-names.v1";

pub(crate) fn clear(view: &BinaryView) {
    let previous: BTreeMap<String, Vec<String>> = view
        .get_metadata::<String>(NAMES)
        .and_then(|value| serde_json::from_str(&value).ok())
        .unwrap_or_default();
    let mut protected = BTreeMap::new();
    for (id, name) in previous {
        if let Some(current) = view.type_name_by_id(&id) {
            if current.items == name && view.is_type_auto_defined(current) {
                view.undefine_auto_type(&id);
            } else {
                protected.insert(id, name);
            }
        }
    }
    if let Ok(value) = serde_json::to_string(&protected) {
        view.store_metadata(NAMES, value, MetadataStoreFlags::PERSISTENT);
    }
}

pub(crate) fn identity(address: u64) -> String {
    format!("go-rust.go:{address:x}")
}

fn structure(fields: Vec<(u64, Ref<Type>, String)>, size: u64, alignment: usize) -> Ref<Type> {
    let mut builder = StructureBuilder::new();
    for (offset, ty, name) in fields {
        builder.insert(
            ty.as_ref(),
            &name,
            offset,
            false,
            MemberAccess::PublicAccess,
            MemberScope::NoScope,
        );
    }
    builder.width(size).alignment(alignment);
    Type::structure(&builder.finalize())
}

pub(crate) struct Installed {
    pub references: BTreeMap<u64, Ref<Type>>,
    pub count: usize,
}

pub(crate) fn install(
    view: &BinaryView,
    binary: &GoBinary,
    graph: &TypeGraph,
) -> Result<Installed, String> {
    let previous: BTreeMap<String, Vec<String>> = view
        .get_metadata::<String>(NAMES)
        .and_then(|value| serde_json::from_str(&value).ok())
        .unwrap_or_default();
    let mut owned = previous.clone();
    let mut counts = BTreeMap::<&str, usize>::new();
    for node in graph.nodes.values() {
        *counts.entry(&node.name).or_default() += 1;
    }
    let mut references = BTreeMap::new();
    let mut names = BTreeMap::new();
    let mut protected = BTreeMap::new();
    for (&address, node) in &graph.nodes {
        let id = identity(address);
        // The core can retain an ID/name association after the type is removed.
        let current = view.type_by_id(&id).and_then(|_| view.type_name_by_id(&id));
        let analyst_name = current
            .as_ref()
            .is_some_and(|name| previous.get(&id) != Some(&name.items));
        let analyst_type = current
            .as_ref()
            .is_some_and(|name| !view.is_type_auto_defined(name.clone()));
        let preferred = {
            let mut name = if node.name.is_empty() {
                format!("type_{address:x}")
            } else {
                node.name.clone()
            };
            if counts[node.name.as_str()] > 1 {
                name.push_str(&format!("_{address:x}"));
            }
            QualifiedName::new(["go".to_string(), name])
        };
        let mut name = current.clone().unwrap_or_else(|| preferred.clone());
        // The core rename operation can replace a destination type.
        if !analyst_name
            && !analyst_type
            && name != preferred
            && view.type_by_name(preferred.clone()).is_none()
            && view
                .auto_type_container()
                .rename_type(preferred.clone(), &id)
        {
            name = preferred;
        }
        let alignment = alignment(binary, address)?;
        // Establish identities before creating references, including recursive pointers.
        if current.is_none() {
            name = view.define_auto_type_with_id(
                name.clone(),
                &id,
                &structure(Vec::new(), node.size, alignment),
            );
        }
        let reference = NamedTypeReference::new_with_id(
            NamedTypeReferenceClass::TypedefNamedTypeClass,
            &id,
            name.clone(),
        );
        let builder = TypeBuilder::named_type(&reference);
        builder
            .set_width(
                usize::try_from(node.size).map_err(|_| "type width exceeds host address space")?,
            )
            .set_alignment(alignment);
        references.insert(address, builder.finalize());
        protected.insert(address, (analyst_name, analyst_type));
        if !analyst_name {
            owned.insert(id, name.items.clone());
        }
        names.insert(address, name);
    }
    // Record ownership before filling definitions so failed imports can be withdrawn.
    view.store_metadata(
        NAMES,
        serde_json::to_string(&owned).map_err(|error| error.to_string())?,
        MetadataStoreFlags::PERSISTENT,
    );
    let ps = binary.pointer_size();
    let pointer = |ty: &Type| Type::pointer_of_width(ty, ps, false, false, None);
    let opaque = pointer(&Type::void());
    let mut installed = 0;
    for (&address, node) in &graph.nodes {
        let (analyst_name, analyst_type) = protected[&address];
        if analyst_type {
            continue;
        }
        let alignment = alignment(binary, address)?;
        let word = Type::int(ps, true);
        let ty = match (&node.kind, &node.kind_data) {
            (KindName::Bool, _) => Type::bool(),
            (
                KindName::Int
                | KindName::Int8
                | KindName::Int16
                | KindName::Int32
                | KindName::Int64,
                _,
            ) => Type::int(node.size as usize, true),
            (
                KindName::Uint
                | KindName::Uint8
                | KindName::Uint16
                | KindName::Uint32
                | KindName::Uint64
                | KindName::Uintptr,
                _,
            ) => Type::int(node.size as usize, false),
            (KindName::Float32 | KindName::Float64, _) => Type::float(node.size as usize),
            (KindName::Complex64 | KindName::Complex128, _) => {
                let half = node.size / 2;
                let part = Type::float(half as usize);
                structure(
                    vec![
                        (0, part.clone(), "real".into()),
                        (half, part, "imaginary".into()),
                    ],
                    node.size,
                    alignment,
                )
            }
            (KindName::Pointer, KindData::Pointer { elem }) => pointer(&references[elem]),
            (KindName::Array, KindData::Array { elem, len }) => {
                Type::array(references[elem].as_ref(), *len)
            }
            (KindName::Map | KindName::Chan | KindName::UnsafePointer, _) => opaque.clone(),
            (KindName::Func, _) => pointer(&structure(
                vec![(0, opaque.clone(), "entry".into())],
                ps as u64,
                ps,
            )),
            (KindName::String | KindName::Slice, data) => {
                let element = if let KindData::Slice { elem } = data {
                    references[elem].clone()
                } else {
                    Type::int(1, false)
                };
                let mut fields = vec![
                    (0, pointer(&element), "data".into()),
                    (ps as u64, word.clone(), "length".into()),
                ];
                if node.kind == KindName::Slice {
                    fields.push((2 * ps as u64, word, "capacity".into()));
                }
                structure(fields, node.size, alignment)
            }
            (KindName::Interface, KindData::Interface { methods }) => structure(
                vec![
                    (
                        0,
                        opaque.clone(),
                        if methods.is_empty() {
                            "type_descriptor"
                        } else {
                            "itab"
                        }
                        .into(),
                    ),
                    (ps as u64, opaque.clone(), "data".into()),
                ],
                node.size,
                alignment,
            ),
            (KindName::Struct, KindData::Struct { fields }) => structure(
                fields
                    .iter()
                    .map(|field| {
                        (
                            field.offset,
                            references[&field.typ].clone(),
                            field.name.clone(),
                        )
                    })
                    .collect(),
                node.size,
                alignment,
            ),
            _ => return Err(format!("unhandled validated kind at {address:#x}")),
        };
        let builder = TypeBuilder::new(&ty);
        builder.set_alignment(alignment);
        let ty = builder.finalize();
        if ty.width() != node.size || (ty.alignment() != alignment && node.kind != KindName::Bool) {
            return Err(format!("type layout differs from metadata at {address:#x}"));
        }
        let id = identity(address);
        let name = view.define_auto_type_with_id(names[&address].clone(), &id, &ty);
        if !analyst_name {
            owned.insert(id, name.items);
        }
        installed += 1;
    }
    for (id, name) in previous {
        if id
            .strip_prefix("go-rust.go:")
            .and_then(|value| u64::from_str_radix(value, 16).ok())
            .is_some_and(|address| graph.nodes.contains_key(&address))
        {
            continue;
        }
        if let Some(current) = view.type_name_by_id(&id) {
            if current.items == name && view.is_type_auto_defined(current) {
                view.undefine_auto_type(&id);
                owned.remove(&id);
            }
        }
    }
    view.store_metadata(
        NAMES,
        serde_json::to_string(&owned).map_err(|error| error.to_string())?,
        MetadataStoreFlags::PERSISTENT,
    );
    Ok(Installed {
        references,
        count: installed,
    })
}

pub(crate) fn alignment(binary: &GoBinary, address: u64) -> Result<usize, String> {
    binary
        .read_at_addr(address + (2 * binary.pointer_size() + 5) as u64, 1)
        .map(|bytes| usize::from(bytes[0]))
        .ok_or_else(|| "unmapped type alignment".into())
}
