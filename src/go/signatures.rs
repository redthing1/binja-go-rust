use std::collections::BTreeMap;

use binaryninja::architecture::{ArchitectureExt, CoreArchitecture};
use binaryninja::binary_view::BinaryView;
use binaryninja::confidence::Conf;
use binaryninja::rc::Ref;
use binaryninja::types::{
    FunctionParameter, MemberAccess, MemberScope, ReturnValue, StructureBuilder, Type,
    ValueLocation, ValueLocationComponent, ValueLocationSource,
};
use binaryninja::variable::Variable;
use unstrip::types::{KindData, KindName};

use super::image::Image;
use super::{abi, convention, metadata::Metadata, types};

fn shape(
    binary: &unstrip::GoBinary,
    graph: &super::metadata::TypeGraph,
    address: u64,
    depth: usize,
) -> Result<abi::Shape, String> {
    if depth > 128 {
        return Err("type layout nesting exceeds 128 levels".into());
    }
    let node = &graph.nodes[&address];
    let ps = binary.pointer_size() as u64;
    let word = || abi::Shape {
        size: ps,
        alignment: ps,
        kind: abi::Kind::Integer,
    };
    let kind = match (&node.kind, &node.kind_data) {
        (KindName::Float32 | KindName::Float64, _) => abi::Kind::Float,
        (KindName::Complex64 | KindName::Complex128, _) => {
            let half = node.size / 2;
            let part = abi::Shape {
                size: half,
                alignment: half,
                kind: abi::Kind::Float,
            };
            abi::Kind::Fields(vec![(0, part.clone()), (half, part)])
        }
        (KindName::Struct, KindData::Struct { fields }) => abi::Kind::Fields(
            fields
                .iter()
                .map(|field| Ok((field.offset, shape(binary, graph, field.typ, depth + 1)?)))
                .collect::<Result<_, String>>()?,
        ),
        (KindName::Array, KindData::Array { elem, len }) => abi::Kind::Array {
            element: Box::new(shape(binary, graph, *elem, depth + 1)?),
            count: *len,
        },
        (KindName::String | KindName::Slice | KindName::Interface, _) => {
            abi::Kind::Fields((0..node.size / ps).map(|i| (i * ps, word())).collect())
        }
        _ => abi::Kind::Integer,
    };
    Ok(abi::Shape {
        size: node.size,
        alignment: types::alignment(binary, address)? as u64,
        kind,
    })
}

fn location(
    arch: CoreArchitecture,
    parts: &[abi::Part],
    base: u64,
) -> Result<ValueLocation, String> {
    let mut components = Vec::new();
    for part in parts.iter().filter(|part| part.size != 0) {
        let variable = match part.storage {
            abi::Storage::Integer(index) => Variable::from_register(
                arch.register_by_name(convention::INTEGERS[index as usize])
                    .ok_or("missing Go integer register")?,
            ),
            // BN value locations use the full-width SIMD parent register.
            abi::Storage::Float(index) => Variable::from_register(
                arch.register_by_name(convention::FLOATS[index as usize])
                    .ok_or("missing Go float register")?,
            ),
            abi::Storage::Stack(offset) => Variable::from_stack_offset(
                i64::try_from(offset).map_err(|_| "stack location overflow")?,
            ),
        };
        components.push(ValueLocationComponent {
            variable,
            offset: i64::try_from(base + part.offset).map_err(|_| "value offset overflow")?,
            size: Some(part.size),
        });
    }
    Ok(ValueLocation {
        components,
        indirect: false,
        returned_pointer: None,
    })
}

fn signature(
    view: &BinaryView,
    snapshot: &Image,
    metadata: &Metadata,
    installed: &types::Installed,
    owner: u64,
    descriptor: u64,
    boxed: bool,
) -> Result<Ref<Type>, String> {
    let arch = view.default_arch().ok_or("missing architecture")?;
    let cc = convention::amd64().ok_or("Go amd64 convention unavailable")?;
    let KindData::Func {
        in_types,
        out_types,
        ..
    } = &metadata.types.nodes[&descriptor].kind_data
    else {
        return Err("method signature is not a function".into());
    };
    let mut parameters = vec![installed.references[&owner].clone()];
    let mut shapes = vec![shape(&snapshot.binary, &metadata.types, owner, 0)?];
    if let KindData::Pointer { elem } = metadata.types.nodes[&owner].kind_data {
        parameters[0] =
            Type::pointer_of_width(installed.references[&elem].as_ref(), 8, false, false, None);
    }
    if boxed {
        parameters[0] = Type::pointer_of_width(parameters[0].as_ref(), 8, false, false, None);
        shapes[0] = abi::Shape {
            size: 8,
            alignment: 8,
            kind: abi::Kind::Integer,
        };
    }
    parameters.extend(
        in_types
            .iter()
            .map(|address| installed.references[address].clone()),
    );
    for address in in_types {
        shapes.push(shape(&snapshot.binary, &metadata.types, *address, 0)?);
    }
    let result_shapes = out_types
        .iter()
        .map(|address| shape(&snapshot.binary, &metadata.types, *address, 0))
        .collect::<Result<Vec<_>, _>>()?;
    let layout = abi::layout(&shapes, &result_shapes, false)?;
    let parameters = parameters
        .into_iter()
        .zip(&layout.parameters)
        .enumerate()
        .map(|(index, (ty, parts))| {
            Ok(FunctionParameter {
                ty: ty.into(),
                name: if index == 0 {
                    "receiver".into()
                } else {
                    format!("arg{}", index - 1)
                },
                location: ValueLocationSource::Custom(location(arch, parts, 0)?),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let result = match out_types.as_slice() {
        [] => ReturnValue {
            ty: Type::void().into(),
            location: None,
        },
        [address] => ReturnValue {
            ty: installed.references[address].clone().into(),
            location: Some(location(arch, &layout.results[0], 0)?.into()),
        },
        _ => {
            let mut builder = StructureBuilder::new();
            let mut components = Vec::new();
            let mut offset = 0;
            for (index, ((address, shape), parts)) in out_types
                .iter()
                .zip(&result_shapes)
                .zip(&layout.results)
                .enumerate()
            {
                offset = (offset + shape.alignment - 1) & !(shape.alignment - 1);
                builder.insert(
                    installed.references[address].as_ref(),
                    &format!("result{index}"),
                    offset,
                    false,
                    MemberAccess::PublicAccess,
                    MemberScope::NoScope,
                );
                components.extend(location(arch, parts, offset)?.components);
                offset += shape.size;
            }
            ReturnValue {
                ty: Type::structure(&builder.finalize()).into(),
                location: Some(
                    ValueLocation {
                        components,
                        indirect: false,
                        returned_pointer: None,
                    }
                    .into(),
                ),
            }
        }
    };
    tracing::debug!(
        stack_size = layout.stack_size,
        spill_count = layout.spills.len(),
        "Go call layout"
    );
    Ok(Type::function_with_opts(
        result,
        &parameters,
        false,
        cc.clone(),
        Conf::new(0, 255),
    ))
}

/// Apply only signatures for which all metadata owners agree.
pub(crate) fn install(
    view: &BinaryView,
    snapshot: &Image,
    metadata: &Metadata,
    installed: &types::Installed,
) -> Result<usize, String> {
    let Some(arch) = view.default_arch() else {
        return Ok(0);
    };
    if arch.name() != "x86_64"
        || snapshot.binary.pointer_size() != 8
        || !super::runtime::checked_abi(&snapshot.binary)
    {
        return Ok(0);
    }
    let mut votes = [0usize; 3];
    for node in metadata
        .types
        .nodes
        .values()
        .filter(|node| node.kind == KindName::Pointer && node.ptr_bytes == 8 && node.size == 8)
    {
        let kind = snapshot
            .binary
            .read_at_addr(node.addr + 23, 1)
            .ok_or("missing kind flags")?[0];
        match (kind & 32 != 0, node.tflag & 32 != 0) {
            (true, false) => votes[0] += 1,
            (false, true) => votes[1] += 1,
            _ => votes[2] += 1,
        }
    }
    let modern = match votes {
        [old, 0, 0] if old > 0 => Some(false),
        [0, new, 0] if new > 0 => Some(true),
        _ => None,
    };
    let names: BTreeMap<_, _> = metadata
        .functions
        .iter()
        .map(|function| (function.address, function.name.as_str()))
        .collect();
    let mut candidates: BTreeMap<u64, Option<Ref<Type>>> = BTreeMap::new();
    for (owner, method) in &metadata.types.methods {
        if method.mtyp_addr == 0 {
            continue;
        }
        let node = &metadata.types.nodes[owner];
        if node.name.contains('[') {
            continue;
        }
        let direct = modern.map(|modern| {
            if modern {
                node.tflag & 32 != 0
            } else {
                snapshot
                    .binary
                    .read_at_addr(node.addr + 23, 1)
                    .is_some_and(|bytes| bytes[0] & 32 != 0)
            }
        });
        for (pc, boxed) in [
            (method.tfn_pc, Some(false)),
            (method.ifn_pc, direct.map(|direct| !direct)),
        ] {
            if pc == 0 || boxed.is_none() {
                continue;
            }
            let Some(name) = names.get(&pc) else { continue };
            // Shape bodies have hidden dictionary context; ABI0 uses a different layout.
            if name.is_empty()
                || *name == "runtime.unreachableMethod"
                || name.contains("go.shape.")
                || name.ends_with(".abi0")
            {
                continue;
            }
            let ty = match signature(
                view,
                snapshot,
                metadata,
                installed,
                *owner,
                method.mtyp_addr,
                boxed.unwrap(),
            ) {
                Ok(ty) => ty,
                Err(error) => {
                    tracing::debug!("Skipped method {pc:#x}: {error}");
                    continue;
                }
            };
            candidates
                .entry(pc)
                .and_modify(|candidate| {
                    if candidate.as_ref() != Some(&ty) {
                        *candidate = None;
                    }
                })
                .or_insert(Some(ty));
        }
    }
    let mut count = 0;
    for (pc, signature) in candidates {
        let (Some(address), Some(signature)) = (snapshot.loaded_address(pc), signature) else {
            continue;
        };
        let Some(function) = view.add_auto_function(address) else {
            continue;
        };
        if function.has_user_type() || function.has_user_annotations() {
            tracing::debug!("Preserved analyst method {pc:#x}");
            continue;
        }
        tracing::debug!("Applying method {pc:#x}: {signature}");
        function.apply_auto_discovered_type(&signature);
        count += 1;
    }
    Ok(count)
}
