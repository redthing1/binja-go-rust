use std::collections::{BTreeMap, BTreeSet, VecDeque};

use unstrip::{GoBinary, ModuleData, Pclntab, funcsig, itabs, types};

use super::validation;

pub(crate) struct TypeGraph {
    pub nodes: BTreeMap<u64, types::Type>,
    pub methods: Vec<(u64, funcsig::RecoveredMethod)>,
    pub rejected: BTreeMap<u64, String>,
}

pub(crate) struct Metadata {
    pub functions: Vec<unstrip::Function>,
    pub extents: BTreeMap<u64, u64>,
    pub types: TypeGraph,
    pub bounds: BTreeMap<u64, Vec<super::bounds::Span>>,
    pub itabs: Vec<itabs::Itab>,
}

pub(crate) fn read(binary: &mut GoBinary) -> Result<Metadata, String> {
    let module = ModuleData::locate(binary).map_err(|error| error.to_string())?;
    // Go 1.27 may omit textStart from the PCLN header.
    binary.text_addr = module.text;
    let table = Pclntab::parse(binary).map_err(|error| error.to_string())?;
    let functions: Vec<_> = table
        .functions()
        .map_err(|error| error.to_string())?
        .into_iter()
        .filter(|function| {
            !matches!(
                function.name.as_str(),
                "go:buildid" | "go:textfipsstart" | "go:textfipsend"
            ) && binary.text_slice_at(function.address, 1).is_some()
                && !function.name.contains('\0')
        })
        .collect();
    let entries = functions.iter().map(|function| function.address).collect();
    let extents = table
        .functions_with_offsets()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|function| {
            let length = usize::try_from(function.size).ok()?;
            (length != 0 && binary.text_slice_at(function.address, length).is_some())
                .then_some((function.address, function.size))
        })
        .collect();
    let itabs = itabs::recover_all(binary, &module).map_err(|error| error.to_string())?;
    let types = read_types(binary, &module, &entries, &itabs)?;
    let bounds = if matches!(super::runtime::checked_version(binary), Some(26 | 27)) {
        super::bounds::read(&table)
    } else {
        BTreeMap::new()
    };
    Ok(Metadata {
        functions,
        extents,
        types,
        bounds,
        itabs,
    })
}

fn read_types(
    binary: &GoBinary,
    module: &ModuleData,
    entries: &BTreeSet<u64>,
    itabs: &[itabs::Itab],
) -> Result<TypeGraph, String> {
    let roots = types::recover_all(binary, module).map_err(|error| error.to_string())?;
    let mut cache = funcsig::TypeCache::new(binary, module);
    cache.seed_from(&roots);
    let mut pending: VecDeque<_> = roots.iter().map(|ty| ty.addr).collect();
    let mut rejected = BTreeMap::new();
    // Interfaces reachable only through itabs are absent from typelinks.
    for itab in itabs {
        let ps = binary.pointer_size();
        let Some(header) = binary.read_at_addr(itab.addr, 2 * ps) else {
            continue;
        };
        for (index, bytes) in header.chunks_exact(ps).enumerate() {
            let address = if binary.little_endian {
                bytes
                    .iter()
                    .rev()
                    .fold(0, |value, byte| (value << 8) | u64::from(*byte))
            } else {
                bytes
                    .iter()
                    .fold(0, |value, byte| (value << 8) | u64::from(*byte))
            };
            if validation::in_region(binary, module, address)
                && cache.get(address).is_some_and(|ty| {
                    if index == 0 {
                        ty.kind == types::KindName::Interface
                    } else {
                        !matches!(
                            ty.kind,
                            types::KindName::Interface
                                | types::KindName::Invalid
                                | types::KindName::Unknown(_)
                        )
                    }
                })
            {
                pending.push_back(address);
            }
        }
    }
    let offsets = validation::offset_encoding(binary, module);
    let mut seen = BTreeSet::new();
    let mut nodes = BTreeMap::new();
    let mut methods = Vec::new();
    while let Some(address) = pending.pop_front() {
        if address == 0 || !seen.insert(address) {
            continue;
        }
        if seen.len() > 100_000 {
            return Err("type graph exceeds 100,000 descriptors".into());
        }
        if !validation::in_region(binary, module, address) {
            rejected.insert(address, "type header outside aligned types region".into());
            continue;
        }
        let Some(ty) = cache.get(address).cloned() else {
            rejected.insert(address, "unreadable type descriptor".into());
            continue;
        };
        let ty = match validation::prepare(binary, offsets, ty) {
            Ok(ty) => ty,
            Err(reason) => {
                rejected.insert(address, reason);
                continue;
            }
        };
        pending.extend(validation::children(&ty.kind_data));
        if let Ok(recovered) = funcsig::methods_for_type(binary, module, &ty) {
            for mut method in recovered {
                for pc in [&mut method.tfn_pc, &mut method.ifn_pc] {
                    if *pc != 0 && (!entries.contains(pc) || binary.text_slice_at(*pc, 1).is_none())
                    {
                        *pc = 0;
                    }
                }
                pending.push_back(method.mtyp_addr);
                methods.push((address, method));
            }
        }
        nodes.insert(address, ty);
    }
    rejected.extend(validation::quarantine(binary, &mut nodes));
    methods.retain(|(owner, method)| {
        nodes.contains_key(owner)
            && (method.mtyp_addr == 0
                || nodes
                    .get(&method.mtyp_addr)
                    .is_some_and(|ty| ty.kind == types::KindName::Func))
    });
    Ok(TypeGraph {
        nodes,
        methods,
        rejected,
    })
}
