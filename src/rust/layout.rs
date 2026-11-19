use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use serde::{Deserialize, Serialize};

pub(super) const MAX_FIELDS: usize = 256;
pub(super) const MAX_OFFSET: u64 = 1_048_576;
pub(super) const MAX_GUARDS: usize = 8;
const MAX_PATH: usize = 5;

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(super) struct Key {
    pub address: u64,
    pub platform: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(super) enum Root {
    Parameter(usize),
    Call(u64),
}

impl fmt::Display for Root {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parameter(index) => write!(f, "Parameter {}", index + 1),
            Self::Call(address) => write!(f, "Call result at {address:#x}"),
        }
    }
}

/// Intermediate offsets are pointer loads; the final offset is within the pointee.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(super) struct Place {
    pub root: Root,
    pub path: Vec<i64>,
}

impl Place {
    pub fn parameter(parameter: usize) -> Self {
        Self {
            root: Root::Parameter(parameter),
            path: vec![0],
        }
    }

    pub fn call(address: u64) -> Self {
        Self {
            root: Root::Call(address),
            path: vec![0],
        }
    }

    pub fn shift(&self, offset: i64) -> Option<Self> {
        let mut result = self.clone();
        let last = result.path.last_mut()?;
        *last = last.checked_add(offset)?;
        (last.unsigned_abs() <= MAX_OFFSET).then_some(result)
    }

    pub fn load(&self) -> Option<Self> {
        let mut result = self.clone();
        if result.path.len() >= MAX_PATH {
            return None;
        }
        result.path.push(0);
        Some(result)
    }

    pub fn through(&self, argument: &Place) -> Result<Self, Status> {
        let (&first, rest) = self.path.split_first().ok_or(Status::Unavailable)?;
        let mut result = argument.shift(first).ok_or(Status::Limit)?;
        result.path.extend_from_slice(rest);
        if result.path.len() > MAX_PATH {
            return Err(Status::Limit);
        }
        Ok(result)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(super) struct Access {
    pub place: Place,
    pub width: usize,
    pub guards: Vec<Guard>,
    /// A controlling path could not be qualified at this memory state.
    #[serde(default, skip_serializing_if = "is_false")]
    pub uncertain: bool,
}

fn is_false(value: &bool) -> bool {
    !value
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(super) struct Selector {
    pub place: Place,
    pub width: usize,
    pub loaded: bool,
}

impl Selector {
    pub fn overlaps(&self, access: &Access, pointer_width: usize) -> bool {
        if !self.loaded || self.place.root != access.place.root {
            return false;
        }
        let Some((&offset, prefix)) = self.place.path.split_last() else {
            return false;
        };
        if !access.place.path.starts_with(prefix) {
            return false;
        }
        let Some(path) = access.place.path.get(prefix.len()..) else {
            return false;
        };
        let Some(&other) = path.first() else {
            return false;
        };
        let width = if path.len() > 1 {
            pointer_width
        } else {
            access.width
        };
        (offset as i128) < other as i128 + width as i128
            && (other as i128) < offset as i128 + self.width as i128
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub(super) struct Guard {
    pub selector: Selector,
    pub values: BTreeSet<u64>,
    pub is_in: bool,
}

impl Guard {
    pub fn implied_by(&self, context: &[Self]) -> bool {
        context.iter().any(|known| {
            known.selector == self.selector
                && match (known.is_in, self.is_in) {
                    (true, true) => known.values.is_subset(&self.values),
                    (true, false) => known.values.is_disjoint(&self.values),
                    (false, false) => self.values.is_subset(&known.values),
                    (false, true) => false,
                }
        })
    }

    pub fn contradicts(&self, other: &Self) -> bool {
        self.selector == other.selector
            && match (self.is_in, other.is_in) {
                (true, true) => self.values.is_disjoint(&other.values),
                (true, false) => self.values.is_subset(&other.values),
                (false, true) => other.values.is_subset(&self.values),
                (false, false) => false,
            }
    }

    fn map(&self, place: Place, pointer_width: usize) -> Self {
        let mut result = self.clone();
        result.selector.place = place;
        // A returned/passed loaded pointer is the same word as its source load.
        if !result.selector.loaded
            && result.selector.width == pointer_width
            && result.selector.place.path.len() > 1
            && result.selector.place.path.last() == Some(&0)
        {
            result.selector.place.path.pop();
            result.selector.loaded = true;
        }
        result
    }
}

impl fmt::Display for Guard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}-byte {} of {} {} {} {{{}}}",
            self.selector.width,
            if self.selector.loaded {
                "load"
            } else {
                "value"
            },
            self.selector.place.root,
            self.selector
                .place
                .path
                .iter()
                .map(|offset| format!("{offset:+#x}"))
                .collect::<Vec<_>>()
                .join(" -> "),
            if self.is_in { "in" } else { "not in" },
            self.values
                .iter()
                .map(|value| format!("{value:#x}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub(super) fn guards(mut values: Vec<Guard>) -> Result<Option<Vec<Guard>>, Status> {
    values.sort();
    values.dedup();
    if values.len() > MAX_GUARDS {
        return Err(Status::Limit);
    }
    let mut result: Vec<Guard> = Vec::new();
    for value in values {
        if let Some(previous) = result
            .last_mut()
            .filter(|previous| previous.selector == value.selector)
        {
            match (previous.is_in, value.is_in) {
                (true, true) => previous.values.retain(|v| value.values.contains(v)),
                (true, false) => previous.values.retain(|v| !value.values.contains(v)),
                (false, true) => {
                    let excluded = &previous.values;
                    let mut value = value;
                    value.values.retain(|v| !excluded.contains(v));
                    *previous = value;
                }
                (false, false) => previous.values.extend(value.values),
            }
        } else {
            result.push(value);
        }
        if result
            .last()
            .is_some_and(|guard| guard.is_in && guard.values.is_empty())
        {
            return Ok(None);
        }
    }
    result.retain(|guard| guard.is_in || !guard.values.is_empty());
    Ok(Some(result))
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Call {
    pub address: u64,
    pub target: Option<Key>,
    pub adjusted: bool,
    pub declarations: Vec<String>,
    pub parameters: Vec<Option<Place>>,
    /// Repaired call arguments mapped to the callee's original parameter slots.
    #[serde(default)]
    pub parameter_order: Vec<usize>,
    pub output: Option<u64>,
    pub guards: Vec<Guard>,
    #[serde(default, skip_serializing_if = "is_false")]
    pub uncertain: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Location {
    /// Variable identifier, byte offset within the value, and explicit byte width.
    pub pieces: Vec<(u64, i64, Option<u64>)>,
    pub indirect: bool,
    pub returned_pointer: Option<u64>,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Slot {
    pub width: u64,
    pub location: Option<Location>,
    #[serde(default)]
    pub integer: Option<bool>,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Contract {
    pub convention: Option<String>,
    pub parameters: Vec<Slot>,
    pub result: Slot,
    #[serde(default)]
    pub stack_adjustment: i64,
    #[serde(default)]
    pub can_return: bool,
    #[serde(default)]
    pub pure: bool,
    #[serde(default)]
    pub variadic: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Wire {
    pub input: u32,
    pub output: u32,
    pub parameter: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Input {
    pub key: Key,
    pub parameters: Vec<u64>,
    pub contract: Contract,
    #[serde(default)]
    pub wire: Option<Wire>,
    pub informed: bool,
    pub register_exits: BTreeMap<u32, Option<u32>>,
    pub overlaid: BTreeMap<u64, u64>,
    pub pointer_width: usize,
    pub fields: BTreeSet<Access>,
    pub calls: Vec<Call>,
    pub returns: Vec<Option<Place>>,
    pub opaque_memory: bool,
    pub sources: Vec<std::ops::Range<u64>>,
    pub readonly: Vec<std::ops::Range<u64>>,
    pub little_endian: bool,
    pub sites: BTreeMap<u64, Vec<Guard>>,
    pub retained_loads: BTreeSet<Selector>,
    pub digest: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct Layout {
    pub function: Key,
    pub fields: BTreeSet<Access>,
    pub return_alias: Option<Place>,
    pub aliases: BTreeMap<u64, Place>,
}

/// A context reuses a function's observations with separately bound call edges.
pub(super) struct Variant {
    pub input: usize,
    pub calls: Vec<(usize, Call)>,
}

pub(super) struct Field {
    pub offset: u64,
    pub width: usize,
    pub children: Vec<Field>,
}

impl Layout {
    pub fn fields_for(&self, place: &Place, pointer_width: usize) -> Option<Vec<Field>> {
        self.fields_in(place, pointer_width, &[], &BTreeSet::new())
    }

    pub fn context(&self, context: &[Guard], pointer_width: usize) -> Result<Vec<Guard>, Status> {
        context
            .iter()
            .map(|guard| Ok(guard.map(self.resolve(&guard.selector.place)?, pointer_width)))
            .collect()
    }

    pub fn fields_in(
        &self,
        place: &Place,
        pointer_width: usize,
        context: &[Guard],
        retained: &BTreeSet<Selector>,
    ) -> Option<Vec<Field>> {
        let context = guards(self.context(context, pointer_width).ok()?).ok()??;
        let retained: Vec<_> = retained
            .iter()
            .map(|selector| {
                let mut selector = selector.clone();
                selector.place = self.resolve(&selector.place).ok()?;
                Some(selector)
            })
            .collect::<Option<_>>()?;
        let base = self.resolve(place).ok()?;
        let (&last, prefix) = base.path.split_last()?;
        let mut accesses = Vec::new();
        for access in &self.fields {
            if retained
                .iter()
                .any(|selector| selector.overlaps(access, pointer_width))
            {
                continue;
            }
            if access
                .guards
                .iter()
                .any(|guard| context.iter().any(|other| guard.contradicts(other)))
            {
                continue;
            }
            let (path, width) = if access.uncertain && access.place.path.len() > 1 {
                (&access.place.path[..1], pointer_width)
            } else {
                (access.place.path.as_slice(), access.width)
            };
            if access.place.root != base.root || !path.starts_with(prefix) {
                continue;
            }
            let Some(suffix) = path.get(prefix.len()..) else {
                continue;
            };
            let mut path = suffix.to_vec();
            let Some(offset) = path.first_mut() else {
                continue;
            };
            *offset = offset.checked_sub(last)?;
            if *offset < 0 {
                if last == 0 {
                    return None;
                }
                continue;
            }
            if path.len() > 1 && !access.guards.iter().all(|guard| guard.implied_by(&context)) {
                // Conditional dereferences establish pointee fields only on their paths.
                path.truncate(1);
                accesses.push((path, pointer_width));
            } else {
                accesses.push((path, width));
            }
        }
        fields(&accesses, pointer_width)
    }

    pub fn resolve(&self, place: &Place) -> Result<Place, Status> {
        resolve(place, &self.aliases)
    }
}

fn fields(accesses: &[(Vec<i64>, usize)], pointer_width: usize) -> Option<Vec<Field>> {
    if accesses.is_empty() {
        return None;
    }
    let mut direct = BTreeMap::new();
    let mut nested: BTreeMap<u64, Vec<(Vec<i64>, usize)>> = BTreeMap::new();
    for (path, width) in accesses {
        let (&offset, rest) = path.split_first()?;
        let offset = u64::try_from(offset).ok()?;
        let size = if rest.is_empty() {
            *width
        } else {
            pointer_width
        };
        if offset > MAX_OFFSET || ![1, 2, 4, 8, 16].contains(&size) {
            return None;
        }
        if direct.insert(offset, size).is_some_and(|old| old != size) {
            return None;
        }
        if !rest.is_empty() {
            nested
                .entry(offset)
                .or_default()
                .push((rest.to_vec(), *width));
        }
    }
    let mut result = Vec::new();
    let mut end = 0;
    for (offset, width) in direct {
        if offset < end {
            return None;
        }
        end = offset.checked_add(width as u64)?;
        let children = match nested.get(&offset) {
            Some(accesses) => fields(accesses, pointer_width)?,
            None => Vec::new(),
        };
        result.push(Field {
            offset,
            width,
            children,
        });
    }
    Some(result)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) enum Status {
    Complete,
    Limit,
    Cancelled,
    Unavailable,
    Unstable,
}

impl Status {
    pub fn label(self) -> &'static str {
        match self {
            Self::Complete => "Observed layouts recovered",
            Self::Limit => "Analysis limit reached; layouts withheld",
            Self::Cancelled => "Analysis cancelled; layouts withheld",
            Self::Unavailable => "Function analysis unavailable; layouts withheld",
            Self::Unstable => "Analysis did not stabilize; layouts withheld",
        }
    }
}

fn resolve(place: &Place, aliases: &BTreeMap<u64, Place>) -> Result<Place, Status> {
    let mut result = place.clone();
    for _ in 0..32 {
        let Root::Call(address) = &result.root else {
            return Ok(result);
        };
        let Some(alias) = aliases.get(address) else {
            return Ok(result);
        };
        result = result.through(alias)?;
    }
    Err(Status::Limit)
}

fn bind(place: &Place, call: &Call) -> Result<Option<Place>, Status> {
    let Root::Parameter(parameter) = place.root else {
        return Ok(None);
    };
    call.parameters
        .get(parameter)
        .and_then(Option::as_ref)
        .map(|argument| place.through(argument))
        .transpose()
}

fn unique_return(
    input: &Input,
    aliases: &BTreeMap<u64, Place>,
    writes: bool,
) -> Result<Option<Place>, Status> {
    let mut result = None;
    for place in &input.returns {
        let Some(place) = place else {
            return Ok(None);
        };
        let place = resolve(place, aliases)?;
        if !matches!(place.root, Root::Parameter(_)) || (writes && place.path.len() > 1) {
            return Ok(None);
        }
        if result.as_ref().is_some_and(|previous| *previous != place) {
            return Ok(None);
        }
        result = Some(place);
    }
    Ok(result)
}

/// Memory effects and aliases are separate: a raw argument alias survives writes,
/// while a returned load needs a proven read-only callee before projection.
pub(super) fn effects<'a>(
    inputs: impl IntoIterator<Item = &'a Input>,
    cancelled: &impl Fn() -> bool,
) -> Result<BTreeMap<Key, bool>, Status> {
    let inputs: Vec<_> = inputs.into_iter().collect();
    let variants = variants(inputs.iter().copied());
    let writes = variant_effects(&inputs, &variants, cancelled)?;
    Ok(inputs
        .iter()
        .zip(writes)
        .map(|(input, writes)| (input.key.clone(), writes))
        .collect())
}

fn variant_effects(
    inputs: &[&Input],
    variants: &[Variant],
    cancelled: &impl Fn() -> bool,
) -> Result<Vec<bool>, Status> {
    let mut writes = Vec::new();
    for variant in variants {
        let input = inputs.get(variant.input).ok_or(Status::Unavailable)?;
        let covered: BTreeSet<_> = variant.calls.iter().map(|(_, call)| call.address).collect();
        if variant
            .calls
            .iter()
            .any(|(target, _)| *target >= variants.len())
        {
            return Err(Status::Unavailable);
        }
        writes.push(
            input.opaque_memory
                || input
                    .calls
                    .iter()
                    .any(|call| call.adjusted || !covered.contains(&call.address)),
        );
    }
    let mut callers = vec![Vec::new(); variants.len()];
    for (index, variant) in variants.iter().enumerate() {
        for &(target, _) in &variant.calls {
            callers[target].push(index);
        }
    }
    let mut queue: VecDeque<_> = writes
        .iter()
        .enumerate()
        .filter_map(|(index, writes)| writes.then_some(index))
        .collect();
    while let Some(target) = queue.pop_front() {
        if cancelled() {
            return Err(Status::Cancelled);
        }
        for &index in &callers[target] {
            if !writes[index] {
                writes[index] = true;
                queue.push_back(index);
            }
        }
    }
    Ok(writes)
}

pub(super) fn variants<'a>(inputs: impl IntoIterator<Item = &'a Input>) -> Vec<Variant> {
    let inputs: Vec<_> = inputs.into_iter().collect();
    let by_key: BTreeMap<_, _> = inputs
        .iter()
        .enumerate()
        .map(|(index, input)| (&input.key, index))
        .collect();
    inputs
        .iter()
        .enumerate()
        .map(|(index, input)| Variant {
            input: index,
            calls: input
                .calls
                .iter()
                .filter_map(|call| {
                    let target = call.target.as_ref().filter(|_| !call.adjusted)?;
                    Some((*by_key.get(target)?, call.clone()))
                })
                .collect(),
        })
        .collect()
}

#[cfg(test)]
pub(super) fn solve(inputs: &[Input], cancelled: impl Fn() -> bool) -> Result<Vec<Layout>, Status> {
    solve_variants(inputs, &variants(inputs), cancelled)
}

pub(super) fn solve_variants(
    inputs: &[Input],
    variants: &[Variant],
    cancelled: impl Fn() -> bool,
) -> Result<Vec<Layout>, Status> {
    let writes = variant_effects(&inputs.iter().collect::<Vec<_>>(), variants, &cancelled)?;
    let mut layouts: Vec<_> = variants
        .iter()
        .enumerate()
        .map(|(index, variant)| {
            let input = inputs.get(variant.input).ok_or(Status::Unavailable)?;
            Ok(Layout {
                function: input.key.clone(),
                fields: input.fields.clone(),
                return_alias: unique_return(input, &BTreeMap::new(), writes[index])?,
                aliases: BTreeMap::new(),
            })
        })
        .collect::<Result<_, Status>>()?;
    let mut work = 1_000_000usize;
    for _ in 0..64 {
        if cancelled() {
            return Err(Status::Cancelled);
        }
        let mut next = Vec::new();
        for (index, variant) in variants.iter().enumerate() {
            let input = &inputs[variant.input];
            let mut output = Layout {
                function: input.key.clone(),
                fields: BTreeSet::new(),
                return_alias: None,
                aliases: BTreeMap::new(),
            };
            for &(target, ref call) in &variant.calls {
                let callee_variant = variants.get(target).ok_or(Status::Unavailable)?;
                let callee = &inputs[callee_variant.input];
                if (callee.parameters.len(), callee.pointer_width)
                    != (call.parameters.len(), input.pointer_width)
                {
                    continue;
                }
                if let Some(alias) = &layouts[target].return_alias
                    && let Some(alias) = bind(alias, call)?
                {
                    if !writes[index] || alias.path.len() == 1 {
                        output.aliases.insert(call.address, alias);
                    }
                }
            }
            let mut add =
                |place: &Place, width, context: &[Guard], uncertain| -> Result<(), Status> {
                    work = work.checked_sub(1).ok_or(Status::Limit)?;
                    if work % 1024 == 0 && cancelled() {
                        return Err(Status::Cancelled);
                    }
                    let place = output.resolve(place)?;
                    let Some(guards) = guards(output.context(context, input.pointer_width)?)?
                    else {
                        return Ok(());
                    };
                    output.fields.insert(Access {
                        place,
                        width,
                        guards,
                        uncertain,
                    });
                    if output.fields.len() > MAX_FIELDS {
                        return Err(Status::Limit);
                    }
                    Ok(())
                };
            for access in &input.fields {
                add(
                    &access.place,
                    access.width,
                    &access.guards,
                    access.uncertain,
                )?;
            }
            for &(target, ref call) in &variant.calls {
                let callee_variant = variants.get(target).ok_or(Status::Unavailable)?;
                let callee = &inputs[callee_variant.input];
                if (callee.parameters.len(), callee.pointer_width)
                    != (call.parameters.len(), input.pointer_width)
                {
                    continue;
                }
                for access in &layouts[target].fields {
                    if let Some(place) = bind(&access.place, call)? {
                        let readonly = !writes[index] && !writes[target];
                        if !readonly
                            && callee.retained_loads.iter().any(|selector| {
                                let Ok(place) = layouts[target].resolve(&selector.place) else {
                                    return true;
                                };
                                let mut selector = selector.clone();
                                selector.place = place;
                                access.place.path.len() > selector.place.path.len()
                                    && selector.overlaps(access, input.pointer_width)
                            })
                        {
                            continue;
                        }
                        if !readonly && !access.guards.is_empty() {
                            continue;
                        }
                        let mut context = if readonly {
                            call.guards.clone()
                        } else {
                            Vec::new()
                        };
                        let mut bound = true;
                        for guard in &access.guards {
                            if let Some(place) = bind(&guard.selector.place, call)? {
                                context.push(guard.map(place, input.pointer_width));
                            } else {
                                bound = false;
                                break;
                            }
                        }
                        if bound {
                            add(
                                &place,
                                access.width,
                                &context,
                                access.uncertain || call.uncertain,
                            )?;
                        }
                    }
                }
            }
            output.return_alias = unique_return(input, &output.aliases, writes[index])?;
            next.push(output);
        }
        if next == layouts {
            if cancelled() {
                return Err(Status::Cancelled);
            }
            return Ok(next);
        }
        layouts = next;
    }
    Err(Status::Limit)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn flat(layout: &Layout, parameter: usize) -> Option<Vec<(u64, usize)>> {
        Some(
            layout
                .fields_for(&Place::parameter(parameter), 8)?
                .iter()
                .map(|field| (field.offset, field.width))
                .collect(),
        )
    }

    fn input(address: u64, count: usize, fields: &[(usize, i64, usize)]) -> Input {
        Input {
            key: Key {
                address,
                platform: "test".into(),
            },
            parameters: (0..count as u64).collect(),
            contract: Contract::default(),
            wire: None,
            informed: false,
            register_exits: BTreeMap::new(),
            overlaid: BTreeMap::new(),
            pointer_width: 8,
            fields: fields
                .iter()
                .map(|&(parameter, offset, width)| Access {
                    place: Place::parameter(parameter).shift(offset).unwrap(),
                    width,
                    uncertain: false,
                    guards: Vec::new(),
                })
                .collect(),
            calls: Vec::new(),
            returns: Vec::new(),
            opaque_memory: false,
            sources: Vec::new(),
            readonly: Vec::new(),
            little_endian: true,
            sites: BTreeMap::new(),
            retained_loads: BTreeSet::new(),
            digest: String::new(),
        }
    }

    #[test]
    fn translates_callee_arguments_without_merging_parameters() {
        let callee = input(2, 2, &[(0, 16, 4), (1, 8, 8)]);
        let mut caller = input(1, 2, &[]);
        caller.calls.push(Call {
            address: 1,
            parameter_order: Vec::new(),
            output: None,
            uncertain: false,
            guards: Vec::new(),
            target: Some(callee.key.clone()),
            adjusted: false,
            declarations: Vec::new(),
            parameters: vec![
                Some(Place::parameter(1).shift(0).unwrap()),
                Some(Place::parameter(0).shift(8).unwrap()),
            ],
        });
        let layouts = solve(&[caller, callee], || false).unwrap();
        assert_eq!(flat(&layouts[0], 0), Some(vec![(16, 8)]));
        assert_eq!(flat(&layouts[0], 1), Some(vec![(16, 4)]));
    }

    #[test]
    fn requires_compatible_parameter_count_and_pointer_width() {
        let mut callee = input(2, 1, &[(0, 8, 8)]);
        let mut caller = input(1, 1, &[]);
        caller.calls.push(Call {
            address: 1,
            parameter_order: Vec::new(),
            output: None,
            uncertain: false,
            guards: Vec::new(),
            target: Some(callee.key.clone()),
            adjusted: false,
            declarations: Vec::new(),
            parameters: Vec::new(),
        });
        assert!(
            solve(&[caller.clone(), callee.clone()], || false).unwrap()[0]
                .fields
                .is_empty()
        );
        caller.calls[0]
            .parameters
            .push(Some(Place::parameter(0).shift(0).unwrap()));
        callee.pointer_width = 4;
        assert!(
            solve(&[caller, callee], || false).unwrap()[0]
                .fields
                .is_empty()
        );
    }

    #[test]
    fn stops_recursive_offset_growth_and_honors_cancellation() {
        let mut recursive = input(1, 1, &[(0, 8, 8)]);
        recursive.calls.push(Call {
            address: 1,
            parameter_order: Vec::new(),
            output: None,
            uncertain: false,
            guards: Vec::new(),
            target: Some(recursive.key.clone()),
            adjusted: false,
            declarations: Vec::new(),
            parameters: vec![Some(Place::parameter(0).shift(8).unwrap())],
        });
        assert_eq!(solve(&[recursive.clone()], || false), Err(Status::Limit));
        let checks = std::cell::Cell::new(0);
        assert_eq!(
            solve(&[recursive], || {
                checks.set(checks.get() + 1);
                checks.get() >= 3
            }),
            Err(Status::Cancelled)
        );
    }

    #[test]
    fn exact_capacity_and_duplicate_accesses_are_valid() {
        let mut recursive = input(1, 1, &[]);
        recursive
            .fields
            .extend((0..MAX_FIELDS).map(|offset| Access {
                place: Place::parameter(0).shift((2 * offset) as i64).unwrap(),
                width: 1,
                uncertain: false,
                guards: Vec::new(),
            }));
        recursive.calls.push(Call {
            address: 1,
            parameter_order: Vec::new(),
            output: None,
            uncertain: false,
            guards: Vec::new(),
            target: Some(recursive.key.clone()),
            adjusted: false,
            declarations: Vec::new(),
            parameters: vec![Some(Place::parameter(0).shift(0).unwrap())],
        });
        assert_eq!(
            solve(&[recursive], || false).unwrap()[0].fields.len(),
            MAX_FIELDS
        );
    }

    #[test]
    fn overlapping_widths_and_negative_offsets_do_not_form_a_record() {
        for fields in [
            &[(0, 0, 8), (0, 4, 4)][..],
            &[(0, -8, 8)],
            &[(0, 8, 4), (0, 8, 8)],
        ] {
            let value = input(1, 1, fields);
            let layout = Layout {
                function: value.key,
                fields: value.fields,
                return_alias: None,
                aliases: BTreeMap::new(),
            };
            assert_eq!(flat(&layout, 0), None);
        }
    }

    fn call(target: &Input, arguments: Vec<Option<Place>>) -> Call {
        Call {
            address: 10,
            parameter_order: Vec::new(),
            target: Some(target.key.clone()),
            adjusted: false,
            declarations: Vec::new(),
            parameters: arguments,
            output: Some(99),
            uncertain: false,
            guards: Vec::new(),
        }
    }

    #[test]
    fn unqualified_conditions_keep_nested_slots_opaque() {
        let mut value = input(1, 1, &[(0, 8, 8)]);
        value.fields.insert(Access {
            place: Place {
                root: Root::Parameter(0),
                path: vec![8, 8],
            },
            width: 8,
            guards: Vec::new(),
            uncertain: true,
        });
        let layout = solve(&[value], || false).unwrap().remove(0);
        let fields = layout.fields_for(&Place::parameter(0), 8).unwrap();
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].offset, 8);
        assert!(fields[0].children.is_empty());
        assert!(
            layout
                .fields_for(
                    &Place {
                        root: Root::Parameter(0),
                        path: vec![8, 0]
                    },
                    8
                )
                .is_none()
        );
    }

    #[test]
    fn unqualified_call_paths_do_not_project_pointer_roles() {
        let callee = input(2, 1, &[(0, 8, 8)]);
        let mut caller = input(1, 1, &[]);
        let mut edge = call(
            &callee,
            vec![Some(Place {
                root: Root::Parameter(0),
                path: vec![8, 0],
            })],
        );
        edge.uncertain = true;
        caller.calls.push(edge);
        let layouts = solve(&[caller, callee], || false).unwrap();
        let fields = layouts[0].fields_for(&Place::parameter(0), 8).unwrap();
        assert_eq!(fields[0].offset, 8);
        assert!(fields[0].children.is_empty());
    }

    #[test]
    fn projects_bound_contexts_without_specializing_the_shared_function() {
        let mut root = input(1, 2, &[]);
        let mut alpha = input(2, 1, &[]);
        let mut beta = input(3, 1, &[]);
        let shared = input(4, 1, &[]);
        let first = input(5, 1, &[(0, 8, 8)]);
        let second = input(6, 1, &[(0, 16, 8)]);
        root.calls
            .push(call(&alpha, vec![Some(Place::parameter(0))]));
        root.calls
            .push(call(&beta, vec![Some(Place::parameter(1))]));
        alpha
            .calls
            .push(call(&shared, vec![Some(Place::parameter(0))]));
        beta.calls
            .push(call(&shared, vec![Some(Place::parameter(0))]));
        let inputs = [root, alpha, beta, shared, first, second];
        let mut graph = variants(&inputs);
        graph.push(Variant {
            input: 3,
            calls: vec![(4, call(&inputs[4], vec![Some(Place::parameter(0))]))],
        });
        graph.push(Variant {
            input: 3,
            calls: vec![(5, call(&inputs[5], vec![Some(Place::parameter(0))]))],
        });
        graph[1].calls[0].0 = 6;
        graph[2].calls[0].0 = 7;
        let layouts = solve_variants(&inputs, &graph, || false).unwrap();
        assert_eq!(flat(&layouts[0], 0), Some(vec![(8, 8)]));
        assert_eq!(flat(&layouts[0], 1), Some(vec![(16, 8)]));
        assert_eq!(flat(&layouts[1], 0), Some(vec![(8, 8)]));
        assert_eq!(flat(&layouts[2], 0), Some(vec![(16, 8)]));
        assert!(layouts[3].fields.is_empty());
        assert_eq!(flat(&layouts[6], 0), Some(vec![(8, 8)]));
        assert_eq!(flat(&layouts[7], 0), Some(vec![(16, 8)]));
    }

    #[test]
    fn composes_nested_offsets_and_rejects_conflicting_pointer_slots() {
        let mut callee = input(2, 1, &[]);
        callee.fields.insert(Access {
            place: Place {
                root: Root::Parameter(0),
                path: vec![8, 16],
            },
            width: 4,
            uncertain: false,
            guards: Vec::new(),
        });
        let mut caller = input(1, 2, &[]);
        caller
            .calls
            .push(call(&callee, vec![Place::parameter(1).shift(24)]));
        let layouts = solve(&[caller.clone(), callee.clone()], || false).unwrap();
        let fields = layouts[0].fields_for(&Place::parameter(1), 8).unwrap();
        assert_eq!((fields[0].offset, fields[0].width), (32, 8));
        assert_eq!(
            (fields[0].children[0].offset, fields[0].children[0].width),
            (16, 4)
        );
        caller.fields.insert(Access {
            place: Place::parameter(1).shift(32).unwrap(),
            width: 4,
            uncertain: false,
            guards: Vec::new(),
        });
        assert!(
            solve(&[caller, callee], || false).unwrap()[0]
                .fields_for(&Place::parameter(1), 8)
                .is_none()
        );
    }

    #[test]
    fn return_alias_translates_fields_and_keeps_the_result_view() {
        let mut callee = input(2, 1, &[]);
        callee.returns.push(Place::parameter(0).shift(8));
        let mut caller = input(1, 1, &[]);
        caller
            .calls
            .push(call(&callee, vec![Some(Place::parameter(0))]));
        caller.fields.insert(Access {
            place: Place::call(10).shift(4).unwrap(),
            width: 4,
            uncertain: false,
            guards: Vec::new(),
        });
        let layouts = solve(&[caller, callee], || false).unwrap();
        assert_eq!(flat(&layouts[0], 0), Some(vec![(12, 4)]));
        assert_eq!(
            layouts[0].fields_for(&Place::call(10), 8).unwrap()[0].offset,
            4
        );
    }

    #[test]
    fn loaded_return_alias_requires_readonly_callee_and_caller() {
        for (callee_writes, caller_writes) in [(false, false), (true, false), (false, true)] {
            let mut callee = input(2, 1, &[(0, 8, 8)]);
            callee
                .returns
                .push(Place::parameter(0).shift(8).unwrap().load());
            callee.opaque_memory = callee_writes;
            let mut caller = input(1, 1, &[]);
            caller.opaque_memory = caller_writes;
            caller
                .calls
                .push(call(&callee, vec![Some(Place::parameter(0))]));
            caller.fields.insert(Access {
                place: Place::call(10).shift(16).unwrap(),
                width: 4,
                uncertain: false,
                guards: Vec::new(),
            });
            let layouts = solve(&[caller, callee], || false).unwrap();
            let fields = layouts[0].fields_for(&Place::parameter(0), 8).unwrap();
            assert_eq!(
                !fields[0].children.is_empty(),
                !callee_writes && !caller_writes
            );
            assert_eq!(
                layouts[0].fields_for(&Place::call(10), 8).unwrap()[0].offset,
                16
            );
        }
    }

    #[test]
    fn ambiguous_returns_and_call_overrides_keep_evidence_local() {
        for adjusted in [false, true] {
            let mut callee = input(2, 2, &[]);
            callee.returns = if adjusted {
                vec![Some(Place::parameter(0))]
            } else {
                vec![Some(Place::parameter(0)), Some(Place::parameter(1))]
            };
            let mut caller = input(1, 2, &[]);
            let mut site = call(
                &callee,
                vec![Some(Place::parameter(0)), Some(Place::parameter(1))],
            );
            site.adjusted = adjusted;
            caller.calls.push(site);
            caller.fields.insert(Access {
                place: Place::call(10).shift(8).unwrap(),
                width: 8,
                uncertain: false,
                guards: Vec::new(),
            });
            let layouts = solve(&[caller, callee], || false).unwrap();
            assert_eq!(flat(&layouts[0], 0), None);
            assert_eq!(flat(&layouts[0], 1), None);
            assert!(layouts[0].fields_for(&Place::call(10), 8).is_some());
        }
    }

    #[test]
    fn transitive_writes_block_loaded_aliases_but_not_raw_arguments() {
        let mut writer = input(3, 0, &[]);
        writer.opaque_memory = true;
        for loaded in [false, true] {
            let mut callee = input(2, 1, &[]);
            callee.calls.push(call(&writer, Vec::new()));
            callee.returns.push(if loaded {
                Place::parameter(0).load()
            } else {
                Some(Place::parameter(0))
            });
            let layouts = solve(&[callee, writer.clone()], || false).unwrap();
            assert_eq!(layouts[0].return_alias.is_some(), !loaded);
        }
    }

    #[test]
    fn recursive_pointer_growth_hits_the_path_bound() {
        let mut recursive = input(1, 1, &[(0, 8, 8)]);
        let mut site = call(
            &recursive,
            vec![Place::parameter(0).shift(8).unwrap().load()],
        );
        site.target = Some(recursive.key.clone());
        recursive.calls.push(site);
        assert_eq!(solve(&[recursive], || false), Err(Status::Limit));
    }

    fn condition(parameter: usize, value: u64, is_in: bool) -> Guard {
        Guard {
            selector: Selector {
                place: Place::parameter(parameter),
                width: 1,
                loaded: true,
            },
            values: BTreeSet::from([value]),
            is_in,
        }
    }

    #[test]
    fn selects_conditional_widths_without_inventing_a_global_union() {
        let mut function = input(1, 1, &[]);
        for (value, width) in [(1, 8), (2, 4)] {
            function.fields.insert(Access {
                place: Place::parameter(0).shift(8).unwrap(),
                width,
                uncertain: false,
                guards: vec![condition(0, value, true)],
            });
        }
        let result = solve(&[function], || false).unwrap();
        assert!(result[0].fields_for(&Place::parameter(0), 8).is_none());
        for (value, width) in [(1, 8), (2, 4)] {
            let fields = result[0]
                .fields_in(
                    &Place::parameter(0),
                    8,
                    &[condition(0, value, true)],
                    &BTreeSet::new(),
                )
                .unwrap();
            assert_eq!((fields[0].offset, fields[0].width), (8, width));
        }
        assert!(
            result[0]
                .fields_in(
                    &Place::parameter(0),
                    8,
                    &[condition(0, 3, true)],
                    &BTreeSet::new()
                )
                .is_none()
        );
    }

    #[test]
    fn translates_guarded_calls_and_retains_callsite_conditions() {
        let mut callee = input(2, 1, &[(0, 8, 4)]);
        callee.fields = callee
            .fields
            .into_iter()
            .map(|mut access| {
                access.guards = vec![condition(0, 2, true)];
                access
            })
            .collect();
        let mut caller = input(1, 2, &[]);
        let mut site = call(&callee, vec![Place::parameter(1).shift(16)]);
        site.guards = vec![condition(0, 7, true)];
        caller.calls.push(site);
        let result = solve(&[caller, callee], || false).unwrap();
        let observed = result[0].fields.iter().next().unwrap();
        assert_eq!(observed.place, Place::parameter(1).shift(24).unwrap());
        assert!(observed.guards.contains(&condition(0, 7, true)));
        let mut translated = condition(1, 2, true);
        translated.selector.place = translated.selector.place.shift(16).unwrap();
        assert!(observed.guards.contains(&translated));
    }

    #[test]
    fn mutable_calls_do_not_project_conditional_memory_facts() {
        for (caller_writes, callee_writes) in [(true, false), (false, true)] {
            let mut callee = input(2, 1, &[]);
            callee.opaque_memory = callee_writes;
            callee.fields.insert(Access {
                place: Place::parameter(0).shift(8).unwrap(),
                width: 8,
                uncertain: false,
                guards: vec![condition(0, 1, true)],
            });
            let mut caller = input(1, 1, &[]);
            caller.opaque_memory = caller_writes;
            caller
                .calls
                .push(call(&callee, vec![Some(Place::parameter(0))]));
            let result = solve(&[caller, callee], || false).unwrap();
            assert!(result[0].fields.is_empty());
            assert_eq!(result[1].fields.len(), 1);
        }
    }

    #[test]
    fn applies_the_intersection_of_path_conditions() {
        let mut function = input(1, 1, &[]);
        function.fields.insert(Access {
            place: Place::parameter(0)
                .shift(8)
                .unwrap()
                .load()
                .unwrap()
                .shift(8)
                .unwrap(),
            width: 4,
            guards: vec![condition(0, 1, true)],
            uncertain: false,
        });
        let mut left = condition(0, 0, true);
        left.values.insert(1);
        let mut right = condition(0, 1, true);
        right.values.insert(2);
        let layouts = solve(&[function], || false).unwrap();
        let fields = layouts[0]
            .fields_in(&Place::parameter(0), 8, &[left, right], &BTreeSet::new())
            .unwrap();
        assert_eq!(fields[0].children[0].offset, 8);
        assert_eq!(fields[0].children[0].width, 4);
    }

    #[test]
    fn normalized_guards_preserve_every_membership_combination() {
        for left in 0..16 {
            for right in 0..16 {
                let inputs: Vec<_> = [left, right]
                    .into_iter()
                    .map(|mask| {
                        let mut guard = condition(0, 0, mask & 8 == 0);
                        guard.values = (0..3).filter(|value| mask & (1 << value) != 0).collect();
                        guard
                    })
                    .collect();
                let normalized = guards(inputs.clone()).unwrap();
                assert!(normalized.as_ref().is_none_or(|guards| guards.len() <= 1));
                for value in 0..4 {
                    let expected = inputs
                        .iter()
                        .all(|guard| guard.is_in == guard.values.contains(&value));
                    let actual = normalized.as_ref().is_some_and(|guards| {
                        guards
                            .iter()
                            .all(|guard| guard.is_in == guard.values.contains(&value))
                    });
                    assert_eq!(actual, expected, "{left}/{right}: {value}");
                }
            }
        }
    }

    #[test]
    fn shared_cases_preserve_sets_and_guard_capacity_is_explicit() {
        let mut shared = condition(0, 1, true);
        shared.values.insert(2);
        assert!(!shared.contradicts(&condition(0, 2, true)));
        assert!(shared.contradicts(&condition(0, 3, true)));
        assert!(!shared.contradicts(&condition(0, 1, false)));
        let mut excluded = shared.clone();
        excluded.is_in = false;
        assert!(shared.contradicts(&excluded));
        assert_eq!(guards(vec![shared, excluded]).unwrap(), None);
        let context: Vec<_> = (0..MAX_GUARDS)
            .map(|index| condition(index, 1, true))
            .collect();
        assert_eq!(guards(context.clone()).unwrap(), Some(context.clone()));
        assert_eq!(
            guards([context, vec![condition(MAX_GUARDS, 1, true)]].concat()),
            Err(Status::Limit)
        );
    }

    #[test]
    fn normalizes_only_a_complete_loaded_pointer_word() {
        let place = Place::parameter(0).shift(8).unwrap().load().unwrap();
        let mut word = condition(0, 0, false);
        word.selector.loaded = false;
        let narrow = word.map(place.clone(), 8);
        assert!(!narrow.selector.loaded);
        assert_eq!(narrow.selector.place.path, [8, 0]);
        word.selector.width = 8;
        let pointer = word.map(place, 8);
        assert!(pointer.selector.loaded);
        assert_eq!(pointer.selector.place.path, [8]);
    }

    #[test]
    fn copied_fields_can_stay_untyped_while_other_fields_are_recovered() {
        let function = input(1, 1, &[(0, 0, 1), (0, 8, 8)]);
        let layout = solve(&[function], || false).unwrap().remove(0);
        let retained = BTreeSet::from([Selector {
            place: Place::parameter(0),
            width: 1,
            loaded: true,
        }]);
        let fields = layout
            .fields_in(&Place::parameter(0), 8, &[], &retained)
            .unwrap();
        assert_eq!((fields[0].offset, fields[0].width, fields.len()), (8, 8, 1));
    }

    #[test]
    fn protecting_a_copied_pointer_also_excludes_its_implicit_nested_field() {
        let mut function = input(1, 1, &[(0, 24, 8)]);
        function.fields.insert(Access {
            place: Place {
                root: Root::Parameter(0),
                path: vec![8, 16],
            },
            width: 8,
            uncertain: false,
            guards: Vec::new(),
        });
        let layout = solve(&[function], || false).unwrap().remove(0);
        let retained = BTreeSet::from([Selector {
            place: Place::parameter(0).shift(8).unwrap(),
            width: 8,
            loaded: true,
        }]);
        let fields = layout
            .fields_in(&Place::parameter(0), 8, &[], &retained)
            .unwrap();
        assert_eq!((fields[0].offset, fields.len()), (24, 1));
    }

    #[test]
    fn a_replaced_pointer_does_not_export_its_historical_pointee_layout() {
        let mut callee = input(2, 1, &[(0, 8, 8)]);
        callee.opaque_memory = true;
        callee.retained_loads.insert(Selector {
            place: Place::parameter(0).shift(8).unwrap(),
            width: 8,
            loaded: true,
        });
        callee.fields.insert(Access {
            place: Place {
                root: Root::Parameter(0),
                path: vec![8, 16],
            },
            width: 4,
            uncertain: false,
            guards: Vec::new(),
        });
        let mut caller = input(1, 1, &[]);
        caller
            .calls
            .push(call(&callee, vec![Some(Place::parameter(0))]));
        let result = solve(&[caller, callee], || false).unwrap();
        let fields = result[0].fields_for(&Place::parameter(0), 8).unwrap();
        assert_eq!(
            (fields[0].offset, fields[0].width, fields[0].children.len()),
            (8, 8, 0)
        );
    }

    #[test]
    fn conditional_pointees_do_not_become_unconditional_pointer_fields() {
        let mut function = input(1, 1, &[(0, 8, 8)]);
        function.fields.insert(Access {
            place: Place {
                root: Root::Parameter(0),
                path: vec![8, 8],
            },
            width: 8,
            uncertain: false,
            guards: vec![condition(0, 1, true)],
        });
        let layout = solve(&[function], || false).unwrap().remove(0);
        assert!(
            layout.fields_for(&Place::parameter(0), 8).unwrap()[0]
                .children
                .is_empty()
        );
        let selected = layout
            .fields_in(
                &Place::parameter(0),
                8,
                &[condition(0, 1, true)],
                &BTreeSet::new(),
            )
            .unwrap();
        assert_eq!(
            (
                selected[0].children[0].offset,
                selected[0].children[0].width
            ),
            (8, 8)
        );
        let excluded = layout
            .fields_in(
                &Place::parameter(0),
                8,
                &[condition(0, 1, false)],
                &BTreeSet::new(),
            )
            .unwrap();
        assert!(excluded[0].children.is_empty());
    }
}
