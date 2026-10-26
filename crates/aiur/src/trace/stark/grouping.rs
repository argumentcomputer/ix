//! Physical groups are compiled by Lean; execution and memo keys retain the
//! original callable identities. Only row placement and lookup superposition
//! change. See Aiur.Optimized.Grouping for the selector and silence arguments.
use super::*;
use crate::trace::{GroupMember, GroupWrite};

pub(super) struct Placement {
  pub grouped: bool,
  pub circuit: usize,
  pub columns: Vec<usize>,
  pub selector: usize,
  pub writes: Vec<GroupWrite>,
}

impl Placement {
  pub fn finish(&self, row: &mut [Val], count: u64) {
    row[self.selector] = Val::ONE;
    for write in &self.writes {
      row[write.column] = write.value.eval(row, NativeField::<Val>::default());
    }
    *row.last_mut().unwrap() = Val::from_u64(count);
  }
}

pub(super) fn build<B: WitnessField>(
  plan: &TracePlan<'_, B>,
  rom: &rom::Rom,
  inputs: &mut Vec<CircuitInputs<Val>>,
  names: &mut Vec<String>,
) -> Result<Vec<Placement>, String> {
  let mut grouped = FxHashMap::default();
  let mut placements: Vec<Option<Placement>> =
    (0..plan.artifact.chips.len()).map(|_| None).collect();
  for (gi, group) in plan.artifact.groups.iter().enumerate() {
    if group.members.len() < 2 || group.width >= u32::MAX as usize {
      return Err("invalid function group size".into());
    }
    for member in &group.members {
      if grouped.insert(member.name.as_str(), gi).is_some() {
        return Err("function appears in multiple groups".into());
      }
    }
  }
  let mut emitted = vec![false; plan.artifact.groups.len()];
  for (ci, chip) in plan.artifact.chips.iter().enumerate() {
    if let Some(&gi) = grouped.get(chip.name.as_str()) {
      if emitted[gi] {
        continue;
      }
      emitted[gi] = true;
      let group = &plan.artifact.groups[gi];
      for member in &group.members {
        let original = plan
          .artifact
          .chips
          .iter()
          .position(|c| c.name == member.name)
          .ok_or("unknown grouped function chip")?;
        let source = &plan.artifact.chips[original];
        validate_member(plan, group.width, member, source)?;
        placements[original] = Some(Placement {
          grouped: true,
          circuit: inputs.len(),
          columns: member.columns.clone(),
          selector: member.selector,
          writes: member.writes.clone(),
        });
      }
      for p in group
        .constraints
        .iter()
        .chain(&group.receive)
        .chain(std::iter::once(&group.activation))
        .chain(
          group
            .sends
            .iter()
            .flat_map(|s| std::iter::once(&s.enable).chain(&s.args)),
        )
      {
        p.validate(group.width, plan.program.field)?;
      }
      let mut constraints: Vec<_> =
        group.constraints.iter().map(lower).collect();
      constraints
        .push((constant(1) - lower(&group.activation)) * main_var(group.width));
      let mut lookups = vec![Lookup::pull(
        main_var(group.width),
        group.receive.iter().map(lower).collect(),
      )];
      lookups.extend(group.sends.iter().map(|s| {
        Lookup::push(lower(&s.enable), s.args.iter().map(lower).collect())
      }));
      inputs.push(CircuitInputs {
        main_width: group.width + 1,
        constraints,
        lookups,
        ..Default::default()
      });
      names.push(group.name.clone());
      continue;
    }
    if chip.width >= u32::MAX as usize {
      return Err("too many circuit columns".into());
    }
    placements[ci] = Some(Placement {
      grouped: false,
      circuit: inputs.len(),
      columns: (0..chip.width).collect(),
      selector: chip.activation,
      writes: vec![],
    });
    let mut args =
      vec![constant(CALL), constant(plan.callables[&chip.name] as u64)];
    args.extend(chip.inputs.iter().map(|&i| main_var(i)));
    args.extend(chip.output.iter().map(lower));
    let mut lookups = vec![Lookup::pull(main_var(chip.width), args)];
    for send in &chip.sends {
      let mut args =
        vec![constant(CALL), constant(plan.callables[&send.channel] as u64)];
      args.extend(send.args.iter().map(lower));
      args.extend(send.result.iter().map(|&i| main_var(i)));
      lookups.push(Lookup::push(lower(&send.enable), args));
    }
    for cell in &chip.memory {
      lookups.push(rom.access(cell)?);
    }
    inputs.push(CircuitInputs {
      main_width: chip.width + 1,
      constraints: chip
        .constraints
        .iter()
        .map(lower)
        .chain([
          (constant(1) - main_var(chip.activation)) * main_var(chip.width)
        ])
        .collect(),
      lookups,
      ..Default::default()
    });
    names.push(chip.name.clone());
  }
  if emitted.contains(&false) {
    return Err("unknown function group members".into());
  }
  placements
    .into_iter()
    .map(|p| p.ok_or_else(|| "missing function placement".into()))
    .collect()
}

fn validate_member<B: WitnessField>(
  plan: &TracePlan<'_, B>,
  width: usize,
  member: &GroupMember,
  source: &crate::trace::Chip,
) -> Result<(), String> {
  if member.columns.len() != source.width
    || member.selector >= width
    || member.columns[source.activation] != member.selector
  {
    return Err("invalid grouped member layout".into());
  }
  let mut used = member.columns.clone();
  used.sort_unstable();
  used.dedup();
  if used.len() != member.columns.len() || used.iter().any(|&c| c >= width) {
    return Err("non-injective group column mapping".into());
  }
  for write in &member.writes {
    if write.column >= width || used.contains(&write.column) {
      return Err("group message column aliases a source column".into());
    }
    write.value.validate(width, plan.program.field)?;
    used.push(write.column);
  }
  Ok(())
}
