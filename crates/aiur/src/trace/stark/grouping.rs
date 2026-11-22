//! Physical groups are compiled by Lean; execution and memo keys retain the
//! original callable identities. Only row placement and lookup superposition
//! change. See Aiur.Optimized.Grouping for the selector and silence arguments.
use super::*;
use crate::trace::FunctionCircuit;

pub(super) use crate::trace::Placement;

impl Placement {
  pub(crate) fn finish(&self, row: &mut [Val], count: u64) {
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
  let layout = plan.layout()?;
  for circuit in &layout.circuits {
    match *circuit {
      FunctionCircuit::Group(gi) => {
        let group = &plan.artifact.groups[gi];
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
        constraints.push(
          (constant(1) - lower(&group.activation)) * main_var(group.width),
        );
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
      },
      FunctionCircuit::Chip(ci) => {
        let chip = &plan.artifact.chips[ci];
        let mut args =
          vec![constant(CALL), constant(plan.callables[&chip.name] as u64)];
        args.extend(chip.inputs.iter().map(|&i| main_var(i)));
        args.extend(chip.output.iter().map(lower));
        let mut lookups = vec![Lookup::pull(main_var(chip.width), args)];
        for send in &chip.sends {
          let mut args = vec![
            constant(CALL),
            constant(plan.callables[&send.channel] as u64),
          ];
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
      },
    }
  }
  Ok(layout.placements)
}
