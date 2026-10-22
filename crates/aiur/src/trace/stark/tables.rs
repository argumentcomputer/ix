//! Fixed maps of equal row count share a chip. Each original input/output
//! table has its own immutable column span and each map its own multiplicity.
use super::*;

pub(super) struct FixedTable {
  maps: Vec<usize>,
  height: usize,
}

pub(super) fn fixed_tables<B: WitnessField>(
  plan: &TracePlan<'_, B>,
  circuits: &mut Vec<CircuitInputs<Val>>,
  names: &mut Vec<String>,
) -> Result<Vec<FixedTable>, String> {
  let program = &plan.program.program;
  let mut groups: Vec<(usize, Vec<usize>)> = vec![];
  for (id, map) in program.maps.iter().enumerate() {
    if let Some((_, maps)) = groups.iter_mut().find(|(input, _)| {
      program.tables[*input].rows.len() == program.tables[map.input].rows.len()
    }) {
      maps.push(id);
    } else {
      groups.push((map.input, vec![id]));
    }
  }
  let mut result = vec![];
  for (input_id, maps) in groups {
    let input = &program.tables[input_id];
    let real_height = input.rows.len();
    let height =
      if real_height == 0 { 0 } else { real_height.next_power_of_two() };
    // Always keep a preprocessed column, even for a unit -> unit table.
    let mut width = 1usize;
    let mut columns: Vec<(usize, usize, usize)> = vec![];
    let mut lookups = vec![];
    let mut constraints = vec![];
    for (column, &mi) in maps.iter().enumerate() {
      let map = &program.maps[mi];
      let input_width =
        plan.program.inputs[program.functions.len() + mi].width();
      let output_width =
        plan.program.outputs[program.functions.len() + mi].width();
      let mut offsets = [0; 2];
      for ((table, size), offset) in
        [(map.input, input_width), (map.output, output_width)]
          .into_iter()
          .zip(&mut offsets)
      {
        *offset = if let Some((_, start, _)) =
          columns.iter().find(|(id, _, _)| *id == table)
        {
          *start
        } else {
          let start = width;
          width =
            width.checked_add(size).ok_or("fixed table width overflow")?;
          columns.push((table, start, size));
          start
        };
      }
      if width > u32::MAX as usize {
        return Err("fixed table too wide".into());
      }
      let mut args =
        vec![constant(CALL), constant((program.functions.len() + mi) as u64)];
      // Empty maps cannot provide anything, including the zero message.
      if height == 0 {
        args.resize(2 + input_width + output_width, constant(0));
        constraints.push(main_var(column));
      } else {
        args.extend(
          (offsets[0]..offsets[0] + input_width)
            .map(|i| Expr::preprocessed(i as u32)),
        );
        args.extend(
          (offsets[1]..offsets[1] + output_width)
            .map(|i| Expr::preprocessed(i as u32)),
        );
      }
      lookups.push(Lookup::pull(main_var(column), args));
    }
    let preprocessed = if height == 0 {
      None
    } else {
      let mut values = Vec::with_capacity(
        height.checked_mul(width).ok_or("fixed table size overflow")?,
      );
      for row in 0..height {
        // Duplicating a valid row preserves table membership. Only the
        // original rows receive witness multiplicities.
        let row = if row < real_height { row } else { 0 };
        values.push(Val::ONE);
        for &(id, _, _) in &columns {
          values.extend(
            program.tables[id].rows[row].iter().copied().map(Val::from_u64),
          );
        }
      }
      Some(RowMajorMatrix::new(values, width))
    };
    circuits.push(CircuitInputs {
      main_width: maps.len(),
      preprocessed,
      constraints,
      lookups,
      ..Default::default()
    });
    names.push(format!("<table:{}>", input.name));
    result.push(FixedTable { maps, height });
  }
  Ok(result)
}

impl FixedTable {
  pub(super) fn witness(&self, counts: &[Vec<u64>]) -> RowMajorMatrix<Val> {
    let mut values = Vec::with_capacity(self.maps.len() * self.height);
    for row in 0..self.height {
      for &map in &self.maps {
        values.push(Val::from_u64(counts[map].get(row).copied().unwrap_or(0)));
      }
    }
    RowMajorMatrix::new(values, self.maps.len())
  }
}
