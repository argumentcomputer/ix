use super::*;
use aiur::field::FieldBackend;
use multi_stark::traits::Algebra;
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use p3_maybe_rayon::prelude::*;

fn empty_trace(
  height: usize,
  width: usize,
) -> Result<RowMajorMatrix<Scalar>, String> {
  let padded = if height == 0 {
    0
  } else {
    height.checked_next_power_of_two().ok_or("trace height overflow")?
  };
  Ok(RowMajorMatrix::new(
    vec![Scalar::ZERO; padded.checked_mul(width).ok_or("trace size overflow")?],
    width,
  ))
}

pub(super) struct Packing<'p, 'a, 'm> {
  pub(super) plan: &'p TracePlan<'a, Bn254>,
  pub(super) placements: &'m [Placement<FieldWord>],
  pub(super) function_widths: &'m [usize],
  pub(super) tables: &'m [circuits::FixedTable],
  pub(super) memory_widths: &'m [usize],
}

impl Packing<'_, '_, '_> {
  pub(super) fn main_traces(
    &self,
    record: &Execution<Bn254>,
    trace: &Trace<Scalar>,
  ) -> Result<Vec<RowMajorMatrix<Scalar>>, String> {
    let mut heights = vec![0usize; self.function_widths.len()];
    for (matrix, placement) in trace.matrices.iter().zip(self.placements) {
      let height =
        if placement.grouped { matrix.unpadded_height } else { matrix.height };
      heights[placement.circuit] = heights[placement.circuit]
        .checked_add(height)
        .ok_or("function trace height overflow")?;
    }
    let mut traces = heights
      .iter()
      .zip(self.function_widths)
      .map(|(&height, &width)| empty_trace(height, width))
      .collect::<Result<Vec<_>, _>>()?;
    let mut cursors = vec![0usize; self.function_widths.len()];
    for ((chip, matrix), placement) in self
      .plan
      .artifact()
      .chips
      .iter()
      .zip(&trace.matrices)
      .zip(self.placements)
    {
      if matrix.height != 0 && !matrix.height.is_power_of_two() {
        return Err("compiler trace height is not a power of two".into());
      }
      if matrix.unpadded_height > matrix.height {
        return Err("compiler rows exceed their padded height".into());
      }
      let real_values = matrix.unpadded_height * matrix.width;
      if matrix.values[real_values..]
        .par_iter()
        .any(|&value| value != Scalar::ZERO)
        || matrix.multiplicities[matrix.unpadded_height..]
          .par_iter()
          .any(|&value| value != 0)
      {
        return Err("nonzero compiler trace padding".into());
      }
      let output = &mut traces[placement.circuit];
      let first = cursors[placement.circuit];
      let end = first + matrix.unpadded_height;
      let width = output.width;
      let identity = !placement.grouped
        && placement.columns.iter().copied().eq(0..matrix.width);
      output.values[first * width..end * width]
        .par_chunks_mut(64 * width)
        .enumerate()
        .try_for_each(|(block, rows)| -> Result<(), String> {
          for (offset, dest) in rows.chunks_mut(width).enumerate() {
            let row_index = block * 64 + offset;
            let source = matrix.row(row_index);
            if source[chip.activation] != Scalar::ONE {
              return Err("inactive real compiler row".into());
            }
            if identity {
              dest[..source.len()].copy_from_slice(source);
            } else {
              for (&column, &value) in placement.columns.iter().zip(source) {
                dest[column] = value;
              }
            }
            dest[placement.selector] = Scalar::ONE;
            for write in &placement.writes {
              dest[write.column] = circuits::evaluate(&write.value, dest);
            }
            *dest.last_mut().ok_or("empty compiler circuit")? =
              Bn254.from_u64(matrix.multiplicities[row_index]);
          }
          Ok(())
        })?;
      cursors[placement.circuit] = end;
    }

    let program = self.plan.program().program();
    let mut counts = (0..program.maps.len())
      .map(|map| {
        record
          .queries
          .fixed_counts(program.functions.len() + map)
          .map(<[u64]>::to_vec)
          .ok_or_else(|| "missing fixed-map counts".to_owned())
      })
      .collect::<Result<Vec<_>, _>>()?;
    let mut range_count = 0;
    for (table, callable) in self.plan.depth_range_tables() {
      range_count += 1;
      let map = callable
        .checked_sub(program.functions.len())
        .ok_or("invalid depth map callable")?;
      let counts = counts.get_mut(map).ok_or("missing depth range map")?;
      let uses = trace.ranges.table(table);
      if uses.len() > counts.len() {
        return Err("depth range counts exceed their table".into());
      }
      for (count, &uses) in counts.iter_mut().zip(uses) {
        *count =
          count.checked_add(uses).ok_or("depth range multiplicity overflow")?;
      }
    }
    if trace
      .ranges
      .0
      .get(range_count..)
      .is_some_and(|tables| tables.iter().any(|table| !table.is_empty()))
    {
      return Err("unknown depth range counts".into());
    }
    for table in self.tables {
      let mut values = Vec::with_capacity(
        table
          .height
          .checked_mul(table.maps.len())
          .ok_or("fixed witness size overflow")?,
      );
      for row in 0..table.height {
        for &map in &table.maps {
          values
            .push(Bn254.from_u64(counts[map].get(row).copied().unwrap_or(0)));
        }
      }
      traces.push(RowMajorMatrix::new(values, table.maps.len()));
    }
    let mut memory = vec![vec![]; self.memory_widths.len()];
    for cell in record.memory.iter() {
      let bucket = self
        .memory_widths
        .binary_search(&cell.cell.value.len())
        .map_err(|_error| "recorded ROM width absent from compiler circuits")?;
      memory[bucket].push(cell);
    }
    for (&width, cells) in self.memory_widths.iter().zip(memory) {
      let mut trace = empty_trace(cells.len(), width + 3)?;
      for (address, (cell, row)) in
        cells.iter().zip(trace.values.chunks_mut(trace.width)).enumerate()
      {
        if cell.address != address {
          return Err("nonconsecutive ROM addresses".into());
        }
        row[0] = Bn254.from_u64(cell.multiplicity);
        row[1] = Scalar::ONE;
        row[2] = Bn254.from_u64(
          u64::try_from(address).map_err(|_error| "ROM address overflow")?,
        );
        row[3..].copy_from_slice(cell.cell.value);
      }
      traces.push(trace);
    }
    Ok(traces)
  }
}

impl Backend<'_, '_> {
  pub(super) fn trace_shape(
    &self,
    traces: &[RowMajorMatrix<Scalar>],
  ) -> Result<(Vec<bool>, Vec<u8>), String> {
    if traces.len() != self.system.circuits.len() {
      return Err("wrong circuit count".into());
    }
    let mut active = vec![];
    let mut degrees = vec![];
    for (trace, circuit) in traces.iter().zip(&self.system.circuits) {
      if trace.width != circuit.main_width
        || trace.width == 0
        || !trace.values.len().is_multiple_of(trace.width)
        || (trace.height() != 0 && !trace.height().is_power_of_two())
      {
        return Err("invalid main trace shape".into());
      }
      active.push(trace.height() != 0);
      if trace.height() != 0 {
        degrees.push(
          u8::try_from(trace.height().ilog2())
            .map_err(|_error| "trace height log overflow")?,
        );
      }
    }
    Ok((active, degrees))
  }
}
