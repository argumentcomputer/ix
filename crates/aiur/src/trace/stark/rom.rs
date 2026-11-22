//! One untyped payload chip per width, with local consecutive addresses.
//! The type-directed provenance proof interprets the words through the static
//! target type of each load. See Aiur/Memory/Partition.lean.
//!
//! Supports both scalar (`K = 1`) and `K`-lane vectorized (`C6`) ROM circuits
//! (`K = 8` for `w <= 4`, `K = 4` for `5 <= w <= 12`, `K = 1` for `w > 12`),
//! preserving the exact external `[ROM, w, addr, payload...]` and
//! `[MEMSEG, w, ptr]` boundary claims.
use super::*;
use crate::trace::MemoryLookup;

/// Physical row layout of `<ROM:w>` circuits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RomLayout {
  /// Scalar 1-lane `<ROM:w>` layout (`[count, active, addr, payload...]`,
  /// width `w + 3`, 1 entry per row). Required by the legacy fixed-root
  /// normalizer (`crates/proof-compression/src/pipeline/root/fixed.rs`).
  #[default]
  Scalar,
  /// `K`-lane vectorized `<ROM:w>` layout (`K = 8` for `w <= 4`, `K = 4` for
  /// `5 <= w <= 12`, `K = 1` for `w > 12`), cutting `<ROM:3>` cells/RAM by
  /// ~51% and `max_log` by 3 while preserving exact `ROM` and `MEMSEG` claims.
  Vectorized,
}

/// Number of ROM entries packed per row in `RomLayout::Vectorized`.
pub const fn rom_lanes(payload_width: usize) -> usize {
  if payload_width <= 4 {
    8
  } else if payload_width <= 12 {
    4
  } else {
    1
  }
}

impl RomLayout {
  pub const fn lanes(self, payload_width: usize) -> usize {
    match self {
      Self::Scalar => 1,
      Self::Vectorized => rom_lanes(payload_width),
    }
  }
}

pub(super) struct Rom {
  pub(super) widths: Vec<usize>,
  pub(super) layout: RomLayout,
}

impl Rom {
  pub(super) fn new<B: WitnessField>(
    plan: &TracePlan<'_, B>,
    layout: RomLayout,
  ) -> Self {
    if !plan.artifact.chips.iter().any(|c| !c.memory.is_empty()) {
      return Self { widths: vec![], layout };
    }
    let mut widths: Vec<_> = plan
      .program
      .memory_layouts
      .values()
      .map(|layout| layout.width())
      .collect();
    widths.sort_unstable();
    widths.dedup();
    Self { widths, layout }
  }

  pub(super) fn circuit_count(&self) -> usize {
    self.widths.len()
  }

  pub(super) fn lanes_for_width(&self, payload_width: usize) -> usize {
    self.layout.lanes(payload_width)
  }

  pub(super) fn row_count_for_entries(
    &self,
    payload_width: usize,
    entries: usize,
  ) -> usize {
    entries.div_ceil(self.lanes_for_width(payload_width))
  }

  /// Count active ROM entries in a populated trace matrix (summing active lanes
  /// across the contiguous active row prefix).
  #[cfg(test)]
  pub(super) fn active_entries(
    &self,
    index: usize,
    trace: &RowMajorMatrix<Val>,
  ) -> usize {
    let payload_width = self.widths[index];
    let lanes = self.layout.lanes(payload_width);
    if lanes == 1 {
      return trace
        .values
        .chunks_exact(trace.width)
        .take_while(|row| row[1] == Val::ONE)
        .count();
    }
    let stride = payload_width + 2;
    trace
      .values
      .chunks_exact(trace.width)
      .take_while(|row| row[2] == Val::ONE)
      .map(|row| {
        (0..lanes).take_while(|&l| row[1 + l * stride + 1] == Val::ONE).count()
      })
      .sum()
  }

  pub(super) fn access(
    &self,
    cell: &MemoryLookup,
  ) -> Result<Lookup<Expr<Val>>, String> {
    // TracePlan already checks the static type's layout. After physical
    // type erasure this view need not occur in the bytecode's type map.
    let width = cell.values.len();
    if self.widths.binary_search(&width).is_err() {
      return Err("unknown circuit ROM width".into());
    }
    // Width explicitly separates messages whose payloads differ only by
    // trailing zeros. Nominal types are static views of these same raw words.
    let mut args =
      vec![constant(ROM), constant(width as u64), lower(&cell.address)];
    args.extend(cell.values.iter().map(lower));
    Ok(Lookup::push(lower(&cell.enable), args))
  }

  pub(super) fn append_circuits(
    &self,
    circuits: &mut Vec<CircuitInputs<Val>>,
    names: &mut Vec<String>,
    segmented: bool,
  ) -> Result<(), String> {
    for &payload_width in &self.widths {
      let lanes = self.layout.lanes(payload_width);
      if lanes == 1 {
        // Scalar layout: [multiplicity, is_real, width-local address, payload...].
        // Consecutive addresses in an active prefix prove functionality.
        let width = payload_width
          .checked_add(3)
          .filter(|&w| u32::try_from(w).is_ok())
          .ok_or("ROM too wide")?;
        let count = main_var(0);
        let active = main_var(1);
        let address = main_var(2);
        let mut args =
          vec![constant(ROM), constant(payload_width as u64), address.clone()];
        args.extend((3..width).map(main_var));
        let transition = Expr::IsTransition * Expr::main_next(1);
        let mut constraints = vec![
          active.clone() * (active.clone() - constant(1)),
          count.clone() * (constant(1) - active.clone()),
          transition.clone() * (active.clone() - constant(1)),
          transition * (Expr::main_next(2) - address.clone() - constant(1)),
        ];
        let mut lookups = vec![Lookup::pull(count, args)];
        if segmented {
          // Each contiguous run leaves its start/end in the batch balance.
          // Authenticated closure messages and the height bound tile [0, N).
          lookups.push(Lookup::push(
            active.clone(),
            vec![
              constant(MEMSEG),
              constant(payload_width as u64),
              address.clone(),
            ],
          ));
          lookups.push(Lookup::pull(
            active,
            vec![
              constant(MEMSEG),
              constant(payload_width as u64),
              address + constant(1),
            ],
          ));
        } else {
          constraints.push(Expr::IsFirstRow * address);
        }
        circuits.push(CircuitInputs {
          main_width: width,
          constraints,
          lookups,
          ..Default::default()
        });
        names.push(format!("<ROM:{payload_width}>"));
        continue;
      }

      // Vectorized K-lane layout:
      //   col 0: base_addr
      //   for lane i in 0..K (stride = payload_width + 2, base = 1 + i * stride):
      //     col base + 0: count_i
      //     col base + 1: active_i
      //     col base + 2 .. base + 2 + payload_width: payload_i[0..payload_width]
      let stride = payload_width.checked_add(2).ok_or("ROM too wide")?;
      let width = lanes
        .checked_mul(stride)
        .and_then(|n| n.checked_add(1))
        .filter(|&w| u32::try_from(w).is_ok())
        .ok_or("ROM too wide")?;
      let base_addr = main_var(0);
      let count_col = |lane: usize| 1 + lane * stride;
      let active_col = |lane: usize| 1 + lane * stride + 1;

      let mut constraints = Vec::with_capacity(3 * lanes + 2);
      for lane in 0..lanes {
        let count = main_var(count_col(lane));
        let active = main_var(active_col(lane));
        constraints.push(active.clone() * (active.clone() - constant(1)));
        constraints.push(count * (constant(1) - active));
      }
      // Intra-row contiguous active prefix: lane i+1 can only be active if lane i is active.
      for lane in 0..lanes - 1 {
        let cur = main_var(active_col(lane));
        let next = main_var(active_col(lane + 1));
        constraints.push(next * (constant(1) - cur));
      }
      // Inter-row transition: a next row can only be active if the current row
      // filled all K lanes, and base_addr advances by K.
      let transition = Expr::IsTransition
        * Expr::main_next(
          u32::try_from(active_col(0)).expect("checked column width"),
        );
      let last_active = main_var(active_col(lanes - 1));
      constraints.push(transition.clone() * (last_active - constant(1)));
      constraints.push(
        transition
          * (Expr::main_next(0) - base_addr.clone() - constant(lanes as u64)),
      );

      let mut lookups =
        Vec::with_capacity(lanes + if segmented { 2 } else { 0 });
      for lane in 0..lanes {
        let lane_addr = if lane == 0 {
          base_addr.clone()
        } else {
          base_addr.clone() + constant(lane as u64)
        };
        let mut args =
          vec![constant(ROM), constant(payload_width as u64), lane_addr];
        let payload_start = 1 + lane * stride + 2;
        args
          .extend((payload_start..payload_start + payload_width).map(main_var));
        lookups.push(Lookup::pull(main_var(count_col(lane)), args));
      }

      if segmented {
        let active_0 = main_var(active_col(0));
        let mut sum_active = active_0.clone();
        for lane in 1..lanes {
          sum_active = sum_active + main_var(active_col(lane));
        }
        lookups.push(Lookup::push(
          active_0.clone(),
          vec![
            constant(MEMSEG),
            constant(payload_width as u64),
            base_addr.clone(),
          ],
        ));
        lookups.push(Lookup::pull(
          active_0,
          vec![
            constant(MEMSEG),
            constant(payload_width as u64),
            base_addr + sum_active,
          ],
        ));
      } else {
        constraints.push(Expr::IsFirstRow * base_addr);
      }

      circuits.push(CircuitInputs {
        main_width: width,
        constraints,
        lookups,
        ..Default::default()
      });
      names.push(format!("<ROM:{payload_width}>"));
    }
    Ok(())
  }

  /// Memory's private interning path already guarantees unique payloads and
  /// consecutive addresses in each width bucket. The backend validates the
  /// recorded types and counts before reading these immutable rows directly.
  pub(super) fn witness<B: WitnessField>(
    &self,
    record: &Execution<B>,
    index: usize,
    min_height: Option<usize>,
  ) -> Result<RowMajorMatrix<Val>, String> {
    Ok(self.witness_with_active(record, index, min_height)?.0)
  }

  /// Populate `rows` active ROM rows starting at `first_row` into `values`
  /// (whose length must be at least `rows * width`), in parallel when large.
  pub(super) fn populate_rows<B: WitnessField>(
    &self,
    record: &Execution<B>,
    index: usize,
    first_row: usize,
    rows: usize,
    values: &mut [Val],
  ) {
    if rows == 0 {
      return;
    }
    let payload_width = self.widths[index];
    let lanes = self.layout.lanes(payload_width);
    let cells = record.memory.width_cells(payload_width);
    let len = cells.len();
    if lanes == 1 {
      let width = payload_width + 3;
      let active_values = &mut values[..rows * width];
      let write_row = |(offset, row): (usize, &mut [Val])| {
        let (address, multiplicity, cell_values) =
          cells.rom_row(first_row + offset);
        row[0] = Val::from_u64(multiplicity);
        row[1] = Val::ONE;
        row[2] = Val::from_usize(address);
        for (dest, &value) in row[3..].iter_mut().zip(cell_values) {
          *dest = B::into_stark(value);
        }
      };
      #[cfg(feature = "parallel")]
      if rows >= 256 {
        active_values.par_chunks_mut(width).enumerate().for_each(write_row);
      } else {
        active_values.chunks_mut(width).enumerate().for_each(write_row);
      }
      #[cfg(not(feature = "parallel"))]
      active_values.chunks_mut(width).enumerate().for_each(write_row);
      return;
    }

    let stride = payload_width + 2;
    let width = 1 + lanes * stride;
    let active_values = &mut values[..rows * width];
    let write_row = |(offset, row): (usize, &mut [Val])| {
      let base_idx = (first_row + offset) * lanes;
      let (first_addr, _, _) = cells.rom_row(base_idx);
      row[0] = Val::from_usize(first_addr);
      let active_in_row = (len - base_idx).min(lanes);
      for lane in 0..active_in_row {
        let (address, multiplicity, cell_values) =
          cells.rom_row(base_idx + lane);
        debug_assert_eq!(address, first_addr + lane);
        let off = 1 + lane * stride;
        row[off] = Val::from_u64(multiplicity);
        row[off + 1] = Val::ONE;
        for (dest, &value) in
          row[off + 2..off + 2 + payload_width].iter_mut().zip(cell_values)
        {
          *dest = B::into_stark(value);
        }
      }
    };
    #[cfg(feature = "parallel")]
    if rows >= 256 {
      active_values.par_chunks_mut(width).enumerate().for_each(write_row);
    } else {
      active_values.chunks_mut(width).enumerate().for_each(write_row);
    }
    #[cfg(not(feature = "parallel"))]
    active_values.chunks_mut(width).enumerate().for_each(write_row);
  }

  /// Populate the ROM trace in parallel when large, returning both the padded
  /// matrix and the count of active rows (`0..active_rows`).
  pub(super) fn witness_with_active<B: WitnessField>(
    &self,
    record: &Execution<B>,
    index: usize,
    min_height: Option<usize>,
  ) -> Result<(RowMajorMatrix<Val>, usize), String> {
    let payload_width = self.widths[index];
    let lanes = self.layout.lanes(payload_width);
    let len = record.memory.width_cells(payload_width).len();
    let (width, active_rows) = if lanes == 1 {
      (payload_width + 3, len)
    } else {
      (1 + lanes * (payload_width + 2), len.div_ceil(lanes))
    };
    let mut trace = empty_trace(active_rows, width, min_height)?;
    self.populate_rows(record, index, 0, active_rows, &mut trace.values);
    Ok((trace, active_rows))
  }
}

fn empty_trace(
  rows: usize,
  width: usize,
  min_height: Option<usize>,
) -> Result<RowMajorMatrix<Val>, String> {
  let natural = if rows == 0 {
    0
  } else {
    rows.checked_next_power_of_two().ok_or("ROM height overflow")?
  };
  let height = match min_height {
    Some(target) => {
      if natural > target {
        return Err(format!(
          "ROM trace height {natural} exceeds normalized height {target}"
        ));
      }
      target
    },
    None => natural,
  };
  let values =
    Val::zero_vec(height.checked_mul(width).ok_or("ROM size overflow")?);
  Ok(RowMajorMatrix::new(values, width))
}
