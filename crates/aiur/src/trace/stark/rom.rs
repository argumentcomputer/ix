//! One untyped payload chip per width, with local consecutive addresses.
//! The type-directed provenance proof interprets the words through the static
//! target type of each load. See Aiur/Memory/Partition.lean.
use super::*;
use crate::trace::MemoryLookup;

pub(super) struct Rom {
  widths: Vec<usize>,
}

impl Rom {
  pub(super) fn new<B: WitnessField>(plan: &TracePlan<'_, B>) -> Self {
    if !plan.artifact.chips.iter().any(|c| !c.memory.is_empty()) {
      return Self { widths: vec![] };
    }
    let mut widths: Vec<_> = plan
      .program
      .memory_layouts
      .values()
      .map(|layout| layout.width())
      .collect();
    widths.sort_unstable();
    widths.dedup();
    Self { widths }
  }

  pub(super) fn circuit_count(&self) -> usize {
    self.widths.len()
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
      // [multiplicity, is_real, width-local address, payload...].
      // Consecutive addresses in an active prefix prove functionality.
      let width = payload_width
        .checked_add(3)
        .filter(|&w| w <= u32::MAX as usize)
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
  ) -> Result<RowMajorMatrix<Val>, String> {
    let bucket = record.memory.indices_for_width(self.widths[index]);
    let width = self.widths[index] + 3;
    let mut trace = empty_trace(bucket.len(), width)?;
    for (&index, row) in bucket.iter().zip(trace.values.chunks_mut(width)) {
      let cell = record.memory.get(index).unwrap();
      row[0] = Val::from_u64(cell.multiplicity);
      row[1] = Val::ONE;
      row[2] = Val::from_usize(cell.address);
      for (dest, &value) in row[3..].iter_mut().zip(cell.cell.value) {
        *dest = B::into_stark(value);
      }
    }
    Ok(trace)
  }
}

fn empty_trace(
  rows: usize,
  width: usize,
) -> Result<RowMajorMatrix<Val>, String> {
  let height = if rows == 0 {
    0
  } else {
    rows.checked_next_power_of_two().ok_or("ROM height overflow")?
  };
  let values =
    Val::zero_vec(height.checked_mul(width).ok_or("ROM size overflow")?);
  Ok(RowMajorMatrix::new(values, width))
}
