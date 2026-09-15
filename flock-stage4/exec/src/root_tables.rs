//! Setup-owned exact table-evaluation prototypes for M6. This does not change
//! the existing root-conditional replay, and does not generate a terminal key.

use crate::CompiledExecReplay;
use anyhow::{Result, ensure};
use flock_prover::{
  matrix_fold::JaggedTable, pcs::jagged::JaggedParams, union::UnionInstance,
};
use ix_stage4_trace::{
  F128CircuitStructureMatrixIdV1, F128FixedTableLimitsV0, F128FixedTableV0,
  F128JaggedMatrixIdV1, F128MatrixSideV1, F128StaticMatrixIdV1,
};
use ixby_flock::ixby::exec::CompiledExec;

/// All root tables are derived from the same approved setup as the replay.
/// Read-only getters expose the exact table programs, not mutable key inputs.
pub struct CompiledExecRootTables<'a> {
  setup: &'a CompiledExec,
  replay_digest: [u8; 32],
  source_entries: usize,
  matrices: Vec<(F128StaticMatrixIdV1, F128FixedTableV0)>,
  structure: (F128CircuitStructureMatrixIdV1, F128FixedTableV0),
  jagged: (F128JaggedMatrixIdV1, F128FixedTableV0),
}

impl<'a> CompiledExecRootTables<'a> {
  pub fn exec_setup(&self) -> &'a CompiledExec {
    self.setup
  }
  pub fn source_entries(&self) -> usize {
    self.source_entries
  }
  pub fn matrices(&self) -> &[(F128StaticMatrixIdV1, F128FixedTableV0)] {
    &self.matrices
  }
  pub fn structure(
    &self,
  ) -> &(F128CircuitStructureMatrixIdV1, F128FixedTableV0) {
    &self.structure
  }
  pub fn jagged(&self) -> &(F128JaggedMatrixIdV1, F128FixedTableV0) {
    &self.jagged
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/exec-root-tables/v0\0");
    hash.update(&self.replay_digest);
    hash.update(&(self.matrices.len() as u64).to_le_bytes());
    for (_, table) in &self.matrices {
      hash.update(&table.digest());
    }
    hash.update(&self.structure.1.digest());
    hash.update(&self.jagged.1.digest());
    *hash.finalize().as_bytes()
  }
}

/// Compile exact multilinear extensions of every fixed table. Bounds apply
/// to the TOTAL source entries and retained nodes, not independently per
/// table. Input enumeration and table layout are exclusively verifier-owned.
pub fn compile_exec_root_tables<'a>(
  replay: &CompiledExecReplay<'a>,
  limits: F128FixedTableLimitsV0,
) -> Result<CompiledExecRootTables<'a>> {
  let setup = replay.exec_setup();
  let shape = setup.verifier_shape();
  ensure!(
    shape.registry.num_element() == 0,
    "Exec table prototype supports the approved Boolean registry only"
  );
  let mut remaining = limits;
  let mut matrices = Vec::new();
  for fold in &replay.folds.matrices.folds {
    let id = fold.matrix;
    let ty = shape
      .registry
      .boolean_types()
      .get(usize::try_from(id.table)?)
      .ok_or_else(|| anyhow::anyhow!("Exec root table registry slot"))?;
    ensure!(
      id.registry_digest == setup.identities().registry
        && id.variables as usize == ty.k_log,
      "Exec root table identity"
    );
    let matrix = match id.side {
      F128MatrixSideV1::A => &ty.a_0,
      F128MatrixSideV1::B => &ty.b_0,
    };
    ensure!(
      id.variables <= 32
        && matrix.num_rows == (1usize << id.variables)
        && matrix.num_cols == matrix.num_rows
        && matrix.rows.len() == matrix.num_rows,
      "Exec root table square geometry"
    );
    ensure!(
      matrix.rows.iter().flatten().all(|&col| col < matrix.num_cols),
      "Exec root table column range"
    );
    let entries = matrix.rows.iter().enumerate().flat_map(|(row, columns)| {
      columns.iter().map(move |&column| {
        (row as u64 | ((column as u64) << id.variables), 1u128.to_le_bytes())
      })
    });
    let table = compile(
      &interleaved_order(id.variables, id.variables),
      entries,
      &mut remaining,
    )?;
    matrices.push((id, table));
  }

  let id = replay.folds.structure.matrix;
  let circuit = &shape.circuit;
  let row_variables = u32::try_from(circuit.cells().nu())?;
  let cell_variables = u32::try_from(circuit.cells().mu())?;
  let base_variables = replay.wiring.structure_base_variables;
  ensure!(
    id.circuit_digest == setup.identities().circuit
      && id.row_variables == row_variables
      && id.column_variables == base_variables + 3
      && row_variables + id.column_variables <= 64
      && cell_variables < usize::BITS
      && base_variables < usize::BITS,
    "Exec root structure geometry"
  );
  let base_columns = 1usize << base_variables;
  let expected_base = (1usize << (cell_variables - row_variables))
    .max(shape.registry.num_boolean().next_power_of_two());
  ensure!(base_columns == expected_base, "Exec root structure base width");
  let mask = circuit.live_mask();
  let index = move |row: u64, column: u64| row | (column << row_variables);
  let plane = move |cell: usize, plane: u64| {
    index(
      cell as u64 & ((1u64 << row_variables) - 1),
      ((cell as u64) >> row_variables) + plane * base_columns as u64,
    )
  };
  // Exact eight-plane layout of the pinned CircuitStructureMatrix:
  // 0 live*id, 1 live, 2 live*sigma, 3/4 element constants (absent for
  // this approved Boolean profile), 5 constant-wire pins, 6/7 zero.
  // Keeping plane 5 matters even though the fresh GKR claims select 0..2:
  // the fold's random column point evaluates the ENTIRE fixed matrix.
  let cells = (0..1usize << cell_variables)
    .filter(|&cell| mask.is_live(cell))
    .flat_map(|cell| {
      [
        (plane(cell, 0), (cell as u128).to_le_bytes()),
        (plane(cell, 1), 1u128.to_le_bytes()),
        (plane(cell, 2), (circuit.sigma()[cell] as u128).to_le_bytes()),
      ]
    });
  let pins =
    shape.registry.boolean_types().iter().enumerate().flat_map(|(slot, ty)| {
      let rows = if ty.const_pin.is_some() { shape.counts[slot] } else { 0 };
      (0..rows).map(move |row| {
        (
          index(row as u64, slot as u64 + 5 * base_columns as u64),
          1u128.to_le_bytes(),
        )
      })
    });
  let structure = (
    id,
    compile(
      &interleaved_order(id.row_variables, id.column_variables),
      cells.chain(pins),
      &mut remaining,
    )?,
  );

  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let dense_variables = setup
    .pcs_params()
    .m
    .checked_sub(7)
    .ok_or_else(|| anyhow::anyhow!("Exec root jagged PCS dimension"))?;
  let params = JaggedParams::from_heights(
    &union.jagged_heights(),
    union.n_log(),
    dense_variables,
  );
  let table = JaggedTable::from_params(&params);
  let id = replay.folds.jagged.matrix;
  ensure!(
    id.circuit_digest == setup.identities().circuit
      && id.row_variables as usize == table.k
      && id.column_variables as usize == table.n_col_vars()
      && id.row_variables + id.column_variables <= 64,
    "Exec root jagged geometry"
  );
  let mut row = 0u64;
  let entries = table.bounds.iter().flat_map(|&(left, right, run)| {
    let mut pair = 0u64;
    for bit in 0..=table.m {
      pair |= ((left >> bit) & 1) << (2 * bit);
      pair |= ((right >> bit) & 1) << (2 * bit + 1);
    }
    let first = row;
    row += u64::from(run);
    (first..row)
      .map(move |row| (row | (pair << id.row_variables), 1u128.to_le_bytes()))
  });
  let jagged = (
    id,
    compile(
      &interleaved_order(id.row_variables, id.column_variables),
      entries,
      &mut remaining,
    )?,
  );
  ensure!(row == 1u64 << id.row_variables, "Exec root jagged row coverage");
  Ok(CompiledExecRootTables {
    setup,
    replay_digest: replay.identities().digest(),
    source_entries: limits.entries - remaining.entries,
    matrices,
    structure,
    jagged,
  })
}

fn interleaved_order(rows: u32, columns: u32) -> Vec<u32> {
  (0..rows.max(columns))
    .rev()
    .flat_map(|bit| {
      (bit < rows)
        .then_some(bit)
        .into_iter()
        .chain((bit < columns).then_some(rows + bit))
    })
    .collect()
}

fn compile(
  order: &[u32],
  entries: impl IntoIterator<Item = (u64, [u8; 16])>,
  remaining: &mut F128FixedTableLimitsV0,
) -> Result<F128FixedTableV0> {
  let mut count = 0;
  let entries = entries.into_iter().inspect(|_| count += 1);
  let table = F128FixedTableV0::compile(order, entries, *remaining)?;
  remaining.entries -= count;
  remaining.nodes -= u32::try_from(table.nodes().len())?;
  Ok(table)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn fixed_table_budgets_are_shared_across_tables() {
    let entries = [(0, 1u128.to_le_bytes()), (3, 1u128.to_le_bytes())];
    let table = F128FixedTableV0::compile(
      &[1, 0],
      entries,
      F128FixedTableLimitsV0 { entries: 2, nodes: 100 },
    )
    .unwrap();
    let nodes = u32::try_from(table.nodes().len()).unwrap();
    let mut remaining = F128FixedTableLimitsV0 { entries: 4, nodes: 2 * nodes };
    for expected in [
      F128FixedTableLimitsV0 { entries: 2, nodes },
      F128FixedTableLimitsV0 { entries: 0, nodes: 0 },
    ] {
      assert_eq!(compile(&[1, 0], entries, &mut remaining).unwrap(), table);
      assert_eq!(remaining, expected);
    }
    assert!(compile(&[1, 0], entries, &mut remaining).is_err());
    // Even a zero table needs one retained constant node. Exhausting only
    // the node allowance must reject independently of the entry allowance.
    remaining.entries = 100;
    assert!(compile(&[1, 0], [], &mut remaining).is_err());
  }

  #[test]
  fn canceled_and_zero_coefficients_still_use_the_source_entry_budget() {
    let mut remaining = F128FixedTableLimitsV0 { entries: 3, nodes: 10 };
    let table =
      compile(&[0], [(0, [0; 16]), (1, [7; 16]), (1, [7; 16])], &mut remaining)
        .unwrap();
    assert_eq!(table.nonzero_entries(), 0);
    assert_eq!(remaining, F128FixedTableLimitsV0 { entries: 0, nodes: 9 });
    assert!(compile(&[0], [(0, [0; 16])], &mut remaining).is_err());
  }

  #[test]
  fn rectangular_interleaving_preserves_lsb_coordinate_addresses() {
    for (rows, cols) in [(0, 0), (0, 3), (3, 0), (2, 3), (4, 1), (32, 32)] {
      let order = interleaved_order(rows, cols);
      let mut sorted = order.clone();
      sorted.sort_unstable();
      assert_eq!(sorted, (0..rows + cols).collect::<Vec<_>>());
      assert!(order.iter().filter(|&&x| x < rows).copied().eq((0..rows).rev()));
      assert!(
        order
          .iter()
          .filter(|&&x| x >= rows)
          .copied()
          .eq((rows..rows + cols).rev())
      );
    }
    assert_eq!(interleaved_order(2, 3), [4, 1, 3, 0, 2]);
  }
}
