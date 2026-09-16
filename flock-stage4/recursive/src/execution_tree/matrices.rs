//! Merge claims only when their approved complete Boolean matrices are equal.
//! Registry/table/side claims are first resolved against the actual child
//! setup. This content identity changes neither a claim nor its fixed table.
use crate::fold::{Groups, StaticTable, TableKey};
use anyhow::{Result, ensure};
use flock_prover::r1cs::SparseBinaryMatrix;
use ix_stage4_trace::F128MatrixSideV1;
use std::collections::BTreeMap;

fn matrix_key(matrix: &SparseBinaryMatrix, variables: u32) -> TableKey {
  let mut h = blake3::Hasher::new();
  h.update(b"IxBy/Flock/complete-Boolean-matrix/v0\0");
  h.update(&variables.to_le_bytes());
  for n in [matrix.num_rows, matrix.num_cols, matrix.rows.len()] {
    h.update(&u64::try_from(n).unwrap().to_le_bytes());
  }
  for row in &matrix.rows {
    h.update(&u64::try_from(row.len()).unwrap().to_le_bytes());
    for &column in row {
      h.update(&u64::try_from(column).unwrap().to_le_bytes());
    }
  }
  TableKey::Matrix { digest: *h.finalize().as_bytes(), variables }
}
pub(super) fn canonicalize(groups: Groups) -> Result<Groups> {
  let mut out: Groups = BTreeMap::new();
  for (original, (table, claims)) in groups {
    let key = if let StaticTable::Boolean { registry, table, side } = &table {
      let ty = &registry.boolean_types()[*table];
      let matrix = match side {
        F128MatrixSideV1::A => &ty.a_0,
        F128MatrixSideV1::B => &ty.b_0,
      };
      matrix_key(matrix, u32::try_from(ty.k_log)?)
    } else {
      original.clone()
    };
    ensure!(
      key.dimensions() == original.dimensions(),
      "canonical matrix dimensions differ"
    );
    out.entry(key).or_insert_with(|| (table, Vec::new())).1.extend(claims);
  }
  Ok(out)
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn identity_binds_every_sparse_entry_row_dimension_and_variable() {
    let matrix = SparseBinaryMatrix {
      num_rows: 4,
      num_cols: 4,
      rows: vec![vec![0, 3], vec![1], vec![2], vec![]],
    };
    let key = matrix_key(&matrix, 2);
    assert_eq!(key, matrix_key(&matrix.clone(), 2));
    for i in 0..matrix.rows.len() {
      let mut bad = matrix.clone();
      bad.rows[i].push(1);
      assert_ne!(key, matrix_key(&bad, 2));
    }
    let mut bad = matrix.clone();
    bad.rows.swap(0, 1);
    assert_ne!(key, matrix_key(&bad, 2));
    let mut bad = matrix.clone();
    bad.num_cols *= 2;
    assert_ne!(key, matrix_key(&bad, 2));
    let mut bad = matrix.clone();
    bad.num_rows *= 2;
    assert_ne!(key, matrix_key(&bad, 2));
    assert_ne!(key, matrix_key(&matrix, 3));
  }
}
