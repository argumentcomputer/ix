//! Immutable programs for all three terminal root families. Construction
//! checks geometry and identities, not matrix provenance: the approved setup
//! must derive or exhaustively check every program's coefficients.

use crate::{
  BinaryLinearMapV0, F128CircuitStructureMatrixIdV1, F128FixedTableBasisV0,
  F128FixedTableV0, F128JaggedMatrixIdV1, F128StaticMatrixIdV1,
};
use std::{collections::BTreeSet, fmt};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128FixedMatrixProgramV0 {
  DecisionDiagram(F128FixedTableV0),
  BinaryLinear(BinaryLinearMapV0),
  CofactorBasis(F128FixedTableBasisV0),
}

impl F128FixedMatrixProgramV0 {
  pub fn has_shape(&self, row: u32, column: u32) -> bool {
    match self {
      Self::DecisionDiagram(table) => row
        .checked_add(column)
        .is_some_and(|n| n as usize == table.order().len()),
      Self::BinaryLinear(map) => {
        1usize.checked_shl(row) == Some(map.outputs().len())
          && 1u32.checked_shl(column) == Some(map.inputs())
      },
      Self::CofactorBasis(table) => row
        .checked_add(column)
        .is_some_and(|n| n as usize == table.layers().len()),
    }
  }

  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/fixed-matrix-program/v0\0");
    let (tag, digest) = match self {
      Self::DecisionDiagram(table) => (0, table.digest()),
      Self::BinaryLinear(map) => (1, map.digest()),
      Self::CofactorBasis(table) => (2, table.digest()),
    };
    hash.update(&[tag]);
    hash.update(&digest);
    *hash.finalize().as_bytes()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128RootTableSetError {
  RegistryIdentity,
  CircuitIdentity,
  DuplicateMatrix,
  MatrixGeometry,
  StructureGeometry,
  JaggedGeometry,
}
impl fmt::Display for F128RootTableSetError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "fixed root-table set: {self:?}")
  }
}
impl std::error::Error for F128RootTableSetError {}

/// A fixed ordered table set, with no proof-dependent points or values.
/// This is not an authorization certificate or a terminal verification key.
/// Its source matrices and order must come from the approved replay compiler.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128RootTableSetV0 {
  registry: [u8; 32],
  circuit: [u8; 32],
  matrices: Vec<(F128StaticMatrixIdV1, F128FixedMatrixProgramV0)>,
  structure: (F128CircuitStructureMatrixIdV1, F128FixedMatrixProgramV0),
  jagged: (F128JaggedMatrixIdV1, F128FixedMatrixProgramV0),
}

impl F128RootTableSetV0 {
  pub fn new(
    registry: [u8; 32],
    circuit: [u8; 32],
    matrices: Vec<(F128StaticMatrixIdV1, F128FixedMatrixProgramV0)>,
    structure: (F128CircuitStructureMatrixIdV1, F128FixedMatrixProgramV0),
    jagged: (F128JaggedMatrixIdV1, F128FixedMatrixProgramV0),
  ) -> Result<Self, F128RootTableSetError> {
    use F128RootTableSetError as Error;
    let mut seen = BTreeSet::new();
    for (id, table) in &matrices {
      if id.registry_digest != registry {
        return Err(Error::RegistryIdentity);
      }
      if !seen.insert(*id) {
        return Err(Error::DuplicateMatrix);
      }
      if !table.has_shape(id.variables, id.variables) {
        return Err(Error::MatrixGeometry);
      }
    }
    if structure.0.circuit_digest != circuit
      || jagged.0.circuit_digest != circuit
    {
      return Err(Error::CircuitIdentity);
    }
    if !structure
      .1
      .has_shape(structure.0.row_variables, structure.0.column_variables)
    {
      return Err(Error::StructureGeometry);
    }
    if !jagged.1.has_shape(jagged.0.row_variables, jagged.0.column_variables) {
      return Err(Error::JaggedGeometry);
    }
    Ok(Self { registry, circuit, matrices, structure, jagged })
  }

  pub fn registry_digest(&self) -> [u8; 32] {
    self.registry
  }
  pub fn circuit_digest(&self) -> [u8; 32] {
    self.circuit
  }
  pub fn matrices(
    &self,
  ) -> &[(F128StaticMatrixIdV1, F128FixedMatrixProgramV0)] {
    &self.matrices
  }
  pub fn structure(
    &self,
  ) -> &(F128CircuitStructureMatrixIdV1, F128FixedMatrixProgramV0) {
    &self.structure
  }
  pub fn jagged(&self) -> &(F128JaggedMatrixIdV1, F128FixedMatrixProgramV0) {
    &self.jagged
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/fixed-root-table-set/v0\0");
    hash.update(&self.registry);
    hash.update(&self.circuit);
    hash.update(&(self.matrices.len() as u64).to_le_bytes());
    for (id, table) in &self.matrices {
      hash.update(&id.table.to_le_bytes());
      hash.update(&[id.side as u8]);
      hash.update(&id.variables.to_le_bytes());
      hash.update(&table.digest());
    }
    for (row, column, table) in [
      (
        self.structure.0.row_variables,
        self.structure.0.column_variables,
        &self.structure.1,
      ),
      (
        self.jagged.0.row_variables,
        self.jagged.0.column_variables,
        &self.jagged.1,
      ),
    ] {
      hash.update(&row.to_le_bytes());
      hash.update(&column.to_le_bytes());
      hash.update(&table.digest());
    }
    *hash.finalize().as_bytes()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{F128FixedTableLimitsV0, F128MatrixSideV1};

  fn fixture() -> F128RootTableSetV0 {
    let zero = || {
      F128FixedMatrixProgramV0::DecisionDiagram(
        F128FixedTableV0::compile(
          &[1, 0],
          [],
          F128FixedTableLimitsV0 { entries: 0, nodes: 1 },
        )
        .unwrap(),
      )
    };
    let id = F128StaticMatrixIdV1 {
      registry_digest: [3; 32],
      table: 0,
      side: F128MatrixSideV1::A,
      variables: 1,
    };
    F128RootTableSetV0::new(
      [3; 32],
      [5; 32],
      vec![
        (id, zero()),
        (F128StaticMatrixIdV1 { side: F128MatrixSideV1::B, ..id }, zero()),
      ],
      (
        F128CircuitStructureMatrixIdV1 {
          circuit_digest: [5; 32],
          row_variables: 1,
          column_variables: 1,
        },
        zero(),
      ),
      (
        F128JaggedMatrixIdV1 {
          circuit_digest: [5; 32],
          row_variables: 1,
          column_variables: 1,
        },
        zero(),
      ),
    )
    .unwrap()
  }

  fn rebuild(
    t: F128RootTableSetV0,
  ) -> Result<F128RootTableSetV0, F128RootTableSetError> {
    F128RootTableSetV0::new(
      t.registry,
      t.circuit,
      t.matrices,
      t.structure,
      t.jagged,
    )
  }

  #[test]
  fn table_set_rejects_wrong_identities_duplicate_ids_and_geometry() {
    use F128RootTableSetError as E;
    for (kind, expected) in [
      E::RegistryIdentity,
      E::CircuitIdentity,
      E::DuplicateMatrix,
      E::MatrixGeometry,
      E::StructureGeometry,
      E::JaggedGeometry,
    ]
    .into_iter()
    .enumerate()
    {
      let mut t = fixture();
      match kind {
        0 => t.matrices[0].0.registry_digest[0] ^= 1,
        1 => t.jagged.0.circuit_digest[0] ^= 1,
        2 => t.matrices[1].0 = t.matrices[0].0,
        3 => t.matrices[0].0.variables = u32::MAX,
        4 => t.structure.0.row_variables = 2,
        5 => t.jagged.0.column_variables = 2,
        _ => unreachable!(),
      }
      assert_eq!(rebuild(t), Err(expected));
    }
  }

  #[test]
  fn table_set_identity_binds_order_table_program_and_family_dimensions() {
    let t = fixture();
    let original = t.digest();
    let mut reordered = t.clone();
    reordered.matrices.swap(0, 1);
    assert_ne!(rebuild(reordered).unwrap().digest(), original);
    let mut changed = t.clone();
    changed.matrices[0].1 = F128FixedMatrixProgramV0::DecisionDiagram(
      F128FixedTableV0::compile(
        &[1, 0],
        [(0, [7; 16])],
        F128FixedTableLimitsV0 { entries: 1, nodes: 10 },
      )
      .unwrap(),
    );
    assert_ne!(rebuild(changed).unwrap().digest(), original);
    let mut changed = t;
    changed.structure.0.row_variables = 0;
    changed.structure.0.column_variables = 2;
    assert_ne!(rebuild(changed).unwrap().digest(), original);
  }

  #[test]
  fn cofactor_program_kind_and_each_family_geometry_are_bound() {
    use crate::{F128FixedTableBasisLimitsV0, F128FixedTableBasisV0};
    let t = fixture();
    let F128FixedMatrixProgramV0::DecisionDiagram(source) = &t.structure.1
    else {
      unreachable!();
    };
    let program = F128FixedMatrixProgramV0::CofactorBasis(
      F128FixedTableBasisV0::compile(
        source,
        F128FixedTableBasisLimitsV0 {
          state_slots: 10,
          dense_words: 10,
          word_operations: 100,
          coefficient_terms: 0,
        },
      )
      .unwrap(),
    );
    assert!(program.has_shape(1, 1));
    assert!(program.has_shape(0, 2));
    assert!(!program.has_shape(u32::MAX, 1));
    assert_ne!(program.digest(), t.structure.1.digest());
    for family in 0..3 {
      let mut changed = t.clone();
      match family {
        0 => changed.matrices[0].1 = program.clone(),
        1 => changed.structure.1 = program.clone(),
        _ => changed.jagged.1 = program.clone(),
      }
      assert_ne!(rebuild(changed.clone()).unwrap().digest(), t.digest());
      let expected = match family {
        0 => {
          changed.matrices[0].0.variables = 0;
          F128RootTableSetError::MatrixGeometry
        },
        1 => {
          changed.structure.0.row_variables = 0;
          F128RootTableSetError::StructureGeometry
        },
        _ => {
          changed.jagged.0.column_variables = 0;
          F128RootTableSetError::JaggedGeometry
        },
      };
      assert_eq!(rebuild(changed), Err(expected));
    }
  }
}
