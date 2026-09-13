//! Immutable fixed programs for direct discharge of every ORIGINAL claim.
//! This is a distinct composition from the auxiliary random-fold root route.

use crate::{
  F128CircuitStructureMatrixIdV1, F128FixedTableBasisV0,
  F128JaggedDirectTableV0, F128RootTableSetError, F128StructuredMatricesV0,
};

/// No points, values, proofs, or native evaluation callbacks occur here.
/// Construction checks identity/geometry only; coefficient provenance and
/// original-claim completeness must be supplied by the approved setup owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128OriginalClaimTablesV0 {
  registry: [u8; 32],
  circuit: [u8; 32],
  matrices: F128StructuredMatricesV0,
  structure: (F128CircuitStructureMatrixIdV1, F128FixedTableBasisV0),
  jagged: F128JaggedDirectTableV0,
}

impl F128OriginalClaimTablesV0 {
  pub fn new(
    registry: [u8; 32],
    circuit: [u8; 32],
    matrices: F128StructuredMatricesV0,
    structure: (F128CircuitStructureMatrixIdV1, F128FixedTableBasisV0),
    jagged: F128JaggedDirectTableV0,
  ) -> Result<Self, F128RootTableSetError> {
    use F128RootTableSetError as Error;
    if matrices.outputs().iter().any(|(id, _)| id.registry_digest != registry) {
      return Err(Error::RegistryIdentity);
    }
    if structure.0.circuit_digest != circuit
      || jagged.matrix().circuit_digest != circuit
    {
      return Err(Error::CircuitIdentity);
    }
    if u64::from(structure.0.row_variables)
      + u64::from(structure.0.column_variables)
      != structure.1.layers().len() as u64
    {
      return Err(Error::StructureGeometry);
    }
    Ok(Self { registry, circuit, matrices, structure, jagged })
  }
  pub fn registry_digest(&self) -> [u8; 32] {
    self.registry
  }
  pub fn circuit_digest(&self) -> [u8; 32] {
    self.circuit
  }
  pub fn matrices(&self) -> &F128StructuredMatricesV0 {
    &self.matrices
  }
  pub fn structure(
    &self,
  ) -> &(F128CircuitStructureMatrixIdV1, F128FixedTableBasisV0) {
    &self.structure
  }
  pub fn jagged(&self) -> &F128JaggedDirectTableV0 {
    &self.jagged
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/original-claim-table-set/v0\0");
    hash.update(&self.registry);
    hash.update(&self.circuit);
    hash.update(&self.matrices.digest());
    hash.update(&self.structure.0.circuit_digest);
    hash.update(&self.structure.0.row_variables.to_le_bytes());
    hash.update(&self.structure.0.column_variables.to_le_bytes());
    hash.update(&self.structure.1.digest());
    hash.update(&self.jagged.digest());
    *hash.finalize().as_bytes()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    F128FixedTableBasisLimitsV0, F128FixedTableLimitsV0, F128FixedTableV0,
    F128JaggedDirectLimitsV0, F128JaggedMatrixIdV1, F128MatrixSideV1,
    F128StaticMatrixIdV1, F128StructuredMatricesLimitsV0,
  };
  fn fixture() -> F128OriginalClaimTablesV0 {
    let matrices = F128StructuredMatricesV0::compile(
      0,
      [(
        F128StaticMatrixIdV1 {
          registry_digest: [1; 32],
          table: 0,
          side: F128MatrixSideV1::A,
          variables: 1,
        },
        [(0, 1)],
      )],
      F128StructuredMatricesLimitsV0 {
        tables: 1,
        source_entries: 1,
        blocks: 10,
        coefficient_terms: 10,
        shared_nodes: 10,
        temporary_nodes: 100,
      },
    )
    .unwrap();
    let source = F128FixedTableV0::compile(
      &[1, 0],
      [(1, [7; 16])],
      F128FixedTableLimitsV0 { entries: 1, nodes: 100 },
    )
    .unwrap();
    let structure = (
      F128CircuitStructureMatrixIdV1 {
        circuit_digest: [2; 32],
        row_variables: 1,
        column_variables: 1,
      },
      F128FixedTableBasisV0::compile(
        &source,
        F128FixedTableBasisLimitsV0 {
          state_slots: 100,
          dense_words: 1000,
          word_operations: 10000,
          coefficient_terms: 1000,
        },
      )
      .unwrap(),
    );
    let jagged = F128JaggedDirectTableV0::compile(
      F128JaggedMatrixIdV1 {
        circuit_digest: [2; 32],
        row_variables: 1,
        column_variables: 2,
      },
      [(0, 1, 2)],
      [0, 1],
      F128JaggedDirectLimitsV0 {
        runs: 1,
        combo_terms: 2,
        row_nodes: 100,
        equality_nodes: 100,
      },
    )
    .unwrap();
    F128OriginalClaimTablesV0::new(
      [1; 32], [2; 32], matrices, structure, jagged,
    )
    .unwrap()
  }
  #[test]
  fn identity_geometry_and_each_program_are_bound() {
    let original = fixture();
    assert_eq!(original, fixture());
    for field in 0..5 {
      let mut changed = original.clone();
      match field {
        0 => changed.registry[0] ^= 1,
        1 => changed.circuit[0] ^= 1,
        2 => changed.structure.0.circuit_digest[0] ^= 1,
        3 => changed.structure.0.row_variables += 1,
        4 => changed.structure.0.column_variables = u32::MAX,
        _ => unreachable!(),
      }
      assert_ne!(original.digest(), changed.digest());
      assert!(
        F128OriginalClaimTablesV0::new(
          changed.registry,
          changed.circuit,
          changed.matrices,
          changed.structure,
          changed.jagged
        )
        .is_err()
      );
    }
    let mut changed = original.clone();
    changed.structure.1 = F128FixedTableBasisV0::compile(
      &F128FixedTableV0::compile(
        &[1, 0],
        [(1, [9; 16])],
        F128FixedTableLimitsV0 { entries: 1, nodes: 100 },
      )
      .unwrap(),
      F128FixedTableBasisLimitsV0 {
        state_slots: 100,
        dense_words: 1000,
        word_operations: 10000,
        coefficient_terms: 1000,
      },
    )
    .unwrap();
    assert_ne!(original.digest(), changed.digest());
  }
}
