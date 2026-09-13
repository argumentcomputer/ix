//! Exact, setup-owned linear formulas for the approved BLAKE3 root matrices.
//! This component does not alter Stage 3 tables or close the Exec relation.

use crate::CompiledExecReplay;
use anyhow::{Result, ensure};
use flock_prover::r1cs_hashes::blake3 as b;
use ix_stage4_trace::{
  BinaryLinearMapLimitsV0, BinaryLinearMapV0, BinaryLinearValidationLimitsV0,
  F128MatrixSideV1, F128StaticMatrixIdV1,
};
use ixby_flock::ixby::exec::CompiledExec;

#[path = "blake3_table_formula.rs"]
mod formula;

pub struct CompiledExecBlake3RootMaps<'a> {
  setup: &'a CompiledExec,
  replay_digest: [u8; 32],
  matrices: [(F128StaticMatrixIdV1, BinaryLinearMapV0); 2],
}

impl<'a> CompiledExecBlake3RootMaps<'a> {
  pub fn exec_setup(&self) -> &'a CompiledExec {
    self.setup
  }
  pub fn matrices(&self) -> &[(F128StaticMatrixIdV1, BinaryLinearMapV0); 2] {
    &self.matrices
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/exec-blake3-linear-roots/v0\0");
    hash.update(&self.replay_digest);
    hash.update(&self.matrices[0].0.table.to_le_bytes());
    for (_, map) in &self.matrices {
      hash.update(&map.digest());
    }
    *hash.finalize().as_bytes()
  }
}

/// Compile only from approved setup and accept the formula ONLY after every
/// A/B coefficient matches that setup's concrete registry. The coefficient
/// memory limit is peak scratch per matrix; the entry limit covers BOTH
/// matrices together. No digest-only or sampled-value match is sufficient.
pub fn compile_exec_blake3_root_maps<'a>(
  replay: &CompiledExecReplay<'a>,
  shape_limits: BinaryLinearMapLimitsV0,
  validation_limits: BinaryLinearValidationLimitsV0,
) -> Result<CompiledExecBlake3RootMaps<'a>> {
  let setup = replay.exec_setup();
  let slots = setup
    .verifier_shape()
    .registry
    .boolean_types()
    .iter()
    .enumerate()
    .filter(|(_, ty)| {
      ty.k_log == b::K_LOG
        && ty.useful_bits == b::USEFUL_BITS
        && ty.const_pin == Some(b::Z_CONST_POS)
    })
    .collect::<Vec<_>>();
  ensure!(slots.len() == 1, "approved Exec BLAKE3 table must be unique");
  let (slot, ty) = slots[0];
  for matrix in [&ty.a_0, &ty.b_0] {
    ensure!(
      matrix.num_rows == b::K
        && matrix.num_cols == b::K
        && matrix.rows.len() == b::K,
      "approved BLAKE3 table geometry"
    );
  }
  let entries = [&ty.a_0, &ty.b_0]
    .into_iter()
    .flat_map(|m| &m.rows)
    .try_fold(0u64, |sum, row| sum.checked_add(row.len() as u64))
    .ok_or_else(|| anyhow::anyhow!("BLAKE3 source entry count overflow"))?;
  ensure!(
    entries <= validation_limits.source_entries,
    "BLAKE3 source entry bound"
  );
  let [a, bv] = formula::compile(shape_limits)?;
  a.check_rows(&ty.a_0.rows, validation_limits)?;
  bv.check_rows(&ty.b_0.rows, validation_limits)?;
  let variables = u32::try_from(b::K_LOG)?;
  let id = |side| F128StaticMatrixIdV1 {
    registry_digest: setup.identities().registry,
    table: slot as u64,
    side,
    variables,
  };
  let matrices = [(id(F128MatrixSideV1::A), a), (id(F128MatrixSideV1::B), bv)];
  for (id, _) in &matrices {
    ensure!(
      replay.folds.matrices.folds.iter().filter(|f| f.matrix == *id).count()
        == 1,
      "BLAKE3 matrix must have one exact approved replay root"
    );
  }
  Ok(CompiledExecBlake3RootMaps {
    setup,
    replay_digest: replay.identities().digest(),
    matrices,
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn fixed_formula_compilation_is_bounded_and_deterministic() {
    let limits = BinaryLinearMapLimitsV0 {
      inputs: 16_384,
      outputs: 16_384,
      xors: 100_000,
    };
    let maps = formula::compile(limits).unwrap();
    assert_eq!(maps, formula::compile(limits).unwrap());
    for map in maps {
      assert_eq!(map.inputs(), 16_384);
      assert_eq!(map.outputs().len(), 16_384);
      assert!(map.xors().len() > 10_000 && map.xors().len() < 100_000);
    }
    for limits in [
      BinaryLinearMapLimitsV0 { inputs: 16_383, ..limits },
      BinaryLinearMapLimitsV0 { outputs: 16_383, ..limits },
      BinaryLinearMapLimitsV0 { xors: 1, ..limits },
    ] {
      assert!(formula::compile(limits).is_err());
    }
  }
}
