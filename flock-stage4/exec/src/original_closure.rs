//! Proof-free setup ownership for direct closure of ALL original claims.
//! This is a separate composition identity, not a change to the old fold route.

use crate::{CompiledExecReplay, ExecReplayWitness};
use anyhow::{Result, ensure};
use flock_prover::{
  matrix_fold::JaggedTable, pcs::jagged::JaggedParams, union::UnionInstance,
};
use ix_stage4_trace::{
  F128FixedTableBasisLimitsV0, F128FixedTableBasisV0, F128FixedTableLimitsV0,
  F128JaggedDirectLimitsV0, F128JaggedDirectTableV0, F128MatrixSideV1,
  F128OriginalClaimTablesV0, F128StructuredMatricesLimitsV0,
  F128StructuredMatricesV0,
};
use ix_terminal_circuit::{
  ExecOriginalClaimsClosedOutputV0, R1csBuilder, Stage4PublicInputsV1,
  constrain_exec_original_claims_closed, validate_exec_original_claim_tables,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecOriginalClosureLimitsV0 {
  /// Shared matrix construction, including temporary diagrams and all tables.
  pub matrices: F128StructuredMatricesLimitsV0,
  /// Existing exact source-table compiler, including its temporary tables.
  pub source_tables: F128FixedTableLimitsV0,
  pub structure: F128FixedTableBasisLimitsV0,
  pub jagged: F128JaggedDirectLimitsV0,
}

/// No public constructor, replacement fields, or prover-selected programs.
/// This object borrows the complete approved replay and owns exact programs
/// derived from its registry/circuit/layout. Its digest is NOT a terminal key.
pub struct CompiledExecOriginalClaimsClosure<'r, 's> {
  replay: &'r CompiledExecReplay<'s>,
  tables: F128OriginalClaimTablesV0,
}
impl<'r, 's> CompiledExecOriginalClaimsClosure<'r, 's> {
  pub fn replay_setup(&self) -> &'r CompiledExecReplay<'s> {
    self.replay
  }
  pub fn tables(&self) -> &F128OriginalClaimTablesV0 {
    &self.tables
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/original-claims-closed-composition/v0\0");
    hash.update(&self.replay.identities().digest());
    hash.update(&self.tables.digest());
    *hash.finalize().as_bytes()
  }
  pub fn constrain(
    &self,
    builder: &mut R1csBuilder,
    public: Stage4PublicInputsV1,
    witness: &ExecReplayWitness<'_>,
  ) -> Result<ExecOriginalClaimsClosedOutputV0> {
    self.validate_witness(witness)?;
    Ok(constrain_exec_original_claims_closed(
      builder,
      public,
      &self.tables,
      witness.diagnostic_witness().original_claims(),
    )?)
  }
  pub(crate) fn validate_witness(
    &self,
    witness: &ExecReplayWitness<'_>,
  ) -> Result<()> {
    ensure!(
      witness.setup().identities() == self.replay.exec_setup().identities()
        && witness.topology_digest() == self.replay.identities().digest()
        && witness.binding() == self.replay.binding(),
      "original-claim closure requires the same approved Exec replay setup"
    );
    Ok(())
  }
}

/// No guest, proof, commitment, claim value, or transcript point is an input.
/// Every registry A/B matrix, all eight structure planes and the complete
/// fixed jagged layout are supplied by the approved generic Exec setup.
pub fn compile_exec_original_claims_closure<'r, 's>(
  replay: &'r CompiledExecReplay<'s>,
  limits: ExecOriginalClosureLimitsV0,
) -> Result<CompiledExecOriginalClaimsClosure<'r, 's>> {
  let setup = replay.exec_setup();
  let shape = setup.verifier_shape();
  ensure!(
    shape.registry.num_element() == 0,
    "original-claim closure requires the approved Boolean registry"
  );
  let claims = &replay.boolean.trace.deferred_matrix_claims;
  ensure!(
    claims.len()
      == shape
        .registry
        .num_boolean()
        .checked_mul(2)
        .ok_or_else(|| anyhow::anyhow!("matrix claim count overflow"))?,
    "every original registry A/B claim is required"
  );
  let shared = claims
    .iter()
    .max_by_key(|c| c.matrix.variables)
    .ok_or_else(|| anyhow::anyhow!("missing original matrix claims"))?;
  ensure!(
    shared.row.low.len().is_power_of_two(),
    "original matrix low-vector length"
  );
  let low = shared.row.low.len().ilog2();
  ensure!(low <= 6, "original matrix low-vector compiler limit");
  for (index, claim) in claims.iter().enumerate() {
    let id = claim.matrix;
    let slot = index / 2;
    let ty = &shape.registry.boolean_types()[slot];
    ensure!(
      id.table == slot as u64
        && id.side
          == if index % 2 == 0 {
            F128MatrixSideV1::A
          } else {
            F128MatrixSideV1::B
          }
        && id.registry_digest == setup.identities().registry
        && id.variables as usize == ty.k_log
        && id.variables >= low
        && id.variables <= 32,
      "original matrix identity/order/geometry"
    );
    let high = (id.variables - low) as usize;
    ensure!(
      claim.row.low == shared.row.low
        && claim.column.low == shared.column.low
        && shared.column.low.len() == shared.row.low.len()
        && shared.row.point.get(..high) == Some(claim.row.point.as_slice())
        && shared.column.point.get(..high)
          == Some(claim.column.point.as_slice()),
      "original matrix weights must use the same symbolic references"
    );
    let matrix = match id.side {
      F128MatrixSideV1::A => &ty.a_0,
      F128MatrixSideV1::B => &ty.b_0,
    };
    let side = 1usize
      .checked_shl(id.variables)
      .ok_or_else(|| anyhow::anyhow!("matrix dimension overflow"))?;
    ensure!(
      matrix.num_rows == side
        && matrix.num_cols == side
        && matrix.rows.len() == side
        && matrix.rows.iter().flatten().all(|&col| col < side),
      "original matrix source geometry"
    );
  }
  let matrices = F128StructuredMatricesV0::compile(
    low,
    claims.iter().enumerate().map(|(index, claim)| {
      let ty = &shape.registry.boolean_types()[index / 2];
      let matrix = match claim.matrix.side {
        F128MatrixSideV1::A => &ty.a_0,
        F128MatrixSideV1::B => &ty.b_0,
      };
      (
        claim.matrix,
        matrix.rows.iter().enumerate().flat_map(|(row, cols)| {
          cols.iter().map(move |&col| {
            (
              u32::try_from(row).expect("validated 32-bit matrix row"),
              u32::try_from(col).expect("validated 32-bit matrix column"),
            )
          })
        }),
      )
    }),
    limits.matrices,
  )?;
  // Retain the existing independently checked FULL structure table compiler.
  // Its temporary other tables are bounded and discarded, not used as hints.
  let sources = crate::compile_exec_root_tables(replay, limits.source_tables)?;
  let (structure_id, source) = sources.structure();
  let structure =
    (*structure_id, F128FixedTableBasisV0::compile(source, limits.structure)?);
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let dense = setup
    .pcs_params()
    .m
    .checked_sub(7)
    .ok_or_else(|| anyhow::anyhow!("jagged PCS dimension"))?;
  let params =
    JaggedParams::from_heights(&union.jagged_heights(), union.n_log(), dense);
  let native = JaggedTable::from_params(&params);
  let id = replay.pcs.multipoint.matrix;
  ensure!(
    id.circuit_digest == setup.identities().circuit
      && id.row_variables as usize == native.k
      && id.column_variables as usize == native.n_col_vars(),
    "original jagged source identity/geometry"
  );
  let jagged = F128JaggedDirectTableV0::compile(
    id,
    native.bounds.iter().copied(),
    replay.pcs.multipoint.group_column_addresses.iter().copied(),
    limits.jagged,
  )?;
  let tables = F128OriginalClaimTablesV0::new(
    setup.identities().registry,
    setup.identities().circuit,
    matrices,
    structure,
    jagged,
  )?;
  validate_exec_original_claim_tables(
    &tables,
    replay.binding(),
    &replay.boolean.trace,
    &replay.wiring,
    &replay.pcs.multipoint,
  )?;
  Ok(CompiledExecOriginalClaimsClosure { replay, tables })
}
