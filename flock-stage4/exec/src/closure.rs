//! Approved setup ownership for the prototype root-closed composition.
//! This is not a terminal key compiler, resource admission, or proof API.

use crate::{CompiledExecReplay, ExecReplayWitness};
use anyhow::{Result, ensure};
use ix_stage4_trace::{
  BinaryLinearMapLimitsV0, BinaryLinearValidationLimitsV0,
  F128FixedMatrixProgramV0 as Program, F128FixedTableLimitsV0,
  F128RootTableSetV0,
};
use ix_terminal_circuit::{
  ExecRootClosedCircuitOutputV0, R1csBuilder, Stage4PublicInputsV1,
  constrain_exec_root_closed, validate_exec_root_tables,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecRootClosureCompilationLimitsV0 {
  /// Entire exact diagram compiler, including its temporary BLAKE3 diagrams.
  pub diagrams: F128FixedTableLimitsV0,
  /// Shared BLAKE3 formula construction and per-map geometry bounds.
  pub linear_program: BinaryLinearMapLimitsV0,
  /// Additional exhaustive A/B coefficient-check pass.
  pub linear_validation: BinaryLinearValidationLimitsV0,
}

/// The topology and tables are both borrowed/derived from the same approved
/// setup before any guest or proof is provided. Private fields prevent phase
/// or table substitution. Its digest is NOT an R1CS/FFLONK key identity.
pub struct CompiledExecRootClosure<'r, 's> {
  replay: &'r CompiledExecReplay<'s>,
  tables: F128RootTableSetV0,
}

impl<'r, 's> CompiledExecRootClosure<'r, 's> {
  pub fn replay_setup(&self) -> &'r CompiledExecReplay<'s> {
    self.replay
  }
  pub fn tables(&self) -> &F128RootTableSetV0 {
    &self.tables
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/root-closed-composition/v0\0");
    hash.update(&self.replay.identities().digest());
    hash.update(&self.tables.digest());
    *hash.finalize().as_bytes()
  }

  /// Emit using already-validated native replay values and the caller's
  /// EXTERNALLY EXPECTED public Q, never a Q selected from the witness here.
  /// Native replay is witness generation, not the circuit's soundness proof.
  /// The current emitter still needs a witness; this is not proof-free setup
  /// of R1CS matrices or a terminal verification key.
  pub fn constrain(
    &self,
    builder: &mut R1csBuilder,
    public: Stage4PublicInputsV1,
    witness: &ExecReplayWitness<'_>,
  ) -> Result<ExecRootClosedCircuitOutputV0> {
    self.validate_witness(witness)?;
    Ok(constrain_exec_root_closed(
      builder,
      public,
      &self.tables,
      witness.diagnostic_witness(),
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
      "closed composition requires the same approved Exec replay setup"
    );
    Ok(())
  }
}

/// Compile a complete root set with BLAKE3's exhaustively checked linear
/// formulas and exact diagrams for every other matrix, structure, and layout.
/// No point, value, statement, image, or proof is a setup input.
pub fn compile_exec_root_closure<'r, 's>(
  replay: &'r CompiledExecReplay<'s>,
  limits: ExecRootClosureCompilationLimitsV0,
) -> Result<CompiledExecRootClosure<'r, 's>> {
  let diagrams = crate::compile_exec_root_tables(replay, limits.diagrams)?;
  let linear = crate::compile_exec_blake3_root_maps(
    replay,
    limits.linear_program,
    limits.linear_validation,
  )?;
  let mut replaced = 0;
  let matrices = diagrams
    .matrices()
    .iter()
    .map(|(id, diagram)| {
      let program = if let Some((_, map)) =
        linear.matrices().iter().find(|(key, _)| key == id)
      {
        replaced += 1;
        Program::BinaryLinear(map.clone())
      } else {
        Program::DecisionDiagram(diagram.clone())
      };
      (*id, program)
    })
    .collect();
  ensure!(
    replaced == 2,
    "both approved BLAKE3 matrices must be covered exactly once"
  );
  let (structure_id, structure) = diagrams.structure();
  let (jagged_id, jagged) = diagrams.jagged();
  let binding = replay.binding();
  let tables = F128RootTableSetV0::new(
    binding.registry_digest,
    binding.circuit_digest,
    matrices,
    (*structure_id, Program::DecisionDiagram(structure.clone())),
    (*jagged_id, Program::DecisionDiagram(jagged.clone())),
  )?;
  validate_exec_root_tables(
    &tables,
    binding,
    &replay.folds.matrices,
    &replay.folds.structure,
    &replay.folds.jagged,
  )?;
  Ok(CompiledExecRootClosure { replay, tables })
}
