//! Whole original-claim relation materialization without retained R1CS
//! matrices. These APIs consume setup-owned complete census expectations;
//! their full streamed identity is checked again before any result escapes.

use crate::{
  CompiledExecOriginalClaimsClosure, ExecReplayWitness, ExecRootClosedCensusV0,
};
use anyhow::{Result, ensure};
use ix_fflonk::{
  FflonkCheckedWitnessV1, PlonkArithmetizationStreamV0, PlonkArithmetizationV1,
  plan_plonk_stream_memory,
};
use ix_terminal_circuit::{
  Constraint, ConstraintPhase, R1csBuilder, R1csError, Stage4PublicInputsV1,
};

/// Progress only, not a completed census, assignment or proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecOriginalMaterializationProgressV0 {
  pub r1cs_constraints: u64,
  pub phase: ConstraintPhase,
}

fn validate_census(
  compiled: &CompiledExecOriginalClaimsClosure<'_, '_>,
  census: &ExecRootClosedCensusV0,
) -> Result<()> {
  ensure!(
    census.composition_digest == compiled.digest(),
    "streamed materialization requires this approved composition's census"
  );
  ensure!(
    census.r1cs.public_variables() == 2
      && census.plonk.public_input_rows == 2
      && census.public_scalar_bytes == 64,
    "streamed closed relation requires exactly two external Q limbs"
  );
  // Validates the complete PLONK dimensions, phase totals and supported
  // size-4n FFT domain without allocating any large arrays.
  plan_plonk_stream_memory(census.r1cs.variables(), &census.plonk)?;
  Ok(())
}

fn observed(
  mut emit: impl FnMut(&Constraint) -> Result<(), R1csError> + 'static,
  mut report: impl FnMut(ExecOriginalMaterializationProgressV0) + 'static,
) -> impl FnMut(&Constraint) -> Result<(), R1csError> + 'static {
  let mut count = 0u64;
  let mut last_phase = None;
  move |constraint| {
    emit(constraint)?;
    count = count.checked_add(1).ok_or(R1csError::CountOverflow)?;
    if last_phase != Some(constraint.phase) || count.is_multiple_of(10_000_000)
    {
      report(ExecOriginalMaterializationProgressV0 {
        r1cs_constraints: count,
        phase: constraint.phase,
      });
      last_phase = Some(constraint.phase);
    }
    Ok(())
  }
}

/// Materialize the complete approved PLONK relation directly from setup.
/// No guest, proof, expected statement or witness assignment is an input.
/// The caller supplies separate hard element-payload caps for the source
/// scratch and gate/copy/tail arrays; these do not admit full-process RSS,
/// SRS/key storage or subsequent proving. Every constraint is rehashed.
pub fn materialize_exec_original_claims_setup_observed(
  compiled: &CompiledExecOriginalClaimsClosure<'_, '_>,
  census: &ExecRootClosedCensusV0,
  source_payload_limit: u64,
  plonk_payload_limit: u64,
  report: impl FnMut(ExecOriginalMaterializationProgressV0) + 'static,
) -> Result<PlonkArithmetizationV1> {
  validate_census(compiled, census)?;
  // Full blueprint/source preflight precedes the large gate reservation.
  let source_bytes = compiled.setup_source_slots()?.payload_bytes()?;
  if source_bytes > source_payload_limit {
    return Err(
      R1csError::ResourceLimit {
        resource: "Exec setup source-slot payload bytes",
        limit: source_payload_limit,
        actual: source_bytes,
      }
      .into(),
    );
  }
  let stream = PlonkArithmetizationStreamV0::new(
    census.r1cs.clone(),
    census.plonk.clone(),
    plonk_payload_limit,
  )?;
  let mut builder = R1csBuilder::new_shape_streamed_observed(
    census.r1cs.clone(),
    observed(stream.observer(), report),
  )?;
  let emitted = compiled.emit_setup(&mut builder, source_payload_limit);
  builder.check_status()?;
  emitted?;
  let shape = builder.finish_streamed_shape()?;
  let arithmetization = stream.finish()?;
  ensure!(
    arithmetization.r1cs_digest() == shape.canonical_digest(),
    "independent R1CS/lowering streams must agree on the complete canonical matrix identity"
  );
  Ok(arithmetization)
}

/// Build an immutable, fully checked assignment for the WHOLE closed
/// relation without storing its R1CS matrices. The byte cap covers assignment
/// Vec capacity, not emitter state or whole-process RSS. This is not a proof.
/// A native replay or root check alone cannot construct the returned token.
pub fn check_exec_original_claims_streamed_observed(
  compiled: &CompiledExecOriginalClaimsClosure<'_, '_>,
  census: &ExecRootClosedCensusV0,
  public: Stage4PublicInputsV1,
  witness: &ExecReplayWitness<'_>,
  assignment_payload_limit: u64,
  report: impl FnMut(ExecOriginalMaterializationProgressV0) + 'static,
) -> Result<FflonkCheckedWitnessV1> {
  compiled.validate_witness(witness)?;
  validate_census(compiled, census)?;
  let mut builder = R1csBuilder::new_checked_streamed_observed(
    census.r1cs.clone(),
    assignment_payload_limit,
    observed(|_| Ok(()), report),
  )?;
  let emitted = compiled.constrain(&mut builder, public, witness);
  builder.check_status()?;
  let output = emitted?;
  ensure!(
    output.tables_digest() == compiled.tables().digest(),
    "streamed closed relation root-table identity mismatch"
  );
  let checked = builder.finish_checked_stream()?;
  Ok(FflonkCheckedWitnessV1::from_streamed(checked))
}
