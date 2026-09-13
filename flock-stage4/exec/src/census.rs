//! Matrix-free diagnostics; no key is constructed from a witness topology.

use crate::{ExecReplayWitness, replay::Stage4FlockVerifierCensusV1};
use anyhow::{Result, ensure};
use ix_fflonk::{PlonkGateCensusV1, PlonkGateProjectionV1};
use ix_terminal_circuit::*;

impl ExecReplayWitness<'_> {
  /// The explicit unresolved root sidecar for diagnostics only.
  pub fn diagnostic_public_inputs(&self) -> ExecRootConditionalPublicV0 {
    let roots = self.matrix_accumulator();
    let structure = roots.circuit_structure_root_claim();
    let jagged = roots.jagged_root_claim();
    ExecRootConditionalPublicV0 {
      public_digest: Stage4PublicInputsV1::from_statement_digest(
        self.public_digest(),
      ),
      matrices: roots
        .root_claims()
        .iter()
        .map(|root| F128RootMatrixClaimPublicInputV1 {
          matrix: root.matrix(),
          row_point: root.row_point().to_vec(),
          column_point: root.column_point().to_vec(),
          value: *root.value(),
        })
        .collect(),
      structure: F128CircuitStructureRootClaimPublicInputV1 {
        matrix: structure.matrix(),
        row_point: structure.row_point().to_vec(),
        column_point: structure.column_point().to_vec(),
        value: *structure.value(),
      },
      jagged: F128JaggedRootClaimPublicInputV1 {
        matrix: jagged.matrix(),
        row_point: jagged.row_point().to_vec(),
        column_point: jagged.column_point().to_vec(),
        value: *jagged.value(),
      },
    }
  }

  /// Borrow every verifier phase with the new generic statement binding.
  /// Topology here is diagnostic exporter output, NOT approved key material.
  pub fn diagnostic_witness(&self) -> ExecRootConditionalWitnessV0<'_> {
    let tape = self.transcript();
    let accumulator = self.matrix_accumulator();
    ExecRootConditionalWitnessV0 {
      statement_binding: self.binding(),
      commitments: self.commitments(),
      transcript: Stage4TranscriptWitnessV1 {
        trace: tape.chained_blake3(),
        observed_values: tape.observed_values(),
        byte_payloads: tape.byte_payloads(),
        challenges: tape.challenges(),
      },
      algebra: Stage4TraceWitnessV1 {
        trace: tape.f128_algebra(),
        private_values: tape.f128_private_values(),
      },
      wiring: Stage4TraceWitnessV1 {
        trace: self.wiring().trace(),
        private_values: self.wiring().private_values(),
      },
      merged_pcs: self.merged_pcs().trace(),
      multipoint: Stage4TraceWitnessV1 {
        trace: self.multipoint_assist().trace(),
        private_values: self.multipoint_assist().private_values(),
      },
      inner_ligerito: Stage4TraceWitnessV1 {
        trace: self.inner_ligerito().trace(),
        private_values: self.inner_ligerito().private_values(),
      },
      inner_ligerito_private_digests: self.inner_ligerito().private_digests(),
      accumulator_transcript: Stage4TranscriptWitnessV1 {
        trace: accumulator.chained_blake3(),
        observed_values: accumulator.observed_values(),
        byte_payloads: accumulator.byte_payloads(),
        challenges: accumulator.challenges(),
      },
      matrix_fold: accumulator.trace(),
      structure_fold: accumulator.circuit_structure_trace(),
      jagged_fold: accumulator.jagged_trace(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecReplayCensusV0 {
  pub native: Stage4FlockVerifierCensusV1,
  pub r1cs: R1csProjectionV1,
  pub plonk: PlonkGateCensusV1,
  pub root_conditional_public_scalar_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecReplayProgressV0 {
  pub constraints: u64,
  pub phase: ConstraintPhase,
}

/// Emit every relation constraint into matrix-free R1CS/PLONK counters and
/// compare all folded root values against the independently checked native
/// replay. This is not a satisfying-assignment check or a full FFLONK proof.
pub fn census_exec_replay(
  replay: &ExecReplayWitness<'_>,
) -> Result<ExecReplayCensusV0> {
  census_exec_replay_observed(replay, |_| {})
}

/// Same matrix-free census, reporting every phase transition and ten million
/// emitted constraints. The observer is diagnostic and never supplies values,
/// topology, or an acceptance result to the relation.
pub fn census_exec_replay_observed(
  replay: &ExecReplayWitness<'_>,
  mut report: impl FnMut(ExecReplayProgressV0) + 'static,
) -> Result<ExecReplayCensusV0> {
  let projection = PlonkGateProjectionV1::new();
  let mut project = projection.observer();
  let mut count = 0u64;
  let mut last_phase = None;
  let mut builder = R1csBuilder::new_projection_observed(move |constraint| {
    project(constraint);
    count += 1;
    if last_phase != Some(constraint.phase) || count.is_multiple_of(10_000_000)
    {
      report(ExecReplayProgressV0 {
        constraints: count,
        phase: constraint.phase,
      });
      last_phase = Some(constraint.phase);
    }
  });
  let public = replay.diagnostic_public_inputs();
  let output = constrain_exec_root_conditional(
    &mut builder,
    &public,
    replay.diagnostic_witness(),
  )?;
  check_roots(&output, &public)?;
  let r1cs = builder.finish_projection()?;
  let plonk = projection.finish_for_sizing(&r1cs)?;
  Ok(ExecReplayCensusV0 {
    native: replay.census(),
    root_conditional_public_scalar_bytes: 32
      * u64::try_from(public.field_elements().len())?,
    r1cs,
    plonk,
  })
}

pub(crate) fn check_roots(
  output: &Stage4RelationCircuitOutputV1,
  public: &ExecRootConditionalPublicV0,
) -> Result<()> {
  ensure!(
    output.matrices.root_claims.len() == public.matrices.len(),
    "Exec matrix root count differential"
  );
  for (root, expected) in
    output.matrices.root_claims.iter().zip(&public.matrices)
  {
    ensure!(
      root.matrix == expected.matrix,
      "Exec matrix root identity differential"
    );
    check_root(
      &root.row_point,
      &root.column_point,
      &root.value,
      &expected.row_point,
      &expected.column_point,
      &expected.value,
    )?;
  }
  let root = &output.structure.root_claim;
  ensure!(
    root.matrix == public.structure.matrix,
    "Exec structure identity differential"
  );
  check_root(
    &root.row_point,
    &root.column_point,
    &root.value,
    &public.structure.row_point,
    &public.structure.column_point,
    &public.structure.value,
  )?;
  let root = &output.jagged.root_claim;
  ensure!(
    root.matrix == public.jagged.matrix,
    "Exec jagged identity differential"
  );
  check_root(
    &root.row_point,
    &root.column_point,
    &root.value,
    &public.jagged.row_point,
    &public.jagged.column_point,
    &public.jagged.value,
  )
}

fn check_root(
  row: &[F128VariablesV1],
  col: &[F128VariablesV1],
  value: &F128VariablesV1,
  expected_row: &[[u8; 16]],
  expected_col: &[[u8; 16]],
  expected: &[u8; 16],
) -> Result<()> {
  ensure!(
    row.iter().map(|x| *x.value()).collect::<Vec<_>>() == expected_row,
    "Exec root row differential"
  );
  ensure!(
    col.iter().map(|x| *x.value()).collect::<Vec<_>>() == expected_col,
    "Exec root column differential"
  );
  ensure!(value.value() == expected, "Exec root evaluation differential");
  Ok(())
}
