//! Complete leaf accumulation topology. All input claims are covered exactly
//! once; this compiler neither computes nor discharges their table values.

use super::{
  boolean::BooleanBlueprint,
  pcs::PcsBlueprint,
  tape::{Tape, nonzero},
};
use crate::replay::Stage4TranscriptOpV1;
use anyhow::Result;
use flock_prover::matrix_fold::FoldGrinding;
use ix_stage4_trace::{
  F128CircuitStructureAccumulatorTraceV1, F128CircuitStructureMatrixIdV1,
  F128JaggedAccumulatorTraceV1, F128JaggedComboTermBindingV1,
  F128JaggedFoldClaimBindingV1, F128JaggedRowBindingV1,
  F128MatrixAccumulatorTraceV1, F128MatrixFoldClaimBindingV1,
  F128MatrixFoldRoundV1, F128MatrixFoldTraceV1, F128WiringTraceV1,
};
use ixby_flock::ixby::exec::CompiledExec;

pub(crate) struct FoldBlueprint {
  pub(crate) hash: super::hash::HashBlueprint,
  pub(crate) operations: Vec<Stage4TranscriptOpV1>,
  pub(crate) payload_lengths: Vec<usize>,
  pub(crate) observed_values: u64,
  pub(crate) challenges: u64,
  pub(crate) matrices: F128MatrixAccumulatorTraceV1,
  pub(crate) structure: F128CircuitStructureAccumulatorTraceV1,
  pub(crate) jagged: F128JaggedAccumulatorTraceV1,
}

pub(crate) fn compile_folds(
  setup: &CompiledExec,
  wiring: &F128WiringTraceV1,
  boolean: &BooleanBlueprint,
  pcs: &PcsBlueprint,
) -> Result<FoldBlueprint> {
  // Same fixed auxiliary protocol as replay_exec; this is not a recursive
  // aggregation of an unspecified number of prior accumulators.
  let grinding = FoldGrinding::per_challenge_128();
  let mut tape = Tape::new();
  tape.label(b"flock-aggregate-v0");
  let registry_digest_payload = tape.bytes(32);
  let prior_count_payload = tape.bytes(1);
  let mut folds = Vec::new();
  for (index, claim) in boolean.trace.deferred_matrix_claims.iter().enumerate()
  {
    tape.label(b"flock-matrix-fold-v0");
    let binding = F128MatrixFoldClaimBindingV1 {
      claim: index as u64,
      row_low_observations: tape.observe_slice(claim.row.low.len()),
      row_point_observations: tape.observe_slice(claim.row.point.len()),
      column_low_observations: tape.observe_slice(claim.column.low.len()),
      column_point_observations: tape.observe_slice(claim.column.point.len()),
      value_observation: tape.observe(),
    };
    let tail = fold_tail(
      &mut tape,
      1,
      claim.matrix.variables,
      claim.matrix.variables,
      grinding,
    );
    folds.push(F128MatrixFoldTraceV1 {
      matrix: claim.matrix,
      claims: vec![binding],
      lambda_challenges: tail.lambda,
      column_rounds: tail.column,
      bridge_observations: tail.bridge,
      mu_challenges: tail.mu,
      row_rounds: tail.row,
      value_observation: tail.value,
    });
  }
  let matrices = F128MatrixAccumulatorTraceV1 {
    registry_digest: setup.identities().registry,
    registry_digest_payload,
    prior_count_payload,
    prior_accumulators: 0,
    folds,
  };
  tape.label(b"flock-aggregate-sigma-v1");
  let circuit_digest_payload = tape.bytes(32);
  tape.label(b"flock-matrix-fold-v0");
  let row_variables = wiring.row_variables;
  let column_variables = wiring.structure_base_variables + 3;
  let structure_claims = (0..3)
    .map(|claim| F128MatrixFoldClaimBindingV1 {
      claim,
      row_low_observations: tape.observe_slice(1),
      row_point_observations: tape.observe_slice(row_variables as usize),
      column_low_observations: tape.observe_slice(1),
      column_point_observations: tape.observe_slice(column_variables as usize),
      value_observation: tape.observe(),
    })
    .collect();
  let tail = fold_tail(&mut tape, 3, row_variables, column_variables, grinding);
  let structure = F128CircuitStructureAccumulatorTraceV1 {
    matrix: F128CircuitStructureMatrixIdV1 {
      circuit_digest: setup.identities().circuit,
      row_variables,
      column_variables,
    },
    circuit_digest_payload,
    claims: structure_claims,
    lambda_challenges: tail.lambda,
    column_rounds: tail.column,
    bridge_observations: tail.bridge,
    mu_challenges: tail.mu,
    row_rounds: tail.row,
    value_observation: tail.value,
  };
  tape.label(b"flock-aggregate-jagged-v0");
  let circuit_digest_payload = tape.bytes(32);
  tape.label(b"flock-jagged-fold-v0");
  let shape_observation = tape.observe();
  let matrix = pcs.multipoint.matrix;
  let mut jagged_claims = Vec::new();
  for claim in 0..3 {
    let row = if claim < 2 {
      F128JaggedRowBindingV1::Eq {
        header_observation: tape.observe(),
        scale_observation: tape.observe(),
        point_observations: tape.observe_slice(matrix.row_variables as usize),
      }
    } else {
      F128JaggedRowBindingV1::Combo {
        header_observation: tape.observe(),
        terms: pcs
          .multipoint
          .group_column_addresses
          .iter()
          .map(|&address| F128JaggedComboTermBindingV1 {
            coefficient_observation: tape.observe(),
            address_observation: tape.observe(),
            address,
          })
          .collect(),
      }
    };
    jagged_claims.push(F128JaggedFoldClaimBindingV1 {
      claim,
      row,
      column_point_observations: tape
        .observe_slice(matrix.column_variables as usize),
      value_observation: tape.observe(),
    });
  }
  let tail = fold_tail(
    &mut tape,
    3,
    matrix.row_variables,
    matrix.column_variables,
    grinding,
  );
  let jagged = F128JaggedAccumulatorTraceV1 {
    matrix,
    circuit_digest_payload,
    shape_observation,
    claims: jagged_claims,
    lambda_challenges: tail.lambda,
    column_rounds: tail.column,
    bridge_observations: tail.bridge,
    mu_challenges: tail.mu,
    row_rounds: tail.row,
    value_observation: tail.value,
  };
  let (observed, challenges) = (
    usize::try_from(tape.address.observed)?,
    usize::try_from(tape.address.challenges)?,
  );
  matrices.validate(
    boolean.trace.deferred_matrix_claims.len(),
    observed,
    tape.payload_lengths.len(),
    challenges,
  )?;
  structure.validate(3, observed, tape.payload_lengths.len(), challenges)?;
  jagged.validate(3, observed, tape.payload_lengths.len(), challenges)?;
  Ok(FoldBlueprint {
    hash: super::hash::compile_hash(
      &tape.ops,
      crate::replay::STAGE4_MATRIX_ACCUMULATOR_TRANSCRIPT_DOMAIN,
      tape.address.observed,
      tape.address.challenges,
      &tape.payload_lengths,
    )?,
    operations: tape.ops,
    payload_lengths: tape.payload_lengths,
    observed_values: tape.address.observed,
    challenges: tape.address.challenges,
    matrices,
    structure,
    jagged,
  })
}

struct Tail {
  lambda: Vec<u64>,
  column: Vec<F128MatrixFoldRoundV1>,
  bridge: Vec<u64>,
  mu: Vec<u64>,
  row: Vec<F128MatrixFoldRoundV1>,
  value: u64,
}

fn fold_tail(
  tape: &mut Tape,
  claims: usize,
  rows: u32,
  columns: u32,
  grinding: FoldGrinding,
) -> Tail {
  Tail {
    lambda: tape.squeeze_slice(claims, nonzero(grinding.combination_bits)),
    column: rounds(tape, columns, grinding),
    bridge: (0..claims).map(|_| tape.observe()).collect(),
    mu: tape.squeeze_slice(claims, nonzero(grinding.combination_bits)),
    row: rounds(tape, rows, grinding),
    value: tape.observe(),
  }
}

fn rounds(
  tape: &mut Tape,
  count: u32,
  grinding: FoldGrinding,
) -> Vec<F128MatrixFoldRoundV1> {
  (0..count)
    .map(|_| F128MatrixFoldRoundV1 {
      one_observation: tape.observe(),
      infinity_observation: tape.observe(),
      challenge: tape.squeeze(nonzero(grinding.round_bits)),
    })
    .collect()
}
