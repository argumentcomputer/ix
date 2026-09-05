//! Canonical composition of the complete Flock verifier relation.

use crate::*;
use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ix_stage4_trace::{
  ChainedBlake3TranscriptV1, F128AlgebraTraceV1,
  F128CircuitStructureAccumulatorTraceV1, F128InnerLigeritoTraceV1,
  F128JaggedAccumulatorTraceV1, F128MatrixAccumulatorTraceV1,
  F128MergedPcsFrontendTraceV1, F128MultipointTwistedAssistTraceV1,
  F128StatementBindingTraceV1, F128WiringTraceV1,
};
use std::{error::Error, fmt};

/// Borrowed native values for one already-normalized transcript.
#[derive(Clone, Copy)]
pub struct Stage4TranscriptWitnessV1<'a> {
  pub trace: &'a ChainedBlake3TranscriptV1,
  pub observed_values: &'a [[u8; 16]],
  pub byte_payloads: &'a [Vec<u8>],
  pub challenges: &'a [[u8; 16]],
}

#[derive(Clone, Copy)]
pub struct Stage4TraceWitnessV1<'a, T> {
  pub trace: &'a T,
  pub private_values: &'a [[u8; 16]],
}

/// Backend-neutral inputs to the complete relation. The fixed trace topology
/// and statement constants belong to the circuit-specific verification key;
/// callers must not choose a fresh key from an untrusted proof's topology.
pub struct Stage4RelationWitnessV1<'a> {
  pub statement_binding: &'a F128StatementBindingTraceV1,
  pub stage3_statement: &'a [u8; STAGE4_STAGE3_STATEMENT_BYTES],
  pub public_values: &'a [[u8; 16]],
  pub transcript: Stage4TranscriptWitnessV1<'a>,
  pub algebra: Stage4TraceWitnessV1<'a, F128AlgebraTraceV1>,
  pub wiring: Stage4TraceWitnessV1<'a, F128WiringTraceV1>,
  pub merged_pcs: &'a F128MergedPcsFrontendTraceV1,
  pub multipoint: Stage4TraceWitnessV1<'a, F128MultipointTwistedAssistTraceV1>,
  pub inner_ligerito: Stage4TraceWitnessV1<'a, F128InnerLigeritoTraceV1>,
  pub inner_ligerito_private_digests: &'a [[u8; 32]],
  pub accumulator_transcript: Stage4TranscriptWitnessV1<'a>,
  pub matrix_fold: &'a F128MatrixAccumulatorTraceV1,
  pub structure_fold: &'a F128CircuitStructureAccumulatorTraceV1,
  pub jagged_fold: &'a F128JaggedAccumulatorTraceV1,
}

/// Constrained phase outputs retained for native differential checks and
/// backend diagnostics. Terminal acceptance still requires the proof and
/// the independent static-table root checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4RelationCircuitOutputV1 {
  pub wiring: F128WiringCircuitOutputV1,
  pub algebra: F128AlgebraCircuitOutputV1,
  pub merged_pcs: F128MergedPcsFrontendCircuitOutputV1,
  pub multipoint: F128MultipointTwistedAssistCircuitOutputV1,
  pub inner_ligerito: F128InnerLigeritoCircuitOutputV1,
  pub matrices: F128MatrixAccumulatorCircuitOutputV1,
  pub structure: F128CircuitStructureAccumulatorCircuitOutputV1,
  pub jagged: F128JaggedAccumulatorCircuitOutputV1,
}

/// Exact public-input order: two statement limbs, each Boolean matrix root
/// in fold order, the structure root, then the jagged root. Within each root
/// the order is row coordinates, column coordinates, and evaluation.
///
/// The roots remain conditional until a terminal verifier checks their
/// identities and evaluations against its trusted static tables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4RelationPublicInputsV1 {
  pub statement: Stage4PublicInputsV1,
  pub matrices: Vec<F128RootMatrixClaimPublicInputV1>,
  pub structure: F128CircuitStructureRootClaimPublicInputV1,
  pub jagged: F128JaggedRootClaimPublicInputV1,
}

impl Stage4RelationPublicInputsV1 {
  pub fn field_elements(&self) -> Vec<Fr> {
    let mut values = self.statement.field_elements().to_vec();
    for root in &self.matrices {
      append_root(
        &mut values,
        &root.row_point,
        &root.column_point,
        &root.value,
      );
    }
    append_root(
      &mut values,
      &self.structure.row_point,
      &self.structure.column_point,
      &self.structure.value,
    );
    append_root(
      &mut values,
      &self.jagged.row_point,
      &self.jagged.column_point,
      &self.jagged.value,
    );
    values
  }
}

fn append_root(
  fields: &mut Vec<Fr>,
  row: &[[u8; 16]],
  column: &[[u8; 16]],
  value: &[u8; 16],
) {
  fields.extend(
    row
      .iter()
      .chain(column)
      .chain(std::iter::once(value))
      .map(|word| Fr::from_le_bytes_mod_order(word)),
  );
}

#[derive(Debug)]
pub struct Stage4RelationError {
  pub phase: &'static str,
  source: Box<dyn Error + Send + Sync>,
}

impl fmt::Display for Stage4RelationError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Stage 4 {}: {}", self.phase, self.source)
  }
}

impl Error for Stage4RelationError {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    Some(self.source.as_ref())
  }
}

fn phase<T, E: Error + Send + Sync + 'static>(
  name: &'static str,
  result: Result<T, E>,
) -> Result<T, Stage4RelationError> {
  result.map_err(|source| Stage4RelationError {
    phase: name,
    source: Box::new(source),
  })
}

struct RelationPublicVariables {
  statement: Stage4PublicInputVariablesV1,
  matrices: Vec<F128RootMatrixClaimPublicVariablesV1>,
  structure: F128CircuitStructureRootClaimPublicVariablesV1,
  jagged: F128JaggedRootClaimPublicVariablesV1,
}

fn allocate_public_inputs(
  builder: &mut R1csBuilder,
  public: &Stage4RelationPublicInputsV1,
) -> Result<RelationPublicVariables, Stage4RelationError> {
  let statement = phase(
    "statement public inputs",
    alloc_stage4_public_inputs(builder, public.statement),
  )?;
  let matrices = phase(
    "matrix public inputs",
    alloc_f128_matrix_root_public_inputs(builder, &public.matrices),
  )?;
  let structure = phase(
    "structure public inputs",
    alloc_f128_circuit_structure_root_public_input(builder, &public.structure),
  )?;
  let jagged = phase(
    "jagged public inputs",
    alloc_f128_jagged_root_public_input(builder, &public.jagged),
  )?;
  Ok(RelationPublicVariables { statement, matrices, structure, jagged })
}

/// Compile all verifier phases into one fresh builder. Materialized and
/// streaming backends call this same composition in the same order.
/// Root checks outside the circuit are part of terminal acceptance.
pub fn constrain_stage4_relation(
  builder: &mut R1csBuilder,
  public: &Stage4RelationPublicInputsV1,
  witness: Stage4RelationWitnessV1<'_>,
) -> Result<Stage4RelationCircuitOutputV1, Stage4RelationError> {
  let RelationPublicVariables {
    statement: statement_public,
    matrices: matrix_public,
    structure: structure_public,
    jagged: jagged_public,
  } = allocate_public_inputs(builder, public)?;
  let transcript = witness.transcript;
  let transcript = phase(
    "main transcript",
    constrain_chained_blake3_transcript(
      builder,
      transcript.trace,
      transcript.observed_values,
      transcript.byte_payloads,
      transcript.challenges,
    ),
  )?;
  let statement = phase(
    "statement binding",
    constrain_f128_statement_binding(
      builder,
      statement_public,
      witness.statement_binding,
      F128StatementCircuitInputsV1 {
        stage3_statement: witness.stage3_statement,
        public_values: witness.public_values,
        byte_payloads: &transcript.byte_payloads,
      },
    ),
  )?;
  let wiring = phase(
    "Product-GKR wiring",
    constrain_f128_wiring(
      builder,
      witness.wiring.trace,
      F128WiringCircuitInputsV1 {
        public_values: &statement.public_values,
        observed_values: &transcript.observed_values,
        challenges: &transcript.challenges,
        private_values: witness.wiring.private_values,
      },
    ),
  )?;
  let algebra_private = phase(
    "Boolean PIOP private values",
    witness
      .algebra
      .private_values
      .iter()
      .copied()
      .map(|value| {
        alloc_f128_private(builder, value, ConstraintPhase::Lincheck)
      })
      .collect::<Result<Vec<_>, _>>(),
  )?;
  let algebra = phase(
    "Boolean PIOP",
    constrain_f128_algebra_trace_deferred(
      builder,
      witness.algebra.trace,
      F128AlgebraCircuitInputsV1 {
        public_values: &statement.public_values,
        observed_values: &transcript.observed_values,
        challenges: &transcript.challenges,
        private_values: &algebra_private,
      },
    ),
  )?;
  let frontend = phase(
    "merged PCS",
    constrain_f128_merged_pcs_frontend(
      builder,
      witness.merged_pcs,
      F128MergedPcsFrontendCircuitInputsV1 {
        public_values: &statement.public_values,
        observed_values: &transcript.observed_values,
        challenges: &transcript.challenges,
        private_values: &algebra_private,
        algebra_operations: &algebra.operations,
        byte_payloads: &transcript.byte_payloads,
        packed_direct_claims: &wiring.gather_claims,
      },
    ),
  )?;
  let multipoint = phase(
    "multipoint assist",
    constrain_f128_multipoint_twisted_assist(
      builder,
      witness.multipoint.trace,
      F128MultipointTwistedAssistCircuitInputsV1 {
        observed_values: &transcript.observed_values,
        challenges: &transcript.challenges,
        private_values: witness.multipoint.private_values,
        frontend: &frontend,
      },
    ),
  )?;
  let inner_ligerito = phase(
    "inner Ligerito",
    constrain_f128_inner_ligerito(
      builder,
      witness.inner_ligerito.trace,
      F128InnerLigeritoCircuitInputsV1 {
        observed_values: &transcript.observed_values,
        challenges: &transcript.challenges,
        byte_payloads: &transcript.byte_payloads,
        private_values: witness.inner_ligerito.private_values,
        private_digests: witness.inner_ligerito_private_digests,
        frontend: &frontend,
      },
    ),
  )?;

  let accumulator = witness.accumulator_transcript;
  let accumulator = phase(
    "accumulator transcript",
    constrain_chained_blake3_transcript(
      builder,
      accumulator.trace,
      accumulator.observed_values,
      accumulator.byte_payloads,
      accumulator.challenges,
    ),
  )?;
  let matrices = phase(
    "matrix folds",
    constrain_f128_matrix_accumulator(
      builder,
      witness.matrix_fold,
      F128MatrixAccumulatorCircuitInputsV1 {
        claims: &algebra.deferred_matrix_claims,
        observed_values: &accumulator.observed_values,
        byte_payloads: &accumulator.byte_payloads,
        challenges: &accumulator.challenges,
      },
    ),
  )?;
  phase(
    "matrix root binding",
    constrain_f128_matrix_root_public_inputs(
      builder,
      &matrix_public,
      &matrices.root_claims,
    ),
  )?;
  let structure = phase(
    "structure fold",
    constrain_f128_circuit_structure_accumulator(
      builder,
      witness.structure_fold,
      F128CircuitStructureAccumulatorCircuitInputsV1 {
        claims: &wiring.circuit_structure_claims,
        observed_values: &accumulator.observed_values,
        byte_payloads: &accumulator.byte_payloads,
        challenges: &accumulator.challenges,
      },
    ),
  )?;
  phase(
    "structure root binding",
    constrain_f128_circuit_structure_root_public_input(
      builder,
      &structure_public,
      &structure.root_claim,
    ),
  )?;
  let jagged = phase(
    "jagged fold",
    constrain_f128_jagged_accumulator(
      builder,
      witness.jagged_fold,
      F128JaggedAccumulatorCircuitInputsV1 {
        assertion: &multipoint.jagged_assertion,
        observed_values: &accumulator.observed_values,
        byte_payloads: &accumulator.byte_payloads,
        challenges: &accumulator.challenges,
      },
    ),
  )?;
  phase(
    "jagged root binding",
    constrain_f128_jagged_root_public_input(
      builder,
      &jagged_public,
      &jagged.root_claim,
    ),
  )?;
  Ok(Stage4RelationCircuitOutputV1 {
    wiring,
    algebra,
    merged_pcs: frontend,
    multipoint,
    inner_ligerito,
    matrices,
    structure,
    jagged,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_stage4_trace::{
    F128CircuitStructureMatrixIdV1, F128JaggedMatrixIdV1, F128MatrixSideV1,
    F128StaticMatrixIdV1,
  };

  #[test]
  fn terminal_encoding_matches_circuit_allocation_order() {
    let mut digest = [0u8; 32];
    digest[..16].copy_from_slice(&1u128.to_le_bytes());
    digest[16..].copy_from_slice(&2u128.to_le_bytes());
    let public = Stage4RelationPublicInputsV1 {
      statement: Stage4PublicInputsV1::from_statement_digest(digest),
      matrices: [F128MatrixSideV1::A, F128MatrixSideV1::B]
        .into_iter()
        .zip([3u128, 6])
        .map(|(side, first)| F128RootMatrixClaimPublicInputV1 {
          matrix: F128StaticMatrixIdV1 {
            registry_digest: [17; 32],
            table: 0,
            side,
            variables: 1,
          },
          row_point: vec![first.to_le_bytes()],
          column_point: vec![(first + 1).to_le_bytes()],
          value: (first + 2).to_le_bytes(),
        })
        .collect(),
      structure: F128CircuitStructureRootClaimPublicInputV1 {
        matrix: F128CircuitStructureMatrixIdV1 {
          circuit_digest: [18; 32],
          row_variables: 2,
          column_variables: 1,
        },
        row_point: vec![9u128.to_le_bytes(), 10u128.to_le_bytes()],
        column_point: vec![11u128.to_le_bytes()],
        value: 12u128.to_le_bytes(),
      },
      jagged: F128JaggedRootClaimPublicInputV1 {
        matrix: F128JaggedMatrixIdV1 {
          circuit_digest: [18; 32],
          row_variables: 1,
          column_variables: 2,
        },
        row_point: vec![13u128.to_le_bytes()],
        column_point: vec![14u128.to_le_bytes(), 15u128.to_le_bytes()],
        value: u128::MAX.to_le_bytes(),
      },
    };
    let expected =
      (1u128..=15).chain([u128::MAX]).map(Fr::from).collect::<Vec<_>>();
    let mut builder = R1csBuilder::new();
    allocate_public_inputs(&mut builder, &public).unwrap();
    let (circuit, witness) = builder.finish().unwrap();
    assert_eq!(public.field_elements(), expected);
    assert_eq!(&witness.assignment()[1..], expected);
    assert_eq!(circuit.public_variables(), 16);
  }
}
