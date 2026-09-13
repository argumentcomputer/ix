//! Complete generic Exec replay composition with two root-binding paths.
//!
//! The historical diagnostic path publishes conditional roots; the closed
//! prototype constrains their exact table evaluations and publishes only Q.
//! Neither emission nor census is a terminal proof or proof-free key compiler.

use crate::*;
use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ix_stage4_trace::{
  ExecBindingV0, ExecCommitmentsV0, F128AlgebraTraceV1,
  F128CircuitStructureAccumulatorTraceV1, F128InnerLigeritoTraceV1,
  F128JaggedAccumulatorTraceV1, F128MatrixAccumulatorTraceV1,
  F128MergedPcsFrontendTraceV1, F128MultipointTwistedAssistTraceV1,
  F128RootTableSetV0, F128WiringTraceV1,
};
use std::{error::Error, fmt};

/// Backend-neutral inputs to the complete relation. The fixed trace topology
/// and statement constants belong to the circuit-specific verification key;
/// callers must not choose a fresh key from an untrusted proof's topology.
pub struct ExecReplayCircuitWitnessV0<'a> {
  pub statement_binding: &'a ExecBindingV0,
  pub commitments: ExecCommitmentsV0,
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

/// Compatibility name for the diagnostic public-root entry point. The
/// witness itself has no root sidecar and is shared by both binding paths.
pub type ExecRootConditionalWitnessV0<'a> = ExecReplayCircuitWitnessV0<'a>;

/// Diagnostic outputs of a composition which emitted all table-root checks.
/// This is not a checked satisfying assignment, key, proof, or acceptance bit.
pub struct ExecRootClosedCircuitOutputV0 {
  replay: Stage4RelationCircuitOutputV1,
  root_tables_digest: [u8; 32],
}
impl ExecRootClosedCircuitOutputV0 {
  pub fn replay(&self) -> &Stage4RelationCircuitOutputV1 {
    &self.replay
  }
  pub fn root_tables_digest(&self) -> [u8; 32] {
    self.root_tables_digest
  }
}

/// Exact public-input order: two statement limbs, each Boolean matrix root
/// in fold order, the structure root, then the jagged root. Within each root
/// the order is row coordinates, column coordinates, and evaluation.
///
/// The roots remain conditional until a terminal verifier checks their
/// identities and evaluations against its trusted static tables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecRootConditionalPublicV0 {
  pub public_digest: Stage4PublicInputsV1,
  pub matrices: Vec<F128RootMatrixClaimPublicInputV1>,
  pub structure: F128CircuitStructureRootClaimPublicInputV1,
  pub jagged: F128JaggedRootClaimPublicInputV1,
}

impl ExecRootConditionalPublicV0 {
  pub fn field_elements(&self) -> Vec<Fr> {
    let mut values = self.public_digest.field_elements().to_vec();
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
pub struct ExecRootConditionalError {
  pub phase: &'static str,
  source: Box<dyn Error + Send + Sync>,
}

impl fmt::Display for ExecRootConditionalError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Stage 4 {}: {}", self.phase, self.source)
  }
}

impl Error for ExecRootConditionalError {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    Some(self.source.as_ref())
  }
}

fn phase<T, E: Error + Send + Sync + 'static>(
  name: &'static str,
  result: Result<T, E>,
) -> Result<T, ExecRootConditionalError> {
  result.map_err(|source| ExecRootConditionalError {
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

// There is deliberately no unchecked/private-root variant. Every call to the
// shared composition either binds the diagnostic public root or evaluates
// its exact setup-owned table on the very same derived point/value wires.
enum RootBindings<'a> {
  Public {
    matrices: &'a [F128RootMatrixClaimPublicVariablesV1],
    structure: &'a F128CircuitStructureRootClaimPublicVariablesV1,
    jagged: &'a F128JaggedRootClaimPublicVariablesV1,
  },
  Closed(&'a F128RootTableSetV0),
}

impl RootBindings<'_> {
  fn matrices(
    &self,
    builder: &mut R1csBuilder,
    roots: &[F128RootMatrixClaimVariablesV1],
  ) -> Result<(), ExecRootConditionalError> {
    match self {
      Self::Public { matrices, .. } => phase(
        "matrix root binding",
        constrain_f128_matrix_root_public_inputs(builder, matrices, roots),
      ),
      Self::Closed(tables) => phase(
        "matrix root closure",
        constrain_f128_matrix_root_tables(builder, tables, roots),
      )
      .map(|_| ()),
    }
  }
  fn structure(
    &self,
    builder: &mut R1csBuilder,
    root: &F128CircuitStructureRootClaimVariablesV1,
  ) -> Result<(), ExecRootConditionalError> {
    match self {
      Self::Public { structure, .. } => phase(
        "structure root binding",
        constrain_f128_circuit_structure_root_public_input(
          builder, structure, root,
        ),
      ),
      Self::Closed(tables) => phase(
        "structure root closure",
        constrain_f128_structure_root_table(builder, tables, root),
      )
      .map(|_| ()),
    }
  }
  fn jagged(
    &self,
    builder: &mut R1csBuilder,
    root: &F128JaggedRootClaimVariablesV1,
  ) -> Result<(), ExecRootConditionalError> {
    match self {
      Self::Public { jagged, .. } => phase(
        "jagged root binding",
        constrain_f128_jagged_root_public_input(builder, jagged, root),
      ),
      Self::Closed(tables) => phase(
        "jagged root closure",
        constrain_f128_jagged_root_table(builder, tables, root),
      )
      .map(|_| ()),
    }
  }
}

fn allocate_public_inputs(
  builder: &mut R1csBuilder,
  public: &ExecRootConditionalPublicV0,
) -> Result<RelationPublicVariables, ExecRootConditionalError> {
  let statement = phase(
    "statement public inputs",
    alloc_stage4_public_inputs(builder, public.public_digest),
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

/// Diagnostic composition of all generic verifier phases. Materialized and
/// streaming backends call this same composition in the same order.
/// This root-conditional relation is not the closed terminal API.
pub fn constrain_exec_root_conditional(
  builder: &mut R1csBuilder,
  public: &ExecRootConditionalPublicV0,
  witness: ExecRootConditionalWitnessV0<'_>,
) -> Result<Stage4RelationCircuitOutputV1, ExecRootConditionalError> {
  let RelationPublicVariables {
    statement: statement_public,
    matrices: matrix_public,
    structure: structure_public,
    jagged: jagged_public,
  } = allocate_public_inputs(builder, public)?;
  constrain_exec_with_roots(
    builder,
    statement_public,
    witness,
    RootBindings::Public {
      matrices: &matrix_public,
      structure: &structure_public,
      jagged: &jagged_public,
    },
  )
}

/// Emit the complete replay and all three exact root families with ONLY the
/// two public Q limbs. The setup must supply approved coefficient-checked
/// tables and topology; no sidecar, hinted value, or callback discharges a root.
/// This prototype still needs proof-free R1CS/key compilation, resource
/// admission and an actual complete proof before terminal deployment.
pub fn constrain_exec_root_closed(
  builder: &mut R1csBuilder,
  public: Stage4PublicInputsV1,
  tables: &F128RootTableSetV0,
  witness: ExecReplayCircuitWitnessV0<'_>,
) -> Result<ExecRootClosedCircuitOutputV0, ExecRootConditionalError> {
  phase(
    "root table setup",
    validate_exec_root_tables(
      tables,
      witness.statement_binding,
      witness.matrix_fold,
      witness.structure_fold,
      witness.jagged_fold,
    ),
  )?;
  let statement = phase(
    "statement public inputs",
    alloc_stage4_public_inputs(builder, public),
  )?;
  let replay = constrain_exec_with_roots(
    builder,
    statement,
    witness,
    RootBindings::Closed(tables),
  )?;
  Ok(ExecRootClosedCircuitOutputV0 {
    replay,
    root_tables_digest: tables.digest(),
  })
}

fn constrain_exec_with_roots(
  builder: &mut R1csBuilder,
  statement_public: Stage4PublicInputVariablesV1,
  witness: ExecReplayCircuitWitnessV0<'_>,
  roots: RootBindings<'_>,
) -> Result<Stage4RelationCircuitOutputV1, ExecRootConditionalError> {
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
    constrain_exec_binding(
      builder,
      statement_public,
      witness.statement_binding,
      ExecBindingCircuitInputsV0 {
        commitments: witness.commitments,
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
  roots.matrices(builder, &matrices.root_claims)?;
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
  roots.structure(builder, &structure.root_claim)?;
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
  roots.jagged(builder, &jagged.root_claim)?;
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
