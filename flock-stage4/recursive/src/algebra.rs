//! Native-field lowering of the verifier relation in `../../circuit/src/algebra.rs`.
//! The protocol equations and transcript topology are shared by specification;
//! arithmetic and hashing below use the Flock backend defined in this crate.

use crate::f128::{
  alloc_f128_constant, native_f128_add, native_f128_inverse,
  native_f128_multiply,
};
use crate::{
  ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError, constrain_f128_add,
  constrain_f128_inverse, constrain_f128_multiply, enforce_f128_equal,
};
use ix_stage4_trace::{
  F128AlgebraTraceV1, F128InputSourceV1, F128OperationV1, F128ReferenceV1,
  F128StaticMatrixIdV1, F128VerifierPhaseV1,
};
use std::collections::BTreeMap;
use std::fmt;

/// Already-constrained inputs shared with the transcript and statement
/// portions of the terminal relation.
#[derive(Clone, Copy)]
pub(crate) struct F128AlgebraCircuitInputsV1<'a> {
  pub(crate) public_values: &'a [F128VariablesV1],
  pub(crate) observed_values: &'a [F128VariablesV1],
  pub(crate) challenges: &'a [F128VariablesV1],
  pub(crate) private_values: &'a [F128VariablesV1],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128StructuredWeightVariablesV1 {
  pub(crate) low: Vec<F128VariablesV1>,
  pub(crate) point: Vec<F128VariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128DeferredMatrixClaimVariablesV1 {
  pub(crate) matrix: F128StaticMatrixIdV1,
  pub(crate) row: F128StructuredWeightVariablesV1,
  pub(crate) column: F128StructuredWeightVariablesV1,
  pub(crate) value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128AlgebraCircuitOutputV1 {
  pub(crate) topology_digest: [u8; 32],
  pub(crate) operations: Vec<F128VariablesV1>,
  /// Claims which must be folded into a parent or checked against their
  /// registry-static matrices before this relation is a complete verifier.
  pub(crate) deferred_matrix_claims: Vec<F128DeferredMatrixClaimVariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum F128AlgebraCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  MissingInput(&'static str),
  AssertionMismatch { assertion: usize },
  UnresolvedMatrixClaims { count: usize },
}

impl fmt::Display for F128AlgebraCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid F128 trace: {error}")
      },
      Self::R1cs(error) => write!(formatter, "F128 algebra R1CS: {error}"),
      Self::MissingInput(kind) => write!(formatter, "missing F128 {kind}"),
      Self::AssertionMismatch { assertion } => {
        write!(formatter, "F128 assertion {assertion} is false")
      },
      Self::UnresolvedMatrixClaims { count } => write!(
        formatter,
        "F128 algebra trace leaves {count} static-matrix claims unresolved",
      ),
    }
  }
}

impl std::error::Error for F128AlgebraCircuitError {}

impl From<R1csError> for F128AlgebraCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

pub(crate) fn constrain_f128_algebra_trace(
  builder: &mut R1csBuilder,
  trace: &F128AlgebraTraceV1,
  inputs: F128AlgebraCircuitInputsV1<'_>,
) -> Result<F128AlgebraCircuitOutputV1, F128AlgebraCircuitError> {
  if !trace.deferred_matrix_claims.is_empty() {
    return Err(F128AlgebraCircuitError::UnresolvedMatrixClaims {
      count: trace.deferred_matrix_claims.len(),
    });
  }
  constrain_f128_algebra_trace_deferred(builder, trace, inputs)
}

/// Add a verifier DAG while deliberately carrying its static-matrix claims
/// to an accumulator boundary.
///
/// Unlike [`constrain_f128_algebra_trace`], this entry point accepts a
/// conditional relation and returns every unresolved claim as constrained
/// circuit wires.  Callers must publish/fold those outputs or perform a root
/// discharge; merely constraining this prefix is not full Flock verification.
pub(crate) fn constrain_f128_algebra_trace_deferred(
  builder: &mut R1csBuilder,
  trace: &F128AlgebraTraceV1,
  inputs: F128AlgebraCircuitInputsV1<'_>,
) -> Result<F128AlgebraCircuitOutputV1, F128AlgebraCircuitError> {
  trace
    .validate(
      inputs.public_values.len(),
      inputs.observed_values.len(),
      inputs.challenges.len(),
      inputs.private_values.len(),
    )
    .map_err(|error| {
      F128AlgebraCircuitError::InvalidTrace(error.to_string())
    })?;

  let mut constants = BTreeMap::new();
  let mut operations = Vec::with_capacity(trace.operations.len());
  for operation in &trace.operations {
    let phase = operation_phase(operation);
    let output = match *operation {
      F128OperationV1::Add { left, right, .. } => {
        let left = resolve_reference(
          builder,
          left,
          phase,
          inputs,
          &operations,
          &mut constants,
        )?;
        let right = resolve_reference(
          builder,
          right,
          phase,
          inputs,
          &operations,
          &mut constants,
        )?;
        let expected = native_f128_add(*left.value(), *right.value());
        let output = constrain_f128_add(builder, &left, &right, phase)?;
        debug_assert_eq!(output.value(), &expected);
        output
      },
      F128OperationV1::Multiply { left, right, .. } => {
        let left = resolve_reference(
          builder,
          left,
          phase,
          inputs,
          &operations,
          &mut constants,
        )?;
        let right = resolve_reference(
          builder,
          right,
          phase,
          inputs,
          &operations,
          &mut constants,
        )?;
        let expected = native_f128_multiply(*left.value(), *right.value());
        let output = constrain_f128_multiply(builder, &left, &right, phase)?;
        debug_assert_eq!(output.value(), &expected);
        output
      },
      F128OperationV1::Inverse { value, .. } => {
        let value = resolve_reference(
          builder,
          value,
          phase,
          inputs,
          &operations,
          &mut constants,
        )?;
        let expected = native_f128_inverse(*value.value());
        let output = constrain_f128_inverse(builder, &value, phase)?;
        debug_assert!(
          builder.is_shape_only() || Some(*output.value()) == expected
        );
        output
      },
    };
    operations.push(output);
  }

  for (index, equality) in trace.equalities.iter().enumerate() {
    let phase = constraint_phase(equality.phase);
    let left = resolve_reference(
      builder,
      equality.left,
      phase,
      inputs,
      &operations,
      &mut constants,
    )?;
    let right = resolve_reference(
      builder,
      equality.right,
      phase,
      inputs,
      &operations,
      &mut constants,
    )?;
    if !builder.is_shape_only() && left.value() != right.value() {
      return Err(F128AlgebraCircuitError::AssertionMismatch {
        assertion: index,
      });
    }
    enforce_f128_equal(builder, &left, &right, phase);
  }

  let deferred_matrix_claims = trace
    .deferred_matrix_claims
    .iter()
    .map(|claim| {
      let phase = constraint_phase(claim.phase);
      Ok(F128DeferredMatrixClaimVariablesV1 {
        matrix: claim.matrix,
        row: F128StructuredWeightVariablesV1 {
          low: resolve_references(
            builder,
            &claim.row.low,
            phase,
            inputs,
            &operations,
            &mut constants,
          )?,
          point: resolve_references(
            builder,
            &claim.row.point,
            phase,
            inputs,
            &operations,
            &mut constants,
          )?,
        },
        column: F128StructuredWeightVariablesV1 {
          low: resolve_references(
            builder,
            &claim.column.low,
            phase,
            inputs,
            &operations,
            &mut constants,
          )?,
          point: resolve_references(
            builder,
            &claim.column.point,
            phase,
            inputs,
            &operations,
            &mut constants,
          )?,
        },
        value: resolve_reference(
          builder,
          claim.value,
          phase,
          inputs,
          &operations,
          &mut constants,
        )?,
      })
    })
    .collect::<Result<Vec<_>, F128AlgebraCircuitError>>()?;

  Ok(F128AlgebraCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    operations,
    deferred_matrix_claims,
  })
}

fn resolve_references(
  builder: &mut R1csBuilder,
  references: &[F128ReferenceV1],
  phase: ConstraintPhase,
  inputs: F128AlgebraCircuitInputsV1<'_>,
  operations: &[F128VariablesV1],
  constants: &mut BTreeMap<[u8; 16], F128VariablesV1>,
) -> Result<Vec<F128VariablesV1>, F128AlgebraCircuitError> {
  references
    .iter()
    .map(|reference| {
      resolve_reference(
        builder, *reference, phase, inputs, operations, constants,
      )
    })
    .collect()
}

fn operation_phase(operation: &F128OperationV1) -> ConstraintPhase {
  match operation {
    F128OperationV1::Add { phase, .. }
    | F128OperationV1::Multiply { phase, .. }
    | F128OperationV1::Inverse { phase, .. } => constraint_phase(*phase),
  }
}

const fn constraint_phase(phase: F128VerifierPhaseV1) -> ConstraintPhase {
  match phase {
    F128VerifierPhaseV1::Zerocheck => ConstraintPhase::Zerocheck,
    F128VerifierPhaseV1::Lincheck => ConstraintPhase::Lincheck,
    F128VerifierPhaseV1::Wiring => ConstraintPhase::Wiring,
    F128VerifierPhaseV1::Pcs => ConstraintPhase::Pcs,
  }
}

fn to_usize(
  value: u64,
  kind: &'static str,
) -> Result<usize, F128AlgebraCircuitError> {
  usize::try_from(value)
    .map_err(|_| F128AlgebraCircuitError::MissingInput(kind))
}

pub(crate) fn resolve_reference(
  builder: &mut R1csBuilder,
  reference: F128ReferenceV1,
  phase: ConstraintPhase,
  inputs: F128AlgebraCircuitInputsV1<'_>,
  operations: &[F128VariablesV1],
  constants: &mut BTreeMap<[u8; 16], F128VariablesV1>,
) -> Result<F128VariablesV1, F128AlgebraCircuitError> {
  match reference {
    F128ReferenceV1::Input(F128InputSourceV1::PublicValue(index)) => inputs
      .public_values
      .get(to_usize(index, "public-value index")?)
      .cloned()
      .ok_or(F128AlgebraCircuitError::MissingInput("public value")),
    F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(index)) => inputs
      .observed_values
      .get(to_usize(index, "observed-value index")?)
      .cloned()
      .ok_or(F128AlgebraCircuitError::MissingInput("observed value")),
    F128ReferenceV1::Input(F128InputSourceV1::Challenge(index)) => inputs
      .challenges
      .get(to_usize(index, "challenge index")?)
      .cloned()
      .ok_or(F128AlgebraCircuitError::MissingInput("challenge")),
    F128ReferenceV1::Input(F128InputSourceV1::PrivateValue(index)) => inputs
      .private_values
      .get(to_usize(index, "private-value index")?)
      .cloned()
      .ok_or(F128AlgebraCircuitError::MissingInput("private value")),
    F128ReferenceV1::Input(F128InputSourceV1::Constant(value)) => {
      if let Some(constant) = constants.get(&value) {
        return Ok(constant.clone());
      }
      let constant = alloc_f128_constant(builder, value, phase)?;
      constants.insert(value, constant.clone());
      Ok(constant)
    },
    F128ReferenceV1::Operation(index) => operations
      .get(to_usize(index, "operation index")?)
      .cloned()
      .ok_or(F128AlgebraCircuitError::MissingInput("operation")),
  }
}
