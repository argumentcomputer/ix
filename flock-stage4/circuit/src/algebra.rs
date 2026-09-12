use crate::f128::{
  alloc_f128_constant, native_f128_add, native_f128_inverse,
  native_f128_multiply,
};
use crate::{
  CanonicalR1csV1, ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError,
  R1csProjectionV1, Witness, alloc_f128_private, constrain_f128_add,
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
pub struct F128AlgebraCircuitInputsV1<'a> {
  pub public_values: &'a [F128VariablesV1],
  pub observed_values: &'a [F128VariablesV1],
  pub challenges: &'a [F128VariablesV1],
  pub private_values: &'a [F128VariablesV1],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StructuredWeightVariablesV1 {
  pub low: Vec<F128VariablesV1>,
  pub point: Vec<F128VariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128DeferredMatrixClaimVariablesV1 {
  pub matrix: F128StaticMatrixIdV1,
  pub row: F128StructuredWeightVariablesV1,
  pub column: F128StructuredWeightVariablesV1,
  pub value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128AlgebraCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  pub operations: Vec<F128VariablesV1>,
  /// Claims which must be folded into a parent or checked against their
  /// registry-static matrices before this relation is a complete verifier.
  pub deferred_matrix_claims: Vec<F128DeferredMatrixClaimVariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128AlgebraCircuitError {
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

/// Build a standalone materialized relation from raw source values.
pub fn build_f128_algebra_trace_r1cs(
  trace: &F128AlgebraTraceV1,
  public_values: &[[u8; 16]],
  observed_values: &[[u8; 16]],
  challenges: &[[u8; 16]],
  private_values: &[[u8; 16]],
) -> Result<
  (CanonicalR1csV1, Witness, F128AlgebraCircuitOutputV1),
  F128AlgebraCircuitError,
> {
  let mut builder = R1csBuilder::new();
  let public_values = alloc_sources(&mut builder, public_values)?;
  let observed_values = alloc_sources(&mut builder, observed_values)?;
  let challenges = alloc_sources(&mut builder, challenges)?;
  let private_values = alloc_sources(&mut builder, private_values)?;
  let output = constrain_f128_algebra_trace(
    &mut builder,
    trace,
    F128AlgebraCircuitInputsV1 {
      public_values: &public_values,
      observed_values: &observed_values,
      challenges: &challenges,
      private_values: &private_values,
    },
  )?;
  let (r1cs, witness) = builder.finish()?;
  Ok((r1cs, witness, output))
}

/// Stream a standalone relation into an exact digest and census.
pub fn project_f128_algebra_trace_r1cs(
  trace: &F128AlgebraTraceV1,
  public_values: &[[u8; 16]],
  observed_values: &[[u8; 16]],
  challenges: &[[u8; 16]],
  private_values: &[[u8; 16]],
) -> Result<R1csProjectionV1, F128AlgebraCircuitError> {
  let mut builder = R1csBuilder::new_projection();
  let public_values = alloc_sources(&mut builder, public_values)?;
  let observed_values = alloc_sources(&mut builder, observed_values)?;
  let challenges = alloc_sources(&mut builder, challenges)?;
  let private_values = alloc_sources(&mut builder, private_values)?;
  constrain_f128_algebra_trace(
    &mut builder,
    trace,
    F128AlgebraCircuitInputsV1 {
      public_values: &public_values,
      observed_values: &observed_values,
      challenges: &challenges,
      private_values: &private_values,
    },
  )?;
  Ok(builder.finish_projection()?)
}

/// Add a verifier arithmetic DAG to an existing terminal relation.
pub fn constrain_f128_algebra_trace(
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
pub fn constrain_f128_algebra_trace_deferred(
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
        let expected = native_f128_inverse(*value.value())
          .ok_or(R1csError::NonInvertibleBinaryFieldElement)?;
        let output = constrain_f128_inverse(builder, &value, phase)?;
        debug_assert_eq!(output.value(), &expected);
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
    if left.value() != right.value() {
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

fn alloc_sources(
  builder: &mut R1csBuilder,
  values: &[[u8; 16]],
) -> Result<Vec<F128VariablesV1>, R1csError> {
  values
    .iter()
    .copied()
    .map(|value| alloc_f128_private(builder, value, ConstraintPhase::Statement))
    .collect()
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

#[cfg(test)]
mod tests {
  use super::*;
  use ix_stage4_trace::{
    F128DeferredMatrixClaimV1, F128EqualityV1, F128MatrixSideV1,
    F128StaticMatrixIdV1, F128StructuredWeightV1, F128VerifierPhaseV1,
  };

  fn value(low: u64, high: u64) -> [u8; 16] {
    (u128::from(low) | (u128::from(high) << 64)).to_le_bytes()
  }

  fn identity_trace() -> F128AlgebraTraceV1 {
    let observed = F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(0));
    let challenge = F128ReferenceV1::Input(F128InputSourceV1::Challenge(0));
    let one = F128ReferenceV1::Input(F128InputSourceV1::Constant(value(1, 0)));
    F128AlgebraTraceV1 {
      operations: vec![
        F128OperationV1::Add {
          phase: F128VerifierPhaseV1::Zerocheck,
          left: observed,
          right: challenge,
        },
        F128OperationV1::Add {
          phase: F128VerifierPhaseV1::Zerocheck,
          left: F128ReferenceV1::Operation(0),
          right: challenge,
        },
        F128OperationV1::Multiply {
          phase: F128VerifierPhaseV1::Zerocheck,
          left: F128ReferenceV1::Operation(1),
          right: one,
        },
      ],
      equalities: vec![F128EqualityV1 {
        phase: F128VerifierPhaseV1::Zerocheck,
        left: F128ReferenceV1::Operation(2),
        right: F128ReferenceV1::Input(F128InputSourceV1::PublicValue(0)),
      }],
      deferred_matrix_claims: Vec::new(),
    }
  }

  #[test]
  fn arithmetic_dag_compiles_and_reuses_bound_sources() {
    let observed = value(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let challenge = value(0x0f1e_2d3c_4b5a_6978, 0x8877_6655_4433_2211);
    let trace = identity_trace();
    let (r1cs, witness, output) = build_f128_algebra_trace_r1cs(
      &trace,
      &[observed],
      &[observed],
      &[challenge],
      &[],
    )
    .unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(output.operations[2].value(), &observed);
    assert_eq!(output.topology_digest, trace.topology_digest());
  }

  #[test]
  fn false_native_assertion_is_rejected_before_finish() {
    let observed = value(3, 5);
    let challenge = value(7, 11);
    let result = build_f128_algebra_trace_r1cs(
      &identity_trace(),
      &[value(13, 17)],
      &[observed],
      &[challenge],
      &[],
    );
    assert!(matches!(
      result,
      Err(F128AlgebraCircuitError::AssertionMismatch { assertion: 0 })
    ));
  }

  #[test]
  fn deferred_claims_require_the_explicit_accumulator_entry_point() {
    let private = F128ReferenceV1::Input(F128InputSourceV1::PrivateValue(0));
    let trace = F128AlgebraTraceV1 {
      operations: Vec::new(),
      equalities: Vec::new(),
      deferred_matrix_claims: vec![F128DeferredMatrixClaimV1 {
        phase: F128VerifierPhaseV1::Lincheck,
        matrix: F128StaticMatrixIdV1 {
          registry_digest: [9; 32],
          table: 0,
          side: F128MatrixSideV1::A,
          variables: 0,
        },
        row: F128StructuredWeightV1 { low: vec![private], point: Vec::new() },
        column: F128StructuredWeightV1 {
          low: vec![private],
          point: Vec::new(),
        },
        value: private,
      }],
    };
    assert!(matches!(
      build_f128_algebra_trace_r1cs(&trace, &[], &[], &[], &[value(1, 0)]),
      Err(F128AlgebraCircuitError::UnresolvedMatrixClaims { count: 1 })
    ));

    let mut builder = R1csBuilder::new();
    let advice =
      alloc_f128_private(&mut builder, value(1, 0), ConstraintPhase::Lincheck)
        .unwrap();
    let output = constrain_f128_algebra_trace_deferred(
      &mut builder,
      &trace,
      F128AlgebraCircuitInputsV1 {
        public_values: &[],
        observed_values: &[],
        challenges: &[],
        private_values: &[advice],
      },
    )
    .unwrap();
    assert_eq!(output.deferred_matrix_claims.len(), 1);
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
  }
}
