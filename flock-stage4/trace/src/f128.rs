use std::fmt;

const ALGEBRA_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-f128-algebra-topology:v2";

/// A serializer-independent source of one Flock `GF(2^128)` value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum F128InputSourceV1 {
  /// One value in the Stage 3 circuit's public vector.
  PublicValue(u64),
  /// One value absorbed by the Fiat-Shamir transcript.
  ObservedValue(u64),
  /// One value squeezed by the Fiat-Shamir transcript.
  Challenge(u64),
  /// Private verifier advice which is not part of the Fiat-Shamir tape.
  ///
  /// These values are only sound when every use is either constrained by an
  /// equality in this trace or exported as an explicit deferred claim.  The
  /// production union lincheck uses this source for its canonical static
  /// matrix evaluations: Flock deliberately leaves those values out of the
  /// transcript so they can be accumulated by a parent verifier. The Stage 4
  /// handoff recomputes them from the registry matrices rather than copying
  /// the proof's unused `matrix_evals` fields.
  PrivateValue(u64),
  /// A verifier constant in the GHASH polynomial basis.
  Constant([u8; 16]),
}

/// An input or the result of an earlier algebra operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum F128ReferenceV1 {
  Input(F128InputSourceV1),
  Operation(u64),
}

/// One arithmetic operation executed by the pinned Flock verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum F128OperationV1 {
  Add {
    phase: F128VerifierPhaseV1,
    left: F128ReferenceV1,
    right: F128ReferenceV1,
  },
  Multiply {
    phase: F128VerifierPhaseV1,
    left: F128ReferenceV1,
    right: F128ReferenceV1,
  },
  Inverse {
    phase: F128VerifierPhaseV1,
    value: F128ReferenceV1,
  },
}

/// Semantic verifier phase responsible for an equality assertion.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum F128VerifierPhaseV1 {
  Zerocheck = 1,
  Lincheck = 2,
  Wiring = 3,
  Pcs = 4,
}

/// One equality the verifier must accept in the named phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128EqualityV1 {
  pub phase: F128VerifierPhaseV1,
  pub left: F128ReferenceV1,
  pub right: F128ReferenceV1,
}

/// Which binary constraint matrix a deferred lincheck claim names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum F128MatrixSideV1 {
  A = 1,
  B = 2,
}

/// Stable identity of one registry-static Flock matrix.
///
/// The registry digest commits to every matrix entry and table order.  A
/// root discharge therefore needs only this identity, not a second copy of
/// the (potentially tens-of-millions-of-nonzeros) matrix in the trace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F128StaticMatrixIdV1 {
  pub registry_digest: [u8; 32],
  pub table: u64,
  pub side: F128MatrixSideV1,
  /// Both dimensions of Flock's square base matrix are `2^variables`.
  pub variables: u32,
}

/// A structured vector `low ⊗ eq(point)` over `GF(2^128)`.
///
/// `low` occupies the least-significant coordinates and must have nonzero
/// power-of-two length.  This is exactly Flock's matrix-accumulator weight
/// representation; in production `low` has 64 entries on each side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StructuredWeightV1 {
  pub low: Vec<F128ReferenceV1>,
  pub point: Vec<F128ReferenceV1>,
}

/// One static-matrix assertion intentionally carried out of this verifier.
///
/// A trace containing one of these is a conditional verifier relation until
/// a parent fold or a root matrix check discharges it.  Keeping the claims in
/// the schema prevents the succinct lincheck replay from being mistaken for
/// a complete verification of the underlying R1CS matrices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128DeferredMatrixClaimV1 {
  pub phase: F128VerifierPhaseV1,
  pub matrix: F128StaticMatrixIdV1,
  pub row: F128StructuredWeightV1,
  pub column: F128StructuredWeightV1,
  pub value: F128ReferenceV1,
}

/// Value-independent arithmetic DAG for the non-transcript part of Flock.
///
/// Operation results are deliberately absent: the Stage 4 compiler derives
/// them from circuit-bound inputs. This prevents a native precomputation from
/// becoming an unconstrained verifier hint.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct F128AlgebraTraceV1 {
  pub operations: Vec<F128OperationV1>,
  pub equalities: Vec<F128EqualityV1>,
  pub deferred_matrix_claims: Vec<F128DeferredMatrixClaimV1>,
}

impl F128AlgebraTraceV1 {
  pub fn validate(
    &self,
    public_values: usize,
    observed_values: usize,
    challenges: usize,
    private_values: usize,
  ) -> Result<(), F128AlgebraTraceError> {
    for (index, operation) in self.operations.iter().enumerate() {
      match operation {
        F128OperationV1::Add { left, right, .. }
        | F128OperationV1::Multiply { left, right, .. } => {
          validate_reference(
            *left,
            index,
            public_values,
            observed_values,
            challenges,
            private_values,
          )?;
          validate_reference(
            *right,
            index,
            public_values,
            observed_values,
            challenges,
            private_values,
          )?;
        },
        F128OperationV1::Inverse { value, .. } => validate_reference(
          *value,
          index,
          public_values,
          observed_values,
          challenges,
          private_values,
        )?,
      }
    }
    for equality in &self.equalities {
      validate_reference(
        equality.left,
        self.operations.len(),
        public_values,
        observed_values,
        challenges,
        private_values,
      )?;
      validate_reference(
        equality.right,
        self.operations.len(),
        public_values,
        observed_values,
        challenges,
        private_values,
      )?;
    }
    for (claim_index, claim) in self.deferred_matrix_claims.iter().enumerate() {
      validate_weight(
        &claim.row,
        claim.matrix.variables,
        claim_index,
        "row",
        self.operations.len(),
        public_values,
        observed_values,
        challenges,
        private_values,
      )?;
      validate_weight(
        &claim.column,
        claim.matrix.variables,
        claim_index,
        "column",
        self.operations.len(),
        public_values,
        observed_values,
        challenges,
        private_values,
      )?;
      validate_reference(
        claim.value,
        self.operations.len(),
        public_values,
        observed_values,
        challenges,
        private_values,
      )?;
    }
    Ok(())
  }

  pub fn census(&self) -> F128AlgebraCensusV1 {
    let mut census = F128AlgebraCensusV1 {
      operations: u64::try_from(self.operations.len())
        .expect("operation count fits u64"),
      equalities: u64::try_from(self.equalities.len())
        .expect("equality count fits u64"),
      deferred_matrix_claims: u64::try_from(self.deferred_matrix_claims.len())
        .expect("matrix-claim count fits u64"),
      ..F128AlgebraCensusV1::default()
    };
    for operation in &self.operations {
      match operation {
        F128OperationV1::Add { .. } => census.additions += 1,
        F128OperationV1::Multiply { .. } => census.multiplications += 1,
        F128OperationV1::Inverse { .. } => census.inversions += 1,
      }
    }
    census
  }

  /// Content address of the operation DAG and phase assertions.
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(ALGEBRA_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(
      &u64::try_from(self.operations.len())
        .expect("operation count fits u64")
        .to_le_bytes(),
    );
    for operation in &self.operations {
      match operation {
        F128OperationV1::Add { phase, left, right } => {
          hasher.update(&[0]);
          hasher.update(&[*phase as u8]);
          hash_reference(&mut hasher, *left);
          hash_reference(&mut hasher, *right);
        },
        F128OperationV1::Multiply { phase, left, right } => {
          hasher.update(&[1]);
          hasher.update(&[*phase as u8]);
          hash_reference(&mut hasher, *left);
          hash_reference(&mut hasher, *right);
        },
        F128OperationV1::Inverse { phase, value } => {
          hasher.update(&[2]);
          hasher.update(&[*phase as u8]);
          hash_reference(&mut hasher, *value);
        },
      }
    }
    hasher.update(
      &u64::try_from(self.equalities.len())
        .expect("equality count fits u64")
        .to_le_bytes(),
    );
    for equality in &self.equalities {
      hasher.update(&[equality.phase as u8]);
      hash_reference(&mut hasher, equality.left);
      hash_reference(&mut hasher, equality.right);
    }
    hasher.update(
      &u64::try_from(self.deferred_matrix_claims.len())
        .expect("matrix-claim count fits u64")
        .to_le_bytes(),
    );
    for claim in &self.deferred_matrix_claims {
      hasher.update(&[claim.phase as u8]);
      hasher.update(&claim.matrix.registry_digest);
      hasher.update(&claim.matrix.table.to_le_bytes());
      hasher.update(&[claim.matrix.side as u8]);
      hasher.update(&claim.matrix.variables.to_le_bytes());
      hash_weight(&mut hasher, &claim.row);
      hash_weight(&mut hasher, &claim.column);
      hash_reference(&mut hasher, claim.value);
    }
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128AlgebraCensusV1 {
  pub operations: u64,
  pub additions: u64,
  pub multiplications: u64,
  pub inversions: u64,
  pub equalities: u64,
  pub deferred_matrix_claims: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128AlgebraTraceError {
  PublicValueIndex {
    index: u64,
    count: usize,
  },
  ObservedValueIndex {
    index: u64,
    count: usize,
  },
  ChallengeIndex {
    index: u64,
    count: usize,
  },
  PrivateValueIndex {
    index: u64,
    count: usize,
  },
  ForwardOperationReference {
    operation: u64,
    available: usize,
  },
  MalformedMatrixWeight {
    claim: usize,
    side: &'static str,
    low: usize,
    point: usize,
    variables: u32,
  },
}

impl fmt::Display for F128AlgebraTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::PublicValueIndex { index, count } => write!(
        formatter,
        "F128 public-value index {index} is outside {count} values",
      ),
      Self::ObservedValueIndex { index, count } => write!(
        formatter,
        "F128 observed-value index {index} is outside {count} values",
      ),
      Self::ChallengeIndex { index, count } => write!(
        formatter,
        "F128 challenge index {index} is outside {count} challenges",
      ),
      Self::PrivateValueIndex { index, count } => write!(
        formatter,
        "F128 private-value index {index} is outside {count} values",
      ),
      Self::ForwardOperationReference { operation, available } => write!(
        formatter,
        "F128 operation reference {operation} has only {available} prior operations",
      ),
      Self::MalformedMatrixWeight { claim, side, low, point, variables } => {
        write!(
          formatter,
          "F128 matrix claim {claim} has malformed {side} weight: low={low}, point={point}, variables={variables}",
        )
      },
    }
  }
}

impl std::error::Error for F128AlgebraTraceError {}

pub(crate) fn validate_reference(
  reference: F128ReferenceV1,
  available_operations: usize,
  public_values: usize,
  observed_values: usize,
  challenges: usize,
  private_values: usize,
) -> Result<(), F128AlgebraTraceError> {
  match reference {
    F128ReferenceV1::Input(F128InputSourceV1::PublicValue(index)) => {
      if usize::try_from(index).ok().is_none_or(|index| index >= public_values)
      {
        return Err(F128AlgebraTraceError::PublicValueIndex {
          index,
          count: public_values,
        });
      }
    },
    F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(index)) => {
      if usize::try_from(index)
        .ok()
        .is_none_or(|index| index >= observed_values)
      {
        return Err(F128AlgebraTraceError::ObservedValueIndex {
          index,
          count: observed_values,
        });
      }
    },
    F128ReferenceV1::Input(F128InputSourceV1::Challenge(index)) => {
      if usize::try_from(index).ok().is_none_or(|index| index >= challenges) {
        return Err(F128AlgebraTraceError::ChallengeIndex {
          index,
          count: challenges,
        });
      }
    },
    F128ReferenceV1::Input(F128InputSourceV1::PrivateValue(index)) => {
      if usize::try_from(index).ok().is_none_or(|index| index >= private_values)
      {
        return Err(F128AlgebraTraceError::PrivateValueIndex {
          index,
          count: private_values,
        });
      }
    },
    F128ReferenceV1::Input(F128InputSourceV1::Constant(_)) => {},
    F128ReferenceV1::Operation(operation) => {
      if usize::try_from(operation)
        .ok()
        .is_none_or(|operation| operation >= available_operations)
      {
        return Err(F128AlgebraTraceError::ForwardOperationReference {
          operation,
          available: available_operations,
        });
      }
    },
  }
  Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_weight(
  weight: &F128StructuredWeightV1,
  variables: u32,
  claim: usize,
  side: &'static str,
  available_operations: usize,
  public_values: usize,
  observed_values: usize,
  challenges: usize,
  private_values: usize,
) -> Result<(), F128AlgebraTraceError> {
  let low_variables = weight.low.len().checked_ilog2();
  let well_formed = !weight.low.is_empty()
    && weight.low.len().is_power_of_two()
    && low_variables.and_then(|low| {
      u32::try_from(weight.point.len())
        .ok()
        .and_then(|point| low.checked_add(point))
    }) == Some(variables);
  if !well_formed {
    return Err(F128AlgebraTraceError::MalformedMatrixWeight {
      claim,
      side,
      low: weight.low.len(),
      point: weight.point.len(),
      variables,
    });
  }
  for reference in weight.low.iter().chain(&weight.point) {
    validate_reference(
      *reference,
      available_operations,
      public_values,
      observed_values,
      challenges,
      private_values,
    )?;
  }
  Ok(())
}

pub(crate) fn hash_reference(
  hasher: &mut blake3::Hasher,
  reference: F128ReferenceV1,
) {
  match reference {
    F128ReferenceV1::Input(F128InputSourceV1::PublicValue(index)) => {
      hasher.update(&[0]);
      hasher.update(&index.to_le_bytes());
    },
    F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(index)) => {
      hasher.update(&[1]);
      hasher.update(&index.to_le_bytes());
    },
    F128ReferenceV1::Input(F128InputSourceV1::Challenge(index)) => {
      hasher.update(&[2]);
      hasher.update(&index.to_le_bytes());
    },
    F128ReferenceV1::Input(F128InputSourceV1::PrivateValue(index)) => {
      hasher.update(&[3]);
      hasher.update(&index.to_le_bytes());
    },
    F128ReferenceV1::Input(F128InputSourceV1::Constant(value)) => {
      hasher.update(&[4]);
      hasher.update(&value);
    },
    F128ReferenceV1::Operation(index) => {
      hasher.update(&[5]);
      hasher.update(&index.to_le_bytes());
    },
  }
}

fn hash_weight(hasher: &mut blake3::Hasher, weight: &F128StructuredWeightV1) {
  for references in [&weight.low, &weight.point] {
    hasher.update(
      &u64::try_from(references.len())
        .expect("matrix-weight length fits u64")
        .to_le_bytes(),
    );
    for reference in references {
      hash_reference(hasher, *reference);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn validates_backward_dag_and_counts_operations() {
    let trace = F128AlgebraTraceV1 {
      operations: vec![
        F128OperationV1::Add {
          phase: F128VerifierPhaseV1::Zerocheck,
          left: F128ReferenceV1::Input(F128InputSourceV1::Challenge(0)),
          right: F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(0)),
        },
        F128OperationV1::Multiply {
          phase: F128VerifierPhaseV1::Lincheck,
          left: F128ReferenceV1::Operation(0),
          right: F128ReferenceV1::Input(F128InputSourceV1::PublicValue(0)),
        },
        F128OperationV1::Inverse {
          phase: F128VerifierPhaseV1::Pcs,
          value: F128ReferenceV1::Operation(1),
        },
      ],
      equalities: vec![F128EqualityV1 {
        phase: F128VerifierPhaseV1::Zerocheck,
        left: F128ReferenceV1::Operation(2),
        right: F128ReferenceV1::Input(F128InputSourceV1::Constant([0; 16])),
      }],
      deferred_matrix_claims: Vec::new(),
    };
    trace.validate(1, 1, 1, 0).unwrap();
    assert_eq!(
      trace.census(),
      F128AlgebraCensusV1 {
        operations: 3,
        additions: 1,
        multiplications: 1,
        inversions: 1,
        equalities: 1,
        deferred_matrix_claims: 0,
      },
    );
    assert_ne!(trace.topology_digest(), [0; 32]);
  }

  #[test]
  fn rejects_forward_operation_reference() {
    let trace = F128AlgebraTraceV1 {
      operations: vec![F128OperationV1::Inverse {
        phase: F128VerifierPhaseV1::Pcs,
        value: F128ReferenceV1::Operation(0),
      }],
      equalities: Vec::new(),
      deferred_matrix_claims: Vec::new(),
    };
    assert!(matches!(
      trace.validate(0, 0, 0, 0),
      Err(F128AlgebraTraceError::ForwardOperationReference { .. })
    ));
  }

  #[test]
  fn validates_structured_deferred_matrix_claims() {
    let private = F128ReferenceV1::Input(F128InputSourceV1::PrivateValue(0));
    let challenge = F128ReferenceV1::Input(F128InputSourceV1::Challenge(0));
    let trace = F128AlgebraTraceV1 {
      operations: Vec::new(),
      equalities: Vec::new(),
      deferred_matrix_claims: vec![F128DeferredMatrixClaimV1 {
        phase: F128VerifierPhaseV1::Lincheck,
        matrix: F128StaticMatrixIdV1 {
          registry_digest: [7; 32],
          table: 3,
          side: F128MatrixSideV1::A,
          variables: 2,
        },
        row: F128StructuredWeightV1 {
          low: vec![challenge, challenge],
          point: vec![challenge],
        },
        column: F128StructuredWeightV1 {
          low: vec![challenge],
          point: vec![challenge, challenge],
        },
        value: private,
      }],
    };
    trace.validate(0, 0, 1, 1).unwrap();
    assert_eq!(trace.census().deferred_matrix_claims, 1);

    let mut malformed = trace;
    malformed.deferred_matrix_claims[0].row.low.push(challenge);
    assert!(matches!(
      malformed.validate(0, 0, 1, 1),
      Err(F128AlgebraTraceError::MalformedMatrixWeight { .. })
    ));
  }
}
