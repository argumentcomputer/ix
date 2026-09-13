//! Bounded one-pass matrix identity and checked-assignment construction.
//! A complete, externally approved census pins the canonical hash header.
//! Every emitted constraint is also hashed with the original projection
//! identity; finish compares the entire expected projection, never just size.

use super::*;

/// A completed matrix stream, not an assignment or a proof. Only a stream
/// matching its complete expected projection can construct this object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1csStreamedShapeV0 {
  projection: R1csProjectionV1,
  canonical_digest: [u8; 32],
}

impl R1csStreamedShapeV0 {
  pub fn projection(&self) -> &R1csProjectionV1 {
    &self.projection
  }

  /// Identical to `CanonicalR1csV1::digest` for the same matrices/layout.
  pub const fn canonical_digest(&self) -> [u8; 32] {
    self.canonical_digest
  }
}

/// Incremental value-free identity checker. The caller owns selection of
/// the approved expected census; it must not be chosen by a private witness.
/// This type never materializes matrices or mints a checked assignment.
pub struct R1csShapeStreamV0 {
  expected: R1csProjectionV1,
  accumulator: ProjectionAccumulator,
  canonical: blake3::Hasher,
  error: Option<R1csError>,
}

impl R1csShapeStreamV0 {
  pub fn new(expected: R1csProjectionV1) -> Result<Self, R1csError> {
    1u32
      .checked_add(expected.public_variables)
      .and_then(|n| n.checked_add(expected.private_variables))
      .ok_or(R1csError::TooManyVariables)?;
    let phase_count = expected
      .census
      .constraints_by_phase
      .values()
      .try_fold(0u64, |sum, count| sum.checked_add(*count))
      .ok_or(R1csError::CountOverflow)?;
    if expected.census.public_variables != u64::from(expected.public_variables)
      || expected.census.private_variables
        != u64::from(expected.private_variables)
      || phase_count != expected.census.constraints
    {
      return Err(R1csError::StreamMismatch);
    }
    let canonical = canonical_hasher(
      expected.public_variables,
      expected.private_variables,
      expected.census.constraints,
    );
    Ok(Self {
      expected,
      accumulator: ProjectionAccumulator::new(),
      canonical,
      error: None,
    })
  }

  /// Refusal is sticky, including unknown wires and any census bound crossed
  /// by the final row. No completed shape can be recovered from a prefix.
  pub fn observe(&mut self, constraint: &Constraint) -> Result<(), R1csError> {
    if let Some(error) = &self.error {
      return Err(error.clone());
    }
    let result = self.observe_inner(constraint);
    if let Err(error) = &result {
      self.error = Some(error.clone());
    }
    result
  }

  fn observe_inner(
    &mut self,
    constraint: &Constraint,
  ) -> Result<(), R1csError> {
    for (variable, _) in constraint
      .a
      .terms()
      .iter()
      .chain(constraint.b.terms())
      .chain(constraint.c.terms())
    {
      if variable.index() >= self.expected.variables() {
        return Err(R1csError::UnknownVariable(*variable));
      }
    }
    let rows = self
      .accumulator
      .constraints
      .checked_add(1)
      .ok_or(R1csError::CountOverflow)?;
    let terms = constraint
      .a
      .terms()
      .len()
      .checked_add(constraint.b.terms().len())
      .and_then(|n| n.checked_add(constraint.c.terms().len()))
      .and_then(|n| u64::try_from(n).ok())
      .and_then(|n| self.accumulator.nonzero_terms.checked_add(n))
      .ok_or(R1csError::CountOverflow)?;
    let phase_rows = self
      .accumulator
      .constraints_by_phase
      .get(&constraint.phase)
      .copied()
      .unwrap_or(0)
      .checked_add(1)
      .ok_or(R1csError::CountOverflow)?;
    for (resource, limit, actual) in [
      ("streamed R1CS constraints", self.expected.census.constraints, rows),
      (
        "streamed R1CS nonzero terms",
        self.expected.census.nonzero_terms,
        terms,
      ),
      (
        "streamed R1CS phase constraints",
        self
          .expected
          .census
          .constraints_by_phase
          .get(&constraint.phase)
          .copied()
          .unwrap_or(0),
        phase_rows,
      ),
    ] {
      if actual > limit {
        return Err(R1csError::ResourceLimit { resource, limit, actual });
      }
    }
    self.accumulator.observe(constraint)?;
    hash_constraint(&mut self.canonical, constraint);
    Ok(())
  }

  pub fn finish(self) -> Result<R1csStreamedShapeV0, R1csError> {
    if let Some(error) = self.error {
      return Err(error);
    }
    let projection = self
      .accumulator
      .finish(self.expected.public_variables, self.expected.private_variables);
    if projection != self.expected {
      return Err(R1csError::StreamMismatch);
    }
    Ok(R1csStreamedShapeV0 {
      projection,
      canonical_digest: *self.canonical.finalize().as_bytes(),
    })
  }
}

/// Immutable assignment checked against EVERY emitted constraint and bound
/// to both the complete projection and canonical matrix identity. There is
/// no constructor from unchecked assignments, prefix digests or counts.
#[derive(Debug, PartialEq, Eq)]
pub struct R1csCheckedStreamV0 {
  shape: R1csStreamedShapeV0,
  witness: Witness,
}

impl R1csCheckedStreamV0 {
  pub fn shape(&self) -> &R1csStreamedShapeV0 {
    &self.shape
  }

  pub fn assignment(&self) -> &[Fr] {
    self.witness.assignment()
  }

  /// Consumes the checked token. Changing the returned witness does not
  /// reconstruct checked state; a backend must consume this token directly.
  pub fn into_parts(self) -> (R1csStreamedShapeV0, Witness) {
    (self.shape, self.witness)
  }
}

pub(super) struct StreamingBuilder {
  shape: R1csShapeStreamV0,
  assignment: Option<Vec<Fr>>,
  observer: Box<dyn FnMut(&Constraint) -> Result<(), R1csError>>,
}

impl StreamingBuilder {
  pub(super) fn is_shape_only(&self) -> bool {
    self.assignment.is_none()
  }

  pub(super) fn constraints_started(&self) -> bool {
    self.shape.accumulator.constraints != 0
  }

  pub(super) fn push_value(&mut self, value: Fr) {
    if let Some(assignment) = &mut self.assignment {
      // Full exact-count capacity is reserved before any emission. Allocation
      // checks prevent both layout changes and capacity growth during push.
      debug_assert!(assignment.len() < assignment.capacity());
      assignment.push(value);
    }
  }

  pub(super) fn observe(
    &mut self,
    constraint: &Constraint,
    allocated: usize,
  ) -> Result<(), R1csError> {
    for (variable, _) in constraint
      .a
      .terms()
      .iter()
      .chain(constraint.b.terms())
      .chain(constraint.c.terms())
    {
      if usize::try_from(variable.index())
        .map_err(|_| R1csError::CountOverflow)?
        >= allocated
      {
        return Err(R1csError::UnknownVariable(*variable));
      }
    }
    if let Some(assignment) = &self.assignment {
      let a = constraint.a.evaluate(assignment)?;
      let b = constraint.b.evaluate(assignment)?;
      let c = constraint.c.evaluate(assignment)?;
      if a * b != c {
        return Err(R1csError::Unsatisfied {
          constraint: usize::try_from(self.shape.accumulator.constraints)
            .map_err(|_| R1csError::CountOverflow)?,
        });
      }
    }
    self.shape.observe(constraint)?;
    (self.observer)(constraint)
  }
}

impl R1csBuilder {
  /// Emit and hash setup matrices without retaining them. All referenced
  /// wires must already be allocated. Scratch values remain unchecked and
  /// cannot be exported as a witness. The expected census is setup-owned.
  pub fn new_shape_streamed_observed(
    expected: R1csProjectionV1,
    observer: impl FnMut(&Constraint) -> Result<(), R1csError> + 'static,
  ) -> Result<Self, R1csError> {
    Self::new_streamed_inner(expected, None, observer)
  }

  /// Retain only the assignment, checking each constraint before forwarding
  /// it. The complete assignment allocation is admitted and reserved once;
  /// the byte cap covers Vec element capacity, not process RSS/overhead.
  pub fn new_checked_streamed_observed(
    expected: R1csProjectionV1,
    maximum_assignment_bytes: u64,
    observer: impl FnMut(&Constraint) -> Result<(), R1csError> + 'static,
  ) -> Result<Self, R1csError> {
    Self::new_streamed_inner(expected, Some(maximum_assignment_bytes), observer)
  }

  fn new_streamed_inner(
    expected: R1csProjectionV1,
    maximum_assignment_bytes: Option<u64>,
    observer: impl FnMut(&Constraint) -> Result<(), R1csError> + 'static,
  ) -> Result<Self, R1csError> {
    let shape = R1csShapeStreamV0::new(expected)?;
    let assignment = if let Some(limit) = maximum_assignment_bytes {
      let fields = usize::try_from(shape.expected.variables())
        .map_err(|_| R1csError::CountOverflow)?;
      let bytes = u64::from(shape.expected.variables())
        .checked_mul(size_of::<Fr>() as u64)
        .ok_or(R1csError::CountOverflow)?;
      if bytes > limit {
        return Err(R1csError::ResourceLimit {
          resource: "streamed R1CS assignment bytes",
          limit,
          actual: bytes,
        });
      }
      let mut assignment = Vec::new();
      assignment.try_reserve_exact(fields).map_err(|_| {
        R1csError::AllocationFailed {
          resource: "streamed R1CS assignment",
          bytes,
        }
      })?;
      let actual = u64::try_from(assignment.capacity())
        .ok()
        .and_then(|n| n.checked_mul(size_of::<Fr>() as u64))
        .ok_or(R1csError::CountOverflow)?;
      if actual > limit {
        return Err(R1csError::ResourceLimit {
          resource: "streamed R1CS assignment capacity bytes",
          limit,
          actual,
        });
      }
      assignment.push(Fr::ONE);
      Some(assignment)
    } else {
      None
    };
    Ok(Self {
      public_variables: 0,
      private_variables: 0,
      error: None,
      f128_preparations: None,
      storage: BuilderStorage::Streamed {
        state: Box::new(StreamingBuilder {
          shape,
          assignment,
          observer: Box::new(observer),
        }),
      },
    })
  }

  pub(super) fn check_streamed_allocation(
    &mut self,
    public: bool,
  ) -> Result<(), R1csError> {
    let BuilderStorage::Streamed { state } = &self.storage else {
      return Ok(());
    };
    let expected = &state.shape.expected;
    let error = if public && self.private_variables != 0 {
      Some(R1csError::PublicAfterPrivate)
    } else if (!public
      && self.public_variables != expected.public_variables as usize)
      || (public && self.public_variables >= expected.public_variables as usize)
      || (!public
        && self.private_variables >= expected.private_variables as usize)
    {
      Some(R1csError::StreamMismatch)
    } else {
      None
    };
    if let Some(error) = error {
      self.error = Some(error.clone());
      return Err(error);
    }
    Ok(())
  }

  fn take_streamed(self) -> Result<StreamingBuilder, R1csError> {
    self.check_status()?;
    let BuilderStorage::Streamed { state } = self.storage else {
      return Err(R1csError::WrongBuilderMode);
    };
    if self.public_variables != state.shape.expected.public_variables as usize
      || self.private_variables
        != state.shape.expected.private_variables as usize
    {
      return Err(R1csError::StreamMismatch);
    }
    Ok(*state)
  }

  pub fn finish_streamed_shape(self) -> Result<R1csStreamedShapeV0, R1csError> {
    let state = self.take_streamed()?;
    if state.assignment.is_some() {
      return Err(R1csError::WrongBuilderMode);
    }
    state.shape.finish()
  }

  pub fn finish_checked_stream(self) -> Result<R1csCheckedStreamV0, R1csError> {
    let state = self.take_streamed()?;
    let assignment = state.assignment.ok_or(R1csError::WrongBuilderMode)?;
    let shape = state.shape.finish()?;
    if assignment.len() != shape.projection.variables() as usize {
      return Err(R1csError::StreamMismatch);
    }
    Ok(R1csCheckedStreamV0 { shape, witness: Witness { assignment } })
  }
}

#[cfg(test)]
#[path = "r1cs_stream_tests.rs"]
mod tests;
