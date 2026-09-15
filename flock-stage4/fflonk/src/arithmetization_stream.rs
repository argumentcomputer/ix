//! Stream canonical R1CS constraints directly into preallocated PLONK gates.
//! The independent matrix stream must match the full expected projection;
//! counts alone cannot authorize a different matrix or a completed prefix.

use super::*;
use ark_ff::AdditiveGroup;
use ix_terminal_circuit::R1csShapeStreamV0;

/// Native element payloads for streamed materialization and copy cycles.
/// Excludes the assignment, emitter state, SRS/key, allocator/Vec headers,
/// and process/OS memory. This is not whole-pipeline RSS admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlonkStreamMemoryV0 {
  pub gate_bytes: u64,
  pub copy_target_bytes: u64,
  pub copy_tail_bytes: u64,
  pub peak_payload_bytes: u64,
}

/// Checked arithmetic only: does not allocate gate, copy or witness arrays.
pub fn plan_plonk_stream_memory(
  r1cs_variables: u32,
  census: &PlonkGateCensusV1,
) -> Result<PlonkStreamMemoryV0, PlonkArithmetizationError> {
  let expected = size_census(
    census.public_input_rows,
    census.constraint_rows,
    census.auxiliary_wires,
    census.rows_by_phase.clone(),
  )?;
  let phase_rows = census
    .rows_by_phase
    .values()
    .try_fold(0u64, |sum, rows| sum.checked_add(*rows))
    .ok_or(PlonkArithmetizationError::CountOverflow)?;
  if r1cs_variables == 0
    || census.public_input_rows >= u64::from(r1cs_variables)
    || &expected != census
    || phase_rows != census.constraint_rows
  {
    return Err(PlonkArithmetizationError::StreamCensusMismatch);
  }
  if census.domain_size > crate::FFLONK_MAX_BASE_DOMAIN {
    return Err(PlonkArithmetizationError::DomainTooLarge {
      required_rows: census
        .active_rows()
        .checked_add(FFLONK_BLINDING_ROWS)
        .ok_or(PlonkArithmetizationError::CountOverflow)?,
      maximum_domain: crate::FFLONK_MAX_BASE_DOMAIN,
    });
  }
  let bytes = |count: u64, width: usize| {
    count
      .checked_mul(width as u64)
      .ok_or(PlonkArithmetizationError::CountOverflow)
  };
  let gate_bytes = bytes(census.domain_size, size_of::<PlonkGateV1>())?;
  let copy_target_bytes =
    bytes(census.domain_size, 3 * size_of::<PlonkCellV1>())?;
  let copy_tail_bytes = bytes(
    u64::from(r1cs_variables)
      .checked_add(census.auxiliary_wires)
      .ok_or(PlonkArithmetizationError::CountOverflow)?,
    size_of::<u64>(),
  )?;
  let peak_payload_bytes = gate_bytes
    .checked_add(copy_target_bytes)
    .and_then(|n| n.checked_add(copy_tail_bytes))
    .ok_or(PlonkArithmetizationError::CountOverflow)?;
  Ok(PlonkStreamMemoryV0 {
    gate_bytes,
    copy_target_bytes,
    copy_tail_bytes,
    peak_payload_bytes,
  })
}

struct PayloadBudget {
  used: u64,
  limit: u64,
}

impl PayloadBudget {
  fn reserve<T>(
    &mut self,
    count: usize,
    resource: &'static str,
  ) -> Result<Vec<T>, PlonkArithmetizationError> {
    let bytes = |count: usize| {
      u64::try_from(count)
        .ok()
        .and_then(|n| n.checked_mul(size_of::<T>() as u64))
        .ok_or(PlonkArithmetizationError::CountOverflow)
    };
    let requested = bytes(count)?;
    self.check_add(requested)?;
    let mut values = Vec::new();
    values.try_reserve_exact(count).map_err(|_| {
      R1csError::AllocationFailed { resource, bytes: requested }
    })?;
    let actual = bytes(values.capacity())?;
    self.check_add(actual)?;
    self.used += actual;
    Ok(values)
  }

  fn check_add(&self, bytes: u64) -> Result<(), PlonkArithmetizationError> {
    let actual = self
      .used
      .checked_add(bytes)
      .ok_or(PlonkArithmetizationError::CountOverflow)?;
    if actual > self.limit {
      return Err(
        R1csError::ResourceLimit {
          resource: "streamed PLONK payload bytes",
          limit: self.limit,
          actual,
        }
        .into(),
      );
    }
    Ok(())
  }
}

struct BoundedSink {
  inner: MaterializingSink,
  maximum_rows: u64,
  maximum_auxiliaries: u64,
}

impl GateSink for BoundedSink {
  fn allocate_auxiliary(
    &mut self,
  ) -> Result<PlonkWireV1, PlonkArithmetizationError> {
    if self.inner.next_auxiliary >= self.maximum_auxiliaries {
      return Err(
        R1csError::ResourceLimit {
          resource: "streamed PLONK auxiliary wires",
          limit: self.maximum_auxiliaries,
          actual: self
            .inner
            .next_auxiliary
            .checked_add(1)
            .ok_or(PlonkArithmetizationError::CountOverflow)?,
        }
        .into(),
      );
    }
    self.inner.allocate_auxiliary()
  }

  fn push(
    &mut self,
    gate: PlonkGateV1,
  ) -> Result<(), PlonkArithmetizationError> {
    let rows = u64::try_from(self.inner.gates.len())
      .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
    if rows >= self.maximum_rows {
      return Err(
        R1csError::ResourceLimit {
          resource: "streamed PLONK active rows",
          limit: self.maximum_rows,
          actual: rows
            .checked_add(1)
            .ok_or(PlonkArithmetizationError::CountOverflow)?,
        }
        .into(),
      );
    }
    debug_assert!(self.inner.gates.len() < self.inner.gates.capacity());
    self.inner.push(gate)
  }
}

struct StreamState {
  matrix: R1csShapeStreamV0,
  sink: BoundedSink,
  expected: PlonkGateCensusV1,
  payload_limit: u64,
  error: Option<PlonkArithmetizationError>,
}

impl StreamState {
  fn observe(
    &mut self,
    constraint: &Constraint,
  ) -> Result<(), PlonkArithmetizationError> {
    if let Some(error) = &self.error {
      return Err(error.clone());
    }
    let result = self
      .matrix
      .observe(constraint)
      .map_err(PlonkArithmetizationError::from)
      .and_then(|()| lower_constraint(&mut self.sink, constraint));
    if let Err(error) = &result {
      self.error = Some(error.clone());
    }
    result
  }

  fn finish(self) -> Result<PlonkArithmetizationV1, PlonkArithmetizationError> {
    if let Some(error) = self.error {
      return Err(error);
    }
    let shape = self.matrix.finish()?;
    let mut sink = self.sink.inner;
    let constraint_rows = u64::try_from(sink.gates.len())
      .map_err(|_| PlonkArithmetizationError::CountOverflow)?
      .checked_sub(self.expected.public_input_rows)
      .ok_or(PlonkArithmetizationError::CountOverflow)?;
    let actual = finish_census(
      self.expected.public_input_rows,
      constraint_rows,
      sink.next_auxiliary,
      sink.rows_by_phase,
    )?;
    if actual != self.expected {
      return Err(PlonkArithmetizationError::StreamCensusMismatch);
    }
    let n = usize::try_from(actual.domain_size)
      .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
    // Capacity was reserved once before the first emitted gate.
    debug_assert!(sink.gates.capacity() >= n);
    sink.gates.resize_with(n, PlonkGateV1::blank);
    let mut budget = PayloadBudget {
      used: u64::try_from(sink.gates.capacity())
        .ok()
        .and_then(|n| n.checked_mul(size_of::<PlonkGateV1>() as u64))
        .ok_or(PlonkArithmetizationError::CountOverflow)?,
      limit: self.payload_limit,
    };
    let mut sigma: [Vec<PlonkCellV1>; 3] = core::array::from_fn(|_| Vec::new());
    for (column, values) in sigma.iter_mut().enumerate() {
      *values = budget.reserve(n, "streamed PLONK copy targets")?;
      values.extend((0..n).map(|row| PlonkCellV1 {
        column: u8::try_from(column).expect("three columns"),
        row: row as u64,
      }));
    }
    let variables = shape.projection().variables();
    let slots = u64::from(variables)
      .checked_add(actual.auxiliary_wires)
      .and_then(|n| usize::try_from(n).ok())
      .ok_or(PlonkArithmetizationError::CountOverflow)?;
    let mut tails = budget.reserve(slots, "streamed PLONK copy tails")?;
    tails.resize(slots, 0u64);
    // The explicit budget includes dense tails even for unused wire slots;
    // no unbounded sparse map can grow outside this payload accounting.
    populate_copy_permutation(
      &sink.gates,
      variables,
      actual.auxiliary_wires,
      &mut sigma,
      &mut CopyTails::Dense(tails),
    )?;
    Ok(PlonkArithmetizationV1 {
      r1cs_digest: shape.canonical_digest(),
      r1cs_variables: variables,
      census: actual,
      gates: sink.gates,
      sigma,
    })
  }
}

/// Materializes PLONK directly from an R1CS stream without retaining R1CS
/// matrices. The expected complete geometry is selected by approved setup.
/// A separately hashed constraint stream must match that complete identity.
/// Only gate/copy/tail element payloads are admitted here, not the full prover.
pub struct PlonkArithmetizationStreamV0 {
  state: Rc<RefCell<StreamState>>,
}

impl PlonkArithmetizationStreamV0 {
  pub fn new(
    expected_r1cs: R1csProjectionV1,
    expected_plonk: PlonkGateCensusV1,
    maximum_payload_bytes: u64,
  ) -> Result<Self, PlonkArithmetizationError> {
    let matrix = R1csShapeStreamV0::new(expected_r1cs.clone())?;
    if u64::from(expected_r1cs.public_variables())
      != expected_plonk.public_input_rows
    {
      return Err(PlonkArithmetizationError::StreamCensusMismatch);
    }
    let plan =
      plan_plonk_stream_memory(expected_r1cs.variables(), &expected_plonk)?;
    let mut budget = PayloadBudget { used: 0, limit: maximum_payload_bytes };
    budget.check_add(plan.peak_payload_bytes)?;
    let n = usize::try_from(expected_plonk.domain_size)
      .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
    let gates = budget.reserve(n, "streamed PLONK gates")?;
    budget.check_add(
      plan
        .copy_target_bytes
        .checked_add(plan.copy_tail_bytes)
        .ok_or(PlonkArithmetizationError::CountOverflow)?,
    )?;
    let mut sink = BoundedSink {
      inner: MaterializingSink { gates, ..MaterializingSink::default() },
      maximum_rows: expected_plonk.active_rows(),
      maximum_auxiliaries: expected_plonk.auxiliary_wires,
    };
    for index in 0..expected_r1cs.public_variables() {
      sink.push(PlonkGateV1 {
        phase: None,
        wires: [
          Some(PlonkWireV1::R1cs(Variable::from_index(index + 1))),
          None,
          None,
        ],
        ql: Fr::ONE,
        qr: Fr::ZERO,
        qm: Fr::ZERO,
        qo: Fr::ZERO,
        qc: Fr::ZERO,
      })?;
    }
    Ok(Self {
      state: Rc::new(RefCell::new(StreamState {
        matrix,
        sink,
        expected: expected_plonk,
        payload_limit: maximum_payload_bytes,
        error: None,
      })),
    })
  }

  /// Attach to a streamed R1CS builder. Drop all observers (normally by
  /// finishing the builder) before finishing this materialization.
  pub fn observer(
    &self,
  ) -> impl FnMut(&Constraint) -> Result<(), R1csError> + 'static {
    let state = self.state.clone();
    move |constraint| {
      state
        .try_borrow_mut()
        .map_err(|_| {
          R1csError::ObserverFailure("PLONK stream already borrowed".into())
        })?
        .observe(constraint)
        .map_err(|error| match error {
          PlonkArithmetizationError::R1cs(error) => error,
          other => R1csError::ObserverFailure(other.to_string()),
        })
    }
  }

  pub fn finish(
    self,
  ) -> Result<PlonkArithmetizationV1, PlonkArithmetizationError> {
    let state = Rc::try_unwrap(self.state)
      .map_err(|_| PlonkArithmetizationError::StreamObserverAttached)?;
    state.into_inner().finish()
  }
}

#[cfg(test)]
#[path = "arithmetization_stream_tests.rs"]
mod tests;
