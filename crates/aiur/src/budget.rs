//! Optional counted storage reservations for resident execution pools.
//! Charges cover allocation capacity, conservatively including hash buckets.
//! Program artifacts, host advice and prover workspaces are charged by the host.
pub use record_pool::{BudgetError, RecordPool, RecordReservation};

#[derive(Clone, Debug, Default)]
pub(crate) struct Budget(pub Option<RecordReservation>);

#[derive(Debug)]
pub(crate) enum StorageError {
  Resource(BudgetError),
  Invalid(&'static str),
}
impl From<BudgetError> for StorageError {
  fn from(error: BudgetError) -> Self {
    Self::Resource(error)
  }
}
impl From<&'static str> for StorageError {
  fn from(error: &'static str) -> Self {
    Self::Invalid(error)
  }
}
impl std::fmt::Display for StorageError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Resource(e) => e.fmt(f),
      Self::Invalid(e) => f.write_str(e),
    }
  }
}

impl Budget {
  #[inline]
  pub fn reserve(&self, bytes: usize) -> Result<(), BudgetError> {
    if let Some(reservation) = &self.0 {
      reservation.reserve(bytes)?;
    }
    Ok(())
  }

  #[inline]
  pub fn vector<T>(
    &self,
    values: &Vec<T>,
    additional: usize,
  ) -> Result<(), BudgetError> {
    if self.0.is_some()
      && values.len().saturating_add(additional) > values.capacity()
    {
      let capacity = values
        .len()
        .saturating_add(additional)
        .max(values.capacity().saturating_mul(2))
        .max(8);
      self.reserve(capacity.saturating_mul(std::mem::size_of::<T>()))?;
    }
    Ok(())
  }

  #[inline]
  pub fn hash<T>(
    &self,
    len: usize,
    capacity: usize,
  ) -> Result<(), BudgetError> {
    if self.0.is_some() && len == capacity {
      // At least twice the required capacity, including the control bytes.
      self.reserve(
        len
          .saturating_add(1)
          .next_power_of_two()
          .saturating_mul(4)
          .saturating_mul(std::mem::size_of::<T>() + 1),
      )?;
    }
    Ok(())
  }
}
