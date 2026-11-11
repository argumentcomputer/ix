//! Optional counted storage reservations for resident execution pools.
//! Charges cover allocation capacity, conservatively including hash buckets.
//! Program artifacts, host advice and prover workspaces are charged by the host.
pub use record_pool::{BudgetError, RecordPool, RecordReservation};

#[derive(Clone, Debug, Default)]
pub(crate) struct Budget(pub Option<RecordReservation>);

pub(crate) struct ReplacedAllocation {
  reservation: Option<RecordReservation>,
  bytes: usize,
}
impl Drop for ReplacedAllocation {
  fn drop(&mut self) {
    if let Some(reservation) = &self.reservation {
      reservation.release(self.bytes);
    }
  }
}

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

/// Rows a query table or the ROM may hold: their hash indexes store 32-bit
/// row numbers.
pub(crate) const MAX_ROWS: usize = 1 << 32;

impl Budget {
  /// The index entry number of `row`, in a table whose rows take
  /// `row_bytes` each. A table beyond [`MAX_ROWS`] rows is a resource error,
  /// reservation or not, as if it had exceeded its record budget.
  #[inline(always)]
  pub(crate) fn row(
    &self,
    row: usize,
    row_bytes: usize,
  ) -> Result<u32, BudgetError> {
    u32::try_from(row).ok().ok_or_else(|| {
      let row_bytes = row_bytes.max(1);
      BudgetError::Exceeded {
        bytes: row.saturating_add(1).saturating_mul(row_bytes),
        cap: MAX_ROWS.saturating_mul(row_bytes),
      }
    })
  }

  #[inline]
  pub(crate) fn reserve(&self, bytes: usize) -> Result<(), BudgetError> {
    if let Some(reservation) = &self.0 {
      reservation.reserve(bytes)?;
    }
    Ok(())
  }

  #[inline]
  pub(crate) fn vector<T>(
    &self,
    values: &mut Vec<T>,
    additional: usize,
  ) -> Result<(), BudgetError> {
    if let Some(reservation) = &self.0
      && values.len().saturating_add(additional) > values.capacity()
    {
      let capacity = values
        .len()
        .saturating_add(additional)
        .max(values.capacity().saturating_mul(2))
        .max(8);
      self.reserve(capacity.saturating_mul(size_of::<T>()))?;
      let old = values.capacity().saturating_mul(size_of::<T>());
      values.reserve_exact(capacity - values.len());
      reservation.release(old);
    }
    Ok(())
  }

  #[inline]
  pub(crate) fn hash<T>(
    &self,
    len: usize,
    capacity: usize,
    charged: &mut usize,
  ) -> Result<ReplacedAllocation, BudgetError> {
    let mut replaced = ReplacedAllocation { reservation: None, bytes: 0 };
    if self.0.is_some() && len == capacity {
      // At least twice the required capacity, including the control bytes.
      let bytes = len
        .saturating_add(1)
        .next_power_of_two()
        .saturating_mul(4)
        .saturating_mul(size_of::<T>() + 1);
      self.reserve(bytes)?;
      replaced =
        ReplacedAllocation { reservation: self.0.clone(), bytes: *charged };
      *charged = bytes;
    }
    Ok(replaced)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn vector_growth_charges_live_capacity_and_transient_peak() {
    let pool = RecordPool::new(4096, 8);
    let reservation = pool.try_admit().unwrap().unwrap();
    let budget = Budget(Some(reservation.clone()));
    let mut values = Vec::<u64>::new();
    for value in 0..128 {
      budget.vector(&mut values, 1).unwrap();
      values.push(value);
      assert_eq!(reservation.bytes(), values.capacity() * 8);
    }
    assert!(pool.stats().peak_reserved >= (64 + 128) * 8);
    reservation.finish_execution();
    assert_eq!(pool.stats().reserved, 128 * 8);
  }

  #[test]
  fn rows_beyond_the_index_width_are_resource_errors() {
    for budget in [
      Budget(None),
      Budget(Some(RecordPool::new(64, 8).try_admit().unwrap().unwrap())),
    ] {
      assert_eq!(budget.row(0, 24), Ok(0));
      assert_eq!(budget.row(MAX_ROWS - 1, 24), Ok(u32::MAX));
      assert_eq!(
        budget.row(MAX_ROWS, 24),
        Err(BudgetError::Exceeded {
          bytes: (MAX_ROWS + 1) * 24,
          cap: MAX_ROWS * 24
        })
      );
      assert!(matches!(
        budget.row(usize::MAX, 0),
        Err(BudgetError::Exceeded { .. })
      ));
    }
  }
}
