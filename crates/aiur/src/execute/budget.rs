//! Cooperative limits for retained execution data, NOT validity judgments.
//! A child budget belongs to one record; its parent bounds all live records.
//! Reservations are made before query-arena/table growth and released on drop.
//! These conservative accounting limits supplement, not replace, an OS cap:
//! stacks, allocator fragmentation and witness construction also consume RAM.

use std::sync::{
  Arc, Mutex,
  atomic::{AtomicU64, Ordering},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetExceeded {
  pub shared: bool,
  pub used: u64,
  pub requested: u64,
  pub limit: u64,
}

impl std::fmt::Display for BudgetExceeded {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "{} execution memory limit: {} accounted + {} requested > {} bytes",
      if self.shared { "batch" } else { "shard" },
      self.used,
      self.requested,
      self.limit
    )
  }
}

pub struct ExecutionBudget {
  limit: u64,
  used: AtomicU64,
  peak: AtomicU64,
  parent: Option<Arc<Self>>,
  failure: Mutex<Option<BudgetExceeded>>,
  pub label: String,
}

impl ExecutionBudget {
  pub fn new(
    limit: u64,
    label: String,
    parent: Option<Arc<Self>>,
  ) -> Arc<Self> {
    assert!(
      parent.as_ref().is_none_or(|p| p.parent.is_none()),
      "execution budgets support one shared parent, not nested hierarchies"
    );
    Arc::new(Self {
      limit,
      label,
      parent,
      used: AtomicU64::new(0),
      peak: AtomicU64::new(0),
      failure: Mutex::new(None),
    })
  }

  pub fn used(&self) -> u64 {
    self.used.load(Ordering::Relaxed)
  }
  pub fn peak(&self) -> u64 {
    self.peak.load(Ordering::Relaxed)
  }
  pub fn limit(&self) -> u64 {
    self.limit
  }
  pub fn failure(&self) -> Option<BudgetExceeded> {
    self.failure.lock().unwrap().clone()
  }

  fn reserve(&self, bytes: u64, shared: bool) -> Result<(), BudgetExceeded> {
    let previous = self
      .used
      .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |used| {
        used.checked_add(bytes).filter(|next| *next <= self.limit)
      })
      .map_err(|used| BudgetExceeded {
        shared,
        used,
        requested: bytes,
        limit: self.limit,
      })?;
    self.peak.fetch_max(previous + bytes, Ordering::Relaxed);
    Ok(())
  }

  pub fn charge(
    self: &Arc<Self>,
    bytes: u64,
  ) -> Result<Charge, BudgetExceeded> {
    let result = self.reserve(bytes, false).and_then(|()| {
      if let Some(parent) = &self.parent
        && let Err(error) = parent.reserve(bytes, true)
      {
        self.used.fetch_sub(bytes, Ordering::Relaxed);
        return Err(error);
      }
      Ok(())
    });
    if let Err(error) = result {
      *self.failure.lock().unwrap() = Some(error.clone());
      return Err(error);
    }
    Ok(Charge { budget: Arc::clone(self), bytes })
  }

  pub(crate) fn release(&self, bytes: u64) {
    let previous = self.used.fetch_sub(bytes, Ordering::Relaxed);
    debug_assert!(previous >= bytes);
    if let Some(parent) = &self.parent {
      parent.used.fetch_sub(bytes, Ordering::Relaxed);
    }
  }
}

pub struct Charge {
  budget: Arc<ExecutionBudget>,
  bytes: u64,
}

impl Charge {
  /// Transfer responsibility for releasing this reservation to its map.
  pub(crate) fn retain_bytes(mut self, bytes: u64) {
    assert!(bytes <= self.bytes, "execution growth estimate undercharged");
    self.budget.release(self.bytes - bytes);
    self.bytes = 0;
  }
}

impl Drop for Charge {
  fn drop(&mut self) {
    self.budget.release(self.bytes);
  }
}

#[cfg(test)]
mod tests;
