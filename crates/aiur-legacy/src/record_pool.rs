//! Shared capacity for execution records, retained until their storage drops.

use std::collections::{BTreeMap, VecDeque};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

const GRANT_BYTES: usize = 16 << 20;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BudgetError {
  Exceeded { bytes: usize, cap: usize },
  Cancelled,
  Shutdown,
}

#[derive(Clone, Copy, Debug)]
pub struct ProverBudget {
  pub trace_cells: usize,
  pub host_workspace: usize,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct PoolStats {
  pub reserved: usize,
  pub peak_reserved: usize,
  pub waits: usize,
  pub wait_time: Duration,
  pub retries: usize,
}

#[derive(Debug, Default)]
struct Credit {
  available: AtomicUsize,
  cancelled: AtomicBool,
}

#[derive(Debug)]
struct Entry {
  grant: usize,
  credit: Arc<Credit>,
  executing: bool,
  waiting: bool,
  needed: usize,
}

#[derive(Debug, Default)]
struct State {
  entries: BTreeMap<u64, Entry>,
  next_id: u64,
  waiters: VecDeque<u64>,
  preferred: Option<u64>,
  stats: PoolStats,
}

#[derive(Debug)]
struct PoolInner {
  limit: usize,
  record_limit: usize,
  initial: usize,
  chunk: usize,
  prover: Option<ProverBudget>,
  shutdown: AtomicBool,
  state: Mutex<State>,
  changed: Condvar,
}

#[derive(Clone, Debug)]
pub struct RecordPool(Arc<PoolInner>);

/// Clones share one charge. Query maps own clones so credit is released
/// only after the last associated storage allocation has been dropped.
#[derive(Clone, Debug)]
pub struct RecordReservation(Arc<ReservationInner>);

#[derive(Debug)]
struct ReservationInner {
  pool: RecordPool,
  id: u64,
  credit: Arc<Credit>,
}

impl RecordPool {
  pub fn new(limit: usize, initial: usize) -> Self {
    Self::with_chunk(limit, initial, GRANT_BYTES)
  }

  pub fn for_provers(
    limit: usize,
    initial: usize,
    prover: ProverBudget,
  ) -> Self {
    assert!(prover.trace_cells > 0 && prover.host_workspace > 0);
    let mut pool = Self::new(limit, initial);
    Arc::get_mut(&mut pool.0).unwrap().prover = Some(prover);
    pool
  }

  /// Bound each record independently of aggregate capacity. Clamping
  /// grants also enforces the bound on the insertion fast path.
  pub fn with_record_limit(mut self, limit: usize) -> Self {
    assert!(limit > 0);
    let pool = Arc::get_mut(&mut self.0)
      .expect("record limit must be set before sharing the pool");
    pool.record_limit = limit.min(pool.limit);
    pool.initial = pool.initial.min(pool.record_limit);
    self
  }

  fn with_chunk(limit: usize, initial: usize, chunk: usize) -> Self {
    assert!(limit > 0 && initial > 0 && initial <= limit && chunk > 0);
    Self(Arc::new(PoolInner {
      limit,
      record_limit: limit,
      initial,
      chunk,
      prover: None,
      shutdown: AtomicBool::new(false),
      state: Mutex::new(State::default()),
      changed: Condvar::new(),
    }))
  }

  pub fn limit(&self) -> usize {
    self.0.limit
  }

  pub fn record_limit(&self) -> usize {
    self.0.record_limit
  }

  /// Admission never blocks the dependency scheduler. Growth takes
  /// precedence until the selected execution finishes.
  pub fn try_admit(&self) -> Result<Option<RecordReservation>, BudgetError> {
    let mut state = self.0.state.lock().unwrap();
    if self.0.shutdown.load(Ordering::Relaxed) {
      return Err(BudgetError::Shutdown);
    }
    if state.preferred.is_some()
      || self.0.limit - state.stats.reserved < self.0.initial
    {
      return Ok(None);
    }
    let id = state.next_id;
    state.next_id += 1;
    let credit = Arc::new(Credit::default());
    credit.available.store(self.0.initial, Ordering::Relaxed);
    state.entries.insert(
      id,
      Entry {
        grant: self.0.initial,
        credit: Arc::clone(&credit),
        executing: true,
        waiting: false,
        needed: 0,
      },
    );
    state.stats.reserved += self.0.initial;
    state.stats.peak_reserved =
      state.stats.peak_reserved.max(state.stats.reserved);
    Ok(Some(RecordReservation(Arc::new(ReservationInner {
      pool: self.clone(),
      id,
      credit,
    }))))
  }

  pub fn stats(&self) -> PoolStats {
    self.0.state.lock().unwrap().stats
  }

  pub fn shutdown(&self) {
    let _state = self.0.state.lock().unwrap();
    self.0.shutdown.store(true, Ordering::Relaxed);
    self.0.changed.notify_all();
  }
}

impl State {
  fn select_waiter(&mut self) {
    if self.preferred.is_none() {
      self.preferred = self.waiters.front().copied();
    }
  }

  fn remove_waiter(&mut self, id: u64) {
    self.waiters.retain(|&waiting| waiting != id);
    if self.preferred == Some(id) {
      self.preferred = None;
    }
    self.select_waiter();
  }

  fn cancel_blocked_peer(&mut self, available: usize) -> bool {
    if self.preferred.is_none_or(|id| self.entries[&id].needed <= available) {
      return false;
    }
    // A retained record can drain through a prover. A cancelled execution
    // must drop its storage before another victim can be selected.
    if self.entries.values().any(|entry| {
      !entry.executing
        || !entry.waiting
        || entry.credit.cancelled.load(Ordering::Relaxed)
    }) {
      return false;
    }
    let victim = self
      .entries
      .iter()
      .rev()
      .find(|(id, _)| Some(**id) != self.preferred)
      .map(|(&id, _)| id);
    let Some(victim) = victim else { return false };
    self.entries[&victim].credit.cancelled.store(true, Ordering::Relaxed);
    self.waiters.retain(|&id| id != victim);
    self.stats.retries += 1;
    true
  }
}

impl RecordReservation {
  pub fn prover_budget(&self) -> Option<ProverBudget> {
    self.0.pool.0.prover
  }

  #[inline]
  pub fn check(&self) -> Result<(), BudgetError> {
    if self.0.pool.0.shutdown.load(Ordering::Relaxed) {
      Err(BudgetError::Shutdown)
    } else if self.0.credit.cancelled.load(Ordering::Relaxed) {
      Err(BudgetError::Cancelled)
    } else {
      Ok(())
    }
  }

  /// Charge before allocation. Most insertions consume local credit;
  /// only replenishing a chunk takes the process-wide mutex.
  #[inline]
  pub fn reserve(&self, bytes: usize) -> Result<(), BudgetError> {
    loop {
      self.check()?;
      if self
        .0
        .credit
        .available
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |credit| {
          credit.checked_sub(bytes)
        })
        .is_ok()
      {
        return Ok(());
      }
      self.grow(bytes)?;
    }
  }

  fn grow(&self, bytes: usize) -> Result<(), BudgetError> {
    let pool = &self.0.pool.0;
    let id = self.0.id;
    let mut state = pool.state.lock().unwrap();
    let mut began = None;
    let result = loop {
      if let Err(error) = self.check() {
        break Err(error);
      }
      let entry = &state.entries[&id];
      let credit = entry.credit.available.load(Ordering::Relaxed);
      if credit >= bytes {
        break Ok(());
      }
      let required = (entry.grant - credit).saturating_add(bytes);
      if required > pool.record_limit {
        break Err(BudgetError::Exceeded {
          bytes: required,
          cap: pool.record_limit,
        });
      }
      let missing = bytes - credit;
      let available = pool.limit - state.stats.reserved;
      if state.preferred.is_none_or(|preferred| preferred == id)
        && available >= missing
      {
        let extra = missing
          .max(pool.chunk)
          .min(available)
          .min(pool.record_limit - entry.grant);
        let entry = state.entries.get_mut(&id).unwrap();
        entry.grant += extra;
        entry.waiting = false;
        entry.credit.available.fetch_add(extra, Ordering::Relaxed);
        state.stats.reserved += extra;
        state.stats.peak_reserved =
          state.stats.peak_reserved.max(state.stats.reserved);
        break Ok(());
      }
      if began.is_none() {
        began = Some(Instant::now());
        state.stats.waits += 1;
      }
      let entry = state.entries.get_mut(&id).unwrap();
      entry.waiting = true;
      entry.needed = missing;
      if !state.waiters.contains(&id) {
        state.waiters.push_back(id);
      }
      state.select_waiter();
      if state.cancel_blocked_peer(available) {
        pool.changed.notify_all();
        continue;
      }
      state = pool.changed.wait(state).unwrap();
    };
    if let Some(began) = began {
      state.stats.wait_time += began.elapsed();
    }
    result
  }

  pub fn bytes(&self) -> usize {
    let state = self.0.pool.0.state.lock().unwrap();
    state.entries[&self.0.id].grant
      - self.0.credit.available.load(Ordering::Relaxed)
  }

  /// Planning and proving only read the record. Return speculative
  /// capacity now, retaining its used charge through both proving rounds.
  pub fn finish_execution(&self) {
    let pool = &self.0.pool.0;
    let mut state = pool.state.lock().unwrap();
    let unused = self.0.credit.available.swap(0, Ordering::Relaxed);
    let entry = state.entries.get_mut(&self.0.id).unwrap();
    entry.grant -= unused;
    entry.executing = false;
    entry.waiting = false;
    state.stats.reserved -= unused;
    state.remove_waiter(self.0.id);
    pool.changed.notify_all();
  }
}

impl Drop for ReservationInner {
  fn drop(&mut self) {
    let pool = &self.pool.0;
    let mut state = pool.state.lock().unwrap();
    let entry = state.entries.remove(&self.id).unwrap();
    state.stats.reserved -= entry.grant;
    state.remove_waiter(self.id);
    pool.changed.notify_all();
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::{sync::mpsc, thread};

  struct Shutdown(RecordPool);
  impl Drop for Shutdown {
    fn drop(&mut self) {
      self.0.shutdown();
    }
  }

  fn wait_for(pool: &RecordPool, waits: usize) {
    let deadline = Instant::now() + Duration::from_secs(3);
    while pool.stats().waits < waits {
      assert!(Instant::now() < deadline, "growth request did not wait");
      thread::sleep(Duration::from_millis(1));
    }
  }

  #[test]
  fn reservation_follows_storage_and_returns_unused_credit() {
    let pool = RecordPool::with_chunk(100, 40, 8);
    let record = pool.try_admit().unwrap().unwrap();
    record.reserve(13).unwrap();
    let storage = record.clone();
    record.finish_execution();
    assert_eq!(pool.stats().reserved, 13);
    drop(record);
    assert_eq!(pool.stats().reserved, 13);
    thread::spawn(move || drop(storage)).join().unwrap();
    assert_eq!(pool.stats().reserved, 0);
  }

  #[test]
  fn waits_for_proving_record_and_keeps_execution() {
    let pool = RecordPool::with_chunk(100, 40, 8).with_record_limit(95);
    let _shutdown = Shutdown(pool.clone());
    let running = pool.try_admit().unwrap().unwrap();
    let proving = pool.try_admit().unwrap().unwrap();
    running.reserve(40).unwrap();
    proving.reserve(40).unwrap();
    proving.finish_execution();
    let task = thread::spawn(move || {
      running.reserve(50).unwrap();
      assert_eq!(running.bytes(), 90);
      running.finish_execution();
    });
    wait_for(&pool, 1);
    assert!(pool.try_admit().unwrap().is_none());
    drop(proving);
    task.join().unwrap();
    assert_eq!(pool.stats().retries, 0);
    assert_eq!(pool.stats().reserved, 0);
  }

  #[test]
  fn mutual_block_cancels_youngest_then_selected_fits_alone() {
    let pool = RecordPool::with_chunk(100, 40, 8);
    let _shutdown = Shutdown(pool.clone());
    let older = pool.try_admit().unwrap().unwrap();
    let younger = pool.try_admit().unwrap().unwrap();
    older.reserve(40).unwrap();
    younger.reserve(40).unwrap();
    let first = thread::spawn(move || older.reserve(50));
    wait_for(&pool, 1);
    let second = thread::spawn(move || younger.reserve(1));
    assert_eq!(second.join().unwrap(), Err(BudgetError::Cancelled));
    assert_eq!(first.join().unwrap(), Ok(()));
    assert_eq!(pool.stats().retries, 1);
    assert_eq!(pool.stats().reserved, 0);
  }

  #[test]
  fn growth_priority_lasts_until_execution_finishes() {
    let pool = RecordPool::with_chunk(120, 30, 8);
    let _shutdown = Shutdown(pool.clone());
    let first = pool.try_admit().unwrap().unwrap();
    let second = pool.try_admit().unwrap().unwrap();
    let proving = pool.try_admit().unwrap().unwrap();
    for record in [&first, &second, &proving] {
      record.reserve(30).unwrap();
    }
    proving.finish_execution();
    let (grown_tx, grown_rx) = mpsc::channel();
    let (finish_tx, finish_rx) = mpsc::channel();
    let owner = thread::spawn(move || {
      first.reserve(50).unwrap();
      grown_tx.send(()).unwrap();
      finish_rx.recv().unwrap();
      first.finish_execution();
    });
    wait_for(&pool, 1);
    let (second_tx, second_rx) = mpsc::channel();
    let peer = thread::spawn(move || {
      second.reserve(10).unwrap();
      second_tx.send(()).unwrap();
    });
    wait_for(&pool, 2);
    drop(proving);
    grown_rx.recv_timeout(Duration::from_secs(3)).unwrap();
    assert!(second_rx.try_recv().is_err());
    assert!(pool.try_admit().unwrap().is_none());
    finish_tx.send(()).unwrap();
    second_rx.recv_timeout(Duration::from_secs(3)).unwrap();
    owner.join().unwrap();
    peer.join().unwrap();
    assert_eq!(pool.stats().retries, 0);
  }

  #[test]
  fn shutdown_wakes_blocked_growth() {
    let pool = RecordPool::with_chunk(100, 40, 8);
    let _shutdown = Shutdown(pool.clone());
    let running = pool.try_admit().unwrap().unwrap();
    let proving = pool.try_admit().unwrap().unwrap();
    running.reserve(40).unwrap();
    proving.reserve(40).unwrap();
    proving.finish_execution();
    let task = thread::spawn(move || running.reserve(50));
    wait_for(&pool, 1);
    pool.shutdown();
    assert_eq!(task.join().unwrap(), Err(BudgetError::Shutdown));
    assert!(matches!(pool.try_admit(), Err(BudgetError::Shutdown)));
    drop(proving);
    assert_eq!(pool.stats().reserved, 0);
  }

  #[test]
  fn large_entry_and_whole_pool_overflow() {
    let pool = RecordPool::with_chunk(100, 10, 8);
    let record = pool.try_admit().unwrap().unwrap();
    record.reserve(100).unwrap();
    assert_eq!(record.bytes(), 100);
    assert_eq!(
      record.reserve(1),
      Err(BudgetError::Exceeded { bytes: 101, cap: 100 })
    );
    assert_eq!(record.bytes(), 100);
    drop(record);
    assert_eq!(pool.stats().reserved, 0);
    assert_eq!(pool.stats().peak_reserved, 100);
  }

  #[test]
  fn record_ceiling_clamps_initial_and_growth_credit() {
    for initial in [10, 80] {
      let pool = RecordPool::with_chunk(200, initial, 80).with_record_limit(60);
      let record = pool.try_admit().unwrap().unwrap();
      record.reserve(59).unwrap();
      record.reserve(1).unwrap();
      assert_eq!(record.bytes(), 60);
      assert_eq!(pool.stats().reserved, 60);
      assert_eq!(
        record.reserve(1),
        Err(BudgetError::Exceeded { bytes: 61, cap: 60 })
      );
      assert_eq!(pool.stats().waits, 0);
      assert!(pool.try_admit().unwrap().is_some());
      drop(record);
      assert_eq!(pool.stats().reserved, 0);
    }
  }

  #[test]
  fn record_ceiling_rejects_before_waiting_on_a_full_pool() {
    let pool = RecordPool::with_chunk(100, 50, 8).with_record_limit(60);
    let first = pool.try_admit().unwrap().unwrap();
    let second = pool.try_admit().unwrap().unwrap();
    first.reserve(50).unwrap();
    assert_eq!(
      first.reserve(11),
      Err(BudgetError::Exceeded { bytes: 61, cap: 60 })
    );
    assert_eq!(pool.stats().waits, 0);
    assert_eq!(pool.stats().retries, 0);
    drop((first, second));
    assert_eq!(pool.stats().reserved, 0);
  }
}
