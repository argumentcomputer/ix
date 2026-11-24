//! Shared capacity for execution records, retained until their storage drops.
pub mod host;
pub mod queue;

use std::collections::{BTreeMap, BTreeSet};
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

impl std::fmt::Display for BudgetError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Exceeded { bytes, cap } => {
        write!(f, "record needs {bytes} bytes, limit is {cap}")
      },
      Self::Cancelled => {
        f.write_str("record execution cancelled for memory contention")
      },
      Self::Shutdown => f.write_str("record pool shut down"),
    }
  }
}
impl std::error::Error for BudgetError {}

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
  /// Executions cancelled so a blocked peer could grow.
  pub retries: usize,
  /// Times admission froze because running executions outgrew their
  /// charges by more than the overshoot buffer.
  pub freezes: usize,
  pub frozen_time: Duration,
}

/// A snapshot of what the pool holds now.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PoolUsage {
  /// Bytes granted to reservations: their storage plus unused credit.
  pub granted: usize,
  /// Granted bytes backed by storage, without unused credit.
  pub used: usize,
  /// Reservations held: executing, or executed records not yet dropped.
  pub records: usize,
  pub executing: usize,
}

/// What a growth request gets from the [`Ledger`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Growth {
  /// The entry's grant grew by this many bytes (0: its credit sufficed).
  Granted(usize),
  /// No capacity now; retry when the ledger changes. `cancel` names a peer
  /// cancelled so the selected waiter can grow.
  Wait {
    cancel: Option<u64>,
  },
  Exceeded {
    bytes: usize,
    cap: usize,
  },
  Cancelled,
}

#[derive(Debug)]
struct Entry {
  grant: usize,
  /// The bytes the entry was admitted for.
  charge: usize,
  executing: bool,
  waiting: bool,
  needed: usize,
  cancelled: bool,
}

/// The record pool's accounting, without threads or clocks: admission,
/// growth, contention and the freeze, over entries identified by admission
/// order. [`RecordPool`] runs it under a mutex; a simulation can drive it
/// directly.
///
/// Predicted admission ([`Self::admit`]) charges each execution its
/// predicted record. Up to a floor the caller sets, executions are admitted
/// as fixed admission ([`Self::admit_initial`]) admits them; beyond it, only
/// while the running executions' charges, the executed records awaiting or
/// in proof, the new charge and an overshoot buffer fit the limit.
///
/// An execution grows freely, into any free capacity, up to one buffer past
/// its charge. Further growth contends: it waits for the execution holding
/// growth priority (the oldest waiter, until it finishes) and never takes
/// capacity other running executions were admitted for and have not yet
/// grown into. While running executions exceed their charges by more than
/// the buffer, and from the moment they do or one waits to, until an
/// execution finishes, admission above the floor is frozen. Only when every
/// execution waits, no executed record is draining, and the priority holder
/// cannot grow is the youngest other execution cancelled.
#[derive(Debug)]
pub struct Ledger {
  limit: usize,
  record_limit: usize,
  initial: usize,
  chunk: usize,
  buffer: usize,
  entries: BTreeMap<u64, Entry>,
  next_id: u64,
  waiters: BTreeSet<u64>,
  preferred: Option<u64>,
  frozen: bool,
  stats: PoolStats,
}

impl Ledger {
  pub fn new(limit: usize, initial: usize) -> Self {
    Self::with_chunk(limit, initial, GRANT_BYTES)
  }

  fn with_chunk(limit: usize, initial: usize, chunk: usize) -> Self {
    assert!(limit > 0 && initial > 0 && initial <= limit && chunk > 0);
    Self {
      limit,
      record_limit: limit,
      initial,
      chunk,
      buffer: 0,
      entries: BTreeMap::new(),
      next_id: 0,
      waiters: BTreeSet::new(),
      preferred: None,
      frozen: false,
      stats: PoolStats::default(),
    }
  }

  /// Bound each record independently of aggregate capacity.
  #[must_use]
  pub fn with_record_limit(mut self, limit: usize) -> Self {
    assert!(limit > 0);
    self.record_limit = limit.min(self.limit);
    self.initial = self.initial.min(self.record_limit);
    self
  }

  /// Capacity predicted admission leaves free for running executions that
  /// outgrow their charges.
  #[must_use]
  pub fn with_buffer(mut self, buffer: usize) -> Self {
    self.buffer = buffer;
    self
  }

  pub fn limit(&self) -> usize {
    self.limit
  }

  pub fn record_limit(&self) -> usize {
    self.record_limit
  }

  pub fn buffer(&self) -> usize {
    self.buffer
  }

  pub fn stats(&self) -> PoolStats {
    self.stats
  }

  /// Executions admitted and not yet finished.
  pub fn executing(&self) -> usize {
    self.entries.values().filter(|entry| entry.executing).count()
  }

  /// Whether predicted admission is stopped: while running executions
  /// exceed their charges by more than the buffer, and from the moment they
  /// do, or one waits to, until an execution finishes.
  pub fn frozen(&self) -> bool {
    self.frozen || self.overshoot() > self.buffer
  }

  /// Bytes by which running executions exceed their charges.
  pub fn overshoot(&self) -> usize {
    self
      .entries
      .values()
      .filter(|entry| entry.executing)
      .map(|entry| entry.grant.saturating_sub(entry.charge))
      .sum()
  }

  /// Bytes promised: each running execution's charge or grant, whichever
  /// is larger, and each executed record's grant.
  fn committed(&self) -> usize {
    self
      .entries
      .values()
      .map(|entry| {
        if entry.executing {
          entry.grant.max(entry.charge)
        } else {
          entry.grant
        }
      })
      .sum()
  }

  /// Bytes running executions other than `id` were admitted for and have
  /// not been granted yet.
  fn promised(&self, id: u64) -> usize {
    self
      .entries
      .iter()
      .filter(|&(&other, entry)| other != id && entry.executing)
      .map(|(_, entry)| entry.charge.saturating_sub(entry.grant))
      .sum()
  }

  fn insert(&mut self, grant: usize, charge: usize) -> u64 {
    let id = self.next_id;
    self.next_id += 1;
    self.entries.insert(
      id,
      Entry {
        grant,
        charge,
        executing: true,
        waiting: false,
        needed: 0,
        cancelled: false,
      },
    );
    self.stats.reserved += grant;
    self.stats.peak_reserved =
      self.stats.peak_reserved.max(self.stats.reserved);
    id
  }

  /// Fixed admission: the initial grant whenever it is free and no
  /// execution holds growth priority. Returns the entry and its grant.
  pub fn admit_initial(&mut self) -> Option<(u64, usize)> {
    if self.preferred.is_some()
      || self.limit - self.stats.reserved < self.initial
    {
      return None;
    }
    Some((self.insert(self.initial, self.initial), self.initial))
  }

  /// Predicted admission of an execution charged `charge` bytes (clamped to
  /// the record ceiling). With `floor`, it is admitted as fixed admission
  /// would admit it, granted up to the initial grant. Otherwise, unless
  /// admission is frozen, it needs the committed bytes, this charge and the
  /// buffer to fit the limit; with nothing executing the buffer has nobody
  /// to serve, so a record larger than the pool still runs alone. Up to the
  /// charge is granted from what is free; the rest is grown into. Returns
  /// the entry and its grant.
  pub fn admit(&mut self, charge: usize, floor: bool) -> Option<(u64, usize)> {
    let charge = charge.min(self.record_limit);
    if floor
      && self.preferred.is_none()
      && self.limit - self.stats.reserved >= self.initial
    {
      let grant = charge.min(self.initial);
      return Some((self.insert(grant, charge), grant));
    }
    if self.frozen() {
      return None;
    }
    if self.executing() > 0 {
      let needed = self
        .committed()
        .checked_add(charge)
        .and_then(|n| n.checked_add(self.buffer))?;
      if needed > self.limit {
        return None;
      }
    }
    let grant = charge.min(self.limit - self.stats.reserved);
    Some((self.insert(grant, charge), grant))
  }

  fn select_waiter(&mut self) {
    if self.preferred.is_none() {
      self.preferred = self.waiters.first().copied();
    }
  }

  fn remove_waiter(&mut self, id: u64) {
    self.waiters.remove(&id);
    if self.preferred == Some(id) {
      self.preferred = None;
    }
    self.select_waiter();
  }

  fn freeze(&mut self) {
    if !self.frozen {
      self.frozen = true;
      self.stats.freezes += 1;
    }
  }

  /// When every execution waits, no record drains, and the selected waiter
  /// cannot grow, cancels the youngest other execution.
  fn cancel_blocked_peer(&mut self) -> Option<u64> {
    let preferred = self.preferred?;
    let entry = &self.entries[&preferred];
    let available = self.limit - self.stats.reserved;
    let usable = if (entry.grant + entry.needed).saturating_sub(entry.charge)
      > self.buffer
    {
      available.saturating_sub(self.promised(preferred))
    } else {
      available
    };
    if entry.needed <= usable {
      return None;
    }
    // A retained record can drain through a prover. A cancelled execution
    // must drop its storage before another victim can be selected.
    if self
      .entries
      .values()
      .any(|entry| !entry.executing || !entry.waiting || entry.cancelled)
    {
      return None;
    }
    let victim = self
      .entries
      .iter()
      .rev()
      .find(|(id, _)| Some(**id) != self.preferred)
      .map(|(&id, _)| id)?;
    self.entries.get_mut(&victim).unwrap().cancelled = true;
    self.waiters.remove(&victim);
    self.stats.retries += 1;
    Some(victim)
  }

  /// Entry `id`, holding `credit` unused granted bytes, needs `bytes` more.
  /// `first` counts the request's first wait in the statistics.
  pub fn grow(
    &mut self,
    id: u64,
    credit: usize,
    bytes: usize,
    first: bool,
  ) -> Growth {
    let entry = &self.entries[&id];
    if entry.cancelled {
      return Growth::Cancelled;
    }
    if credit >= bytes {
      return Growth::Granted(0);
    }
    let required = (entry.grant - credit).saturating_add(bytes);
    if required > self.record_limit {
      return Growth::Exceeded { bytes: required, cap: self.record_limit };
    }
    let missing = bytes - credit;
    let available = self.limit - self.stats.reserved;
    let over = entry.grant.saturating_sub(entry.charge);
    let wanted = (entry.grant + missing).saturating_sub(entry.charge);
    // Growth up to one buffer past the charge is close to the execution's
    // prediction, and the execution likely near its end: the priority
    // holder does not hold it back. Growth further past the charge contends:
    // it waits for the priority holder to finish, and never takes what other
    // running executions were admitted for and have not yet grown into.
    let contends = wanted > self.buffer;
    let usable = if contends {
      available.saturating_sub(self.promised(id))
    } else {
      available
    };
    if (!contends || self.preferred.is_none_or(|preferred| preferred == id))
      && usable >= missing
    {
      // Growth within the charge stops at it, so that rounding up to a
      // chunk is not counted as overshoot.
      let ceiling = if wanted == 0 {
        entry.charge - entry.grant
      } else {
        self.record_limit - entry.grant
      };
      let extra = missing.max(self.chunk).min(usable).min(ceiling);
      let entry = self.entries.get_mut(&id).unwrap();
      entry.grant += extra;
      entry.waiting = false;
      self.stats.reserved += extra;
      self.stats.peak_reserved =
        self.stats.peak_reserved.max(self.stats.reserved);
      if self.overshoot() > self.buffer {
        self.freeze();
      }
      return Growth::Granted(extra);
    }
    if first {
      self.stats.waits += 1;
    }
    let entry = self.entries.get_mut(&id).unwrap();
    entry.waiting = true;
    entry.needed = missing;
    if self.overshoot() - over + wanted > self.buffer {
      self.freeze();
    }
    self.waiters.insert(id);
    self.select_waiter();
    Growth::Wait { cancel: self.cancel_blocked_peer() }
  }

  /// The entry's counted bytes, given its unused credit.
  pub fn bytes(&self, id: u64, credit: usize) -> usize {
    self.entries[&id].grant - credit
  }

  /// Return `bytes` of freed storage, keeping the rest of the record.
  pub fn release(&mut self, id: u64, credit: usize, bytes: usize) {
    let entry = self.entries.get_mut(&id).unwrap();
    assert!(
      bytes <= entry.grant - credit,
      "released more storage than reserved"
    );
    entry.grant -= bytes;
    self.stats.reserved -= bytes;
  }

  /// The execution is done: return its `unused` credit and keep its record
  /// for proving. Unfreezes admission.
  pub fn finish_execution(&mut self, id: u64, unused: usize) {
    let entry = self.entries.get_mut(&id).unwrap();
    entry.grant -= unused;
    let was_executing = std::mem::replace(&mut entry.executing, false);
    entry.waiting = false;
    self.stats.reserved -= unused;
    if was_executing {
      self.frozen = false;
    }
    self.remove_waiter(id);
  }

  /// Drop the entry and its whole grant. An execution dropped before it
  /// finished unfreezes admission like a finished one.
  pub fn remove(&mut self, id: u64) {
    let entry = self.entries.remove(&id).unwrap();
    self.stats.reserved -= entry.grant;
    if entry.executing {
      self.frozen = false;
    }
    self.remove_waiter(id);
  }
}

#[derive(Debug, Default)]
struct Credit {
  available: AtomicUsize,
  cancelled: AtomicBool,
}

#[derive(Debug)]
struct State {
  ledger: Ledger,
  credits: BTreeMap<u64, Arc<Credit>>,
  frozen_since: Option<Instant>,
}

impl State {
  /// Accumulates the time predicted admission spends frozen.
  fn track_freeze(&mut self) {
    let frozen = self.ledger.frozen();
    match (frozen, self.frozen_since) {
      (true, None) => self.frozen_since = Some(Instant::now()),
      (false, Some(since)) => {
        self.ledger.stats.frozen_time += since.elapsed();
        self.frozen_since = None;
      },
      _ => {},
    }
  }

  fn stats(&self) -> PoolStats {
    let mut stats = self.ledger.stats;
    if let Some(since) = self.frozen_since {
      stats.frozen_time += since.elapsed();
    }
    stats
  }
}

#[derive(Debug)]
struct PoolInner {
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
    Self::from_ledger(Ledger::new(limit, initial))
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

  fn from_ledger(ledger: Ledger) -> Self {
    Self(Arc::new(PoolInner {
      prover: None,
      shutdown: AtomicBool::new(false),
      state: Mutex::new(State {
        ledger,
        credits: BTreeMap::new(),
        frozen_since: None,
      }),
      changed: Condvar::new(),
    }))
  }

  fn configure(mut self, f: impl FnOnce(Ledger) -> Ledger) -> Self {
    let pool = Arc::get_mut(&mut self.0)
      .expect("the pool must be configured before it is shared");
    let state = pool.state.get_mut().unwrap();
    let ledger = std::mem::replace(&mut state.ledger, Ledger::new(1, 1));
    state.ledger = f(ledger);
    self
  }

  /// Bound each record independently of aggregate capacity. Clamping
  /// grants also enforces the bound on the insertion fast path.
  #[must_use]
  pub fn with_record_limit(self, limit: usize) -> Self {
    self.configure(|ledger| ledger.with_record_limit(limit))
  }

  /// The overshoot buffer of predicted admission ([`Self::admit`]).
  #[must_use]
  pub fn with_buffer(self, buffer: usize) -> Self {
    self.configure(|ledger| ledger.with_buffer(buffer))
  }

  #[cfg(test)]
  fn with_chunk(limit: usize, initial: usize, chunk: usize) -> Self {
    Self::from_ledger(Ledger::with_chunk(limit, initial, chunk))
  }

  pub fn limit(&self) -> usize {
    self.0.state.lock().unwrap().ledger.limit
  }

  pub fn record_limit(&self) -> usize {
    self.0.state.lock().unwrap().ledger.record_limit
  }

  fn reservation(
    &self,
    state: &mut State,
    id: u64,
    grant: usize,
  ) -> RecordReservation {
    let credit = Arc::new(Credit::default());
    credit.available.store(grant, Ordering::Relaxed);
    state.credits.insert(id, Arc::clone(&credit));
    RecordReservation(Arc::new(ReservationInner {
      pool: self.clone(),
      id,
      credit,
    }))
  }

  /// Fixed admission ([`Ledger::admit_initial`]). Admission never blocks
  /// the dependency scheduler. Growth takes precedence until the selected
  /// execution finishes.
  pub fn try_admit(&self) -> Result<Option<RecordReservation>, BudgetError> {
    let mut state = self.0.state.lock().unwrap();
    if self.0.shutdown.load(Ordering::Relaxed) {
      return Err(BudgetError::Shutdown);
    }
    let Some((id, grant)) = state.ledger.admit_initial() else {
      return Ok(None);
    };
    Ok(Some(self.reservation(&mut state, id, grant)))
  }

  /// Predicted admission ([`Ledger::admit`]) of an execution whose record
  /// is expected to need `charge` bytes. Never blocks.
  pub fn admit(
    &self,
    charge: usize,
    floor: bool,
  ) -> Result<Option<RecordReservation>, BudgetError> {
    let mut state = self.0.state.lock().unwrap();
    if self.0.shutdown.load(Ordering::Relaxed) {
      return Err(BudgetError::Shutdown);
    }
    let Some((id, grant)) = state.ledger.admit(charge, floor) else {
      state.track_freeze();
      return Ok(None);
    };
    let reservation = self.reservation(&mut state, id, grant);
    state.track_freeze();
    Ok(Some(reservation))
  }

  pub fn stats(&self) -> PoolStats {
    self.0.state.lock().unwrap().stats()
  }

  pub fn usage(&self) -> PoolUsage {
    let state = self.0.state.lock().unwrap();
    let granted = state.ledger.stats.reserved;
    let unused: usize = state
      .credits
      .values()
      .map(|credit| credit.available.load(Ordering::Relaxed))
      .sum();
    PoolUsage {
      granted,
      used: granted.saturating_sub(unused),
      records: state.ledger.entries.len(),
      executing: state.ledger.executing(),
    }
  }

  pub fn shutdown(&self) {
    let _state = self.0.state.lock().unwrap();
    self.0.shutdown.store(true, Ordering::Relaxed);
    self.0.changed.notify_all();
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
      let credit = self.0.credit.available.load(Ordering::Relaxed);
      let growth = state.ledger.grow(id, credit, bytes, began.is_none());
      state.track_freeze();
      match growth {
        Growth::Granted(extra) => {
          self.0.credit.available.fetch_add(extra, Ordering::Relaxed);
          break Ok(());
        },
        Growth::Exceeded { bytes, cap } => {
          break Err(BudgetError::Exceeded { bytes, cap });
        },
        Growth::Cancelled => break Err(BudgetError::Cancelled),
        Growth::Wait { cancel } => {
          began.get_or_insert_with(Instant::now);
          if let Some(victim) = cancel {
            state.credits[&victim].cancelled.store(true, Ordering::Relaxed);
            pool.changed.notify_all();
            continue;
          }
          state = pool.changed.wait(state).unwrap();
        },
      }
    };
    if let Some(began) = began {
      state.ledger.stats.wait_time += began.elapsed();
    }
    result
  }

  pub fn bytes(&self) -> usize {
    let state = self.0.pool.0.state.lock().unwrap();
    state
      .ledger
      .bytes(self.0.id, self.0.credit.available.load(Ordering::Relaxed))
  }

  /// Return the charge for storage that has been freed, without releasing
  /// the reservation owning the remaining record. Unused credit is separate.
  pub fn release(&self, bytes: usize) {
    if bytes == 0 {
      return;
    }
    let pool = &self.0.pool.0;
    let mut state = pool.state.lock().unwrap();
    let credit = self.0.credit.available.load(Ordering::Relaxed);
    state.ledger.release(self.0.id, credit, bytes);
    pool.changed.notify_all();
  }

  /// Planning and proving only read the record. Return speculative
  /// capacity now, retaining its used charge through both proving rounds.
  pub fn finish_execution(&self) {
    let pool = &self.0.pool.0;
    let mut state = pool.state.lock().unwrap();
    let unused = self.0.credit.available.swap(0, Ordering::Relaxed);
    state.ledger.finish_execution(self.0.id, unused);
    state.track_freeze();
    pool.changed.notify_all();
  }
}

impl Drop for ReservationInner {
  fn drop(&mut self) {
    let pool = &self.pool.0;
    let mut state = pool.state.lock().unwrap();
    state.ledger.remove(self.id);
    state.credits.remove(&self.id);
    state.track_freeze();
    pool.changed.notify_all();
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::{sync::mpsc, thread};

  #[test]
  fn partial_release_preserves_credit_and_unblocks_other_records() {
    let pool = RecordPool::with_chunk(100, 40, 8);
    let record = pool.try_admit().unwrap().unwrap();
    record.reserve(30).unwrap();
    record.release(20);
    assert_eq!(record.bytes(), 10);
    assert_eq!(pool.stats().reserved, 20);
    record.reserve(10).unwrap();
    record.finish_execution();
    assert_eq!(record.bytes(), 20);
    let other = pool.try_admit().unwrap().unwrap();
    other.reserve(40).unwrap();
    assert_eq!(pool.stats().reserved, 60);
    assert_eq!(
      pool.usage(),
      PoolUsage { granted: 60, used: 60, records: 2, executing: 1 }
    );
    record.release(20);
    drop(record);
    assert_eq!(pool.stats().reserved, 40);
    drop(other);
    assert_eq!(pool.stats().reserved, 0);
    assert_eq!(pool.stats().peak_reserved, 60);
  }

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
  fn predicted_admission_charges_records_and_keeps_the_buffer() {
    let mut ledger = Ledger::with_chunk(100, 10, 1).with_buffer(20);
    let (a, grant) = ledger.admit(30, false).unwrap();
    assert_eq!(grant, 30);
    let (b, _) = ledger.admit(30, false).unwrap();
    // 30 + 30 committed, 30 more and the 20-byte buffer exceed 100.
    assert_eq!(ledger.admit(30, false), None);
    let (c, _) = ledger.admit(20, false).unwrap();
    assert_eq!(ledger.stats().reserved, 80);
    // Overshoot within the buffer grows without a wait or a freeze.
    assert_eq!(ledger.grow(a, 0, 15, true), Growth::Granted(15));
    assert!(!ledger.frozen());
    assert_eq!(ledger.admit(0, false), None, "the buffer is in use");
    assert_eq!(ledger.grow(b, 0, 5, true), Growth::Granted(5));
    assert!(!ledger.frozen(), "20 bytes over the charges is the buffer");
    // Past the buffer the pool is exhausted and admission freezes. `b`, the
    // first to wait, takes growth priority; `a`, asking for more than the
    // buffer past its charge, waits behind it.
    assert_eq!(ledger.grow(b, 0, 10, true), Growth::Wait { cancel: None });
    assert!(ledger.frozen());
    assert_eq!(ledger.grow(a, 0, 10, true), Growth::Wait { cancel: None });
    // Every execution waits and nothing drains: the youngest is cancelled.
    assert_eq!(ledger.grow(c, 0, 1, true), Growth::Wait { cancel: Some(c) });
    assert_eq!(ledger.grow(c, 0, 1, false), Growth::Cancelled);
    ledger.remove(c);
    assert_eq!(ledger.grow(a, 0, 10, false), Growth::Wait { cancel: None });
    assert_eq!(ledger.grow(b, 0, 10, false), Growth::Granted(10));
    ledger.finish_execution(b, 0);
    assert_eq!(ledger.grow(a, 0, 10, false), Growth::Granted(10));
    let stats = ledger.stats();
    assert_eq!((stats.retries, stats.waits), (1, 3));
    assert_eq!(stats.reserved, 100);
  }

  #[test]
  fn outgrowing_past_the_buffer_waits_for_the_oldest() {
    let mut ledger = Ledger::with_chunk(100, 10, 1).with_buffer(10);
    let (a, _) = ledger.admit(20, false).unwrap();
    let (b, _) = ledger.admit(20, false).unwrap();
    let (c, _) = ledger.admit(20, false).unwrap();
    assert_eq!(ledger.grow(a, 0, 45, true), Growth::Wait { cancel: None });
    assert!(ledger.frozen());
    assert_eq!(ledger.grow(b, 0, 25, true), Growth::Wait { cancel: None });
    // Within the buffer over its own charge, `c` is not held back by `a`.
    assert_eq!(ledger.grow(c, 0, 5, true), Growth::Granted(5));
    ledger.finish_execution(c, 0);
    ledger.remove(c);
    assert_eq!(ledger.grow(b, 0, 25, false), Growth::Wait { cancel: None });
    assert_eq!(ledger.grow(a, 0, 45, false), Growth::Granted(45));
    ledger.finish_execution(a, 0);
    assert_eq!(ledger.grow(b, 0, 25, false), Growth::Wait { cancel: None });
    ledger.remove(a);
    assert_eq!(ledger.grow(b, 0, 25, false), Growth::Granted(25));
    assert_eq!(ledger.stats().retries, 0);
  }

  #[test]
  fn freeze_lasts_until_an_execution_finishes() {
    let mut ledger = Ledger::with_chunk(200, 10, 1).with_buffer(20);
    let (a, _) = ledger.admit(30, false).unwrap();
    let (b, _) = ledger.admit(30, false).unwrap();
    let (held, _) = ledger.admit(30, false).unwrap();
    ledger.finish_execution(held, 0);
    assert_eq!(ledger.grow(a, 0, 25, true), Growth::Granted(25));
    assert!(ledger.frozen());
    assert_eq!(ledger.stats().freezes, 1);
    ledger.release(a, 0, 10);
    assert_eq!(ledger.overshoot(), 15);
    assert!(ledger.frozen(), "the freeze is latched");
    // A proven record draining does not reopen admission.
    ledger.remove(held);
    assert_eq!(ledger.admit(10, false), None);
    // An execution finishing does.
    ledger.finish_execution(b, 0);
    assert!(!ledger.frozen());
    assert!(ledger.admit(10, false).is_some());
  }

  #[test]
  fn a_record_larger_than_the_free_pool_runs_alone() {
    let mut ledger = Ledger::with_chunk(100, 10, 1).with_buffer(40);
    let (held, _) = ledger.admit(30, false).unwrap();
    ledger.finish_execution(held, 0);
    // Nothing executes: the whole free pool is granted, without the buffer.
    let (big, grant) = ledger.admit(90, false).unwrap();
    assert_eq!(grant, 70);
    assert_eq!(ledger.admit(0, false), None);
    assert_eq!(ledger.grow(big, 0, 20, true), Growth::Wait { cancel: None });
    ledger.remove(held);
    assert_eq!(ledger.grow(big, 0, 20, false), Growth::Granted(20));
    assert_eq!(ledger.bytes(big, 0), 90);
  }

  #[test]
  fn the_fixed_floor_admits_as_fixed_admission_did() {
    let mut ledger = Ledger::with_chunk(100, 10, 1).with_buffer(40);
    let (a, _) = ledger.admit(50, false).unwrap();
    assert_eq!(ledger.admit(30, false), None);
    // Below the floor, one initial grant free is enough, frozen or not.
    let (b, grant) = ledger.admit(30, true).unwrap();
    assert_eq!(grant, 10);
    assert_eq!(
      ledger.grow(a, 0, 50 + 40 + 1, true),
      Growth::Exceeded { bytes: 50 + 40 + 1 + 50, cap: 100 }
    );
    assert_eq!(ledger.grow(a, 0, 41, true), Growth::Wait { cancel: None });
    assert!(ledger.frozen());
    assert_eq!(ledger.admit(0, false), None);
    assert!(ledger.admit(0, true).is_none(), "the priority is held");
    ledger.remove(b);
    assert_eq!(ledger.grow(a, 0, 41, false), Growth::Granted(41));
  }

  #[test]
  fn pool_admits_by_charge_and_reports_freezes() {
    let pool = RecordPool::with_chunk(100, 10, 8).with_buffer(20);
    let first = pool.admit(40, false).unwrap().unwrap();
    let second = pool.admit(30, false).unwrap().unwrap();
    assert!(pool.admit(20, false).unwrap().is_none());
    first.reserve(40).unwrap();
    first.reserve(20).unwrap();
    assert_eq!(pool.stats().freezes, 0);
    first.reserve(8).unwrap();
    assert_eq!(pool.stats().freezes, 1);
    assert!(pool.admit(0, false).unwrap().is_none());
    first.finish_execution();
    assert_eq!(first.bytes(), 68);
    // The executed record counts until it is proven: 68 + 30 + 10 + 20.
    assert!(pool.admit(10, false).unwrap().is_none());
    // Within the fixed count, admission needs only one initial grant free.
    assert!(pool.admit(10, true).unwrap().is_none(), "2 bytes free");
    drop(first);
    let third = pool.admit(10, false).unwrap().unwrap();
    assert_eq!(third.bytes(), 0);
    drop((second, third));
    assert_eq!(pool.stats().reserved, 0);
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
