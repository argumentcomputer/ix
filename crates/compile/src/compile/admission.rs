//! Non-preemptive memory-aware admission for the main dependency scheduler.
//!
//! A main-compiler block publishes shared names and auxiliary metadata before
//! returning, unlike a pure inductive validation. It cannot safely be retried
//! after arbitrary cancellation. Permits are therefore acquired BEFORE
//! dequeuing work and released AFTER block-local scratch and publication.
//! Backoff stops admissions; already-active blocks keep running, never park
//! holding their scratch. This is not an allocator-enforced memory limit.

use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use super::memory::{
  GIB, Memory, MemoryReader, Pressure, budget_from_env, pressure,
  resource_error,
};
use ixon::CompileError;

#[derive(Clone, Copy)]
struct Options {
  max_workers: usize,
  process_budget: Option<u64>,
  tick: Duration,
  ramp_interval: Duration,
  recovery: Duration,
  idle_timeout: Duration,
  lookahead: Duration,
  verbose: bool,
}

impl Options {
  fn from_env(max_workers: usize) -> Result<Self, CompileError> {
    Ok(Self {
      max_workers: max_workers.max(1),
      process_budget: budget_from_env("IX_COMPILE_MEMORY_GIB")?,
      tick: Duration::from_millis(250),
      ramp_interval: Duration::from_secs(1),
      recovery: Duration::from_secs(5),
      idle_timeout: Duration::from_secs(30),
      lookahead: Duration::from_secs(10),
      verbose: *super::env::IX_VERBOSE,
    })
  }
}

struct Policy {
  limit: usize,
  open: bool,
  pressure: Pressure,
  previous: Memory,
  sampled: Instant,
  ramped: Instant,
  pressured: Option<Instant>,
  growth_per_second: u64,
  projected_growth: u64,
  completed: u64,
}

impl Policy {
  fn new(memory: Memory, now: Instant, options: Options) -> Self {
    let pressure =
      pressure(memory, memory, options.tick, options.process_budget);
    Self {
      limit: options.max_workers.min(2),
      open: pressure == Pressure::Healthy,
      pressure,
      previous: memory,
      sampled: now,
      ramped: now,
      pressured: (pressure != Pressure::Healthy).then_some(now),
      growth_per_second: 0,
      projected_growth: 0,
      completed: 0,
    }
  }

  fn sample(
    &mut self,
    memory: Memory,
    now: Instant,
    active: usize,
    completed: u64,
    options: Options,
  ) {
    let elapsed = now.duration_since(self.sampled);
    let delta = memory
      .process
      .saturating_sub(self.previous.process)
      .max(self.previous.available.saturating_sub(memory.available));
    // Fast rise, gradual decay: reserve space for another ten seconds of
    // recent growth, including external pressure, before starting more work.
    // This is process-level prediction, NOT an attributed per-block footprint.
    let growth = (u128::from(delta) * 1_000_000 / elapsed.as_micros().max(1))
      .min(u128::from(u64::MAX)) as u64;
    self.growth_per_second =
      growth.max(self.growth_per_second.saturating_mul(3) / 4);
    self.projected_growth =
      self.growth_per_second.saturating_mul(options.lookahead.as_secs());
    let reserve = memory.reserve(options.process_budget);
    let headroom = memory.headroom(options.process_budget);
    self.pressure =
      pressure(memory, self.previous, elapsed, options.process_budget);
    let forecast_tight =
      headroom < reserve.saturating_add(self.projected_growth);
    let reclaiming = super::memory::reclaiming(memory, self.previous, elapsed);
    let blocked =
      self.pressure == Pressure::Critical || reclaiming || forecast_tight;
    let wide_headroom = self.pressure == Pressure::Healthy
      && headroom
        >= reserve.saturating_mul(3).saturating_add(self.projected_growth);
    if blocked {
      self.limit = self.limit.min((active / 2).max(1));
      self.pressured = Some(now);
    } else if !wide_headroom {
      // Retained, successfully compiled data cannot be reclaimed by reducing
      // workers. With stable memory and a reserve, allow one job at a time
      // instead of waiting forever for the accumulator to shrink.
      self.limit = 1;
    }
    let recovered =
      self.pressured.is_none_or(|t| now.duration_since(t) >= options.recovery);
    self.open = !blocked && recovered;
    // A long-running block with no completions is not evidence that it is
    // safe to ramp up. Require actual completed work before raising the cap.
    if self.open
      && wide_headroom
      && completed > self.completed
      && now.duration_since(self.ramped) >= options.ramp_interval
    {
      self.limit = (self.limit + 1).min(options.max_workers);
      self.ramped = now;
    }
    self.previous = memory;
    self.sampled = now;
    self.completed = completed;
  }
}

struct State {
  policy: Option<Policy>,
  active: usize,
  completed: u64,
  stopped: bool,
  error: Option<CompileError>,
  idle_since: Option<Instant>,
}
struct Shared {
  options: Options,
  state: Mutex<State>,
  changed: Condvar,
  shutdown: Condvar,
}

pub(super) struct Admission {
  shared: Arc<Shared>,
  monitor: Option<JoinHandle<()>>,
}

/// Borrowed permit: no per-block thread or Arc allocation.
pub(super) struct Permit<'a> {
  shared: &'a Shared,
  completed: bool,
}
impl Permit<'_> {
  pub(super) fn complete(mut self) {
    self.completed = true;
  }
}
impl Drop for Permit<'_> {
  fn drop(&mut self) {
    let mut state = self.shared.state.lock().unwrap();
    state.active -= 1;
    state.completed += u64::from(self.completed);
    if state.active == 0 {
      state.idle_since = Some(Instant::now());
    }
    self.shared.changed.notify_one();
  }
}

impl Admission {
  pub(super) fn new(max_workers: usize) -> Result<Self, CompileError> {
    let options = Options::from_env(max_workers)?;
    let disabled = std::env::var("IX_COMPILE_ADAPTIVE").as_deref() == Ok("0");
    if disabled && options.process_budget.is_some() {
      return Err(resource_error(
        "IX_COMPILE_MEMORY_GIB cannot be combined with IX_COMPILE_ADAPTIVE=0",
      ));
    }
    let mut reader = MemoryReader::new();
    let initial = if disabled { None } else { reader.read() };
    if initial.is_none() && options.process_budget.is_some() {
      return Err(resource_error(
        "IX_COMPILE_MEMORY_GIB requires Linux memory telemetry",
      ));
    }
    Self::with_reader(options, initial, move || reader.read())
  }

  fn with_reader(
    options: Options,
    initial: Option<Memory>,
    mut read: impl FnMut() -> Option<Memory> + Send + 'static,
  ) -> Result<Self, CompileError> {
    let now = Instant::now();
    let shared = Arc::new(Shared {
      options,
      state: Mutex::new(State {
        policy: initial.map(|memory| Policy::new(memory, now, options)),
        active: 0,
        completed: 0,
        stopped: false,
        error: None,
        idle_since: Some(now),
      }),
      changed: Condvar::new(),
      shutdown: Condvar::new(),
    });
    if options.verbose {
      eprintln!(
        "[compile_memory] {}: initial={} max={} budget_gib={:?}; active blocks finish before slots are reused",
        if initial.is_some() {
          "adaptive admission"
        } else {
          "fixed admission (disabled or telemetry unavailable)"
        },
        if initial.is_some() {
          options.max_workers.min(2)
        } else {
          options.max_workers
        },
        options.max_workers,
        options.process_budget.map(|v| v as f64 / GIB as f64)
      );
    }
    let monitor = if initial.is_some() {
      let shared = Arc::clone(&shared);
      Some(thread::Builder::new().name("ix-compile-memory".into()).spawn(move || {
        let mut logged = now;
        loop {
          let mut state = shared.state.lock().unwrap();
          let deadline = state.policy.as_ref().unwrap().sampled + options.tick;
          // Permit releases wake waiters often; they must not cause /proc
          // sampling on every block (millions of blocks in a large env).
          while !state.stopped && Instant::now() < deadline {
            let wait = deadline.saturating_duration_since(Instant::now());
            state = shared.shutdown.wait_timeout(state, wait).unwrap().0;
          }
          if state.stopped { return; }
          drop(state);
          let sample = read();
          let mut state = shared.state.lock().unwrap();
          if state.stopped { return; }
          let Some(memory) = sample else {
            state.error = Some(resource_error("memory telemetry became unavailable during main compilation"));
            state.stopped = true;
            shared.changed.notify_all();
            return;
          };
          let now = Instant::now();
          let active = state.active;
          let completed = state.completed;
          let policy = state.policy.as_mut().unwrap();
          let before = (policy.limit, policy.open, policy.pressure);
          policy.sample(memory, now, active, completed, options);
          if options.verbose && (before != (policy.limit, policy.open, policy.pressure)
            || now.duration_since(logged) >= Duration::from_secs(5)) {
            eprintln!("[compile_memory] {:?}: limit={}/{} active={active} admitting={} completed={completed} available={:.1} GiB resident+swap={:.1} GiB growth_forecast={:.1} GiB",
              policy.pressure, policy.limit, options.max_workers, policy.open,
              memory.available as f64 / GIB as f64, memory.process as f64 / GIB as f64,
              policy.projected_growth as f64 / GIB as f64);
            logged = now;
          }
          shared.changed.notify_all();
        }
      }).map_err(|e| resource_error(format!("could not start memory admission monitor: {e}")))?)
    } else {
      None
    };
    Ok(Self { shared, monitor })
  }

  pub(super) fn acquire(&self) -> Result<Option<Permit<'_>>, CompileError> {
    let mut state = self.shared.state.lock().unwrap();
    loop {
      if let Some(error) = &state.error {
        return Err(error.clone());
      }
      if state.stopped {
        return Ok(None);
      }
      let (open, limit) = state
        .policy
        .as_ref()
        .map_or((true, self.shared.options.max_workers), |p| (p.open, p.limit));
      if open && state.active < limit {
        state.active += 1;
        state.idle_since = None;
        return Ok(Some(Permit { shared: &self.shared, completed: false }));
      }
      if state.active == 0 {
        let start = *state.idle_since.get_or_insert_with(Instant::now);
        if start.elapsed() >= self.shared.options.idle_timeout {
          let error = resource_error(format!(
            "not enough memory headroom to admit a compiler block; no active work for {:.0}s. Increase IX_COMPILE_MEMORY_GIB if set, or make more RAM available",
            self.shared.options.idle_timeout.as_secs_f64()
          ));
          state.error = Some(error.clone());
          state.stopped = true;
          self.shared.changed.notify_all();
          self.shared.shutdown.notify_all();
          return Err(error);
        }
      }
      state = self
        .shared
        .changed
        .wait_timeout(state, self.shared.options.tick)
        .unwrap()
        .0;
    }
  }

  pub(super) fn stop(&self) {
    self.shared.state.lock().unwrap().stopped = true;
    self.shared.changed.notify_all();
    self.shared.shutdown.notify_all();
  }

  pub(super) fn check(&self) -> Result<(), CompileError> {
    self.shared.state.lock().unwrap().error.clone().map_or(Ok(()), Err)
  }
}
impl Drop for Admission {
  fn drop(&mut self) {
    self.stop();
    if let Some(monitor) = self.monitor.take() {
      monitor.join().unwrap();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::memory::MIB;
  use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

  fn memory() -> Memory {
    Memory {
      capacity: 100 * GIB,
      available: 90 * GIB,
      process: 10 * GIB,
      swap_used: 0,
      stall_us: 0,
    }
  }
  fn options(max_workers: usize) -> Options {
    Options {
      max_workers,
      process_budget: None,
      tick: Duration::from_millis(2),
      ramp_interval: Duration::from_millis(5),
      recovery: Duration::from_millis(5),
      idle_timeout: Duration::from_millis(100),
      lookahead: Duration::from_secs(10),
      verbose: false,
    }
  }
  fn until(mut predicate: impl FnMut() -> bool) {
    let start = Instant::now();
    while !predicate() {
      assert!(
        start.elapsed() < Duration::from_secs(5),
        "test made no progress"
      );
      thread::sleep(Duration::from_millis(1));
    }
  }

  #[test]
  fn healthy_memory_requires_completions_to_ramp_and_respects_the_ceiling() {
    let opt = options(4);
    let now = Instant::now();
    let mut policy = Policy::new(memory(), now, opt);
    for second in 1..10 {
      policy.sample(memory(), now + Duration::from_secs(second), 2, 0, opt);
      assert_eq!(policy.limit, 2, "a long job should not trigger ramp-up");
    }
    for second in 10..20 {
      policy.sample(
        memory(),
        now + Duration::from_secs(second),
        2,
        second,
        opt,
      );
      assert!(policy.limit <= 4);
      assert!(policy.open);
    }
    assert_eq!(policy.limit, 4);
  }

  #[test]
  fn growth_forecast_stops_admissions_before_low_memory_threshold() {
    let opt = options(64);
    let now = Instant::now();
    let mut policy = Policy::new(memory(), now, opt);
    let rising = Memory { process: 16 * GIB, available: 84 * GIB, ..memory() };
    policy.sample(rising, now + Duration::from_millis(250), 2, 0, opt);
    assert_eq!(policy.pressure, Pressure::Healthy);
    assert_eq!(policy.projected_growth, 240 * GIB);
    assert!(
      !policy.open,
      "high current availability must not hide a growth burst"
    );
    assert_eq!(policy.limit, 1);
  }

  #[test]
  fn swap_pressure_reduces_limit_and_recovers_with_hysteresis() {
    let opt = options(8);
    let now = Instant::now();
    let mut policy = Policy::new(memory(), now, opt);
    policy.limit = 8;
    let swapped = Memory { swap_used: 9 * MIB, ..memory() };
    policy.sample(swapped, now + Duration::from_millis(2), 8, 0, opt);
    assert_eq!(policy.pressure, Pressure::Backoff);
    assert_eq!(policy.limit, 4);
    assert!(!policy.open);
    policy.sample(swapped, now + Duration::from_millis(4), 4, 1, opt);
    assert!(!policy.open, "one healthy tick is not enough to recover");
    policy.sample(swapped, now + Duration::from_millis(20), 2, 2, opt);
    assert!(policy.open);
    assert_eq!(policy.limit, 5);
  }

  #[test]
  fn process_budget_uses_resident_plus_swap_headroom() {
    let opt = Options { process_budget: Some(20 * GIB), ..options(8) };
    let now = Instant::now();
    let memory = Memory { process: 19 * GIB, ..memory() };
    let policy = Policy::new(memory, now, opt);
    assert!(!policy.open);
    assert_eq!(policy.pressure, Pressure::Critical);
  }

  #[test]
  fn stable_retained_data_allows_serial_forward_progress() {
    let opt = options(8);
    let now = Instant::now();
    let memory = Memory { process: 70 * GIB, available: 30 * GIB, ..memory() };
    let mut policy = Policy::new(memory, now, opt);
    policy.sample(memory, now + Duration::from_secs(1), 0, 0, opt);
    assert_eq!(policy.pressure, Pressure::Hold);
    assert!(policy.open);
    assert_eq!(policy.limit, 1);
  }

  #[test]
  fn pressure_drains_existing_work_before_reusing_its_slot() {
    let pressured = Arc::new(AtomicBool::new(false));
    let reader_pressure = Arc::clone(&pressured);
    let gate = Admission::with_reader(options(2), Some(memory()), move || {
      Some(if reader_pressure.load(Ordering::SeqCst) {
        Memory { available: 20 * GIB, ..memory() }
      } else {
        memory()
      })
    })
    .unwrap();
    let first = gate.acquire().unwrap().unwrap();
    let second = gate.acquire().unwrap().unwrap();
    pressured.store(true, Ordering::SeqCst);
    until(|| !gate.shared.state.lock().unwrap().policy.as_ref().unwrap().open);
    let started = AtomicBool::new(false);
    let published = AtomicBool::new(false);
    thread::scope(|scope| {
      let waiting = scope.spawn(|| {
        let permit = gate.acquire().unwrap().unwrap();
        started.store(true, Ordering::SeqCst);
        assert!(
          published.load(Ordering::SeqCst),
          "slot reused before prior block published"
        );
        permit.complete();
      });
      // Neither active task is cancelled or parked. A completed block's
      // slot remains unavailable while pressure persists.
      drop(first);
      assert_eq!(gate.shared.state.lock().unwrap().active, 1);
      assert!(!started.load(Ordering::SeqCst));
      pressured.store(false, Ordering::SeqCst);
      until(|| gate.shared.state.lock().unwrap().policy.as_ref().unwrap().open);
      assert!(
        !started.load(Ordering::SeqCst),
        "backoff must respect the reduced active cap"
      );
      published.store(true, Ordering::SeqCst);
      second.complete();
      waiting.join().unwrap();
    });
    let state = gate.shared.state.lock().unwrap();
    assert_eq!(state.active, 0);
    assert_eq!(state.completed, 2);
  }

  #[test]
  fn idle_permits_do_not_count_as_completed_blocks() {
    let gate = Admission::with_reader(options(2), None, || {
      panic!("fixed mode sampled memory")
    })
    .unwrap();
    drop(gate.acquire().unwrap().unwrap());
    assert_eq!(gate.shared.state.lock().unwrap().completed, 0);
    gate.acquire().unwrap().unwrap().complete();
    assert_eq!(gate.shared.state.lock().unwrap().completed, 1);
  }

  #[test]
  fn stop_wakes_waiting_workers_even_while_other_permits_are_live() {
    let gate = Admission::with_reader(options(1), None, || None).unwrap();
    let first = gate.acquire().unwrap().unwrap();
    thread::scope(|scope| {
      let waiting = scope.spawn(|| assert!(gate.acquire().unwrap().is_none()));
      gate.stop();
      waiting.join().unwrap();
    });
    drop(first);
    assert_eq!(gate.shared.state.lock().unwrap().active, 0);
  }

  #[test]
  fn no_headroom_returns_resource_error_without_starting_a_block() {
    let low = Memory { available: GIB, ..memory() };
    let gate =
      Admission::with_reader(options(4), Some(low), move || Some(low)).unwrap();
    assert!(matches!(gate.acquire(), Err(CompileError::ResourceLimit { .. })));
    assert_eq!(gate.shared.state.lock().unwrap().active, 0);
    assert!(matches!(gate.check(), Err(CompileError::ResourceLimit { .. })));
  }

  #[test]
  fn telemetry_failure_is_visible_even_if_no_worker_acquires_again() {
    let gate =
      Admission::with_reader(options(1), Some(memory()), || None).unwrap();
    let last = gate.acquire().unwrap().unwrap();
    until(|| gate.check().is_err());
    last.complete();
    assert!(matches!(gate.check(), Err(CompileError::ResourceLimit { .. })));
    assert!(matches!(gate.acquire(), Err(CompileError::ResourceLimit { .. })));
  }

  #[test]
  fn monitor_does_not_resample_for_each_block_and_shutdown_is_prompt() {
    let reads = Arc::new(AtomicUsize::new(0));
    let reader_count = Arc::clone(&reads);
    let opt = Options { tick: Duration::from_secs(10), ..options(2) };
    let gate = Admission::with_reader(opt, Some(memory()), move || {
      reader_count.fetch_add(1, Ordering::SeqCst);
      Some(memory())
    })
    .unwrap();
    for _ in 0..1000 {
      gate.acquire().unwrap().unwrap().complete();
    }
    assert_eq!(reads.load(Ordering::SeqCst), 0);
    let start = Instant::now();
    drop(gate);
    assert!(start.elapsed() < Duration::from_secs(1));
  }
}
