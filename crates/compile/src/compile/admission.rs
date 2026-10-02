//! Non-preemptive memory-aware admission for the main dependency scheduler.
//!
//! A main-compiler block publishes shared names and auxiliary metadata before
//! returning, unlike a pure inductive validation. It cannot safely be retried
//! after arbitrary cancellation. Permits are therefore acquired BEFORE
//! dequeuing work and released AFTER block-local scratch and publication.
//! Backoff stops admissions; already-active blocks keep running, never park
//! holding their scratch. This is not an allocator-enforced memory limit.
//!
//! The cap follows the headroom left after a ten-second growth forecast, in
//! units of the safety reserve (an eighth of the visible memory, or of the
//! budget): every worker from three reserves up, which is where a compile
//! starts on a machine with memory to spare; a linear share between two and
//! three; one block (serial progress) between one and two; and no admissions
//! below one reserve. Below the supported cap the gate ramps up by doubling
//! per sample after completed work. Reclaim (this process swapping, or its
//! cgroup stalling on memory) counts only below four reserves of headroom
//! and only once it lasts two samples: it halves the cap, but not below
//! `RECLAIM_FLOOR` while two reserves remain, and it closes admissions
//! below two reserves. With no block active, the gate fails after
//! `idle_timeout` when headroom is below two reserves; with more headroom
//! it waits `STUCK_TIMEOUTS` times as long before giving up.

use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use super::memory::{
  GIB, Memory, MemoryReader, Pressure, budget_from_env, reclaiming,
  resource_error,
};
use ixon::CompileError;

/// Consecutive samples of attributed reclaim needed before backing off for
/// it: a single 250 ms sample cannot tell sustained reclaim from a burst.
const RECLAIM_SAMPLES: u32 = 2;
/// While at least two reserves of headroom remain, reclaim halves the cap
/// but leaves this many workers: the headroom itself is still real.
const RECLAIM_FLOOR: usize = 4;
/// With two reserves of headroom or more, a closed gate is not short of
/// memory (only a growth forecast keeps it closed), so it gives up only
/// after this many idle timeouts instead of one.
const STUCK_TIMEOUTS: u32 = 10;

#[derive(Clone, Copy)]
struct Options {
  max_workers: usize,
  process_budget: Option<u64>,
  tick: Duration,
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
      recovery: Duration::from_secs(5),
      idle_timeout: Duration::from_secs(30),
      lookahead: Duration::from_secs(10),
      verbose: *super::env::IX_VERBOSE,
    })
  }
}

/// The active-block cap that `headroom` supports once `forecast` growth is
/// set aside: none below one reserve, one block below two (retained output
/// cannot be reclaimed by running fewer blocks, so serial progress beats
/// waiting for it to shrink), every worker from three reserves up, and a
/// linear share in between.
fn supported(
  headroom: u64,
  reserve: u64,
  forecast: u64,
  max_workers: usize,
) -> usize {
  let net = headroom.saturating_sub(forecast);
  let reserve = reserve.max(1);
  if net < reserve {
    0
  } else if net < reserve.saturating_mul(2) {
    1
  } else if net >= reserve.saturating_mul(3) {
    max_workers
  } else {
    // net - 2·reserve < reserve, so the share stays below max_workers - 1.
    let share = u128::from(net - reserve * 2)
      * (max_workers.saturating_sub(1) as u128)
      / u128::from(reserve);
    1 + share as usize
  }
}

struct Policy {
  limit: usize,
  open: bool,
  pressure: Pressure,
  previous: Memory,
  sampled: Instant,
  pressured: Option<Instant>,
  reclaim_samples: u32,
  growth_per_second: u64,
  projected_growth: u64,
  completed: u64,
}

impl Policy {
  fn new(memory: Memory, now: Instant, options: Options) -> Self {
    let budget = options.process_budget;
    let reserve = memory.reserve(budget);
    let headroom = memory.headroom(budget);
    let supported = supported(headroom, reserve, 0, options.max_workers);
    // Start at the supported cap: with wide headroom, every worker, without
    // a ramp to sit through. Below two reserves, first wait out a recovery
    // period, as after pressure.
    let low = headroom < reserve.saturating_mul(2);
    Self {
      limit: supported.max(1),
      open: !low,
      pressure: Self::classify(
        supported == 0,
        low,
        supported < options.max_workers,
      ),
      previous: memory,
      sampled: now,
      pressured: low.then_some(now),
      reclaim_samples: 0,
      growth_per_second: 0,
      projected_growth: 0,
      completed: 0,
    }
  }

  /// The state reported in verbose logs.
  fn classify(closed: bool, backoff: bool, held: bool) -> Pressure {
    if closed {
      Pressure::Critical
    } else if backoff {
      Pressure::Backoff
    } else if held {
      Pressure::Hold
    } else {
      Pressure::Healthy
    }
  }

  /// Headroom below two reserves: memory is genuinely short.
  fn starving(&self, options: &Options) -> bool {
    let budget = options.process_budget;
    self.previous.headroom(budget)
      < self.previous.reserve(budget).saturating_mul(2)
  }

  fn sample(
    &mut self,
    memory: Memory,
    now: Instant,
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
    let budget = options.process_budget;
    let reserve = memory.reserve(budget);
    let headroom = memory.headroom(budget);
    let supported =
      supported(headroom, reserve, self.projected_growth, options.max_workers);
    let low = headroom < reserve.saturating_mul(2);
    // Attributed and gated by headroom in `reclaiming`; debounced here.
    self.reclaim_samples = if reclaiming(memory, self.previous, elapsed, budget)
    {
      self.reclaim_samples.saturating_add(1)
    } else {
      0
    };
    let reclaim = self.reclaim_samples >= RECLAIM_SAMPLES;
    let closed = supported == 0 || (reclaim && low);
    if closed {
      // Halve the cap once per closure; it applies when admission resumes.
      // Not the active count: with admissions stopped, active blocks drain
      // within milliseconds, so halving that count on every closed sample
      // collapsed the cap to one after a single burst.
      if self.open {
        self.limit = (self.limit / 2).max(1);
      }
      self.pressured = Some(now);
    } else {
      if reclaim {
        self.limit = self.limit.min((self.limit / 2).max(RECLAIM_FLOOR));
        self.pressured = Some(now);
      }
      self.limit = self.limit.min(supported);
    }
    let recovered =
      self.pressured.is_none_or(|t| now.duration_since(t) >= options.recovery);
    // With two reserves of headroom, admit at the reduced cap at once; below
    // that, wait out the recovery period first.
    self.open = !closed && (!low || recovered);
    // A long-running block with no completions is not evidence that it is
    // safe to ramp up. Require actual completed work before raising the cap.
    if self.open && !reclaim && recovered && completed > self.completed {
      self.limit = self.limit.saturating_mul(2).min(supported);
    }
    self.pressure =
      Self::classify(closed, low || reclaim, supported < options.max_workers);
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
    let policy = initial.map(|memory| Policy::new(memory, now, options));
    if options.verbose {
      eprintln!(
        "[compile_memory] {}: initial={}{} max={} budget_gib={:?}{}; active blocks finish before slots are reused",
        if policy.is_some() {
          "adaptive admission"
        } else {
          "fixed admission (disabled or telemetry unavailable)"
        },
        policy.as_ref().map_or(options.max_workers, |p| p.limit),
        match &policy {
          Some(p) if !p.open => " (closed)",
          _ => "",
        },
        options.max_workers,
        options.process_budget.map(|v| v as f64 / GIB as f64),
        initial.map_or(String::new(), |m| format!(
          " headroom={:.1} GiB reserve={:.1} GiB",
          m.headroom(options.process_budget) as f64 / GIB as f64,
          m.reserve(options.process_budget) as f64 / GIB as f64
        )),
      );
    }
    let shared = Arc::new(Shared {
      options,
      state: Mutex::new(State {
        policy,
        active: 0,
        completed: 0,
        stopped: false,
        error: None,
        idle_since: Some(now),
      }),
      changed: Condvar::new(),
      shutdown: Condvar::new(),
    });
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
          policy.sample(memory, now, completed, options);
          if options.verbose && (before != (policy.limit, policy.open, policy.pressure)
            || now.duration_since(logged) >= Duration::from_secs(5)) {
            eprintln!("[compile_memory] {:?}: limit={}/{} active={active} admitting={} completed={completed} available={:.1} GiB reserve={:.1} GiB resident+swap={:.1} GiB (swap {:.2}) growth_forecast={:.1} GiB reclaim_samples={}",
              policy.pressure, policy.limit, options.max_workers, policy.open,
              memory.available as f64 / GIB as f64,
              memory.reserve(options.process_budget) as f64 / GIB as f64,
              memory.process as f64 / GIB as f64,
              memory.process_swap as f64 / GIB as f64,
              policy.projected_growth as f64 / GIB as f64,
              policy.reclaim_samples);
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
        let options = &self.shared.options;
        // Fail promptly only when memory is genuinely short. With ample
        // headroom the gate can only be held shut by a growth forecast that
        // has not settled; give it far longer before giving up.
        let starving =
          state.policy.as_ref().is_none_or(|p| p.starving(options));
        let timeout = if starving {
          options.idle_timeout
        } else {
          options.idle_timeout.saturating_mul(STUCK_TIMEOUTS)
        };
        if start.elapsed() >= timeout {
          let (headroom, reserve, forecast) =
            state.policy.as_ref().map_or((0, 0, 0), |p| {
              (
                p.previous.headroom(options.process_budget),
                p.previous.reserve(options.process_budget),
                p.projected_growth,
              )
            });
          let error = resource_error(format!(
            "not enough memory headroom to admit a compiler block; no active work for {:.0}s (headroom {:.1} GiB, reserve {:.1} GiB, growth forecast {:.1} GiB). Increase IX_COMPILE_MEMORY_GIB if set, or make more RAM available",
            timeout.as_secs_f64(),
            headroom as f64 / GIB as f64,
            reserve as f64 / GIB as f64,
            forecast as f64 / GIB as f64,
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

  /// 100 GiB visible, so the reserve is 12.5 GiB: two reserves are 25 GiB,
  /// three 37.5 GiB, and reclaim counts below four (50 GiB).
  fn memory() -> Memory {
    Memory {
      capacity: 100 * GIB,
      available: 90 * GIB,
      process: 10 * GIB,
      process_swap: 0,
      stall_us: 0,
    }
  }
  fn with_available(available: u64) -> Memory {
    Memory { available, process: 100 * GIB - available, ..memory() }
  }
  fn options(max_workers: usize) -> Options {
    Options {
      max_workers,
      process_budget: None,
      tick: Duration::from_millis(2),
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
  fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
  }

  #[test]
  fn supported_cap_follows_headroom_net_of_the_forecast() {
    let r = 8 * GIB;
    assert_eq!(supported(r - 1, r, 0, 24), 0);
    assert_eq!(supported(r, r, 0, 24), 1);
    assert_eq!(supported(2 * r - 1, r, 0, 24), 1);
    assert_eq!(supported(2 * r, r, 0, 24), 1);
    assert_eq!(supported(2 * r + r / 2, r, 0, 24), 12);
    assert_eq!(supported(3 * r - 1, r, 0, 24), 23);
    assert_eq!(supported(3 * r, r, 0, 24), 24);
    assert_eq!(supported(80 * GIB, r, 0, 24), 24);
    // The forecast is set aside first.
    assert_eq!(supported(80 * GIB, r, 80 * GIB - 2 * r, 24), 1);
    assert_eq!(supported(80 * GIB, r, 80 * GIB, 24), 0);
    assert_eq!(supported(80 * GIB, r, u64::MAX, 24), 0);
    assert_eq!(supported(2 * r + r / 2, r, 0, 1), 1);
    assert_eq!(supported(GIB, 0, 0, 4), 4);
  }

  #[test]
  fn wide_headroom_starts_at_the_ceiling_without_a_ramp() {
    for max in [1, 4, 24] {
      let opt = options(max);
      let now = Instant::now();
      let mut policy = Policy::new(memory(), now, opt);
      assert_eq!(policy.limit, max);
      assert!(policy.open);
      assert_eq!(policy.pressure, Pressure::Healthy);
      // Long-running first blocks (no completions) do not lower the cap.
      for tick in 1..10 {
        policy.sample(memory(), now + ms(tick), 0, opt);
        assert_eq!((policy.limit, policy.open), (max, true));
      }
    }
  }

  #[test]
  fn narrower_headroom_starts_lower() {
    let opt = options(24);
    let now = Instant::now();
    // Between two and three reserves: a linear share of the workers.
    let policy = Policy::new(with_available(30 * GIB), now, opt);
    assert_eq!((policy.limit, policy.open), (10, true));
    assert_eq!(policy.pressure, Pressure::Hold);
    // Between one and two: one block, after a recovery period.
    let policy = Policy::new(with_available(20 * GIB), now, opt);
    assert_eq!((policy.limit, policy.open), (1, false));
    assert_eq!(policy.pressure, Pressure::Backoff);
    // Below one reserve: closed.
    let policy = Policy::new(with_available(10 * GIB), now, opt);
    assert_eq!((policy.limit, policy.open), (1, false));
    assert_eq!(policy.pressure, Pressure::Critical);
  }

  #[test]
  fn ramp_doubles_per_sample_after_completions_up_to_the_supported_cap() {
    let opt = options(24);
    let now = Instant::now();
    let mut policy = Policy::new(with_available(20 * GIB), now, opt);
    assert_eq!(policy.limit, 1);
    // Memory is freed; the start's recovery period still holds the ramp.
    policy.sample(memory(), now + ms(2), 1, opt);
    assert_eq!((policy.limit, policy.open), (1, true));
    // A long-running block (no completions) is no evidence for ramping.
    for t in [6, 8, 10] {
      policy.sample(memory(), now + ms(t), 1, opt);
      assert_eq!(policy.limit, 1, "ramped without completed work");
    }
    let mut limits = Vec::new();
    for (i, t) in (12..24).step_by(2).enumerate() {
      policy.sample(memory(), now + ms(t), 2 + i as u64, opt);
      limits.push(policy.limit);
    }
    assert_eq!(limits, [2, 4, 8, 16, 24, 24]);
    assert_eq!(policy.pressure, Pressure::Healthy);
  }

  #[test]
  fn ramp_stops_at_a_share_of_the_workers_with_moderate_headroom() {
    let opt = options(24);
    let now = Instant::now();
    let mut policy = Policy::new(with_available(20 * GIB), now, opt);
    let moderate = with_available(30 * GIB);
    for (i, t) in (10..30).step_by(2).enumerate() {
      policy.sample(moderate, now + ms(t), 1 + i as u64, opt);
      assert!(policy.limit <= 10);
    }
    assert_eq!((policy.limit, policy.open), (10, true));
    assert_eq!(policy.pressure, Pressure::Hold);
  }

  #[test]
  fn growth_forecast_stops_admissions_before_low_memory_threshold() {
    let opt = options(64);
    let now = Instant::now();
    let mut policy = Policy::new(memory(), now, opt);
    assert_eq!(policy.limit, 64);
    let rising = Memory { process: 16 * GIB, available: 84 * GIB, ..memory() };
    policy.sample(rising, now + ms(250), 0, opt);
    assert_eq!(policy.projected_growth, 240 * GIB);
    assert!(
      !policy.open,
      "high current availability must not hide a growth burst"
    );
    assert_eq!(policy.pressure, Pressure::Critical);
    assert_eq!(policy.limit, 32, "the cap halves, not the drained count");
    policy.sample(rising, now + ms(500), 0, opt);
    assert!(!policy.open);
    assert_eq!(policy.limit, 32, "halved once per closure");
    // Growth stops: admissions resume, at no more than the reduced cap,
    // once the decaying forecast leaves a reserve of headroom.
    let mut t = 500;
    while !policy.open {
      t += 250;
      policy.sample(rising, now + ms(t), 0, opt);
      assert!(t < 5_000, "the forecast never decayed");
    }
    assert!((1..=32).contains(&policy.limit));
  }

  #[test]
  fn reclaim_with_wide_headroom_is_ignored() {
    let opt = options(24);
    let now = Instant::now();
    let mut policy = Policy::new(memory(), now, opt);
    // Every sample: 64 MiB of this process swapped out, and its cgroup
    // stalled for the whole interval. With 90 GiB available that is LRU
    // balancing against other workloads, not a shortage.
    for tick in 1..=40u64 {
      let churn = Memory {
        process_swap: tick * 64 * MIB,
        stall_us: tick * 250_000,
        ..memory()
      };
      policy.sample(churn, now + ms(250 * tick), tick, opt);
      assert_eq!((policy.limit, policy.open), (24, true));
      assert_eq!(policy.pressure, Pressure::Healthy);
    }
  }

  #[test]
  fn baseline_mathlib_backoff_samples_keep_every_worker() {
    // The base binary's Mathlib runs (SP/base/run_mathlib_{a,b}.log, 2026-10-02)
    // backed off to 1-12 of 24 workers at these samples: 93 GiB machine,
    // 65.5-70.1 GiB available, 11.8-16.9 GiB resident+swap, growth forecasts
    // up to 10 GiB, and a reclaim signal. Here every sample carries both
    // attributable reclaim signals as well; none of it may cost a worker.
    let opt = options(24);
    let now = Instant::now();
    let start = Memory {
      capacity: 93 * GIB,
      available: 70 * GIB,
      process: 12 * GIB,
      process_swap: 0,
      stall_us: 0,
    };
    let mut policy = Policy::new(start, now, opt);
    assert_eq!((policy.limit, policy.open), (24, true));
    for tick in 1..=400u64 {
      // 12 MiB of growth per sample plus a 250 MiB burst every 20th (a
      // 10 GiB forecast): 9.6 GiB in all, and availability falls by as much.
      let grown = tick * 12 * MIB + (tick / 20) * 250 * MIB;
      let memory = Memory {
        available: start.available - grown,
        process: start.process + grown,
        process_swap: tick * 16 * MIB,
        stall_us: tick * 100_000,
        ..start
      };
      policy.sample(memory, now + ms(250 * tick), tick * 1_000, opt);
      assert_eq!((policy.limit, policy.open), (24, true), "sample {tick}");
      assert_eq!(policy.pressure, Pressure::Healthy);
    }
  }

  #[test]
  fn reclaim_with_moderate_headroom_is_debounced_and_keeps_a_floor() {
    let opt = options(24);
    let now = Instant::now();
    let base = with_available(40 * GIB);
    let mut policy = Policy::new(base, now, opt);
    assert_eq!(policy.limit, 24);
    let mut swap = 0;
    let mut t = 0;
    let mut tick = |policy: &mut Policy, reclaim: bool| {
      if reclaim {
        swap += 9 * MIB;
      }
      t += 2;
      let memory = Memory { process_swap: swap, ..base };
      policy.sample(memory, now + ms(t), t, opt);
      (policy.limit, policy.open)
    };
    // One sample is a burst, not sustained reclaim.
    assert_eq!(tick(&mut policy, true), (24, true));
    assert_eq!(tick(&mut policy, false), (24, true));
    assert_eq!(tick(&mut policy, true), (24, true));
    // The second consecutive sample halves the cap; admission stays open.
    assert_eq!(tick(&mut policy, true), (12, true));
    assert_eq!(policy.pressure, Pressure::Backoff);
    assert_eq!(tick(&mut policy, true), (6, true));
    assert_eq!(tick(&mut policy, true), (4, true));
    assert_eq!(tick(&mut policy, true), (4, true), "two reserves remain");
    // Reclaim stops: no ramp during the recovery period, then doubling.
    assert_eq!(tick(&mut policy, false), (4, true));
    assert_eq!(tick(&mut policy, false), (4, true));
    assert_eq!(tick(&mut policy, false), (8, true));
    assert_eq!(tick(&mut policy, false), (16, true));
    assert_eq!(tick(&mut policy, false), (24, true));
  }

  #[test]
  fn reclaim_with_low_headroom_closes_admissions() {
    // No growth forecast: isolate the headroom and reclaim decisions.
    let opt = Options { lookahead: Duration::ZERO, ..options(24) };
    let now = Instant::now();
    let mut policy = Policy::new(with_available(40 * GIB), now, opt);
    assert_eq!(policy.limit, 24);
    let low = with_available(22 * GIB);
    let swapped = |n: u64| Memory { process_swap: n * 9 * MIB, ..low };
    // Headroom below two reserves allows one block at once...
    policy.sample(swapped(1), now + ms(2), 0, opt);
    assert_eq!((policy.limit, policy.open), (1, true));
    assert_eq!(policy.pressure, Pressure::Backoff);
    // ...and sustained reclaim there stops admissions altogether.
    policy.sample(swapped(2), now + ms(4), 0, opt);
    assert_eq!((policy.limit, policy.open), (1, false));
    assert_eq!(policy.pressure, Pressure::Critical);
    policy.sample(swapped(3), now + ms(6), 0, opt);
    assert!(!policy.open);
    // Reclaim ends: serial progress resumes only after the recovery period.
    policy.sample(swapped(3), now + ms(8), 0, opt);
    assert!(!policy.open);
    policy.sample(swapped(3), now + ms(12), 0, opt);
    assert_eq!((policy.limit, policy.open), (1, true));
  }

  #[test]
  fn process_budget_uses_resident_plus_swap_headroom() {
    let opt = Options { process_budget: Some(20 * GIB), ..options(8) };
    let now = Instant::now();
    let memory = Memory { process: 19 * GIB, ..memory() };
    let policy = Policy::new(memory, now, opt);
    assert!(!policy.open);
    assert_eq!(policy.pressure, Pressure::Critical);
    // The budget's reserve (2.5 GiB) also scales the reclaim threshold.
    let near = Memory { process: 12 * GIB, process_swap: GIB, ..memory };
    let mut policy = Policy::new(near, now, opt);
    assert_eq!(policy.limit, 8);
    for n in 1..=2 {
      let swapped = Memory { process_swap: GIB + n * 9 * MIB, ..near };
      policy.sample(swapped, now + ms(2 * n), 0, opt);
    }
    assert_eq!((policy.limit, policy.open), (4, true));
  }

  #[test]
  fn stable_retained_data_allows_serial_forward_progress() {
    let opt = options(8);
    let now = Instant::now();
    let memory = with_available(22 * GIB);
    let mut policy = Policy::new(memory, now, opt);
    policy.sample(memory, now + Duration::from_secs(1), 0, opt);
    assert_eq!(policy.pressure, Pressure::Backoff);
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
    let start = Instant::now();
    let gate =
      Admission::with_reader(options(4), Some(low), move || Some(low)).unwrap();
    let Err(CompileError::ResourceLimit { reason }) = gate.acquire() else {
      panic!("admitted a block without headroom");
    };
    assert!(reason.contains("headroom 1.0 GiB, reserve 12.5 GiB"), "{reason}");
    // Genuinely short of memory: one idle timeout, not the long one.
    assert!(start.elapsed() < Duration::from_millis(100 * 5));
    assert_eq!(gate.shared.state.lock().unwrap().active, 0);
    assert!(matches!(gate.check(), Err(CompileError::ResourceLimit { .. })));
  }

  #[test]
  fn background_reclaim_with_wide_headroom_does_not_stall_admissions() {
    // Every sample shows this process swapping and its cgroup stalled for
    // the whole interval, while 90 GiB stay available.
    let reads = Arc::new(AtomicUsize::new(0));
    let reader_reads = Arc::clone(&reads);
    let gate = Admission::with_reader(options(8), Some(memory()), move || {
      let n = reader_reads.fetch_add(1, Ordering::SeqCst) as u64 + 1;
      Some(Memory {
        process_swap: n * 64 * MIB,
        stall_us: n * 1_000_000,
        ..memory()
      })
    })
    .unwrap();
    // Started wide: every worker is admitted at once, with no ramp.
    let permits: Vec<_> =
      (0..8).map(|_| gate.acquire().unwrap().unwrap()).collect();
    until(|| reads.load(Ordering::SeqCst) >= 20);
    {
      let state = gate.shared.state.lock().unwrap();
      let policy = state.policy.as_ref().unwrap();
      assert_eq!((policy.limit, policy.open), (8, true));
    }
    for permit in permits {
      permit.complete();
    }
    let again: Vec<_> =
      (0..8).map(|_| gate.acquire().unwrap().unwrap()).collect();
    assert_eq!(gate.shared.state.lock().unwrap().active, again.len());
  }

  #[test]
  fn closed_gate_with_wide_headroom_outlasts_the_idle_timeout() {
    // Another workload allocates and frees 40 GiB between samples. The
    // growth forecast keeps admission closed, although at least 50 GiB stay
    // available: that is not a shortage, so one idle timeout is not enough
    // to fail, but the gate still gives up rather than wait forever.
    let reads = Arc::new(AtomicUsize::new(0));
    let reader_reads = Arc::clone(&reads);
    let start = Instant::now();
    let gate = Admission::with_reader(options(2), Some(memory()), move || {
      let n = reader_reads.fetch_add(1, Ordering::SeqCst);
      let available = if n.is_multiple_of(2) { 50 * GIB } else { 90 * GIB };
      Some(Memory { available, ..memory() })
    })
    .unwrap();
    until(|| !gate.shared.state.lock().unwrap().policy.as_ref().unwrap().open);
    thread::scope(|scope| {
      let waiting =
        scope.spawn(|| gate.acquire().map(|permit| permit.is_some()));
      thread::sleep(Duration::from_millis(300));
      assert!(gate.check().is_ok(), "failed while headroom was wide");
      assert!(!waiting.is_finished());
      let result = waiting.join().unwrap();
      assert!(matches!(result, Err(CompileError::ResourceLimit { .. })));
    });
    assert!(start.elapsed() >= Duration::from_secs(1));
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
