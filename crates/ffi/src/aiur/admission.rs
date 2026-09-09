//! Non-preemptive admission for shard execution. A 64-thread Rayon pool does
//! not imply 64 live execution records. Reservations, cgroup headroom, recent
//! growth and a completion-driven ramp all have to permit new work.
//!
//! Active shards are never parked/cancelled while holding their records.
//! Estimates cannot bound arbitrary future allocation: keep a supervisor cap.

use std::{
  sync::{Arc, Condvar, Mutex},
  thread::{self, JoinHandle},
  time::{Duration, Instant},
};

use super::memory::{GIB, Memory, MemoryReader};

mod dispatch;
pub(super) use dispatch::Followups;

#[derive(Clone, Copy)]
struct Options {
  max_workers: usize,
  tick: Duration,
  ramp_interval: Duration,
  recovery: Duration,
  idle_timeout: Duration,
  lookahead: Duration,
}

impl Options {
  fn new(max_workers: usize) -> Self {
    Self {
      max_workers: max_workers.max(1),
      tick: Duration::from_millis(250),
      ramp_interval: Duration::from_secs(2),
      recovery: Duration::from_secs(5),
      idle_timeout: Duration::from_secs(30),
      lookahead: Duration::from_secs(10),
    }
  }
}

struct Policy {
  initial_budget: u64,
  memory: Memory,
  sampled: Instant,
  ramped: Instant,
  blocked_at: Option<Instant>,
  limit: usize,
  completed: usize,
  growth_per_second: u64,
  forecast: u64,
  stall_sample_bp: u64,
  swap_growth: u64,
  reason: &'static str,
  open: bool,
}

impl Policy {
  fn new(memory: Memory, now: Instant, options: Options) -> Self {
    let open = memory.budget() > 0 && memory.stall_avg10_bp <= 1000;
    Self {
      initial_budget: memory.budget(),
      memory,
      sampled: now,
      ramped: now,
      blocked_at: (!open).then_some(now),
      limit: options.max_workers.min(8),
      completed: 0,
      growth_per_second: 0,
      forecast: 0,
      stall_sample_bp: 0,
      swap_growth: 0,
      reason: if memory.budget() == 0 {
        "headroom"
      } else if !open {
        "psi-sustained"
      } else {
        "ready"
      },
      open,
    }
  }

  fn sample(
    &mut self,
    memory: Memory,
    now: Instant,
    active: usize,
    completed: usize,
    reserved: u64,
    options: Options,
  ) {
    let elapsed = now.saturating_duration_since(self.sampled);
    let delta = memory
      .rss
      .saturating_add(memory.swap)
      .saturating_sub(self.memory.rss.saturating_add(self.memory.swap))
      .max(self.memory.available.saturating_sub(memory.available));
    let rate =
      u64::try_from(u128::from(delta) * 1_000_000 / elapsed.as_micros().max(1))
        .unwrap_or(u64::MAX);
    self.growth_per_second =
      rate.max(self.growth_per_second.saturating_mul(3) / 4);
    self.forecast =
      self.growth_per_second.saturating_mul(options.lookahead.as_secs());
    let stalls =
      u128::from(memory.stall_us.saturating_sub(self.memory.stall_us));
    self.stall_sample_bp =
      u64::try_from(stalls * 10_000 / elapsed.as_micros().max(1))
        .unwrap_or(u64::MAX);
    self.swap_growth = memory.swap.saturating_sub(self.memory.swap);
    let swapping = self.swap_growth > 8 << 20;
    let psi_spike = stalls > elapsed.as_micros() / 10;
    let psi_sustained = memory.stall_avg10_bp > 1000;
    let needed =
      memory.reserve().saturating_add(reserved).saturating_add(self.forecast);
    let headroom_tight = memory.available <= needed;
    let blocked = headroom_tight || swapping || psi_sustained;
    // React to every >10% stall sample immediately, but do not turn a brief
    // system-wide spike into a fresh five-second cooldown. Repeated 50 ms
    // spikes can otherwise starve even idle, well-provisioned serial work.
    // Sustained PSI, actual swap growth and insufficient headroom retain the
    // full recovery delay; no permit can bypass the live reservation checks.
    if blocked || psi_spike {
      self.limit = self.limit.min((active / 2).max(1));
    }
    if blocked {
      self.blocked_at = Some(now);
    }
    self.open = !blocked
      && !psi_spike
      && self
        .blocked_at
        .is_none_or(|t| now.duration_since(t) >= options.recovery);
    self.reason = if headroom_tight {
      "headroom"
    } else if swapping {
      "swap-growth"
    } else if psi_sustained {
      "psi-sustained"
    } else if psi_spike {
      "psi-spike"
    } else if !self.open {
      "recovery"
    } else {
      "ready"
    };
    // Do not fill the pool based on elapsed time before a single record has
    // finished growing. At most one new concurrency slot per ramp interval.
    if self.open
      && completed > self.completed
      && now.duration_since(self.ramped) >= options.ramp_interval
    {
      self.limit = (self.limit + 1).min(options.max_workers);
      self.ramped = now;
      self.completed = completed;
    }
    // Keep unspent completion evidence until a ramp consumes it. Otherwise
    // frequent short jobs may all finish between two ramp deadlines.
    self.memory = memory;
    self.sampled = now;
  }

  fn fits(&self, reserved: u64, next: u64) -> bool {
    // Deliberately conservative: both the live charge AND all reservations
    // are covered. Memory may grow after the last sample, and a released
    // record may still be resident in the allocator. Never spend that RAM
    // merely because its permit was returned.
    self.open
      && reserved.saturating_add(next) <= self.initial_budget
      && self.memory.available
        >= self
          .memory
          .reserve()
          .saturating_add(reserved)
          .saturating_add(next)
          .saturating_add(self.forecast)
  }
}

struct State {
  policy: Option<Policy>,
  active: usize,
  completed: usize,
  reserved: u64,
  stopped: bool,
  error: Option<String>,
  idle_since: Option<Instant>,
}

struct Shared {
  state: Mutex<State>,
  changed: Condvar,
  shutdown: Condvar,
  options: Options,
}

pub(super) struct Admission {
  shared: Arc<Shared>,
  monitor: Option<JoinHandle<()>>,
}

pub(super) struct Permit<'a> {
  shared: &'a Shared,
  bytes: u64,
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
    state.reserved -= self.bytes;
    state.completed += usize::from(self.completed);
    if state.active == 0 {
      state.idle_since = Some(Instant::now());
    }
    self.shared.changed.notify_all();
  }
}

impl Admission {
  pub(super) fn execution_budget(&self) -> u64 {
    self
      .shared
      .state
      .lock()
      .unwrap()
      .policy
      .as_ref()
      .map_or(1 << 30, |p| p.initial_budget)
  }
  pub(super) fn new(max_workers: usize) -> Result<Self, String> {
    let reader = MemoryReader::new()?;
    let initial = reader.as_ref().map(MemoryReader::read).transpose()?;
    Self::with_reader(Options::new(max_workers), initial, move || {
      reader.as_ref().ok_or("memory reader unavailable")?.read()
    })
  }

  fn with_reader(
    options: Options,
    initial: Option<Memory>,
    read: impl Fn() -> Result<Memory, String> + Send + 'static,
  ) -> Result<Self, String> {
    let now = Instant::now();
    let shared = Arc::new(Shared {
      state: Mutex::new(State {
        policy: initial.map(|m| Policy::new(m, now, options)),
        active: 0,
        completed: 0,
        reserved: 0,
        stopped: false,
        error: None,
        idle_since: Some(now),
      }),
      changed: Condvar::new(),
      shutdown: Condvar::new(),
      options,
    });
    if initial.is_some() {
      log(&shared.state.lock().unwrap(), options);
    } else {
      eprintln!(
        "[ixvm_memory] telemetry unavailable on this platform; serial admission in a {}-worker pool",
        options.max_workers
      );
    }
    let monitor = if initial.is_some() {
      let shared = Arc::clone(&shared);
      Some(
        thread::Builder::new()
          .name("ixvm-memory".into())
          .spawn(move || {
            let mut logged = now;
            loop {
              let mut state = shared.state.lock().unwrap();
              let deadline =
                state.policy.as_ref().unwrap().sampled + options.tick;
              while !state.stopped && Instant::now() < deadline {
                state = shared
                  .shutdown
                  .wait_timeout(
                    state,
                    deadline.saturating_duration_since(Instant::now()),
                  )
                  .unwrap()
                  .0;
              }
              if state.stopped {
                return;
              }
              drop(state);
              let sample = read();
              let mut state = shared.state.lock().unwrap();
              if state.stopped {
                return;
              }
              let memory = match sample {
                Ok(memory) => memory,
                Err(e) => {
                  state.error = Some(format!(
                    "IxVM memory telemetry failed; stopping admission: {e}"
                  ));
                  eprintln!("[ixvm_memory] {}", state.error.as_ref().unwrap());
                  state.stopped = true;
                  shared.changed.notify_all();
                  return;
                },
              };
              let now = Instant::now();
              let (active, completed, reserved) =
                (state.active, state.completed, state.reserved);
              let policy = state.policy.as_mut().unwrap();
              let before = (policy.limit, policy.open, policy.reason);
              policy.sample(memory, now, active, completed, reserved, options);
              if before != (policy.limit, policy.open, policy.reason)
                || now.duration_since(logged) >= Duration::from_secs(5)
              {
                log(&state, options);
                logged = now;
              }
              shared.changed.notify_all();
            }
          })
          .map_err(|e| format!("start IxVM memory monitor: {e}"))?,
      )
    } else {
      None
    };
    Ok(Self { shared, monitor })
  }

  pub(super) fn acquire(&self, estimate: usize) -> Result<Permit<'_>, String> {
    let mut state = self.shared.state.lock().unwrap();
    loop {
      if let Some(permit) = self.probe(&mut state, estimate)? {
        return Ok(permit);
      }
      state = self
        .shared
        .changed
        .wait_timeout(state, self.shared.options.tick)
        .unwrap()
        .0;
    }
  }

  /// Probe once so a dispatcher can consume completions while admission is
  /// closed. Uses the same reservations, pressure policy and idle deadline as
  /// the blocking API; None is not a permit or permission to bypass the gate.
  fn try_acquire(&self, estimate: usize) -> Result<Option<Permit<'_>>, String> {
    self.probe(&mut self.shared.state.lock().unwrap(), estimate)
  }

  fn probe(
    &self,
    state: &mut State,
    estimate: usize,
  ) -> Result<Option<Permit<'_>>, String> {
    // These ISLB/Mathlib fits are heuristics, not FLT upper bounds. Reserve
    // twice the old prediction in addition to live headroom and growth.
    let bytes = u64::try_from(estimate).unwrap_or(u64::MAX).saturating_mul(2);
    if let Some(error) = &state.error {
      return Err(error.clone());
    }
    if state.stopped {
      return Err("IxVM memory admission stopped".into());
    }
    let fits = if let Some(p) = &state.policy {
      if bytes > p.initial_budget {
        let error = format!(
          "IxVM shard memory reservation {bytes} bytes exceeds execution budget {} bytes; refine the shard or free memory",
          p.initial_budget
        );
        state.error = Some(error.clone());
        state.stopped = true;
        self.shared.changed.notify_all();
        self.shared.shutdown.notify_all();
        return Err(error);
      }
      state.active < p.limit && p.fits(state.reserved, bytes)
    } else {
      state.active == 0
    };
    if fits {
      let reserved = state
        .reserved
        .checked_add(bytes)
        .ok_or("IxVM memory reservation overflow")?;
      state.active += 1;
      state.reserved = reserved;
      state.idle_since = None;
      return Ok(Some(Permit {
        shared: &self.shared,
        bytes,
        completed: false,
      }));
    }
    if state.active == 0 {
      let since = state.idle_since.get_or_insert_with(Instant::now);
      if since.elapsed() >= self.shared.options.idle_timeout {
        let error = format!(
          "IxVM memory admission: idle timeout with no active shards; waiting_for={} next_reservation={bytes} bytes; {}",
          state.policy.as_ref().map_or("serial-admission", |p| if p.open {
            "reservation-headroom"
          } else {
            p.reason
          }),
          diagnostics(state, self.shared.options)
        );
        state.error = Some(error.clone());
        state.stopped = true;
        self.shared.changed.notify_all();
        self.shared.shutdown.notify_all();
        return Err(error);
      }
    }
    Ok(None)
  }

  #[cfg(test)]
  pub(super) fn for_test(workers: usize) -> Self {
    let memory = Memory {
      capacity: 1024 * GIB,
      available: 1024 * GIB,
      rss: 0,
      swap: 0,
      stall_us: 0,
      stall_avg10_bp: 0,
      cgroup: None,
    };
    Self::with_reader(Options::new(workers), Some(memory), move || Ok(memory))
      .unwrap()
  }

  /// Admission waits run on the caller, outside the target pool. Witness
  /// construction itself uses nested Rayon work: blocking pool workers on
  /// unadmitted shards could strand every worker behind those witnesses.
  pub(super) fn map<R: Send>(
    &self,
    pool: &rayon::ThreadPool,
    estimates: &[usize],
    work: impl Fn(usize) -> R + Sync,
  ) -> Result<Vec<R>, String> {
    if pool.current_thread_index().is_some() {
      return Err(
        "IxVM admission dispatcher must run outside its Rayon pool".into(),
      );
    }
    let results =
      Mutex::new((0..estimates.len()).map(|_| None).collect::<Vec<_>>());
    pool.in_place_scope(|scope| -> Result<(), String> {
      for (index, estimate) in estimates.iter().enumerate() {
        let permit = self.acquire(*estimate)?;
        let (work, results) = (&work, &results);
        scope.spawn(move |_| {
          let result = work(index);
          permit.complete();
          results.lock().unwrap()[index] = Some(result);
        });
      }
      Ok(())
    })?;
    self.check()?;
    results
      .into_inner()
      .unwrap()
      .into_iter()
      .map(|r| {
        r.ok_or_else(|| "missing IxVM shard execution result".to_owned())
      })
      .collect()
  }

  pub(super) fn check(&self) -> Result<(), String> {
    self.shared.state.lock().unwrap().error.clone().map_or(Ok(()), Err)
  }
}

impl Drop for Admission {
  fn drop(&mut self) {
    self.shared.state.lock().unwrap().stopped = true;
    self.shared.changed.notify_all();
    self.shared.shutdown.notify_all();
    if let Some(monitor) = self.monitor.take() {
      let _ = monitor.join();
    }
  }
}

fn log(state: &State, options: Options) {
  eprintln!("[ixvm_memory] {}", diagnostics(state, options));
}

#[allow(clippy::cast_precision_loss)]
fn diagnostics(state: &State, options: Options) -> String {
  let Some(p) = &state.policy else {
    return "telemetry unavailable; serial admission".into();
  };
  let gib = |v: u64| v as f64 / GIB as f64;
  let cgroup = p.memory.cgroup.map_or_else(
    || "none".into(),
    |(used, limit)| format!("{:.1}/{:.1} GiB", gib(used), gib(limit)),
  );
  let recovery = p.blocked_at.map_or(Duration::ZERO, |t| {
    options.recovery.saturating_sub(p.sampled.saturating_duration_since(t))
  });
  format!(
    "limit={}/{} active={} completed={} admitting={} reason={} reserved={:.1} GiB budget={:.1} GiB rss={:.1} GiB available={:.1} GiB reserve={:.1} GiB growth_forecast={:.1} GiB psi_full={:.2}% psi_avg10={:.2}% swap_growth={:.1} MiB recovery={:.1}s cgroup={cgroup}",
    p.limit,
    options.max_workers,
    state.active,
    state.completed,
    p.open,
    p.reason,
    gib(state.reserved),
    gib(p.initial_budget),
    gib(p.memory.rss),
    gib(p.memory.available),
    gib(p.memory.reserve()),
    gib(p.forecast),
    p.stall_sample_bp as f64 / 100.0,
    p.memory.stall_avg10_bp as f64 / 100.0,
    p.swap_growth as f64 / f64::from(1 << 20),
    recovery.as_secs_f64()
  )
}

#[cfg(test)]
mod tests;
