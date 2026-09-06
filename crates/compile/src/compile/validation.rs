//! Memory-aware admission and cooperative retry for inductive validation.
//!
//! The coordinator never occupies a Rayon worker. Cancelled attempts return
//! normally (the host uses panic=abort), dropping scratch data before retry.
//! This is a soft budget, not an allocator limit: checkpoints cannot interrupt
//! an allocation, a lazy-environment fetch, or destruction already in progress.

use std::cell::Cell;
use std::collections::VecDeque;
use std::sync::{
  Arc,
  atomic::{AtomicBool, AtomicU64, Ordering},
  mpsc,
};
use std::time::{Duration, Instant};

use ixon::CompileError;

use super::memory::{
  GIB, MIB, Memory, MemoryReader, Pressure, pressure, reclaiming,
  resource_error,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Cancelled;

#[derive(Debug)]
pub(crate) enum AttemptError {
  Cancelled,
  Compile(CompileError),
}

impl From<Cancelled> for AttemptError {
  fn from(_: Cancelled) -> Self {
    Self::Cancelled
  }
}
impl From<CompileError> for AttemptError {
  fn from(error: CompileError) -> Self {
    Self::Compile(error)
  }
}
impl AttemptError {
  pub(crate) fn into_compile(self) -> CompileError {
    match self {
      Self::Compile(error) => error,
      Self::Cancelled => resource_error("inductive validation interrupted"),
    }
  }
}

#[derive(Default)]
struct Signals {
  cancel: AtomicBool,
  visits: AtomicU64,
  scratch_peak: AtomicU64,
}

/// Worker-local checkpoint state. Scratch telemetry estimates the largest
/// observed walk cache plus node payload, not total retained scratch or
/// per-job RSS (which cannot be attributed by subtracting process RSS
/// samples while multiple jobs execute). Admission uses OS telemetry.
#[derive(Default)]
pub(crate) struct Checkpoint {
  signals: Option<Arc<Signals>>,
  visits: Cell<u64>,
}

impl Checkpoint {
  pub(crate) fn visit(&self) -> Result<(), Cancelled> {
    if let Some(signals) = &self.signals {
      if signals.cancel.load(Ordering::Relaxed) {
        return Err(Cancelled);
      }
      let n = self.visits.get().saturating_add(1);
      self.visits.set(n);
      if n.is_multiple_of(1024) {
        signals.visits.store(n, Ordering::Relaxed);
      }
    }
    Ok(())
  }

  pub(crate) fn scratch(&self, estimate: usize) {
    if let Some(signals) = &self.signals {
      signals.scratch_peak.fetch_max(estimate as u64, Ordering::Relaxed);
    }
  }
}
impl Drop for Checkpoint {
  fn drop(&mut self) {
    if let Some(signals) = &self.signals {
      signals.visits.store(self.visits.get(), Ordering::Relaxed);
    }
  }
}

#[derive(Clone, Copy, Debug)]
struct Options {
  max_workers: usize,
  initial_workers: usize,
  process_budget: Option<u64>,
  tick: Duration,
  ramp_interval: Duration,
  recovery: Duration,
  idle_timeout: Duration,
  verbose: bool,
}
impl Options {
  fn from_env() -> Result<Self, CompileError> {
    let budget = super::memory::budget_from_env("IX_VALIDATE_MEMORY_GIB")?;
    let max_workers = rayon::current_num_threads().max(1);
    Ok(Self {
      max_workers,
      initial_workers: max_workers.min(2),
      process_budget: budget,
      tick: Duration::from_millis(250),
      ramp_interval: Duration::from_secs(1),
      recovery: Duration::from_secs(5),
      idle_timeout: Duration::from_secs(30),
      verbose: *super::env::IX_VERBOSE,
    })
  }
}

struct Active {
  id: usize,
  solo: bool,
  signals: Arc<Signals>,
}

// Production builds abort on panic. In unwind-enabled test/library builds,
// still notify the coordinator if a task exits abnormally, so the enclosing
// Rayon scope can propagate the panic instead of waiting for a lost result.
struct Completion {
  id: usize,
  sender: Option<mpsc::Sender<(usize, Result<(), AttemptError>)>>,
}
impl Completion {
  fn finish(mut self, result: Result<(), AttemptError>) {
    let _ = self.sender.take().unwrap().send((self.id, result));
  }
}
impl Drop for Completion {
  fn drop(&mut self) {
    if let Some(sender) = self.sender.take() {
      let _ = sender.send((
        self.id,
        Err(resource_error("validation task exited without a result").into()),
      ));
    }
  }
}

/// Cancel the newest attempts, preserving the oldest work. Cancelled work
/// stays active until its result arrives *after* scratch has been dropped.
fn cancel_to(active: &[Active], keep: usize) {
  for job in active
    .iter()
    .filter(|j| !j.signals.cancel.load(Ordering::Relaxed))
    .skip(keep)
  {
    job.signals.cancel.store(true, Ordering::Relaxed);
  }
}

fn coordinate<'scope, T: Sync, F>(
  scope: &rayon::Scope<'scope>,
  jobs: &'scope [T],
  work: &'scope F,
  options: &Options,
  mut read: impl FnMut() -> Option<Memory>,
) -> Result<(), CompileError>
where
  F: Fn(&T, &Checkpoint) -> Result<(), AttemptError> + Sync,
{
  let (sender, receiver) = mpsc::channel();
  let mut ready: VecDeque<usize> = (0..jobs.len()).collect();
  let mut deferred = VecDeque::new();
  let mut active: Vec<Active> = Vec::new();
  let mut error = None;
  let mut limit = options.initial_workers.max(1).min(options.max_workers);
  let mut previous =
    read().ok_or_else(|| resource_error("memory telemetry unavailable"))?;
  let mut sampled = Instant::now();
  let mut ramped = sampled;
  let mut idle_since = None;
  let mut logged = sampled;
  let mut completed = 0;
  let mut retries = 0;
  // Apply limits before the first allocation-heavy job, not only on tick 1.
  let mut state =
    pressure(previous, previous, options.tick, options.process_budget);
  let mut blocked = previous.headroom(options.process_budget)
    < previous.reserve(options.process_budget);
  let mut pressured_at = blocked.then_some(sampled);
  if state != Pressure::Healthy {
    limit = 1;
  }

  loop {
    let now = Instant::now();
    if now.duration_since(sampled) >= options.tick {
      let previous_state = state;
      if let Some(memory) = read() {
        blocked = memory.headroom(options.process_budget)
          < memory.reserve(options.process_budget)
          || reclaiming(memory, previous, now.duration_since(sampled));
        state = pressure(
          memory,
          previous,
          now.duration_since(sampled),
          options.process_budget,
        );
        if blocked {
          pressured_at = Some(now);
        }
        if matches!(state, Pressure::Backoff | Pressure::Critical) {
          let running = active
            .iter()
            .filter(|j| !j.signals.cancel.load(Ordering::Relaxed))
            .count();
          let next =
            if state == Pressure::Critical { 1 } else { (running / 2).max(1) };
          limit = limit.min(next);
          cancel_to(&active, limit);
          // Don't mistake memory still being released by other attempts for
          // the survivor's footprint. Only fail a genuinely isolated attempt.
          if state == Pressure::Critical && active.len() == 1 && error.is_none()
          {
            active[0].signals.cancel.store(true, Ordering::Relaxed);
            error = Some(resource_error(format!(
              "inductive validation group #{} reached the memory safety reserve while running alone (resident+swap {:.1} GiB); increase the budget or reduce this group's working set",
              active[0].id,
              memory.process as f64 / GIB as f64
            )));
          }
        } else if state == Pressure::Hold {
          limit = 1;
        } else if state == Pressure::Healthy
          && pressured_at
            .is_none_or(|t| now.duration_since(t) >= options.recovery)
          && now.duration_since(ramped) >= options.ramp_interval
        {
          limit = (limit + 1).min(options.max_workers);
          ramped = now;
        }
        if options.verbose
          && (state != previous_state
            || now.duration_since(logged) >= Duration::from_secs(5))
        {
          eprintln!(
            "[validate_memory] {state:?}: limit={limit}/{} active={} ready={} deferred={} completed={completed}/{} retries={retries} available={:.1} GiB resident+swap={:.1} GiB",
            options.max_workers,
            active.len(),
            ready.len(),
            deferred.len(),
            jobs.len(),
            memory.available as f64 / GIB as f64,
            memory.process as f64 / GIB as f64
          );
          for job in &active {
            let visits = job.signals.visits.load(Ordering::Relaxed);
            if visits >= 1_000_000 {
              eprintln!(
                "[validate_memory] active group #{}: visits={visits} scratch_estimate_peak={:.1} MiB cancelling={}",
                job.id,
                job.signals.scratch_peak.load(Ordering::Relaxed) as f64
                  / MIB as f64,
                job.signals.cancel.load(Ordering::Relaxed)
              );
            }
          }
          logged = now;
        }
        previous = memory;
      } else if error.is_none() {
        error = Some(resource_error(
          "memory telemetry became unavailable during validation",
        ));
      }
      sampled = now;
    }

    if error.is_some() {
      cancel_to(&active, 0);
    }
    let recovering =
      pressured_at.is_some_and(|t| now.duration_since(t) < options.recovery);
    let draining =
      active.iter().any(|j| j.signals.cancel.load(Ordering::Relaxed));
    // Retained environments can keep headroom below Healthy after every
    // attempt has drained. With a reserve and no active reclaim pressure,
    // continue serially rather than waiting for retained data to disappear.
    let can_admit = error.is_none() && !recovering && !draining && !blocked;
    let admission_limit = if state == Pressure::Healthy { limit } else { 1 };
    if can_admit && !active.iter().any(|j| j.solo) {
      while active.len() < admission_limit {
        let next = if !ready.is_empty() {
          ready.pop_front().map(|id| (id, false))
        } else if active.is_empty() {
          deferred.pop_front().map(|id| (id, true))
        } else {
          None
        };
        let Some((id, solo)) = next else {
          break;
        };
        let signals = Arc::new(Signals::default());
        let token = Arc::clone(&signals);
        let result_sender = sender.clone();
        scope.spawn(move |_| {
          let completion = Completion { id, sender: Some(result_sender) };
          let checkpoint =
            Checkpoint { signals: Some(token), visits: Cell::new(0) };
          let result = work(&jobs[id], &checkpoint);
          drop(checkpoint);
          completion.finish(result);
        });
        active.push(Active { id, solo, signals });
        if solo {
          break;
        }
      }
    }

    if active.is_empty() {
      if let Some(error) = error {
        return Err(error);
      }
      if ready.is_empty() && deferred.is_empty() {
        return Ok(());
      }
      let start = *idle_since.get_or_insert(now);
      if now.duration_since(start) >= options.idle_timeout {
        return Err(resource_error(format!(
          "not enough available memory to admit an inductive validation job; no progress for {:.1} seconds (headroom {:.1} GiB, reserve {:.1} GiB, pressure {state:?})",
          options.idle_timeout.as_secs_f64(),
          previous.headroom(options.process_budget) as f64 / GIB as f64,
          previous.reserve(options.process_budget) as f64 / GIB as f64,
        )));
      }
    } else {
      idle_since = None;
    }

    if let Ok((id, result)) =
      receiver.recv_timeout(options.tick.min(Duration::from_millis(50)))
    {
      let position = active
        .iter()
        .position(|j| j.id == id)
        .expect("result for active validation job");
      let job = active.remove(position);
      if options.verbose
        && (job.solo || job.signals.visits.load(Ordering::Relaxed) >= 1_000_000)
      {
        eprintln!(
          "[validate_memory] group #{id}: visits={} scratch_estimate_peak={:.1} MiB solo={}",
          job.signals.visits.load(Ordering::Relaxed),
          job.signals.scratch_peak.load(Ordering::Relaxed) as f64 / MIB as f64,
          job.solo
        );
      }
      match result {
        Ok(()) => completed += 1,
        Err(AttemptError::Compile(failure)) => {
          if error.is_none() {
            error = Some(failure);
          }
        },
        Err(AttemptError::Cancelled) => {
          if error.is_none() {
            if job.solo {
              error = Some(resource_error(format!(
                "inductive validation group #{id} was cancelled while already running alone"
              )));
            } else {
              retries += 1;
              deferred.push_back(id);
            }
          }
        },
      }
    }
  }
}

fn run_with<T: Sync, F, R>(
  jobs: &[T],
  work: &F,
  options: Options,
  read: R,
) -> Result<(), CompileError>
where
  F: Fn(&T, &Checkpoint) -> Result<(), AttemptError> + Sync,
  R: FnMut() -> Option<Memory> + Send,
{
  rayon::in_place_scope(|scope| {
    std::thread::scope(|threads| {
      let controller =
        threads.spawn(|| coordinate(scope, jobs, work, &options, read));
      // A caller may itself occupy the only thread of a custom Rayon pool.
      // Let it execute scoped work while the independent controller samples
      // memory and sends cancellations; never block that last Rayon worker.
      while !controller.is_finished() {
        rayon::yield_now();
        std::thread::sleep(Duration::from_millis(1));
      }
      controller.join().unwrap()
    })
  })
}

pub(crate) fn run<T: Sync, F>(jobs: &[T], work: F) -> Result<(), CompileError>
where
  F: Fn(&T, &Checkpoint) -> Result<(), AttemptError> + Sync,
{
  if jobs.is_empty() {
    return Ok(());
  }
  let options = Options::from_env()?;
  let mut reader = MemoryReader::new();
  let disabled = std::env::var("IX_VALIDATE_ADAPTIVE").as_deref() == Ok("0");
  if disabled && options.process_budget.is_some() {
    return Err(resource_error(
      "IX_VALIDATE_MEMORY_GIB cannot be combined with IX_VALIDATE_ADAPTIVE=0",
    ));
  }
  if disabled || reader.read().is_none() {
    if !disabled && options.process_budget.is_some() {
      return Err(resource_error(
        "IX_VALIDATE_MEMORY_GIB requires Linux memory telemetry",
      ));
    }
    if options.verbose {
      eprintln!(
        "[validate_memory] adaptive admission disabled or Linux memory telemetry unavailable"
      );
    }
    use rayon::prelude::*;
    return jobs.par_iter().try_for_each(|job| {
      work(job, &Checkpoint::default()).map_err(AttemptError::into_compile)
    });
  }
  if options.verbose {
    eprintln!(
      "[validate_memory] adaptive admission: initial={} max={} budget_gib={:?}",
      options.initial_workers,
      options.max_workers,
      options.process_budget.map(|b| b as f64 / GIB as f64)
    );
  }
  run_with(jobs, &work, options, move || reader.read())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::memory::{cgroup_dirs, field, psi_total};
  use std::path::PathBuf;
  use std::sync::atomic::AtomicUsize;

  fn healthy() -> Memory {
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
      initial_workers: 1,
      process_budget: None,
      tick: Duration::from_millis(2),
      ramp_interval: Duration::from_millis(5),
      recovery: Duration::from_millis(5),
      idle_timeout: Duration::from_millis(100),
      verbose: false,
    }
  }
  fn pool(n: usize) -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new().num_threads(n).build().unwrap()
  }
  fn until(mut ready: impl FnMut() -> bool) {
    let start = Instant::now();
    while !ready() {
      assert!(
        start.elapsed() < Duration::from_secs(5),
        "test made no progress"
      );
      std::thread::sleep(Duration::from_millis(1));
    }
  }
  struct Scratch<'a> {
    live: &'a AtomicUsize,
    dropping: Option<&'a AtomicUsize>,
  }
  impl Drop for Scratch<'_> {
    fn drop(&mut self) {
      if let Some(dropping) = self.dropping {
        dropping.fetch_add(1, Ordering::SeqCst);
        std::thread::sleep(Duration::from_millis(20));
        dropping.fetch_sub(1, Ordering::SeqCst);
      }
      self.live.fetch_sub(1, Ordering::SeqCst);
    }
  }

  #[test]
  fn pressure_accounts_for_resident_plus_swap_budget_and_stalls() {
    let mem = healthy();
    assert_eq!(
      pressure(mem, mem, Duration::from_secs(1), None),
      Pressure::Healthy
    );
    assert_eq!(
      pressure(
        Memory { available: 30 * GIB, ..mem },
        mem,
        Duration::from_secs(1),
        None
      ),
      Pressure::Hold
    );
    assert_eq!(
      pressure(
        Memory { available: 20 * GIB, ..mem },
        mem,
        Duration::from_secs(1),
        None
      ),
      Pressure::Backoff
    );
    assert_eq!(
      pressure(
        Memory { available: 4 * GIB, ..mem },
        mem,
        Duration::from_secs(1),
        None
      ),
      Pressure::Critical
    );
    assert_eq!(
      pressure(
        Memory { stall_us: 110_000, ..mem },
        mem,
        Duration::from_secs(1),
        None
      ),
      Pressure::Backoff
    );
    assert_eq!(
      pressure(
        Memory { swap_used: 9 * MIB, ..mem },
        mem,
        Duration::from_secs(1),
        None
      ),
      Pressure::Backoff
    );
    assert_eq!(
      pressure(
        Memory { process: 96 * GIB, ..mem },
        mem,
        Duration::from_secs(1),
        Some(100 * GIB)
      ),
      Pressure::Critical
    );
    // Old swap occupancy is not new pressure.
    let swapped = Memory { swap_used: 90 * GIB, ..mem };
    assert_eq!(
      pressure(swapped, swapped, Duration::from_secs(1), None),
      Pressure::Healthy
    );
  }

  #[test]
  fn parses_proc_and_cgroup_namespace_ancestors() {
    assert_eq!(
      field("MemTotal: 123 kB\nMemAvailable: 45 kB\n", "MemAvailable:"),
      Some(45)
    );
    assert_eq!(
      psi_total("some avg10=0 total=999\nfull avg10=0 total=123\n"),
      123
    );
    let mount = "30 20 0:25 / /sys/fs/cgroup rw - cgroup2 cgroup rw";
    assert_eq!(
      cgroup_dirs("0::/a/b\n", mount),
      vec![
        PathBuf::from("/sys/fs/cgroup/a/b"),
        PathBuf::from("/sys/fs/cgroup/a"),
        PathBuf::from("/sys/fs/cgroup"),
      ]
    );
    let namespaced =
      "30 20 0:25 /host/container /cg\\040mount rw - cgroup2 cgroup rw";
    assert_eq!(
      cgroup_dirs("0::/\n", namespaced),
      vec![PathBuf::from("/cg mount")]
    );
    assert_eq!(
      cgroup_dirs("0::/host/container/child\n", namespaced),
      vec![PathBuf::from("/cg mount/child"), PathBuf::from("/cg mount"),]
    );
    assert!(cgroup_dirs("0::/../../escape\n", mount).is_empty());
    assert!(cgroup_dirs("1:memory:/old\n", mount).is_empty());
  }

  #[test]
  fn healthy_admission_ramps_up_without_exceeding_pool_limit() {
    let live = AtomicUsize::new(0);
    let peak = AtomicUsize::new(0);
    let calls: Vec<_> = (0..12).map(|_| AtomicUsize::new(0)).collect();
    pool(4)
      .install(|| {
        run_with(
          &calls,
          &|calls: &AtomicUsize, c: &Checkpoint| {
            calls.fetch_add(1, Ordering::SeqCst);
            let n = live.fetch_add(1, Ordering::SeqCst) + 1;
            let _scratch = Scratch { live: &live, dropping: None };
            peak.fetch_max(n, Ordering::SeqCst);
            std::thread::sleep(Duration::from_millis(40));
            c.visit()?;
            Ok(())
          },
          options(4),
          || Some(healthy()),
        )
      })
      .unwrap();
    assert_eq!(peak.load(Ordering::SeqCst), 4);
    assert!(calls.iter().all(|n| n.load(Ordering::SeqCst) == 1));
    assert_eq!(live.load(Ordering::SeqCst), 0);
  }

  #[test]
  fn retained_memory_allows_serial_progress_below_healthy_headroom() {
    for headroom in [30 * GIB, 20 * GIB] {
      for budget in [None, Some(100 * GIB)] {
        let memory = Memory {
          capacity: if budget.is_some() { 200 * GIB } else { 100 * GIB },
          available: if budget.is_some() { 100 * GIB } else { headroom },
          process: 100 * GIB - headroom,
          ..healthy()
        };
        let live = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let calls: Vec<_> = (0..8).map(|_| AtomicUsize::new(0)).collect();
        let opt =
          Options { initial_workers: 4, process_budget: budget, ..options(4) };
        pool(4)
          .install(|| {
            run_with(
              &calls,
              &|calls: &AtomicUsize, c: &Checkpoint| {
                calls.fetch_add(1, Ordering::SeqCst);
                let n = live.fetch_add(1, Ordering::SeqCst) + 1;
                let _scratch = Scratch { live: &live, dropping: None };
                peak.fetch_max(n, Ordering::SeqCst);
                std::thread::sleep(Duration::from_millis(10));
                c.visit()?;
                Ok(())
              },
              opt,
              || Some(memory),
            )
          })
          .unwrap();
        assert_eq!(peak.load(Ordering::SeqCst), 1);
        assert!(calls.iter().all(|n| n.load(Ordering::SeqCst) == 1));
        assert_eq!(live.load(Ordering::SeqCst), 0);
      }
    }
  }

  #[test]
  fn cancellation_drops_scratch_before_admitting_and_retries_once_alone() {
    let live = AtomicUsize::new(0);
    let dropping = AtomicUsize::new(0);
    let cancelled = AtomicBool::new(false);
    let calls: Vec<_> = (0..5).map(|_| AtomicUsize::new(0)).collect();
    let jobs: Vec<_> = (0..5).collect();
    let mut opt = options(2);
    opt.initial_workers = 2;
    pool(2)
      .install(|| {
        run_with(
          &jobs,
          &|id: &usize, c: &Checkpoint| {
            let attempt = calls[*id].fetch_add(1, Ordering::SeqCst);
            assert_eq!(
              dropping.load(Ordering::SeqCst),
              0,
              "admitted while cancelled scratch was dropping"
            );
            let n = live.fetch_add(1, Ordering::SeqCst);
            let _scratch = Scratch {
              live: &live,
              dropping: (*id == 1 && attempt == 0).then_some(&dropping),
            };
            if *id == 1 && attempt == 0 {
              until(|| {
                c.signals.as_ref().unwrap().cancel.load(Ordering::Relaxed)
              });
              cancelled.store(true, Ordering::SeqCst);
              c.visit()?;
              unreachable!();
            }
            if *id == 0 {
              until(|| cancelled.load(Ordering::SeqCst));
            }
            if attempt > 0 {
              assert_eq!(n, 0, "retry was not alone");
            }
            Ok(())
          },
          opt,
          || {
            // Retained data keeps headroom below Healthy even after the
            // cancelled attempt releases its scratch. Retries must still run.
            Some(
              if live.load(Ordering::SeqCst) >= 2
                || cancelled.load(Ordering::SeqCst)
              {
                Memory { available: 20 * GIB, ..healthy() }
              } else {
                healthy()
              },
            )
          },
        )
      })
      .unwrap();
    assert_eq!(calls[1].load(Ordering::SeqCst), 2);
    for id in [0, 2, 3, 4] {
      assert_eq!(calls[id].load(Ordering::SeqCst), 1);
    }
    assert_eq!(live.load(Ordering::SeqCst), 0);
  }

  #[test]
  fn completed_work_is_not_retried_even_if_cancellation_was_requested() {
    let live = AtomicUsize::new(0);
    let finished = AtomicBool::new(false);
    let calls = [AtomicUsize::new(0), AtomicUsize::new(0)];
    let mut opt = options(2);
    opt.initial_workers = 2;
    pool(2)
      .install(|| {
        run_with(
          &[0, 1],
          &|id: &usize, c: &Checkpoint| {
            calls[*id].fetch_add(1, Ordering::SeqCst);
            live.fetch_add(1, Ordering::SeqCst);
            let _scratch = Scratch { live: &live, dropping: None };
            if *id == 1 {
              until(|| {
                c.signals.as_ref().unwrap().cancel.load(Ordering::Relaxed)
              });
              finished.store(true, Ordering::SeqCst);
            } else {
              until(|| finished.load(Ordering::SeqCst));
            }
            Ok(())
          },
          opt,
          || {
            Some(if live.load(Ordering::SeqCst) == 2 {
              Memory { available: 20 * GIB, ..healthy() }
            } else {
              healthy()
            })
          },
        )
      })
      .unwrap();
    assert!(calls.iter().all(|n| n.load(Ordering::SeqCst) == 1));
  }

  #[test]
  fn oversized_solo_job_returns_resource_error_and_releases_memory() {
    let live = AtomicUsize::new(0);
    let calls = AtomicUsize::new(0);
    let result = pool(1).install(|| {
      run_with(
        &[()],
        &|_: &(), c: &Checkpoint| {
          calls.fetch_add(1, Ordering::SeqCst);
          live.fetch_add(1, Ordering::SeqCst);
          let _scratch = Scratch { live: &live, dropping: Some(&calls) };
          until(|| c.signals.as_ref().unwrap().cancel.load(Ordering::Relaxed));
          c.visit()?;
          unreachable!()
        },
        options(1),
        || {
          Some(if live.load(Ordering::SeqCst) == 1 {
            Memory { available: GIB, process: 99 * GIB, ..healthy() }
          } else {
            healthy()
          })
        },
      )
    });
    assert!(matches!(result, Err(CompileError::ResourceLimit { .. })));
    assert_eq!(live.load(Ordering::SeqCst), 0);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
  }

  #[test]
  fn refuses_to_launch_without_headroom_and_does_not_wait_forever() {
    let calls = AtomicUsize::new(0);
    let result = pool(1).install(|| {
      run_with(
        &[()],
        &|_: &(), _: &Checkpoint| {
          calls.fetch_add(1, Ordering::SeqCst);
          Ok(())
        },
        options(1),
        || Some(Memory { available: GIB, ..healthy() }),
      )
    });
    assert!(matches!(result, Err(CompileError::ResourceLimit { .. })));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
  }

  #[test]
  fn serial_admission_preserves_the_reserve_and_waits_out_reclaim_pressure() {
    for reclaiming in [false, true] {
      let calls = AtomicUsize::new(0);
      let mut reads = 0;
      let result = pool(1).install(|| {
        run_with(
          &[()],
          &|_: &(), _: &Checkpoint| {
            calls.fetch_add(1, Ordering::SeqCst);
            Ok(())
          },
          options(1),
          || {
            reads += 1;
            Some(Memory {
              // Start below the admission reserve but above Critical.
              // Later samples can have room for serial work but must not
              // admit it while the system continues swapping.
              available: if reclaiming && reads > 1 {
                20 * GIB
              } else {
                8 * GIB
              },
              swap_used: if reclaiming { reads * 9 * MIB } else { 0 },
              ..healthy()
            })
          },
        )
      });
      assert!(matches!(result, Err(CompileError::ResourceLimit { .. })));
      assert_eq!(calls.load(Ordering::SeqCst), 0);
    }
  }

  #[test]
  fn unavailable_telemetry_cancels_and_drains_active_work() {
    let live = AtomicUsize::new(0);
    let result = pool(1).install(|| {
      run_with(
        &[()],
        &|_: &(), c: &Checkpoint| {
          live.fetch_add(1, Ordering::SeqCst);
          let _scratch = Scratch { live: &live, dropping: None };
          until(|| c.signals.as_ref().unwrap().cancel.load(Ordering::Relaxed));
          c.visit()?;
          unreachable!()
        },
        options(1),
        || {
          if live.load(Ordering::SeqCst) == 0 { Some(healthy()) } else { None }
        },
      )
    });
    assert!(matches!(result, Err(CompileError::ResourceLimit { .. })));
    assert_eq!(live.load(Ordering::SeqCst), 0);
  }

  #[test]
  fn compile_errors_are_preserved_and_other_jobs_are_drained() {
    let live = AtomicUsize::new(0);
    let failure =
      CompileError::InvalidMutualBlock { reason: "test mismatch".into() };
    let mut opt = options(2);
    opt.initial_workers = 2;
    let result = pool(2).install(|| {
      run_with(
        &[0, 1],
        &|id: &usize, c: &Checkpoint| {
          live.fetch_add(1, Ordering::SeqCst);
          let _scratch = Scratch { live: &live, dropping: None };
          if *id == 0 {
            until(|| live.load(Ordering::SeqCst) == 2);
            Err(failure.clone().into())
          } else {
            until(|| {
              c.signals.as_ref().unwrap().cancel.load(Ordering::Relaxed)
            });
            c.visit()?;
            unreachable!()
          }
        },
        opt,
        || Some(healthy()),
      )
    });
    assert_eq!(result, Err(failure));
    assert_eq!(live.load(Ordering::SeqCst), 0);
  }

  #[test]
  fn custom_single_worker_pool_can_make_forward_progress() {
    let calls = AtomicUsize::new(0);
    pool(1)
      .install(|| {
        run_with(
          &[0, 1, 2],
          &|_: &usize, c: &Checkpoint| {
            c.visit()?;
            calls.fetch_add(1, Ordering::SeqCst);
            Ok(())
          },
          options(1),
          || Some(healthy()),
        )
      })
      .unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 3);
  }
}
