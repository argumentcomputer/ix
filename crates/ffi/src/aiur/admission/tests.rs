use super::*;
use std::sync::{
  atomic::{AtomicBool, AtomicUsize, Ordering},
  mpsc,
};

pub(super) fn memory() -> Memory {
  Memory {
    capacity: 420 * GIB,
    available: 410 * GIB,
    rss: 30 * GIB,
    swap: 0,
    stall_us: 0,
    stall_avg10_bp: 0,
    cgroup: Some((10 * GIB, 420 * GIB)),
  }
}

pub(super) fn quick_options(workers: usize) -> Options {
  Options {
    tick: Duration::from_millis(5),
    ramp_interval: Duration::from_millis(10),
    recovery: Duration::from_millis(10),
    idle_timeout: Duration::from_millis(80),
    ..Options::new(workers)
  }
}

#[test]
fn no_full_width_burst_or_time_only_ramp() {
  let options = Options::new(64);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  assert_eq!(policy.limit, 8);
  for second in 1..100 {
    policy.sample(
      memory(),
      now + Duration::from_secs(second),
      8,
      0,
      72 * GIB,
      options,
    );
  }
  assert_eq!(policy.limit, 8);
  assert!(policy.open);
}

#[test]
fn ramp_requires_completions_and_can_reach_the_entire_pool() {
  let options = Options::new(64);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  for completed in 1..=100 {
    policy.sample(
      memory(),
      now + Duration::from_secs(completed * 2),
      2,
      usize::try_from(completed).unwrap(),
      2 * GIB,
      options,
    );
  }
  assert_eq!(policy.limit, 64);
  assert!(policy.fits(63 * GIB, GIB));
}

#[test]
fn live_growth_stops_admission_before_the_limit_is_reached() {
  let options = Options::new(64);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  policy.sample(
    Memory { available: 300 * GIB, rss: 140 * GIB, ..memory() },
    now + Duration::from_secs(1),
    8,
    0,
    72 * GIB,
    options,
  );
  assert!(!policy.open);
  assert!(!policy.fits(72 * GIB, 9 * GIB));
  assert_eq!(policy.limit, 4);
  assert_eq!(policy.forecast, 1100 * GIB);
}

#[test]
fn reservations_and_retained_actual_memory_are_both_covered() {
  let options = Options::new(64);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  assert!(!policy.fits(320 * GIB, 9 * GIB));
  // No recent growth and no outstanding permit does not mean the heap was
  // returned: an allocator-retained 340 GiB must still block a new record.
  policy.memory.available = 80 * GIB;
  assert!(!policy.fits(0, 9 * GIB));
  policy.memory.available = 100 * GIB;
  assert!(policy.fits(0, 9 * GIB));
  assert!(!policy.fits(9 * GIB, 9 * GIB));
}

#[test]
fn released_permits_do_not_override_pressure_or_recovery() {
  let options = Options::new(64);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  let tight = Memory { available: 80 * GIB, ..memory() };
  policy.sample(tight, now + Duration::from_secs(1), 8, 0, 72 * GIB, options);
  assert!(!policy.fits(0, 9 * GIB));
  // Clear growth to isolate recovery from the forecast in this test.
  policy.growth_per_second = 0;
  policy.sample(memory(), now + Duration::from_secs(2), 0, 8, 0, options);
  assert!(!policy.open);
  policy.sample(memory(), now + Duration::from_secs(7), 0, 8, 0, options);
  assert!(policy.open);
}

#[test]
fn brief_psi_spikes_do_not_starve_serial_admission() {
  let options = Options::new(1);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  let mut sample = Memory { stall_avg10_bp: 250, ..memory() };
  // 50 ms of host stalls every two seconds: 20% of one 250 ms sample,
  // but only 2.5% sustained pressure. Resetting a five-second cooldown on
  // every spike used to starve an idle dispatcher until its 30 s deadline.
  for tick in 1..=240 {
    let spike = tick % 8 == 1;
    if spike {
      sample.stall_us += 50_000;
    }
    policy.sample(
      sample,
      now + Duration::from_millis(tick * 250),
      0,
      1,
      0,
      options,
    );
    assert_eq!(policy.open, !spike, "tick {tick}");
    assert_eq!(policy.fits(0, 9 * GIB), !spike, "tick {tick}");
    assert_eq!(policy.limit, 1);
  }
}

#[test]
fn sustained_psi_blocks_initial_admission_and_requires_recovery() {
  let options = Options::new(64);
  let now = Instant::now();
  let pressured = Memory { stall_avg10_bp: 2000, ..memory() };
  let mut policy = Policy::new(pressured, now, options);
  assert!(!policy.fits(0, GIB));
  for second in 1..=60 {
    policy.sample(
      pressured,
      now + Duration::from_secs(second),
      0,
      1,
      0,
      options,
    );
    assert!(!policy.open);
    assert_eq!(policy.reason, "psi-sustained");
  }
  // Clearing the average does not waive the cooldown, even with no workers.
  policy.sample(memory(), now + Duration::from_secs(61), 0, 1, 0, options);
  assert!(!policy.open);
  assert_eq!(policy.reason, "recovery");
  policy.sample(memory(), now + Duration::from_secs(65), 0, 1, 0, options);
  assert!(policy.fits(0, GIB));
}

#[test]
fn psi_spikes_still_back_off_and_cannot_waive_swap_recovery() {
  let options = Options::new(64);
  let now = Instant::now();
  let mut policy = Policy::new(memory(), now, options);
  let spike = Memory { stall_us: 50_000, stall_avg10_bp: 250, ..memory() };
  policy.sample(spike, now + Duration::from_millis(250), 8, 0, 0, options);
  assert!(!policy.open);
  assert_eq!(policy.reason, "psi-spike");
  assert_eq!(policy.limit, 4);
  let swapped = Memory { swap: 16 << 20, ..spike };
  policy.sample(swapped, now + Duration::from_millis(500), 0, 8, 0, options);
  assert!(!policy.open);
  assert_eq!(policy.reason, "swap-growth");
  policy.sample(swapped, now + Duration::from_secs(5), 0, 8, 0, options);
  assert!(!policy.open);
  assert_eq!(policy.reason, "recovery");
  policy.sample(swapped, now + Duration::from_millis(5500), 0, 8, 0, options);
  assert!(policy.fits(0, GIB));
}

#[test]
fn persistent_psi_timeout_identifies_pressure_not_a_lack_of_ram() {
  let pressured = Memory { stall_avg10_bp: 2000, ..memory() };
  let gate =
    Admission::with_reader(quick_options(1), Some(pressured), move || {
      Ok(pressured)
    })
    .unwrap();
  let Err(error) = gate.acquire(1) else {
    panic!("admitted during sustained pressure");
  };
  assert!(error.contains("idle timeout"));
  assert!(error.contains("waiting_for=psi-sustained"));
  assert!(error.contains("psi_avg10=20.00%"));
  assert!(error.contains("next_reservation=2 bytes"));
  assert_eq!(gate.shared.state.lock().unwrap().active, 0);
}

#[test]
fn permits_release_on_unwind_without_claiming_a_completion() {
  let gate =
    Admission::with_reader(quick_options(64), Some(memory()), || Ok(memory()))
      .unwrap();
  let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let _permit = gate.acquire(1024).unwrap();
    panic!("test unwind");
  }));
  let state = gate.shared.state.lock().unwrap();
  assert_eq!(state.active, 0);
  assert_eq!(state.reserved, 0);
  assert_eq!(state.completed, 0);
}

#[test]
fn unknown_platform_is_serial_and_wakes_after_release() {
  let gate =
    Admission::with_reader(quick_options(64), None, || unreachable!()).unwrap();
  let first = gate.acquire(1).unwrap();
  thread::scope(|scope| {
    let (tx, rx) = mpsc::channel();
    let gate = &gate;
    scope.spawn(move || {
      let _permit = gate.acquire(1).unwrap();
      tx.send(()).unwrap();
    });
    assert!(rx.recv_timeout(Duration::from_millis(20)).is_err());
    first.complete();
    rx.recv_timeout(Duration::from_secs(2)).unwrap();
  });
}

#[test]
fn oversized_reservations_fail_instead_of_bypassing_the_limit() {
  let gate =
    Admission::with_reader(quick_options(64), Some(memory()), || Ok(memory()))
      .unwrap();
  let Err(error) = gate.acquire(usize::MAX) else {
    panic!("admitted oversized shard");
  };
  assert!(error.contains("exceeds execution budget"));
  assert!(gate.check().is_err());
  assert_eq!(gate.shared.state.lock().unwrap().active, 0);
}

#[test]
fn telemetry_loss_wakes_waiters_and_is_not_success() {
  let missing = Arc::new(AtomicBool::new(false));
  let input = Arc::clone(&missing);
  let gate =
    Admission::with_reader(quick_options(1), Some(memory()), move || {
      if input.load(Ordering::SeqCst) {
        Err("test telemetry loss".into())
      } else {
        Ok(memory())
      }
    })
    .unwrap();
  let first = gate.acquire(1).unwrap();
  thread::scope(|scope| {
    let (tx, rx) = mpsc::channel();
    let gate = &gate;
    scope.spawn(move || {
      tx.send(gate.acquire(1).err()).unwrap();
    });
    missing.store(true, Ordering::SeqCst);
    assert!(
      rx.recv_timeout(Duration::from_secs(2))
        .unwrap()
        .unwrap()
        .contains("telemetry failed")
    );
    first.complete();
  });
  assert!(gate.check().is_err());
}

#[test]
fn persistent_idle_pressure_returns_a_bounded_resource_error() {
  let tight = Memory { available: 90 * GIB, ..memory() };
  let gate =
    Admission::with_reader(quick_options(64), Some(memory()), move || {
      Ok(tight)
    })
    .unwrap();
  let first = gate.acquire(5 * usize::try_from(GIB).unwrap()).unwrap();
  // Wait for an actual pressure sample, not a scheduling-sensitive sleep.
  let deadline = Instant::now() + Duration::from_secs(2);
  while gate.shared.state.lock().unwrap().policy.as_ref().unwrap().open {
    assert!(Instant::now() < deadline);
    thread::yield_now();
  }
  first.complete();
  let Err(error) = gate.acquire(5 * usize::try_from(GIB).unwrap()) else {
    panic!("admitted under pressure");
  };
  assert!(error.contains("idle timeout"));
  assert!(error.contains("waiting_for=headroom"));
  assert!(error.contains("next_reservation="));
}

#[test]
fn all_jobs_execute_once_while_admission_caps_active_records() {
  let gate =
    Admission::with_reader(Options::new(64), Some(memory()), || Ok(memory()))
      .unwrap();
  let active = AtomicUsize::new(0);
  let peak = AtomicUsize::new(0);
  let calls: Vec<_> = (0..256).map(|_| AtomicUsize::new(0)).collect();
  let pool = rayon::ThreadPoolBuilder::new().num_threads(64).build().unwrap();
  let results = gate
    .map(&pool, &vec![1024; calls.len()], |index| {
      let call = &calls[index];
      let live = active.fetch_add(1, Ordering::SeqCst) + 1;
      peak.fetch_max(live, Ordering::SeqCst);
      call.fetch_add(1, Ordering::SeqCst);
      thread::sleep(Duration::from_millis(1));
      active.fetch_sub(1, Ordering::SeqCst);
      index
    })
    .unwrap();
  assert_eq!(results, (0..calls.len()).collect::<Vec<_>>());
  assert!(peak.load(Ordering::SeqCst) <= 8);
  assert!(calls.iter().all(|c| c.load(Ordering::SeqCst) == 1));
  let state = gate.shared.state.lock().unwrap();
  assert_eq!(state.completed, 256);
  assert_eq!(state.reserved, 0);
}

#[test]
fn nested_rayon_work_runs_with_one_worker_and_with_admission_waiters() {
  use rayon::prelude::*;
  for workers in [1, 2, 64] {
    let gate =
      Admission::with_reader(Options::new(workers), Some(memory()), || {
        Ok(memory())
      })
      .unwrap();
    let pool =
      rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
    let results = gate
      .map(&pool, &[1024; 128], |index| {
        let (a, b) =
          rayon::join(|| (0..1024).into_par_iter().sum::<usize>(), || index);
        a + b
      })
      .unwrap();
    assert_eq!(
      results,
      (0..128).map(|i| 1023 * 1024 / 2 + i).collect::<Vec<_>>()
    );
  }
}

#[test]
fn dispatcher_rejects_blocking_inside_its_own_pool() {
  let gate =
    Admission::with_reader(Options::new(1), Some(memory()), || Ok(memory()))
      .unwrap();
  let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
  assert!(pool.install(|| gate.map(&pool, &[1024; 3], |_| ())).is_err());
}

#[test]
fn dispatch_stops_on_admission_failure_without_partial_success() {
  let gate =
    Admission::with_reader(Options::new(2), Some(memory()), || Ok(memory()))
      .unwrap();
  let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
  let calls = [AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0)];
  assert!(
    gate
      .map(&pool, &[1024, usize::MAX, 1024], |i| {
        calls[i].fetch_add(1, Ordering::SeqCst);
      })
      .is_err()
  );
  assert_eq!(calls[0].load(Ordering::SeqCst), 1);
  assert_eq!(calls[1].load(Ordering::SeqCst), 0);
  assert_eq!(calls[2].load(Ordering::SeqCst), 0);
  assert_eq!(gate.shared.state.lock().unwrap().active, 0);
}
