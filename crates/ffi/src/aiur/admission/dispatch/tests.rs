use super::*;
use crate::aiur::admission::{
  Options,
  tests::{memory, quick_options},
};
use std::sync::{
  Mutex,
  atomic::{AtomicBool, AtomicUsize, Ordering},
};
use std::time::Duration;

fn pool(workers: usize) -> rayon::ThreadPool {
  rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap()
}

struct Dropped<'a>(&'a AtomicBool);
impl Drop for Dropped<'_> {
  fn drop(&mut self) {
    self.0.store(true, Ordering::SeqCst);
  }
}

#[test]
fn children_run_before_an_unrelated_slow_attempt_finishes() {
  let gate = Admission::for_test(2);
  let pool = pool(2);
  let (slow_tx, slow_rx) = mpsc::channel();
  let (child_tx, child_rx) = mpsc::channel();
  let slow_rx = Mutex::new(slow_rx);
  let child_rx = Mutex::new(child_rx);
  let parent_dropped = AtomicBool::new(false);
  let mut finished = Vec::new();
  gate
    .dispatch(
      &pool,
      vec![0, 1],
      |_| 1024,
      |&task| {
        match task {
          0 => {
            let _record = Dropped(&parent_dropped);
            slow_rx
              .lock()
              .unwrap()
              .recv_timeout(Duration::from_secs(3))
              .unwrap();
          },
          1 => {
            slow_tx.send(()).unwrap();
            child_rx
              .lock()
              .unwrap()
              .recv_timeout(Duration::from_secs(3))
              .unwrap();
          },
          2 => {
            assert!(parent_dropped.load(Ordering::SeqCst));
            child_tx.send(()).unwrap();
          },
          _ => unreachable!(),
        }
        Ok(())
      },
      |task, ()| {
        finished.push(task);
        if task == 0 {
          assert!(parent_dropped.load(Ordering::SeqCst));
          assert_eq!(gate.shared.state.lock().unwrap().active, 1);
          Ok(Followups::Ready(vec![2]))
        } else {
          Ok(Followups::Ready(Vec::new()))
        }
      },
    )
    .unwrap();
  finished.sort_unstable();
  assert_eq!(finished, [0, 1, 2]);
  assert_eq!(gate.shared.state.lock().unwrap().reserved, 0);
}

#[test]
fn shared_pressure_closes_admission_until_peers_drain_then_retries_first() {
  let gate = Admission::for_test(2);
  let (started_tx, started_rx) = mpsc::channel();
  let (release_tx, release_rx) = mpsc::channel();
  let started_rx = Mutex::new(started_rx);
  let release_rx = Mutex::new(release_rx);
  let slow_dropped = AtomicBool::new(false);
  let ordinary_started = AtomicBool::new(false);
  let starts = Mutex::new(Vec::new());
  gate
    .dispatch(
      &pool(2),
      vec![(0, false), (1, false), (2, false)],
      |_| 1,
      |&(task, retry)| {
        starts.lock().unwrap().push((task, retry));
        match (task, retry) {
          (0, false) => {
            started_rx
              .lock()
              .unwrap()
              .recv_timeout(Duration::from_secs(3))
              .unwrap();
          },
          (0, true) => assert!(slow_dropped.load(Ordering::SeqCst)),
          (1, _) => {
            let _record = Dropped(&slow_dropped);
            started_tx.send(()).unwrap();
            release_rx
              .lock()
              .unwrap()
              .recv_timeout(Duration::from_secs(3))
              .unwrap();
            assert!(!ordinary_started.load(Ordering::SeqCst));
          },
          (2, _) => {
            ordinary_started.store(true, Ordering::SeqCst);
          },
          _ => unreachable!(),
        }
        Ok(())
      },
      |(task, retry), ()| {
        if task == 0 && !retry {
          release_tx.send(()).unwrap();
          Ok(Followups::AfterDrain((task, true)))
        } else {
          Ok(Followups::Ready(Vec::new()))
        }
      },
    )
    .unwrap();
  let starts = starts.into_inner().unwrap();
  assert_eq!(starts.len(), 4);
  assert!(
    starts.iter().position(|&t| t == (1, false)).unwrap()
      < starts.iter().position(|&t| t == (0, true)).unwrap()
  );
  assert_eq!(gate.shared.state.lock().unwrap().reserved, 0);
}

#[test]
fn recursive_queue_and_nested_rayon_work_complete_once_at_all_pool_widths() {
  use rayon::prelude::*;
  for workers in [1, 2, 64] {
    let gate = Admission::for_test(workers);
    let calls: Vec<_> = (0..127).map(|_| AtomicUsize::new(0)).collect();
    let mut results = Vec::new();
    gate
      .dispatch(
        &pool(workers),
        vec![0usize],
        |_| 1024,
        |&task| {
          calls[task].fetch_add(1, Ordering::SeqCst);
          let (sum, index) =
            rayon::join(|| (0..100).into_par_iter().sum::<usize>(), || task);
          Ok(sum + index)
        },
        |task, result| {
          results.push((task, result));
          Ok(Followups::Ready(if task < 63 {
            vec![2 * task + 1, 2 * task + 2]
          } else {
            vec![]
          }))
        },
      )
      .unwrap();
    results.sort_unstable();
    assert_eq!(results, (0..127).map(|i| (i, 4950 + i)).collect::<Vec<_>>());
    assert!(calls.iter().all(|n| n.load(Ordering::SeqCst) == 1));
    let state = gate.shared.state.lock().unwrap();
    assert_eq!((state.active, state.reserved, state.completed), (0, 0, 127));
  }
}

#[test]
fn worker_error_panic_and_callback_error_join_and_release_permits() {
  for failure in ["error", "panic", "callback"] {
    let gate = Admission::for_test(2);
    let dropped = AtomicBool::new(false);
    let result = gate.dispatch(
      &pool(2),
      vec![0],
      |_| 1024,
      |_| {
        let _record = Dropped(&dropped);
        match failure {
          "error" => Err("worker failure".into()),
          "panic" => panic!("test worker panic"),
          _ => Ok(()),
        }
      },
      |_, ()| Err::<Followups<usize>, _>("callback failure".into()),
    );
    assert!(result.is_err());
    assert!(dropped.load(Ordering::SeqCst));
    let state = gate.shared.state.lock().unwrap();
    assert_eq!(state.active, 0);
    assert_eq!(state.reserved, 0);
    assert_eq!(state.completed, usize::from(failure == "callback"));
  }
}

#[test]
fn queued_oversize_and_telemetry_failure_never_return_partial_success() {
  let gate = Admission::for_test(2);
  let calls = AtomicUsize::new(0);
  let result = gate.dispatch(
    &pool(2),
    vec![0, 1],
    |&task| if task == 0 { 1 } else { usize::MAX },
    |_| {
      calls.fetch_add(1, Ordering::SeqCst);
      Ok(())
    },
    |_, ()| Ok(Followups::Ready(Vec::new())),
  );
  assert!(result.unwrap_err().contains("exceeds execution budget"));
  assert_eq!(calls.load(Ordering::SeqCst), 1);
  assert_eq!(gate.shared.state.lock().unwrap().active, 0);

  let gate = Admission::with_reader(quick_options(1), Some(memory()), || {
    Err("lost telemetry".into())
  })
  .unwrap();
  let result = gate.dispatch(
    &pool(1),
    vec![0, 1],
    |_| 1,
    |_| {
      let deadline = std::time::Instant::now() + Duration::from_secs(3);
      while gate.check().is_ok() {
        assert!(std::time::Instant::now() < deadline);
        std::thread::yield_now();
      }
      Ok(())
    },
    |_, ()| Ok(Followups::Ready(Vec::new())),
  );
  assert!(result.unwrap_err().contains("telemetry failed"));
  assert_eq!(gate.shared.state.lock().unwrap().reserved, 0);
}

#[test]
fn completion_is_observed_even_when_the_next_reservation_is_blocked() {
  let gate = Admission::with_reader(
    Options { tick: Duration::from_secs(10), ..Options::new(2) },
    Some(memory()),
    || Ok(memory()),
  )
  .unwrap();
  // Close live admission while the first task is running. The coordinator must
  // consume its result without waiting for a future telemetry recovery.
  let calls = AtomicUsize::new(0);
  let result = gate.dispatch(
    &pool(2),
    vec![0, 1],
    |_| 100 * (1 << 30),
    |_| {
      calls.fetch_add(1, Ordering::SeqCst);
      gate.shared.state.lock().unwrap().policy.as_mut().unwrap().open = false;
      Ok(())
    },
    |_, ()| Err::<Followups<usize>, _>("observed completion".into()),
  );
  assert_eq!(result.unwrap_err(), "observed completion");
  assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn dispatcher_rejects_its_pool_and_idle_pressure_has_a_deadline() {
  let gate = Admission::for_test(1);
  let pool = pool(1);
  assert!(
    pool
      .install(|| gate.dispatch(
        &pool,
        vec![0],
        |_| 1,
        |_| Ok(()),
        |_, ()| Ok(Followups::Ready(Vec::new()))
      ))
      .is_err()
  );
  let tight = crate::aiur::memory::Memory { available: 0, ..memory() };
  let gate =
    Admission::with_reader(quick_options(1), Some(tight), move || Ok(tight))
      .unwrap();
  let estimates = AtomicUsize::new(0);
  assert!(
    gate
      .dispatch(
        &pool,
        vec![0],
        |_| {
          estimates.fetch_add(1, Ordering::SeqCst);
          0
        },
        |_| panic!("admitted without memory"),
        |_, ()| Ok(Followups::Ready(Vec::new()))
      )
      .unwrap_err()
      .contains("idle timeout")
  );
  assert_eq!(
    estimates.load(Ordering::SeqCst),
    1,
    "a blocked head must not rescan its ownership on every admission tick"
  );
}

#[test]
fn early_coordinator_failure_joins_every_outstanding_worker() {
  let workers = 8;
  let gate = Admission::for_test(workers);
  let rendezvous = (Mutex::new(0), std::sync::Condvar::new());
  let returned = AtomicUsize::new(0);
  let calls = AtomicUsize::new(0);
  let result = gate.dispatch(
    &pool(workers),
    (0..100).collect(),
    |_| 1,
    |_| {
      calls.fetch_add(1, Ordering::SeqCst);
      let mut started = rendezvous.0.lock().unwrap();
      *started += 1;
      rendezvous.1.notify_all();
      let (started, _) = rendezvous
        .1
        .wait_timeout_while(started, Duration::from_secs(3), |n| *n < workers)
        .unwrap();
      assert_eq!(
        *started, workers,
        "dispatcher failed to admit the initial cohort"
      );
      drop(started);
      returned.fetch_add(1, Ordering::SeqCst);
      Ok(())
    },
    |_, ()| Err::<Followups<usize>, _>("stop coordinator".into()),
  );
  assert_eq!(result.unwrap_err(), "stop coordinator");
  assert_eq!(calls.load(Ordering::SeqCst), workers);
  assert_eq!(returned.load(Ordering::SeqCst), workers);
  let state = gate.shared.state.lock().unwrap();
  assert_eq!((state.active, state.reserved), (0, 0));
}

#[test]
fn unknown_telemetry_stays_serial_and_empty_work_is_a_noop() {
  let gate =
    Admission::with_reader(quick_options(64), None, || unreachable!()).unwrap();
  let pool = pool(64);
  let active = AtomicUsize::new(0);
  let peak = AtomicUsize::new(0);
  gate
    .dispatch(
      &pool,
      (0..32).collect(),
      |_| 1024,
      |_| {
        let n = active.fetch_add(1, Ordering::SeqCst) + 1;
        peak.fetch_max(n, Ordering::SeqCst);
        std::thread::yield_now();
        active.fetch_sub(1, Ordering::SeqCst);
        Ok(())
      },
      |_, ()| Ok(Followups::Ready(Vec::<usize>::new())),
    )
    .unwrap();
  assert_eq!(peak.load(Ordering::SeqCst), 1);
  gate
    .dispatch(
      &pool,
      Vec::<usize>::new(),
      |_| panic!("estimated empty work"),
      |_| Err::<(), _>("executed empty work".into()),
      |_, ()| panic!("completed empty work"),
    )
    .unwrap();
  assert_eq!(gate.shared.state.lock().unwrap().completed, 32);
}
