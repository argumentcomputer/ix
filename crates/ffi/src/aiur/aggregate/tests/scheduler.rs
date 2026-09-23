use std::sync::{Arc, Mutex, mpsc};
use std::time::Duration;

use super::super::{
  plan::{PlanOp, SlotSpec},
  protocol::ChildKind,
  scheduler::{Prepared, SlotWorker, run_scheduler_with},
  statement::{ShardSet, Statement, SubjectTree},
};
use super::addr;

const TIMEOUT: Duration = Duration::from_secs(30);

fn specs(ops: &[(PlanOp, usize)]) -> Vec<SlotSpec> {
  let subjects =
    SubjectTree::canonical(vec![addr("scheduler")], ShardSet::singleton(0, 1))
      .unwrap();
  let statement = Statement::new(subjects, None);
  ops
    .iter()
    .map(|(op, ram_bytes)| SlotSpec {
      op: *op,
      statement: statement.clone(),
      subject_count: 1,
      structural: false,
      kind: ChildKind::Aggr,
      shape: Some(0),
      outer_claim: vec![],
      cache_key: addr("key"),
      ram_bytes: *ram_bytes,
    })
    .collect()
}

fn plan() -> Vec<SlotSpec> {
  specs(&[
    (PlanOp::Leaf(0), 2),
    (PlanOp::Leaf(1), 9),
    (PlanOp::Join(0, 1), 100),
    (PlanOp::Leaf(2), 1),
    (PlanOp::Join(2, 3), 4),
  ])
}

fn check_children(spec: &SlotSpec, children: &[Arc<usize>]) {
  let actual: Vec<_> = children.iter().map(|child| **child).collect();
  match spec.op {
    PlanOp::Leaf(_) => assert!(actual.is_empty()),
    PlanOp::Join(left, right) => assert_eq!(actual, vec![left, right]),
  }
}

/// A worker that completes every slot while preparing it, so the fused
/// lanes run each slot on one thread as the production worker would.
struct TestWorker<'a, F> {
  specs: &'a [SlotSpec],
  run: F,
}

impl<F> SlotWorker for TestWorker<'_, F>
where
  F: Fn(usize, &[Arc<usize>]) -> Result<Arc<usize>, String> + Sync,
{
  type Staged = ();
  type Done = usize;

  fn specs(&self) -> &[SlotSpec] {
    self.specs
  }

  fn weight(&self, index: usize) -> usize {
    self.specs[index].ram_bytes
  }

  fn verify_only(&self, _index: usize) -> bool {
    false
  }

  fn cached(&self, _index: usize) -> Option<Arc<usize>> {
    None
  }

  fn prepare(
    &self,
    index: usize,
    children: &[Arc<usize>],
  ) -> Result<Prepared<(), usize>, String> {
    (self.run)(index, children).map(Prepared::Done)
  }

  fn finish(&self, _index: usize, (): ()) -> Result<Arc<usize>, String> {
    unreachable!("test slots complete while preparing")
  }
}

fn run<F>(
  plan: &[SlotSpec],
  jobs: usize,
  budget: usize,
  run: F,
) -> Result<Vec<usize>, String>
where
  F: Fn(usize, &[Arc<usize>]) -> Result<Arc<usize>, String> + Sync,
{
  let active = vec![true; plan.len()];
  let slots = run_scheduler_with(
    jobs,
    0,
    budget,
    &active,
    &TestWorker { specs: plan, run },
  )?;
  Ok(
    slots
      .into_iter()
      .map(|slot| *slot.expect("every active slot has a result"))
      .collect(),
  )
}

#[test]
fn serial_admission_is_bottom_level_first_and_dependencies_are_completed() {
  let plan = plan();
  let order = Mutex::new(Vec::new());
  let result = run(&plan, 1, 10, |index, children| {
    check_children(&plan[index], children);
    order.lock().unwrap().push(index);
    Ok(Arc::new(index))
  })
  .unwrap();
  // Leaves by index, then the joins as their children complete; the
  // over-budget join runs alone once nothing else is in flight.
  assert_eq!(*order.lock().unwrap(), vec![0, 1, 3, 2, 4]);
  assert_eq!(result, vec![0, 1, 2, 3, 4]);
}

#[test]
fn parallel_admission_respects_ram_and_runs_oversized_slots_alone() {
  let plan = plan();
  let (started_tx, started_rx) = mpsc::channel();
  let channels: Vec<_> = (0..plan.len()).map(|_| mpsc::channel()).collect();
  let (releases, receivers): (Vec<_>, Vec<_>) = channels.into_iter().unzip();
  let receivers: Vec<_> = receivers.into_iter().map(Mutex::new).collect();
  let active = Mutex::new((0usize, 0usize, 0usize)); // workers, bytes, peak workers
  std::thread::scope(|scope| {
    let scheduler = scope.spawn(|| {
      run(&plan, 2, 10, |index, children| {
        check_children(&plan[index], children);
        {
          let mut active = active.lock().unwrap();
          active.0 += 1;
          active.1 += plan[index].ram_bytes;
          active.2 = active.2.max(active.0);
          assert!(active.0 <= 2);
          assert!(active.1 <= 10 || active.0 == 1);
        }
        started_tx.send(index).unwrap();
        receivers[index].lock().unwrap().recv_timeout(TIMEOUT).unwrap();
        {
          let mut active = active.lock().unwrap();
          active.0 -= 1;
          active.1 -= plan[index].ram_bytes;
        }
        Ok(Arc::new(index))
      })
    });
    // Drop release senders even when an assertion fails, so blocked workers
    // terminate and the scoped scheduler can drain them.
    let drive = std::panic::catch_unwind(|| {
      let mut initial = vec![
        started_rx.recv_timeout(TIMEOUT).unwrap(),
        started_rx.recv_timeout(TIMEOUT).unwrap(),
      ];
      initial.sort_unstable();
      assert_eq!(initial, vec![0, 3]); // 2 + 9 does not fit; 2 + 1 does.
      releases[0].send(()).unwrap();
      assert_eq!(started_rx.recv_timeout(TIMEOUT).unwrap(), 1); // 1 + 9 fits.
      releases[3].send(()).unwrap();
      releases[1].send(()).unwrap();
      assert_eq!(started_rx.recv_timeout(TIMEOUT).unwrap(), 2); // alone
      releases[2].send(()).unwrap();
      assert_eq!(started_rx.recv_timeout(TIMEOUT).unwrap(), 4);
      releases[4].send(()).unwrap();
    });
    drop(releases);
    let result = scheduler.join().unwrap();
    drive.unwrap();
    assert_eq!(result.unwrap(), vec![0, 1, 2, 3, 4]);
  });
  assert_eq!(*active.lock().unwrap(), (0, 0, 2));
}

#[test]
fn failure_drains_admitted_workers_and_selects_the_lowest_slot_error() {
  let plan =
    specs(&[(PlanOp::Leaf(0), 5), (PlanOp::Leaf(1), 5), (PlanOp::Leaf(2), 1)]);
  let (arrived_tx, arrived_rx) = mpsc::channel();
  let arrived_rx = Mutex::new(arrived_rx);
  let (release_tx, release_rx) = mpsc::channel();
  let release_rx = Mutex::new(release_rx);
  let finished = Mutex::new(Vec::new());
  let result = run(&plan, 2, 10, |index, _| {
    assert!(index < 2, "failure must stop further admission");
    if index == 0 {
      arrived_rx.lock().unwrap().recv_timeout(TIMEOUT).unwrap();
      release_tx.send(()).unwrap();
    } else {
      arrived_tx.send(()).unwrap();
      release_rx.lock().unwrap().recv_timeout(TIMEOUT).unwrap();
    }
    finished.lock().unwrap().push(index);
    Err(format!("failure-{index}"))
  });
  assert_eq!(result.unwrap_err(), "slot 0: failure-0");
  let mut finished = finished.into_inner().unwrap();
  finished.sort_unstable();
  assert_eq!(finished, vec![0, 1]);
}

#[test]
fn worker_panics_become_errors_and_zero_budget_is_rejected() {
  let plan = plan();
  assert!(
    run(&plan, 1, 0, |_, _| panic!("must not start"))
      .unwrap_err()
      .contains("positive")
  );
  let err = run(&plan, 1, 10, |_, _| panic!("test panic")).unwrap_err();
  assert!(err.contains("slot 0: Rust proof worker panicked: test panic"));
}
