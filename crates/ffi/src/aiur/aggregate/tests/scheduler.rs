use std::sync::{Arc, Mutex, mpsc};
use std::time::Duration;

use super::super::{
  plan::{PlanOp, SlotSpec},
  protocol::ChildKind,
  scheduler::run_scheduler_with,
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

#[test]
fn serial_admission_is_heaviest_first_and_dependencies_are_completed() {
  let plan = plan();
  let order = Mutex::new(Vec::new());
  let result = run_scheduler_with(&plan, 1, 10, |index, children| {
    check_children(&plan[index], children);
    order.lock().unwrap().push(index);
    Ok(Arc::new(index))
  })
  .unwrap();
  assert_eq!(*order.lock().unwrap(), vec![1, 0, 2, 3, 4]);
  assert_eq!(
    result.iter().map(|value| **value).collect::<Vec<_>>(),
    vec![0, 1, 2, 3, 4]
  );
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
      run_scheduler_with(&plan, 2, 10, |index, children| {
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
      assert_eq!(initial, vec![1, 3]); // 9 + 1 fits; 9 + 2 does not.
      releases[1].send(()).unwrap();
      assert_eq!(started_rx.recv_timeout(TIMEOUT).unwrap(), 0);
      releases[0].send(()).unwrap();
      releases[3].send(()).unwrap();
      assert_eq!(started_rx.recv_timeout(TIMEOUT).unwrap(), 2);
      releases[2].send(()).unwrap();
      assert_eq!(started_rx.recv_timeout(TIMEOUT).unwrap(), 4);
      releases[4].send(()).unwrap();
    });
    drop(releases);
    let result = scheduler.join().unwrap();
    drive.unwrap();
    assert_eq!(
      result.unwrap().iter().map(|value| **value).collect::<Vec<_>>(),
      vec![0, 1, 2, 3, 4]
    );
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
  let result = run_scheduler_with::<usize>(&plan, 2, 10, |index, _| {
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
    run_scheduler_with::<usize>(&plan, 1, 0, |_, _| panic!("must not start"))
      .unwrap_err()
      .contains("positive")
  );
  let err =
    run_scheduler_with::<usize>(&plan, 1, 10, |_, _| panic!("test panic"))
      .unwrap_err();
  assert!(err.contains("slot 1: Rust proof worker panicked: test panic"));
}
