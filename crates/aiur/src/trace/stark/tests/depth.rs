//! The depth pass (Track A, H1) on the Lean example `Aiur/Examples/Depth.lean`
//! (`tests/fixtures/depth.ixa`): exact slots (`even`/`odd`, `owned`/`link`),
//! gap slots (`fib`), external slots (`run`, `top`), and a unit-returning
//! recursive function whose calls cross records.
use super::*;
use crate::execute::{Partition, owned_heights};
use multi_stark::batch::Retention;

pub(super) fn depth_fixture() -> (CheckedProgram, TraceArtifact) {
  let (program, trace) = crate::artifact::Package::decode(include_bytes!(
    concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/depth.ixa")
  ))
  .and_then(crate::artifact::Package::traced)
  .unwrap();
  let mut program = program.check().unwrap();
  program.track_depth(&trace).unwrap();
  (program, trace)
}

fn chip<'t>(trace: &'t TraceArtifact, name: &str) -> &'t crate::trace::Chip {
  trace.chips.iter().find(|c| c.name == name).unwrap()
}

#[test]
fn fixture_exercises_every_slot_kind() {
  use crate::trace::DepthSlot;
  let (program, trace) = depth_fixture();
  assert_eq!(trace.limbs, [16, 8]);
  let slots: Vec<_> =
    trace.chips.iter().flat_map(|c| c.depth.slots.iter().copied()).collect();
  assert!(slots.contains(&DepthSlot::Exact));
  assert!(slots.iter().any(|s| matches!(s, DepthSlot::Gap { .. })));
  assert!(slots.iter().any(|s| matches!(s, DepthSlot::External { .. })));
  for name in ["Depth::loop", "Depth::even", "Depth::odd", "Depth::fib"] {
    assert!(chip(&trace, name).depth.column.is_some(), "{name}");
  }
  for name in ["Depth::run", "Depth::top"] {
    assert!(chip(&trace, name).depth.column.is_none(), "{name}");
  }
  // Mutual recursion shares an SCC; separate SCCs have separate ranks.
  let rank = |name| chip(&trace, name).depth.rank;
  assert_eq!(rank("Depth::even"), rank("Depth::odd"));
  assert_ne!(rank("Depth::even"), rank("Depth::fib"));
  // The range maps follow every original callable.
  let maps: Vec<_> =
    program.program().maps.iter().map(|m| m.name.as_str()).collect();
  assert_eq!(maps, ["Depth::range16", "Depth::range8"]);
  // A plan needs a program that records heights.
  let untracked = program.program().clone().check().unwrap();
  assert!(TracePlan::new(&untracked, trace).is_err());
}

#[test]
fn honest_recursion_proves_through_every_slot_kind() {
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let entry = "Depth::run";
  let record = program.execute(entry, vec![12]).unwrap();
  // even(12) = 1, fib(12) = 144.
  assert_eq!(record.output, [145]);
  let fib = program.callable_id("Depth::fib").unwrap();
  // fib(n) calls fib(n - 1) last of its intra-SCC callees: height n - 1.
  assert_eq!(record.query_depth(fib, &[12]), Some(11));
  assert_eq!(record.query_depth(fib, &[1]), Some(0));
  let even = program.callable_id("Depth::even").unwrap();
  assert_eq!(record.query_depth(even, &[12]), Some(12));
  let reference = plan.generate_reference(&record, entry, &[12], true).unwrap();
  let fast = plan.generate(&record, entry, &[12], true).unwrap();
  assert_eq!(reference, fast);
  plan.check(&record, &fast, entry, &[12]).unwrap();
  // fib(n) for n >= 2 fires both gap slots: fib(n - 1) with gap 0, and
  // fib(n - 2) with gap 1, except fib(2) (fib(0) has height 0).
  let uses: u64 = fast.ranges.table(0).iter().sum();
  assert_eq!(uses, 2 * 11);
  assert_eq!(fast.ranges.table(0)[0], 12);
  assert_eq!(fast.ranges.table(0)[1], 10);
  assert_eq!(fast.ranges.table(1)[0], 22);

  let backend = Backend::new(&plan, parameters()).unwrap();
  let converted = backend.witness(&record, &fast).unwrap();
  let direct = backend.generate(&record, entry, &[12]).unwrap();
  for (a, b) in converted.traces.iter().zip(&direct.traces) {
    assert_eq!(a.values, b.values);
  }
  let proof = backend.prove(entry, &[12], &record.output, direct).unwrap();
  backend.verify(entry, &[12], &record.output, &proof).unwrap();
  assert!(backend.verify(entry, &[12], &[146], &proof).is_err());

  let batch = Backend::for_batch(&plan, parameters()).unwrap();
  let stage = batch.generate_stage_1(&record, entry, &[12]).unwrap();
  // A wrong depth word in a fib row breaks the balance.
  let ci = batch.names.iter().position(|n| n == "Depth::fib").unwrap();
  let column = batch.placements[plan.members[fib]].columns
    [chip(&plan.artifact, "Depth::fib").depth.column.unwrap()];
  let mut forged = stage.clone();
  forged[ci].values[column] += Val::ONE;
  assert!(
    batch
      .prove_batch_stage_1(
        entry,
        &[12],
        &record.output,
        forged,
        8,
        Retention::Retain
      )
      .is_err()
  );
  let proof = batch
    .prove_batch_stage_1(
      entry,
      &[12],
      &record.output,
      stage,
      8,
      Retention::Retain,
    )
    .unwrap();
  assert!(proof.proofs.len() > 1);
  batch.verify_batch(entry, &[12], &record.output, &proof).unwrap();
}

#[test]
fn recursive_entry_claims_a_depth_word() {
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let entry = "Depth::fib";
  let record = program.execute(entry, vec![10]).unwrap();
  assert_eq!(record.output, [55]);
  assert!(backend.claim(entry, &[10], &[55]).is_err());
  let public = plan.public_args(&record, entry, &[10]).unwrap();
  assert_eq!(public, [10, 9]);
  assert!(plan.public_args(&record, entry, &[10, 8]).is_err());
  let stage = backend.generate_stage_1(&record, entry, &public).unwrap();
  let proof = backend
    .prove_batch_stage_1(entry, &public, &[55], stage, 4, Retention::Regenerate)
    .unwrap();
  backend.verify_batch(entry, &public, &[55], &proof).unwrap();
  // The row provides fib(10) at its recorded depth word only.
  assert!(backend.verify_batch(entry, &[10, 8], &[55], &proof).is_err());
}

#[test]
fn owned_heights_are_longest_paths_over_records() {
  let base: FxHashMap<u32, u64> =
    [(0, 0), (1, 2), (2, 1), (3, 5)].into_iter().collect();
  let heights =
    owned_heights(&base, &[(1, 0, 2), (2, 1, 2), (3, 0, 1)]).unwrap();
  assert_eq!(heights[&0], 0);
  assert_eq!(heights[&1], 2);
  assert_eq!(heights[&2], 4);
  assert_eq!(heights[&3], 5);
  // A shared DAG is fine; a cycle, or an edge to an unowned call, is not.
  assert!(
    owned_heights(&base, &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)]).is_ok()
  );
  assert!(owned_heights(&base, &[(0, 1, 1), (1, 2, 1), (2, 1, 1)]).is_err());
  assert!(owned_heights(&base, &[(0, 0, 1)]).is_err());
  assert!(owned_heights(&base, &[(0, 9, 1)]).is_err());
}

/// `top(6)` calls `owned(6)`, which recurses through `link` down to
/// `owned(0)`: `owned(n)` has height `2n`. Record A owns 6, 3, 2, 1 and 0;
/// record B owns 5 and 4, so each record defers one call to the other and
/// heights must cross records twice (design §9).
#[test]
fn deferred_heights_cross_records() {
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let owned = program.callable_id("Depth::owned").unwrap();
  let hints = program.prepare_hints(&[]).unwrap();
  let owners: [Vec<u64>; 2] = [vec![6, 3, 2, 1, 0], vec![5, 4]];
  let execute = |worker: usize, heights| {
    hints
      .execute_partition(
        (worker == 0).then(|| ("Depth::top", vec![6])),
        Partition {
          function: owned,
          owned: owners[worker].iter().map(|&n| vec![n]).collect(),
          memory_start: 100 * worker as u64,
          memory_end: 100 * (worker as u64 + 1),
          heights,
        },
        None,
      )
      .unwrap()
  };
  // First pass: base heights ignore deferred calls; edges carry offsets.
  let first = [execute(0, None), execute(1, None)];
  assert_eq!(first[0].query_depth(owned, &[6]), Some(1));
  assert_eq!(first[0].query_depth(owned, &[3]), Some(6));
  assert_eq!(first[1].query_depth(owned, &[5]), Some(3));
  let mut base = FxHashMap::default();
  let mut edges = vec![];
  for (worker, record) in first.iter().enumerate() {
    for &n in &owners[worker] {
      base.insert(vec![n], record.query_depth(owned, &[n]).unwrap());
    }
    for (a, b, w) in record.partition_offsets() {
      assert_eq!(w, 2);
      edges.push((a.to_vec(), b.to_vec(), w));
    }
  }
  let heights = owned_heights(&base, &edges).unwrap();
  for n in 0..=6 {
    assert_eq!(heights[&vec![n]], 2 * n, "owned({n})");
  }
  // Second pass: each record learns its deferred calls' heights.
  let supply = |worker: usize| {
    first[worker]
      .deferred_calls()
      .map(|(key, _)| (key.to_vec(), heights[key]))
      .collect::<FxHashMap<_, _>>()
  };
  let mut records = [execute(0, Some(supply(0))), execute(1, Some(supply(1)))];
  for (worker, record) in records.iter().enumerate() {
    for &n in &owners[worker] {
      assert_eq!(record.query_depth(owned, &[n]), Some(2 * n));
    }
  }
  // Without the heights, the replay cannot know its callers' depths.
  assert!(
    hints
      .execute_partition(
        Some(("Depth::top", vec![6])),
        Partition {
          function: owned,
          owned: owners[0].iter().map(|&n| vec![n]).collect(),
          memory_start: 0,
          memory_end: 100,
          heights: Some(Default::default()),
        },
        None,
      )
      .is_err()
  );
  for worker in 0..2 {
    let deferred: Vec<_> = records[1 - worker]
      .deferred_calls()
      .map(|(k, n)| (k.to_vec(), n))
      .collect();
    for (key, count) in deferred {
      records[worker].absorb_deferred(owned, &key, count).unwrap();
    }
  }
  let shapes = [
    backend.record_shape(&records[0]).unwrap(),
    backend.record_shape(&records[1]).unwrap(),
  ];
  let intervals: Vec<_> =
    shapes.iter().flat_map(|s| s.memory_intervals.clone()).collect();
  let traces = [
    backend.generate_stage_1(&records[0], "Depth::top", &[6]).unwrap(),
    backend.generate_record_stage_1(&records[1]).unwrap(),
  ];
  let proof = backend
    .prove_streamed_stage_1(
      "Depth::top",
      &[6],
      &[7],
      StreamPlan {
        shards: 2,
        memory_intervals: intervals,
        retention: Retention::Retain,
      },
      |i| Ok(traces[i].clone()),
    )
    .unwrap();
  backend.verify_batch("Depth::top", &[6], &[7], &proof).unwrap();
}
