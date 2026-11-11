//! The depth pass (Track A, H1) on the Lean example `Aiur/Examples/Depth.lean`
//! (`tests/fixtures/depth.ixa`): exact slots (`even`/`odd`, `owned`/`link`),
//! gap slots (`fib`), external slots (`run`, `top`), and a unit-returning
//! recursive function whose calls cross records.
use super::*;
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

/// A misclassified exact slot fails population with a clear error, rather
/// than as an unbalanced lookup at verification: `fib(n)` calls `fib(n - 2)`
/// two below itself.
#[test]
fn misclassified_exact_slot_fails_population() {
  use crate::trace::DepthSlot;
  let (program, mut trace) = depth_fixture();
  let fib = trace.chips.iter_mut().find(|c| c.name == "Depth::fib").unwrap();
  for slot in &mut fib.depth.slots {
    if matches!(slot, DepthSlot::Gap { .. }) {
      *slot = DepthSlot::Exact;
    }
  }
  let plan = TracePlan::new(&program, trace).unwrap();
  let entry = "Depth::run";
  let record = program.execute(entry, vec![12]).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let errors = [
    plan.generate_reference(&record, entry, &[12], true).err(),
    plan.generate(&record, entry, &[12], true).err(),
    backend.generate(&record, entry, &[12]).err(),
  ];
  for error in errors {
    let error = error.expect("population accepted a misclassified slot");
    assert!(error.contains("exact depth slot into Depth::fib"), "{error}");
  }
}

#[test]
fn invalid_gap_and_limb_bounds_are_rejected() {
  let (program, mut wide_trace) = depth_fixture();
  wide_trace.limbs = vec![16, 16];
  assert!(TracePlan::new(&program, wide_trace).is_err());

  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  let entry = "Depth::run";
  let fib = program.callable_id("Depth::fib").unwrap();

  let mut non_positive = program.execute(entry, vec![2]).unwrap();
  let row0 = non_positive.queries.tables[fib].lookup(&[0]).1.unwrap();
  non_positive.queries.tables[fib].set_depth(row0, 1);
  for error in [
    plan.generate_reference(&non_positive, entry, &[2], true).err(),
    plan.generate(&non_positive, entry, &[2], true).err(),
    backend.generate(&non_positive, entry, &[2]).err(),
  ] {
    let error = error.expect("accepted non-positive depth step");
    assert!(error.contains("callee is not below its caller"), "{error}");
  }

  let mut overflow = program.execute(entry, vec![2]).unwrap();
  let row1 = overflow.queries.tables[fib].lookup(&[1]).1.unwrap();
  let row2 = overflow.queries.tables[fib].lookup(&[2]).1.unwrap();
  overflow.queries.tables[fib].set_depth(row1, (1 << 24) + 9);
  overflow.queries.tables[fib].set_depth(row2, (1 << 24) + 10);
  for error in [
    plan.generate_reference(&overflow, entry, &[2], true).err(),
    plan.generate(&overflow, entry, &[2], true).err(),
    backend.generate(&overflow, entry, &[2]).err(),
  ] {
    let error = error.expect("accepted overflowing depth gap");
    assert!(error.contains("exceeds 2^24"), "{error}");
  }
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
fn out_of_range_gap_limb_is_rejected_by_verifier() {
  use crate::trace::DepthSlot;
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let entry = "Depth::run";
  let record = program.execute(entry, vec![12]).unwrap();
  let output = record.output.clone();
  let stage = backend.generate_stage_1(&record, entry, &[12]).unwrap();
  let fib = program.callable_id("Depth::fib").unwrap();
  let chip =
    plan.artifact.chips.iter().find(|c| c.name == "Depth::fib").unwrap();
  let column = chip
    .depth
    .slots
    .iter()
    .find_map(|s| match s {
      DepthSlot::Gap { column } => Some(*column),
      _ => None,
    })
    .unwrap();
  assert_eq!(plan.artifact.limbs, [16, 8]);
  let ci = backend.names.iter().position(|n| n == "Depth::fib").unwrap();
  let placement = &backend.placements[plan.members[fib]];
  let (lo_col, hi_col) =
    (placement.columns[column], placement.columns[column + 1]);
  // Row 0 is fib(12), where both gap slots fire.
  let lo = stage[ci].values[lo_col];
  let hi = stage[ci].values[hi_col];
  let mut forged = stage.clone();
  forged[ci].values[lo_col] = lo + Val::from_u64(1 << 16);
  forged[ci].values[hi_col] = hi - Val::ONE;
  // Keep the range-table counts balanced, so that only the two out-of-range
  // demands are left unmatched.
  for (name, value) in [
    ("<table:Depth::range16_inputs>", lo),
    ("<table:Depth::range8_inputs>", hi),
  ] {
    let t = backend.names.iter().position(|n| n == name).unwrap();
    assert_eq!(backend.system.circuits[t].main_width, 1);
    let row = usize::try_from(value.as_canonical_u64()).unwrap();
    assert!(forged[t].values[row] != Val::ZERO);
    forged[t].values[row] -= Val::ONE;
  }
  let error = backend
    .prove_batch_stage_1(entry, &[12], &output, forged, 8, Retention::Retain)
    .err()
    .expect("out-of-range gap limb accepted");
  assert!(error.contains("verification failed"), "{error}");
  backend
    .prove_batch_stage_1(entry, &[12], &output, stage, 8, Retention::Retain)
    .unwrap();
}

/// The row bound fires just above 2^39 rows and accepts just at or below it.
#[test]
fn row_bound_boundary() {
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let entry = "Depth::run";
  let record = program.execute(entry, vec![12]).unwrap();
  let output = record.output.clone();
  let stage = backend.generate_stage_1(&record, entry, &[12]).unwrap();
  let proof = backend
    .prove_batch_stage_1(
      entry,
      &[12],
      &output,
      stage,
      1 << 8,
      Retention::Retain,
    )
    .unwrap();
  let key =
    VerifyingKey::from_bytes(&backend.verifying_key_bytes().unwrap()).unwrap();
  let claim = backend.claim(entry, &[12], &output).unwrap();
  key.validate_preamble(&claim, &proof.preamble).unwrap();
  let mut header = proof.preamble.headers[0].clone();
  let max_log = u8::try_from(32 - parameters().log_blowup).unwrap();
  let mut rows = 0u128;
  let mut logs = header.log_degrees.clone().into_iter();
  let mut new_logs = vec![];
  for (circuit, &on) in backend.system.circuits.iter().zip(&header.active) {
    if !on {
      continue;
    }
    let log = logs.next().unwrap();
    let log = if circuit.preprocessed_height == 0 { max_log } else { log };
    rows += 1u128 << log;
    new_logs.push(log);
  }
  header.log_degrees = new_logs;
  let claims = header.claims.clone();
  header.claims.clear();
  let bound = 1u128 << 39;
  let at_bound = usize::try_from(bound / rows).unwrap();
  let preamble = |n: usize| {
    let mut p = proof.preamble.clone();
    p.headers = vec![header.clone(); n];
    p.headers[0].claims = claims.clone();
    p
  };
  key.validate_preamble(&claim, &preamble(at_bound)).unwrap();
  let error =
    key.validate_preamble(&claim, &preamble(at_bound + 1)).unwrap_err();
  assert!(error.contains("2^39"), "{error}");
}
