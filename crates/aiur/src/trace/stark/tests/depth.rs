//! The depth pass (Track A, H1) on the Lean example `Aiur/Examples/Depth.lean`
//! (`tests/fixtures/depth.ixa`): exact slots (`even`/`odd`, `owned`/`link`),
//! gap slots (`fib`), external slots (`run`, `top`), and a unit-returning
//! recursive function whose calls cross records.
//!
//! The fixture's recursions double their argument toward a target (`4096`,
//! or `64` for `owned`), so none is structural or a countdown and every
//! recursive circuit keeps its depth word. On `x = 2^(t - n)` they are the
//! usual functions of `n`: [`at`] and [`owned_at`] give that argument.
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

/// The argument at which `even`, `odd`, `fib` and `run` are at distance `n`
/// from their target: `2^(12 - n)`.
pub(super) fn at(n: u32) -> u64 {
  1 << (12 - n)
}

/// The argument at distance `n` (`n <= 190`, below the multiplicative order
/// `192` of `2` in Goldilocks) from `target` under `x -> x * 2`.
pub(super) fn at_distance(target: u64, n: u32) -> u64 {
  const P: u128 = 0xffff_ffff_0000_0001;
  const INV2: u128 = P.div_ceil(2);
  let mut x = u128::from(target) % P;
  for _ in 0..n {
    x = (x * INV2) % P;
  }
  u64::try_from(x).unwrap()
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
  let x = at(12);
  let record = program.execute(entry, vec![x]).unwrap();
  // At distance 12: even = 1, fib = 144.
  assert_eq!(record.output, [145]);
  let fib = program.callable_id("Depth::fib").unwrap();
  // fib at distance n calls distance n - 1 last of its intra-SCC callees:
  // height n - 1.
  assert_eq!(record.query_depth(fib, &[at(12)]), Some(11));
  assert_eq!(record.query_depth(fib, &[at(1)]), Some(0));
  let even = program.callable_id("Depth::even").unwrap();
  assert_eq!(record.query_depth(even, &[at(12)]), Some(12));
  let reference = plan.generate_reference(&record, entry, &[x], true).unwrap();
  let fast = plan.generate(&record, entry, &[x], true).unwrap();
  assert_eq!(reference, fast);
  plan.check(&record, &fast, entry, &[x]).unwrap();
  // fib at distance n >= 2 fires both gap slots: distance n - 1 with gap 0,
  // and distance n - 2 with gap 1, except at distance 2 (distance 0 has
  // height 0).
  let uses: u64 = fast.ranges.table(0).iter().sum();
  assert_eq!(uses, 2 * 11);
  assert_eq!(fast.ranges.table(0)[0], 12);
  assert_eq!(fast.ranges.table(0)[1], 10);
  assert_eq!(fast.ranges.table(1)[0], 22);

  let backend = Backend::new_below_floor(&plan, toy_parameters()).unwrap();
  let converted = backend.witness(&record, &fast).unwrap();
  let direct = backend.generate(&record, entry, &[x]).unwrap();
  for (a, b) in converted.traces.iter().zip(&direct.traces) {
    assert_eq!(a.values, b.values);
  }
  let proof = backend.prove(entry, &[x], &record.output, direct).unwrap();
  backend.verify(entry, &[x], &record.output, &proof).unwrap();
  assert!(backend.verify(entry, &[x], &[146], &proof).is_err());

  let batch = Backend::for_batch_below_floor(&plan, toy_parameters()).unwrap();
  let stage = batch.generate_stage_1(&record, entry, &[x]).unwrap();
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
        &[x],
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
      &[x],
      &record.output,
      stage,
      8,
      Retention::Retain,
    )
    .unwrap();
  assert!(proof.proofs.len() > 1);
  batch.verify_batch(entry, &[x], &record.output, &proof).unwrap();
}

/// A misclassified exact slot fails population with a clear error, rather
/// than as an unbalanced lookup at verification: `fib(x)` calls `fib(4x)`
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
  let x = at(12);
  let record = program.execute(entry, vec![x]).unwrap();
  let backend = Backend::new_below_floor(&plan, toy_parameters()).unwrap();
  let errors = [
    plan.generate_reference(&record, entry, &[x], true).err(),
    plan.generate(&record, entry, &[x], true).err(),
    backend.generate(&record, entry, &[x]).err(),
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
  let backend = Backend::new_below_floor(&plan, toy_parameters()).unwrap();
  let entry = "Depth::run";
  let fib = program.callable_id("Depth::fib").unwrap();

  // `run` at distance 2: fib rows at distances 2, 1 and 0.
  let x = at(2);
  let mut non_positive = program.execute(entry, vec![x]).unwrap();
  let row0 = non_positive.queries.tables[fib].lookup(&[at(0)]).1.unwrap();
  non_positive.queries.tables[fib].set_depth(row0, 1);
  for error in [
    plan.generate_reference(&non_positive, entry, &[x], true).err(),
    plan.generate(&non_positive, entry, &[x], true).err(),
    backend.generate(&non_positive, entry, &[x]).err(),
  ] {
    let error = error.expect("accepted non-positive depth step");
    assert!(error.contains("callee is not below its caller"), "{error}");
  }

  let mut overflow = program.execute(entry, vec![x]).unwrap();
  let row1 = overflow.queries.tables[fib].lookup(&[at(1)]).1.unwrap();
  let row2 = overflow.queries.tables[fib].lookup(&[at(2)]).1.unwrap();
  overflow.queries.tables[fib].set_depth(row1, (1 << 24) + 9);
  overflow.queries.tables[fib].set_depth(row2, (1 << 24) + 10);
  for error in [
    plan.generate_reference(&overflow, entry, &[x], true).err(),
    plan.generate(&overflow, entry, &[x], true).err(),
    backend.generate(&overflow, entry, &[x]).err(),
  ] {
    let error = error.expect("accepted overflowing depth gap");
    assert!(error.contains("exceeds 2^24"), "{error}");
  }
}

#[test]
fn recursive_entry_claims_a_depth_word() {
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend =
    Backend::for_batch_below_floor(&plan, toy_parameters()).unwrap();
  let entry = "Depth::fib";
  // fib at distance 10 is 55, at height 9.
  let x = at(10);
  let record = program.execute(entry, vec![x]).unwrap();
  assert_eq!(record.output, [55]);
  assert!(backend.claim(entry, &[x], &[55]).is_err());
  let public = plan.public_args(&record, entry, &[x]).unwrap();
  assert_eq!(public, [x, 9]);
  assert!(plan.public_args(&record, entry, &[x, 8]).is_err());
  let stage = backend.generate_stage_1(&record, entry, &public).unwrap();
  let proof = backend
    .prove_batch_stage_1(entry, &public, &[55], stage, 4, Retention::Regenerate)
    .unwrap();
  backend.verify_batch(entry, &public, &[55], &proof).unwrap();
  // The row provides this fib claim at its recorded depth word only.
  assert!(backend.verify_batch(entry, &[x, 8], &[55], &proof).is_err());
}

/// A forged trace whose only imbalance is an out-of-range gap limb must be
/// rejected: lo' = lo + 2^16, hi' = hi - 1 leaves the demanded callee depth
/// word and every other message unchanged.
#[test]
fn out_of_range_gap_limb_is_rejected_by_verifier() {
  use crate::trace::DepthSlot;
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend =
    Backend::for_batch_below_floor(&plan, toy_parameters()).unwrap();
  let entry = "Depth::run";
  let x = at(12);
  let record = program.execute(entry, vec![x]).unwrap();
  let output = record.output.clone();
  let stage = backend.generate_stage_1(&record, entry, &[x]).unwrap();
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
  // Row 0 is fib at distance 12, where both gap slots fire.
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
    .prove_batch_stage_1(entry, &[x], &output, forged, 8, Retention::Retain)
    .err()
    .expect("out-of-range gap limb accepted");
  assert!(error.contains("verification failed"), "{error}");
  backend
    .prove_batch_stage_1(entry, &[x], &output, stage, 8, Retention::Retain)
    .unwrap();
}

/// The row bound fires just above 2^39 weighted rows (with `C6` vectorized ROM
/// circuits weighted by their lane count `K`) and accepts just at or below it.
#[test]
fn row_bound_boundary() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  let key =
    VerifyingKey::from_bytes(&backend.verifying_key_bytes().unwrap()).unwrap();
  let claim = backend.claim("root", &[3], &[9]).unwrap();
  let max_log = u8::try_from(32 - parameters().log_blowup).unwrap();
  let mut weighted_rows = 0u128;
  let mut unweighted_rows = 0u128;
  let mut log_degrees = vec![];
  for circuit in &backend.system.circuits {
    let log = if circuit.preprocessed_height == 0 {
      max_log
    } else {
      u8::try_from(circuit.preprocessed_height.ilog2()).unwrap()
    };
    let h = 1u128 << log;
    unweighted_rows += h;
    weighted_rows += h * u128::from(batch::circuit_row_weight(circuit));
    log_degrees.push(log);
  }
  // Vectorized `<ROM:1>` (`K = 8`) strictly increases weighted rows over unweighted.
  assert!(weighted_rows > unweighted_rows);
  let header = multi_stark::batch::ShardHeader {
    active: vec![true; backend.system.circuits.len()],
    stage_1_trace: backend.system.preprocessed_commit.clone().unwrap(),
    log_degrees,
    claims: vec![],
  };
  let bound = 1u128 << 39;
  let at_bound = usize::try_from(bound / weighted_rows).unwrap();
  let unweighted_at_bound = usize::try_from(bound / unweighted_rows).unwrap();
  assert!(unweighted_at_bound > at_bound);
  use multi_stark::batch::BatchMessage;
  let preamble =
    |n: usize, messages: Vec<BatchMessage<GoldilocksBlake3Config>>| {
      let mut headers = vec![header.clone(); n];
      headers[0].claims = vec![claim.clone()];
      multi_stark::batch::BatchPreamble { headers, messages }
    };
  key.validate_preamble(&claim, &preamble(at_bound, vec![])).unwrap();
  let error =
    key.validate_preamble(&claim, &preamble(at_bound + 1, vec![])).unwrap_err();
  assert!(error.contains("2^39"), "{error}");
  // Unweighted shard count that previously slipped past 2^39 under C6 is rejected.
  assert!(
    key
      .validate_preamble(&claim, &preamble(unweighted_at_bound, vec![]))
      .is_err()
  );

  // Closure-pair hardening (HIGH-1): reject empty `a == b`, unknown ROM width,
  // and excess pairs > shards * rom_widths.
  let mk_pair = |w: u64, a: u64, b: u64| {
    [
      BatchMessage::pull(vec![
        Val::from_u64(MEMSEG),
        Val::from_u64(w),
        Val::from_u64(a),
      ]),
      BatchMessage::push(vec![
        Val::from_u64(MEMSEG),
        Val::from_u64(w),
        Val::from_u64(b),
      ]),
    ]
  };
  // Valid strict interval on known width 1 succeeds.
  key
    .validate_preamble(&claim, &preamble(1, mk_pair(1, 0, 5).to_vec()))
    .unwrap();
  // Empty `a == b` interval rejected.
  assert!(
    key
      .validate_preamble(&claim, &preamble(1, mk_pair(1, 0, 0).to_vec()))
      .is_err()
  );
  assert!(
    key
      .validate_preamble(&claim, &preamble(1, mk_pair(1, 7, 7).to_vec()))
      .is_err()
  );
  // Unknown ROM width (99) rejected.
  assert!(
    key
      .validate_preamble(&claim, &preamble(1, mk_pair(99, 0, 5).to_vec()))
      .is_err()
  );
  // Too many pairs for 1 shard & 1 ROM width rejected.
  let two_pairs: Vec<_> =
    mk_pair(1, 0, 5).into_iter().chain(mk_pair(1, 5, 10)).collect();
  assert!(
    key.validate_preamble(&claim, &preamble(1, two_pairs.clone())).is_err()
  );
  // With 2 shards & 1 ROM width, 2 disjoint pairs succeed.
  key.validate_preamble(&claim, &preamble(2, two_pairs)).unwrap();
}
