use super::*;
use crate::{
  ixby::{
    bits::{fill_words, read_words},
    io::{InputLayout, LayoutEmitter},
  },
  sizing::CountingEmitter,
};
use flock_prover::circuit::builder::{CircuitShape, ShapeBuilder};

fn f(value: u64) -> F128 {
  F128::new(value, 0)
}

#[test]
fn linked_match_checks_every_bit_of_both_records_without_fingerprints() {
  for words in [1, 24, 30] {
    let gate = OrderGate::new(3, OrderKind::Match(words)).unwrap();
    let width = words + 2;
    let record =
      (0..width).map(|i| F128::new(i as u64, !(i as u64))).collect::<Vec<_>>();
    let input = record.iter().chain(&record).copied().collect::<Vec<_>>();
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| fill_words(&input, bits));
    assert_eq!(read_words(&bits, 2 * width, width), vec![F128::ZERO; width]);
    let table = gate.r1cs();
    bits.resize(table.n(), false);
    assert!(table.satisfies(&bits));
    for bit in 0..width * 128 {
      let constraint = 2 * width * 128 + bit;
      for changed in [bit, width * 128 + bit, constraint] {
        bits[changed] ^= true;
        let parity =
          |columns: &[usize]| columns.iter().fold(false, |s, &c| s ^ bits[c]);
        assert_ne!(
          parity(&table.a_0.rows[constraint])
            & parity(&table.b_0.rows[constraint]),
          bits[constraint]
        );
        bits[changed] ^= true;
      }
    }
  }
}

#[test]
fn linked_endpoints_require_positive_progress_and_bind_all_clock_bits() {
  let gate = OrderGate::new(3, OrderKind::Endpoints).unwrap();
  let check = |input: &[F128], valid: bool| {
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
    assert_eq!(read_words(&bits, 2, 1), [f(u64::from(!valid))]);
    let table = gate.r1cs();
    bits.resize(table.n(), false);
    assert!(table.satisfies(&bits));
    if !valid {
      bits[256] = false;
      assert!(!table.satisfies(&bits));
    }
  };
  for (start, end) in
    [(0, 1), (1, 2), (1 << 32, 1 << 40), (u64::MAX - 1, u64::MAX)]
  {
    check(&[f(start), f(end)], true);
    check(&[f(end), f(start)], false);
    check(&[f(start), f(start)], false);
    for at in 0..2 {
      for bit in 0..64 {
        let mut input = [f(start), f(end)];
        input[at].hi = 1 << bit;
        check(&input, false);
      }
    }
  }
}

fn emit(b: &mut impl CircuitEmitter) -> InputLayout {
  let mut b = LayoutEmitter::new(b);
  let chain = StateChainSlots::declare_linked(
    &mut b,
    6,
    2,
    RecordLayout::new(vec![u64::MAX as u128, 0, u128::MAX, u128::MAX]).unwrap(),
  )
  .unwrap();
  let mut boundary = || BoundaryWires {
    clock: b.input(),
    state: (0..2).map(|_| b.input()).collect(),
  };
  let start = boundary();
  let end = boundary();
  let rows = (0..6)
    .map(|_| TransitionWires {
      enabled: b.input(),
      clock: b.input(),
      before: (0..2).map(|_| b.input()).collect(),
      after: (0..2).map(|_| b.input()).collect(),
    })
    .collect::<Vec<_>>();
  let switches = (0..chain.routing_plan(rows.len()).unwrap().switches())
    .map(|_| b.input())
    .collect::<Vec<_>>();
  chain.check(&mut b, start, end, &rows, &switches);
  b.finish().0
}

fn with_routing(mut input: Vec<F128>) -> Vec<F128> {
  assert_eq!(input.len(), 6 + 6 * 6);
  let record = |clock: F128, state: &[F128]| {
    [clock, F128::ZERO].into_iter().chain(state.iter().copied()).collect()
  };
  let mut records = Vec::new();
  for row in input[6..].as_chunks::<6>().0 {
    records.extend([
      record(row[1], &row[2..4]),
      record(if row[0] == f(1) { f(row[1].lo + 1) } else { f(0) }, &row[4..6]),
    ]);
  }
  records
    .extend([record(input[0], &input[1..3]), record(input[3], &input[4..6])]);
  input.extend(linked_routing(&records).unwrap());
  input
}

fn rejects(shape: &CircuitShape, inputs: &InputLayout, input: &[F128]) {
  assert!(
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(
      || shape.run(&inputs.assign(input).unwrap(), &[])
    ))
    .is_err()
  );
}

#[test]
fn linked_circuit_binds_full_states_and_rejects_extra_missing_or_disabled_steps()
 {
  let mut builder = ShapeBuilder::new(6);
  let inputs = emit(&mut builder);
  let shape = builder.finish().unwrap();
  let mut counter = CountingEmitter::new();
  emit(&mut counter);
  counter.ensure_matches(&shape).unwrap();
  let input = with_routing(
    [
      5, 7, 8, 8, 11, 12, 1, 7, 9, 10, 11, 12, 0, 0, 0, 0, 0, 0, 1, 5, 7, 8, 9,
      10, 1, 6, 9, 10, 9, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ]
    .map(f)
    .to_vec(),
  );
  shape.run(&inputs.assign(&input).unwrap(), &[]);
  // Every full state word is tied to the matching boundary or transition.
  for at in [1, 2, 4, 5, 8, 9, 10, 11, 20, 21, 22, 23, 26, 27, 28, 29] {
    for delta in [f(1), F128::new(0, 1 << 63)] {
      let mut bad = input.clone();
      bad[at] += delta;
      rejects(&shape, &inputs, &bad);
    }
  }
  for at in [0, 3, 6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 24, 25] {
    let mut bad = input.clone();
    bad[at] += f(1);
    rejects(&shape, &inputs, &bad);
    bad = input.clone();
    bad[at].hi = 1;
    rejects(&shape, &inputs, &bad);
  }
  let mut duplicate = input.clone();
  duplicate.copy_within(24..30, 12);
  rejects(&shape, &inputs, &duplicate);
  let mut detached = input.clone();
  detached[30..42]
    .copy_from_slice(&[1, 40, 1, 2, 3, 4, 1, 41, 3, 4, 5, 6].map(f));
  rejects(&shape, &inputs, &detached);
  let mut missing = input.clone();
  missing[24..30].fill(F128::ZERO);
  rejects(&shape, &inputs, &missing);
  let mut wrap = input.clone();
  wrap[25] = f(u64::MAX);
  rejects(&shape, &inputs, &wrap);
  // Equality of multisets alone admits this empty chain. The endpoints gate
  // must reject it even with freshly recomputed, correct permutation advice.
  let mut empty = vec![f(0); 42];
  empty[..6].copy_from_slice(&[5, 7, 8, 5, 7, 8].map(f));
  rejects(&shape, &inputs, &with_routing(empty));
  // A live zero record at clock zero may coincide with padding. Equal pad
  // multiplicities cancel, and the two positive steps still form one chain.
  let mut zero = vec![f(0); 42];
  zero[3] = f(2);
  zero[6] = f(1);
  zero[12] = f(1);
  zero[13] = f(1);
  shape.run(&inputs.assign(&with_routing(zero)).unwrap(), &[]);
}

#[test]
fn linked_routing_matches_all_words_and_preserves_duplicate_padding_counts() {
  let input = vec![
    vec![f(5), f(BEFORE), F128::new(7, 1)],
    vec![f(6), f(AFTER), F128::new(8, 2)],
    vec![f(0), f(PAD), f(0)],
    vec![f(0), f(PAD), f(0)],
    vec![f(5), f(SEED), F128::new(7, 1)],
    vec![f(6), f(SEAL), F128::new(8, 2)],
  ];
  assert_eq!(
    linked_routing(&input).unwrap().len(),
    StateChainSlots::linked_plan(2).unwrap().switches()
  );
  for at in [0, 1, 2, 3, 4, 5] {
    let mut bad = input.clone();
    bad[at][2].hi ^= 1 << 63;
    assert!(linked_routing(&bad).is_err());
  }
  assert!(linked_routing(&[]).is_err());
  assert!(linked_routing(&input[..5]).is_err());
  for count in [1, 2, 4, 63, 8128] {
    assert_eq!(
      StateChainSlots::linked_plan(count).unwrap().lanes() * 2,
      StateChainSlots::plan(count).unwrap().lanes()
    );
  }
}
