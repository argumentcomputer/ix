use super::*;
use crate::{
  ixby::{
    auth_memory::{MemoryDepth, MemoryOpeningWires, SparseMemory},
    bits::{fill_words, read_words},
    io::{InputLayout, LayoutEmitter, PublicLayout},
    memory_log::{
      self, AccessWires, MemoryLogSlots, TimedAccessWires, TimedMemoryLogSlots,
    },
  },
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::circuit::builder::{CircuitShape, GateType, ShapeBuilder};

fn evaluate(gate: &OrderGate, input: &[F128]) -> Vec<F128> {
  let mut output = Vec::new();
  gate.eval(input, &(), &mut output);
  output
}
fn checked(gate: &OrderGate, input: &[F128], expected: &[F128]) {
  assert_eq!(evaluate(gate, input), expected);
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  assert_eq!(
    read_words(&bits, gate.input_count(), gate.output_count()),
    expected
  );
  let r1cs = gate.r1cs();
  bits.resize(r1cs.n(), false);
  assert!(r1cs.satisfies(&bits));
}
fn f(v: u64) -> F128 {
  F128::new(v, 0)
}
fn pad(n: usize) -> Vec<F128> {
  let mut p = vec![F128::ZERO; n + 2];
  p[1] = f(PAD);
  p
}
fn record(clock: u64, kind: u64, state: &[F128]) -> Vec<F128> {
  [f(clock), f(kind)].into_iter().chain(state.iter().copied()).collect()
}
#[test]
fn transition_preparation_narrows_every_control_and_canonicalizes_inactive_rows()
 {
  for n in [1, 16, 30] {
    let gate = OrderGate::new(3, OrderKind::Prepare(n)).unwrap();
    for clock in [0, 1, (1 << 32) + 1, u64::MAX - 1] {
      let mut input = vec![f(1), f(clock)];
      input.extend((0..2 * n).map(|i| F128::new(i as u64, !i as u64)));
      checked(
        &gate,
        &input,
        &[f(clock), f(BEFORE), f(clock + 1), f(AFTER), f(0)],
      );
      for at in [0, 1] {
        let mut bad = input.clone();
        bad[at].hi |= 1;
        assert_ne!(*evaluate(&gate, &bad).last().unwrap(), f(0));
      }
    }
    let empty = vec![f(0); gate.input_count()];
    checked(&gate, &empty, &[f(0), f(PAD), f(0), f(PAD), f(0)]);
    for i in 1..empty.len() {
      let mut bad = empty.clone();
      bad[i] = F128::new(0, 1 << 63);
      assert_eq!(*evaluate(&gate, &bad).last().unwrap(), f(1));
    }
    let mut overflow = empty;
    overflow[0] = f(1);
    overflow[1] = f(u64::MAX);
    assert_eq!(*evaluate(&gate, &overflow).last().unwrap(), f(1));
  }
}
fn audit_input(
  previous: &[F128],
  current: &[F128],
  first: bool,
  last: bool,
) -> Vec<F128> {
  previous
    .iter()
    .chain(current)
    .copied()
    .chain([f(first as u64), f(last as u64)])
    .collect()
}
#[test]
fn state_audit_requires_one_positive_unbroken_chain_with_full_state_equality() {
  let n = 16;
  let gate = OrderGate::new(3, OrderKind::Audit(n)).unwrap();
  let states = (0..3)
    .map(|s| {
      (0..n)
        .map(|i| F128::new((s * 100 + i) as u64, !(i as u64)))
        .collect::<Vec<_>>()
    })
    .collect::<Vec<_>>();
  let records = [
    record(9, SEED, &states[0]),
    record(9, BEFORE, &states[0]),
    record(10, AFTER, &states[1]),
    record(10, BEFORE, &states[1]),
    record(11, AFTER, &states[2]),
    record(11, SEAL, &states[2]),
    pad(n),
    pad(n),
  ];
  let padding = pad(n);
  for i in 0..records.len() {
    let previous = if i == 0 { &padding } else { &records[i - 1] };
    let input =
      audit_input(previous, &records[i], i == 0, i + 1 == records.len());
    checked(&gate, &input, &[f(0)]);
    for index in [n + 2, n + 3, 2 * (n + 2), 2 * (n + 2) + 1] {
      let mut bad = input.clone();
      bad[index].hi ^= 1 << 63;
      assert_eq!(evaluate(&gate, &bad), [f(1)]);
    }
    if [1, 3, 5, 6, 7].contains(&i) {
      for at in 0..n {
        let mut bad = input.clone();
        bad[n + 4 + at].hi ^= 1 << 63;
        assert_eq!(evaluate(&gate, &bad), [f(1)]);
      }
    }
  }
  for (previous, current, first, last) in [
    (&padding, &records[1], true, false),
    (&records[0], &records[5], false, true), // Empty or skipped chain.
    (&records[1], &records[4], false, false), // Missing clock.
    (&records[2], &records[2], false, false), // Duplicate clock/kind.
    (&records[4], &records[1], false, false), // Backwards.
    (&records[1], &records[2], false, true), // No seal.
    (&records[5], &records[1], false, false), // Restart.
    (&padding, &records[0], false, false),   // Nonpadding after padding.
  ] {
    checked(&gate, &audit_input(previous, current, first, last), &[f(1)]);
  }
  let high = record(u64::MAX, BEFORE, &states[0]);
  let wrap = record(0, AFTER, &states[1]);
  checked(&gate, &audit_input(&high, &wrap, false, false), &[f(1)]);
}
#[test]
fn memory_times_derive_from_the_actual_step_and_fixed_ordinal_without_wrap() {
  let gate = OrderGate::new(3, OrderKind::Access).unwrap();
  for clock in [0, 1, 1 << 40, (1 << 59) - 2] {
    for ordinal in [0, 1, 30, 31] {
      for write in [0, 1] {
        let input = [
          f(1),
          f(clock),
          f(ordinal),
          f(u64::MAX),
          f(write),
          F128::new(1, 2),
          F128::new(3, 4),
        ];
        let expected = [
          input[3],
          f(clock * 32 + ordinal + 1),
          f(1 + write),
          input[5],
          input[6],
          f(0),
        ];
        checked(&gate, &input, &expected);
        for at in [0, 1, 2, 3, 4] {
          let mut bad = input;
          bad[at].hi ^= 1;
          assert_eq!(*evaluate(&gate, &bad).last().unwrap(), f(1));
        }
      }
    }
  }
  for ordinal in [0, 31] {
    let input = [f(0), f(0), f(ordinal), f(0), f(0), f(0), f(0)];
    checked(&gate, &input, &[f(0), f(0), f(memory_log::PAD), f(0), f(0), f(0)]);
    for at in [1, 3, 4, 5, 6] {
      let mut bad = input;
      bad[at] = f(1);
      assert_eq!(*evaluate(&gate, &bad).last().unwrap(), f(1));
    }
  }
  for (clock, ordinal) in [((1 << 59) - 1, 0), (1 << 59, 0), (0, 32)] {
    let input = [f(1), f(clock), f(ordinal), f(0), f(0), f(0), f(0)];
    assert_eq!(*evaluate(&gate, &input).last().unwrap(), f(1));
  }
}

struct Emission {
  inputs: InputLayout,
  public: PublicLayout,
}
fn emit(b: &mut impl CircuitEmitter, linked: bool) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let chain = if linked {
    StateChainSlots::declare_linked(
      &mut b,
      9,
      2,
      RecordLayout::new(vec![u64::MAX as u128, 0, u128::MAX, u128::MAX])
        .unwrap(),
    )
    .unwrap()
  } else {
    StateChainSlots::declare(&mut b, 9, 2).unwrap()
  };
  let memory =
    TimedMemoryLogSlots::declare(&mut b, 9, MemoryDepth::new(8).unwrap())
      .unwrap();
  let root = std::array::from_fn(|_| b.input());
  for w in root {
    b.publish(w);
  }
  let mut boundary = || {
    let clock = b.input();
    b.publish(clock);
    let state = (0..2)
      .map(|_| {
        let w = b.input();
        b.publish(w);
        w
      })
      .collect();
    BoundaryWires { clock, state }
  };
  let start = boundary();
  let end = boundary();
  let mut rows = Vec::new();
  let mut accesses = Vec::new();
  for _ in 0..4 {
    let enabled = b.input();
    let clock = b.input();
    let before = (0..2).map(|_| b.input()).collect();
    let after = (0..2).map(|_| b.input()).collect();
    rows.push(TransitionWires { enabled, clock, before, after });
    accesses.push(TimedAccessWires {
      enabled,
      clock,
      ordinal: 0,
      access: AccessWires {
        address: b.input(),
        write: b.input(),
        value: std::array::from_fn(|_| b.input()),
      },
    });
  }
  let switches = (0..chain.routing_plan(4).unwrap().switches())
    .map(|_| b.input())
    .collect::<Vec<_>>();
  chain.check(&mut b, start, end, &rows, &switches);
  let cells = [memory_log::BoundaryWires {
    address: b.input(),
    opening: MemoryOpeningWires {
      value: std::array::from_fn(|_| b.input()),
      siblings: (0..8).map(|_| std::array::from_fn(|_| b.input())).collect(),
    },
    final_value: std::array::from_fn(|_| b.input()),
  }];
  let switches = (0..MemoryLogSlots::plan(4, 1).unwrap().switches())
    .map(|_| b.input())
    .collect::<Vec<_>>();
  for w in memory.check(&mut b, root, &accesses, &cells, &switches) {
    b.publish(w);
  }
  let (inputs, public) = b.finish();
  Emission { inputs, public }
}
fn fixture(linked: bool) -> (Vec<F128>, Vec<F128>) {
  let mut memory = SparseMemory::new(MemoryDepth::new(8).unwrap());
  let value = [F128::new(123, 456), F128::new(789, 10)];
  let start = [f(7), f(8)];
  let middle = [f(9), f(10)];
  let end = [f(11), f(12)];
  let mut private = memory.root().to_vec();
  private.extend([f(5), start[0], start[1], f(8), end[0], end[1]]);
  let mut expected = private.clone();
  let mut chain_records = Vec::new();
  let mut memory_records = Vec::new();
  for (enabled, clock, before, after, write, v) in [
    (1, 7, middle, end, 0, value),
    (0, 0, [f(0); 2], [f(0); 2], 0, [f(0); 2]),
    (1, 5, start, middle, 1, value),
    (1, 6, middle, middle, 0, value),
  ] {
    let address = if enabled == 1 { 42 } else { 0 };
    private.extend([f(enabled), f(clock)]);
    private.extend(before);
    private.extend(after);
    private.extend([f(address), f(write), v[0], v[1]]);
    if enabled == 1 {
      chain_records.extend([
        record(clock, BEFORE, &before),
        record(clock + 1, AFTER, &after),
      ]);
      memory_records.push(vec![
        f(address),
        f(clock * 32 + 1),
        f(1 + write),
        v[0],
        v[1],
      ]);
    } else {
      chain_records.extend([pad(2), pad(2)]);
      memory_records.push(vec![f(0), f(0), f(4), f(0), f(0)]);
    }
  }
  chain_records.extend([record(5, SEED, &start), record(8, SEAL, &end)]);
  if linked {
    private.extend(linked_routing(&chain_records).unwrap());
  } else {
    chain_records.resize(StateChainSlots::plan(4).unwrap().lanes(), pad(2));
    private.extend(routing(&chain_records).unwrap());
  }
  let opening = memory.replace(42, value).unwrap();
  private.extend(opening.words());
  private.extend(value);
  memory_records.extend([
    vec![f(42), f(0), f(0), f(0), f(0)],
    vec![f(42), f(u64::MAX), f(3), value[0], value[1]],
  ]);
  let plan = MemoryLogSlots::plan(4, 1).unwrap();
  memory_records.resize(plan.lanes(), vec![f(0), f(0), f(4), f(0), f(0)]);
  let mut order = (0..plan.lanes()).collect::<Vec<_>>();
  order.sort_by_key(|&i| {
    (
      memory_records[i][2].lo == 4,
      memory_records[i][0].lo,
      memory_records[i][1].lo,
    )
  });
  let mut dest = vec![0; plan.lanes()];
  for (to, from) in order.into_iter().enumerate() {
    dest[from] = to;
  }
  private.extend(plan.route(&dest).unwrap());
  expected.extend(memory.root());
  (private, expected)
}
#[test]
fn grouped_rows_share_one_state_chain_and_chronological_authenticated_memory() {
  grouped_rows(false);
}
#[test]
fn linked_rows_share_one_state_chain_and_chronological_authenticated_memory() {
  grouped_rows(true);
}
fn grouped_rows(linked: bool) {
  let mut b = ShapeBuilder::new(9);
  let emission = emit(&mut b, linked);
  let shape: CircuitShape = b.finish().unwrap();
  let mut count = CountingEmitter::new();
  emit(&mut count, linked);
  count.ensure_matches(&shape).unwrap();
  let (private, expected) = fixture(linked);
  let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
  assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
  for at in [2, 3, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 29, 39] {
    let mut bad = private.clone();
    bad[at] += f(1);
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || shape.run(&emission.inputs.assign(&bad).unwrap(), &[])
      ))
      .is_err(),
      "changed {at} accepted"
    );
  }
}
