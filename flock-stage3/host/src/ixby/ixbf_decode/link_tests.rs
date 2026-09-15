use super::*;
use crate::{
  ixby::bits::{fill_words, read_words},
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};

pub(super) fn input(left: [u128; 5], right: [u128; 5]) -> [F128; 11] {
  let mut input = [F128::ZERO; 11];
  input[0] = F128::new(1, 0);
  input[1..6].copy_from_slice(&left.map(record_tests::word));
  input[6..].copy_from_slice(&right.map(record_tests::word));
  input
}

pub(super) fn fixture(kind: RecordLinkKind) -> [F128; 11] {
  let (left, right) = match kind {
    RecordLinkKind::ExactArity => {
      ([1 << 100, 1 << 80, 0, 0, 0], [1 << 100, 1 << 80, 0, 0, 0])
    },
    RecordLinkKind::PartialArity => {
      ([1 << 100, 7, 0, 0, 0], [1 << 100, 1 << 80, 0, 0, 0])
    },
    RecordLinkKind::SuccessorFrame => {
      ([8, (1 << 80) - 1, 1, 0, 0], [8, 1 << 80, u128::MAX, 0, 0])
    },
    RecordLinkKind::ConstructorValue => (
      [u128::MAX, 1 << 127, 1 << 100, 1 << 80, 3],
      [u128::MAX, 1 << 127, 1 << 100, 1 << 80, 3],
    ),
    RecordLinkKind::DistinctConstructors => (
      [u128::MAX, 1 << 127, 1 << 100, 1 << 80, 3],
      [u128::MAX, 1 << 127, 1 << 100, (1 << 80) + 1, 3],
    ),
  };
  input(left, right)
}

pub(super) fn bits(gate: &RecordLinkGate, input: &[F128; 11]) -> Vec<bool> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| fill_words(input, bits));
  assert_eq!(read_words(&row, 11, 1), [link::evaluate(gate.kind(), input)]);
  row
}

fn reject(gate: &RecordLinkGate, r1cs: &BlockR1cs, input: &[F128; 11]) {
  let mut row = bits(gate, input);
  assert!(tests::satisfies(r1cs, &row));
  assert!(row[1408], "{:?} accepted invalid link {input:?}", gate.kind());
  row[1408] = false;
  assert!(!tests::satisfies(r1cs, &row));
}

#[test]
fn decoded_record_links_check_full_indices_arity_frames_and_constructor_identity()
 {
  for kind in RecordLinkKind::ALL {
    let gate = RecordLinkGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    let good = fixture(kind);
    assert_eq!(link::evaluate(kind, &good), F128::ZERO);
    let mut row = bits(&gate, &good);
    tests::output_bits_are_bound(&r1cs, &mut row, 1408, 128);
    row[gate.plan().k() - 1] = true;
    assert!(!tests::satisfies(&r1cs, &row));
    for bit in 1..128 {
      let mut changed = good;
      if bit < 64 {
        changed[0].lo |= 1 << bit;
      } else {
        changed[0].hi |= 1 << (bit - 64);
      }
      reject(&gate, &r1cs, &changed);
    }
    if kind != RecordLinkKind::DistinctConstructors {
      for bit in 0..128 {
        let mut changed = good;
        if bit < 64 {
          changed[6].lo ^= 1 << bit;
        } else {
          changed[6].hi ^= 1 << (bit - 64);
        }
        reject(&gate, &r1cs, &changed);
      }
    }
    let disabled = [F128::ZERO; 11];
    assert!(tests::satisfies(&r1cs, &bits(&gate, &disabled)));
    assert_eq!(link::evaluate(kind, &disabled), F128::ZERO);
    let mut changed = disabled;
    changed[1].hi = 1;
    reject(&gate, &r1cs, &changed);
    eprintln!(
      "record link {kind:?}: k_log={}, useful_bits={}",
      gate.plan().k_log(),
      gate.plan().useful_bits()
    );
  }
}

#[test]
fn every_constructor_identity_bit_and_all_frame_carries_are_checked() {
  let gate = RecordLinkGate::new(3, RecordLinkKind::ConstructorValue).unwrap();
  let r1cs = gate.r1cs();
  let good = fixture(gate.kind());
  for word in 6..11 {
    for bit in 0..128 {
      let mut changed = good;
      if bit < 64 {
        changed[word].lo ^= 1 << bit;
      } else {
        changed[word].hi ^= 1 << (bit - 64);
      }
      reject(&gate, &r1cs, &changed);
    }
  }
  let gate =
    RecordLinkGate::new(3, RecordLinkKind::DistinctConstructors).unwrap();
  let r1cs = gate.r1cs();
  let id = [u128::MAX, 1 << 127, 1 << 100, 1 << 80, 3];
  let mut same_id = id;
  same_id[4] = 17;
  reject(&gate, &r1cs, &input(id, same_id));
  for bit in 0..512 {
    let mut changed = id;
    changed[bit / 128] ^= 1 << (bit % 128);
    let input = input(id, changed);
    assert_eq!(link::evaluate(gate.kind(), &input), F128::ZERO);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
  }
  let gate = RecordLinkGate::new(3, RecordLinkKind::SuccessorFrame).unwrap();
  let r1cs = gate.r1cs();
  for width in 1..128 {
    let next = 1u128 << width;
    let input = input([0, next - 1, 1, 0, 0], [0, next, next, 0, 0]);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
    assert_eq!(link::evaluate(gate.kind(), &input), F128::ZERO);
  }
  for (left, right) in [
    ([0, u128::MAX, 1, 0, 0], [0, 0, u128::MAX, 0, 0]),
    ([0, 7, 3, 0, 0], [0, 10, 9, 0, 0]),
    ([0, 7, 3, 0, 0], [0, 11, 12, 0, 0]),
  ] {
    reject(&gate, &r1cs, &input(left, right));
  }
  for kind in [RecordLinkKind::ExactArity, RecordLinkKind::PartialArity] {
    let gate = RecordLinkGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    let count = if kind == RecordLinkKind::ExactArity { 1 } else { 2 };
    reject(&gate, &r1cs, &input([0, count, 0, 0, 0], [0, 2, 0, 0, 0]));
    reject(&gate, &r1cs, &input([0, 3, 0, 0, 0], [0, 2, 0, 0, 0]));
    reject(&gate, &r1cs, &input([0, 2, 1, 0, 0], [0, 2, 0, 0, 0]));
  }
}

#[test]
fn record_links_have_lazy_count_parity_and_fully_initialized_witness_buffers() {
  use crate::sizing::{CircuitEmitter, CountingEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  fn emit(b: &mut impl CircuitEmitter, gate: RecordLinkGate) {
    let slot = RecordLinkSlot::declare(b, gate);
    for _ in 0..3 {
      let enabled = b.input();
      let left = std::array::from_fn(|_| b.input());
      let right = std::array::from_fn(|_| b.input());
      slot.check(b, enabled, left, right);
    }
  }
  for kind in RecordLinkKind::ALL {
    let gate = RecordLinkGate::new(3, kind).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, gate.clone());
    assert!(gate.plan.get().is_none());
    let mut b = ShapeBuilder::new(3);
    emit(&mut b, gate.clone());
    let shape = b.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    assert_eq!(count.registry(3).1, shape.counts);
    let good = RecordLinkRow(fixture(kind));
    for rows in [vec![], vec![good.clone()], vec![good; 5]] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
    assert_eq!((gate.input_count(), gate.output_count()), (11, 1));
  }
  assert!(RecordLinkGate::new(2, RecordLinkKind::ExactArity).is_err());
  assert!(RecordLinkGate::new(21, RecordLinkKind::ExactArity).is_err());
}
