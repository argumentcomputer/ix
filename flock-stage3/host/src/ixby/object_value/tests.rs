use super::{ObjectDispatchGate, test_support::*};
use crate::{
  ixby::{
    bits::fill_words,
    decode::test_support::{Value as V, meta},
    value::{BYTES_TAG, ValueWords},
  },
  sizing::CountedGate,
};
use flock_prover::{circuit::builder::GateType, field::F128};

fn gate() -> ObjectDispatchGate {
  ObjectDispatchGate::new(3, layout(), CONTROL)
}
fn header() -> usize {
  1 + CONTROL.frame_words()
}
fn args() -> usize {
  header() + 5
}
fn arena(gate: &ObjectDispatchGate) -> usize {
  1 + gate.normalized_words() + layout().program_words()
}
fn row(
  gate: &ObjectDispatchGate,
  kind: u32,
  operands: &[ValueWords],
) -> Vec<F128> {
  let layout = layout();
  let mut words = vec![F128::ZERO; gate.input_count()];
  words[0] = F128::new(layout.input_slots() as u64, 0);
  words[1] = meta(0, 0, operands.len() as u32, 0);
  for (index, value) in operands.iter().enumerate() {
    words[2 + 2 * index..4 + 2 * index].copy_from_slice(value);
    words[args() + 2 * index..args() + 2 * index + 2].copy_from_slice(value);
  }
  words[header()] = meta(operands.len() as u32, kind, 1, 0);
  words[header() + 1] =
    meta(if kind == 7 { 1 } else { 0 }, 0, operands.len() as u32, 0);
  let start = 1 + gate.normalized_words();
  words[start..start + layout.declaration_words()]
    .copy_from_slice(&declarations());
  let alternatives = start + layout.case_word(0, 0);
  words[alternatives] = F128::new(2, 0);
  words[alternatives + 1] = meta(0, 2, 0, 0);
  words[alternatives + 2] = meta(1, 1, 0, 0);
  let fields = [V::Word(11).words(), V::Word(22).words()];
  words[arena(gate)..arena(gate) + layout.record_words()]
    .copy_from_slice(&record(true, &fields));
  words
}
fn rejects(gate: &ObjectDispatchGate, input: &[F128]) {
  assert_eq!(
    result(gate.plan(), input, gate.output_count()).last(),
    Some(&F128::ONE)
  );
}

#[test]
fn construction_projection_and_cases_preserve_exact_order_and_tags() {
  let gate = gate();
  let values = [
    V::Bool(0).words(),
    V::Word(u32::MAX).words(),
    V::Field(0xffff_ffff_0000_0000).words(),
    V::Ext(17, 19).words(),
    V::Erased.words(),
    [F128::new(BYTES_TAG, 0), F128::new(1, 0)],
    handle(0),
  ];
  for value in values {
    let fields = [value, V::Word(22).words()];
    let inputs = row(&gate, 7, &fields);
    let out = result(gate.plan(), &inputs, gate.output_count());
    assert_eq!(out.last(), Some(&F128::ZERO));
    assert_eq!(&out[..CONTROL.frame_words()], &inputs[1..header()]);
    let result_start = CONTROL.frame_words() + 3;
    assert_eq!(
      &out[result_start..result_start + 2],
      handle(layout().input_slots() as u32)
    );
    assert_eq!(
      &out[gate.normalized_words()..out.len() - 1],
      record(true, &fields)
    );
  }
  let mut empty = row(&gate, 7, &[]);
  empty[header() + 1] = F128::ZERO;
  assert_eq!(
    &result(gate.plan(), &empty, gate.output_count())
      [gate.normalized_words()..gate.output_count() - 1],
    record(false, &[])
  );
  check(gate.plan(), &empty, gate.output_count(), true);
  for field in 0..2 {
    let mut inputs = row(&gate, 8, &[handle(0)]);
    inputs[header() + 1].lo = field;
    let out = result(gate.plan(), &inputs, gate.output_count());
    assert_eq!(out.last(), Some(&F128::ZERO));
    let start = CONTROL.frame_words() + 3;
    assert_eq!(
      &out[start..start + 2],
      V::Word(if field == 0 { 11 } else { 22 }).words()
    );
    check(gate.plan(), &inputs, gate.output_count(), true);
  }
  let inputs = row(&gate, 9, &[handle(0)]);
  let out = result(gate.plan(), &inputs, gate.output_count());
  assert_eq!(out[0], meta(0, 0, 3, 0));
  assert_eq!(
    &out[1..7],
    [handle(0), V::Word(11).words(), V::Word(22).words()].concat()
  );
  assert_eq!(out[CONTROL.frame_words()], meta(1, 6, 1, 1));
  check(gate.plan(), &inputs, gate.output_count(), true);
}

#[test]
fn erased_projection_is_total_but_its_entire_cell_is_canonical() {
  let gate = gate();
  for field in [0, 1, 31, 32, 1 << 31, u32::MAX] {
    let mut inputs = row(&gate, 8, &[V::Erased.words()]);
    inputs[header() + 1].lo = field.into();
    let out = result(gate.plan(), &inputs, gate.output_count());
    let start = CONTROL.frame_words() + 3;
    assert_eq!(&out[start..start + 2], V::Erased.words());
    assert_eq!(out.last(), Some(&F128::ZERO));
  }
  let inputs = row(&gate, 8, &[V::Erased.words()]);
  check(gate.plan(), &inputs, gate.output_count(), true);
  for word in [args(), args() + 1] {
    for bit in 0..128 {
      let mut bad = inputs.clone();
      flip(&mut bad[word], bit);
      if word == args() && bit == 1 {
        // 5 xor 2 is the valid constructor tag 7. Operand/frame equality
        // belongs to the wired operand producer, not this local row.
        let out = result(gate.plan(), &bad, gate.output_count());
        let start = CONTROL.frame_words() + 3;
        assert_eq!(&out[start..start + 2], V::Word(11).words());
        assert_eq!(out.last(), Some(&F128::ZERO));
      } else {
        rejects(&gate, &bad);
      }
    }
  }
  let bad = row(&gate, 9, &[V::Erased.words()]);
  rejects(&gate, &bad);
  check(gate.plan(), &bad, gate.output_count(), false);
}

#[test]
fn constructor_bounds_presence_and_backward_edges_are_constrained() {
  let gate = gate();
  let constructor = row(&gate, 7, &[V::Word(11).words(), V::Word(22).words()]);
  for index in [2, 1 << 31, u32::MAX] {
    let mut bad = constructor.clone();
    bad[header() + 1].lo = index.into();
    rejects(&gate, &bad);
  }
  for count in [0, 1, 3, 1 << 31, u32::MAX] {
    let mut bad = constructor.clone();
    bad[header() + 1].hi = count.into();
    rejects(&gate, &bad);
  }
  for index in [
    layout().input_slots(),
    layout().entries() - 1,
    layout().entries(),
    u32::MAX as usize,
  ] {
    let mut bad = constructor.clone();
    bad[args()..args() + 2].copy_from_slice(&handle(index as u32));
    rejects(&gate, &bad);
  }
  let projected = row(&gate, 8, &[handle(0)]);
  for field in [2, 1 << 31, u32::MAX] {
    let mut bad = projected.clone();
    bad[header() + 1].lo = field.into();
    rejects(&gate, &bad);
  }
  for metadata in
    [meta(1, 2, 0, 0), meta(1, 1, 1, 0), meta(2, 2, 1, 0), meta(1, 2, 1, 1)]
  {
    let mut bad = projected.clone();
    bad[arena(&gate)] = metadata;
    rejects(&gate, &bad);
  }
  let mut absent = row(&gate, 9, &[handle(0)]);
  let alternatives = 1 + gate.normalized_words() + layout().case_word(0, 0);
  absent[alternatives] = F128::new(1, 0);
  absent[alternatives + 2] = F128::ZERO;
  rejects(&gate, &absent);
  check(gate.plan(), &absent, gate.output_count(), false);
}

#[test]
fn object_dispatch_outputs_and_count_aware_padding_are_constrained() {
  let gate = gate();
  let inputs = row(&gate, 7, &[V::Word(11).words(), V::Word(22).words()]);
  let r1cs = gate.r1cs();
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&inputs, bits));
  assert!(r1cs.satisfies(&bits));
  for word in 0..gate.output_count() {
    for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
      let at = 128 * (inputs.len() + word) + bit;
      bits[at] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[at] ^= true;
    }
  }
  bits[gate.plan().k() - 1] = true;
  assert!(!r1cs.satisfies(&bits));
  let row = gate.eval(&inputs, &(), &mut Vec::new());
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(row.inputs(), bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
