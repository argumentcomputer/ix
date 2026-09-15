use super::*;
use crate::ixby::{
  byte_value::{ByteCapacity, ByteDecodeLayout},
  decode::test_support::{Value as V, advice, byte_record, input},
  object_value::{
    ObjectCapacity,
    test_support::{CAPACITY, declarations, handle, id, record},
  },
  value::BYTES_TAG,
};

fn setup(values: usize, depth: usize, nodes: usize) -> InputDecodeGate {
  let mut c = CAPACITY;
  c.input.values = values;
  let layout =
    ObjectLayout::new(c, ObjectCapacity::new(2, depth, nodes).unwrap())
      .unwrap();
  InputDecodeGate::new(3, c.input)
    .unwrap()
    .with_byte_values(ByteDecodeLayout {
      capacity: ByteCapacity::new(17).unwrap(),
      base: 5,
    })
    .unwrap()
    .with_objects(layout)
    .unwrap()
}

fn encoded(gate: &InputDecodeGate, bytes: &[u8]) -> Vec<F128> {
  [advice(gate.capacity.bytes, bytes), declarations()].concat()
}

fn check(
  gate: &InputDecodeGate,
  r1cs: &BlockR1cs,
  inputs: &[F128],
  good: bool,
) {
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(inputs, bits));
  let residual = 128 * (gate.input_count() + gate.decoded_words());
  assert_eq!(bits[residual], !good);
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(!r1cs.satisfies(&bits));
}

fn pair(a: V, b: V) -> V {
  V::Ctor(id(true), vec![a, b])
}

#[test]
fn constructor_input_preorder_records_are_derived_from_exact_full_ids() {
  let gate = setup(1, 3, 7);
  let r1cs = gate.r1cs();
  let data = [7, 8, 9];
  let bytes =
    input(&[pair(pair(V::Word(11), V::Bytes(data.to_vec())), V::Erased)]);
  let inputs = encoded(&gate, &bytes);
  let mut expected = vec![F128::new(1, 0)];
  expected.extend(handle(0));
  for slot in 0..7 {
    expected.extend(byte_record(17, (slot == 3).then_some(data.as_slice())));
  }
  expected.extend(record(true, &[handle(1), V::Erased.words()]));
  expected.extend(record(
    true,
    &[V::Word(11).words(), [F128::new(BYTES_TAG, 0), F128::new(8, 0)]],
  ));
  expected.resize(gate.output_count(), F128::ZERO);
  assert_eq!(evaluate(gate.plan(), &inputs, gate.output_count()), expected);
  check(&gate, &r1cs, &inputs, true);
  // Full 256-bit block + u32 member + u32 tag must match the supplied,
  // program-derived declaration bank. No digest prefix is enough.
  for byte in 13..53 {
    for bit in 0..8 {
      let mut bad = bytes.clone();
      bad[byte] ^= 1 << bit;
      check(&gate, &r1cs, &encoded(&gate, &bad), false);
    }
  }
}

#[test]
fn constructor_input_rejects_wrong_arity_truncation_and_shared_forest_overflow()
{
  let gate = setup(2, 3, 7);
  let r1cs = gate.r1cs();
  let small = pair(V::Word(1), V::Word(2));
  let nested = pair(small.clone(), V::Erased);
  for values in
    [vec![], vec![nested.clone()], vec![small.clone(), small.clone()]]
  {
    check(&gate, &r1cs, &encoded(&gate, &input(&values)), true);
  }
  // Five nodes + three nodes exceeds one shared budget of seven, although
  // both roots separately fit. The two-root slot bank itself is large enough.
  check(&gate, &r1cs, &encoded(&gate, &input(&[nested.clone(), small])), false);
  for value in [
    V::Ctor(id(false), vec![V::Erased]),
    V::Ctor(id(true), vec![V::Word(1)]),
    V::Ctor(id(true), vec![V::Erased; 3]),
    pair(nested, V::Erased), // fourth depth level
  ] {
    check(&gate, &r1cs, &encoded(&gate, &input(&[value])), false);
  }
  let bytes = input(&[pair(V::Word(1), V::Erased)]);
  for end in 0..bytes.len() {
    check(&gate, &r1cs, &encoded(&gate, &bytes[..end]), false);
  }
  for at in [4, 12] {
    let mut bad = bytes.clone();
    bad[at] = if at == 4 { 1 } else { 2 }; // v1 header / unsupported PAP tag
    check(&gate, &r1cs, &encoded(&gate, &bad), false);
  }
  for count in [0, 1, 3, 1 << 31, u32::MAX] {
    let mut bad = bytes.clone();
    bad[53..57].copy_from_slice(&count.to_le_bytes());
    check(&gate, &r1cs, &encoded(&gate, &bad), false);
  }
  let mut trailing = bytes;
  trailing.push(0);
  check(&gate, &r1cs, &encoded(&gate, &trailing), false);
}

#[test]
fn constructor_input_outputs_and_recycled_padding_are_constrained() {
  let gate = setup(1, 3, 7);
  let r1cs = gate.r1cs();
  let inputs = encoded(&gate, &input(&[pair(V::Bytes(vec![1]), V::Erased)]));
  let row = InputDecodeRow(inputs);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&row.0, bits));
  assert!(r1cs.satisfies(&bits));
  for word in 0..gate.output_count() {
    for bit in [0, 7, 31, 32, 63, 64, 95, 127] {
      let at = 128 * (gate.input_count() + word) + bit;
      bits[at] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[at] ^= true;
    }
  }
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
