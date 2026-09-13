use super::*;
use crate::ixby::{
  byte_value::{ByteCapacity, ByteDecodeLayout},
  decode::test_support::{Value as V, advice, byte_record, input},
  nat_value::NatCapacity,
  value::NAT_TAG,
};

fn revision(mut bytes: Vec<u8>) -> Vec<u8> {
  bytes[4] = 1;
  bytes
}
fn setup(bits: usize) -> InputDecodeGate {
  InputDecodeGate::new(3, InputCapacities { bytes: 96, values: 2 })
    .unwrap()
    .with_byte_values(ByteDecodeLayout {
      capacity: ByteCapacity::new(17).unwrap(),
      base: 5,
    })
    .unwrap()
    .with_nat_values(NatCapacity::new(bits).unwrap())
    .unwrap()
}
fn check(
  gate: &InputDecodeGate,
  r1cs: &BlockR1cs,
  data: &[u8],
  good: bool,
) -> Vec<F128> {
  let input = advice(gate.capacity.bytes, data);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
  let residual = 128 * (gate.input_count() + gate.decoded_words());
  assert_eq!(bits[residual], !good, "bytes {data:?}");
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(
    !r1cs.satisfies(&bits),
    "cannot force acceptance after recomputing decoder advice"
  );
  evaluate(gate.plan(), &input, gate.output_count())
}

#[test]
fn nat_input_checks_minimal_magnitudes_every_prefix_and_exact_partial_bit_bounds()
 {
  let gate = setup(9);
  let r1cs = gate.r1cs();
  for data in [vec![], vec![1], vec![255], vec![0, 1], vec![255, 1]] {
    let code = revision(input(&[V::Nat(data.clone()), V::Bytes(vec![0, 0])]));
    let got = check(&gate, &r1cs, &code, true);
    assert_eq!(&got[1..3], &[F128::new(NAT_TAG, 0), F128::new(5, 0)]);
    assert_eq!(&got[5..8], byte_record(17, Some(&data)));
  }
  for data in [vec![0], vec![1, 0], vec![0, 2], vec![1, 1, 1]] {
    check(&gate, &r1cs, &revision(input(&[V::Nat(data)])), false);
  }
  let good = revision(input(&[V::Nat(vec![255, 1])]));
  for end in 0..good.len() {
    check(&gate, &r1cs, &good[..end], false);
  }
  let mut trailing = good.clone();
  trailing.push(0);
  check(&gate, &r1cs, &trailing, false);
  let mut hostile = good.clone();
  hostile[14..18].copy_from_slice(&u32::MAX.to_le_bytes());
  check(&gate, &r1cs, &hostile, false);
  for revision in [0, 2, 255] {
    let mut bad = good.clone();
    bad[4] = revision;
    check(&gate, &r1cs, &bad, false);
  }
  let old = InputDecodeGate::new(3, gate.capacity)
    .unwrap()
    .with_byte_values(ByteDecodeLayout {
      capacity: ByteCapacity::new(17).unwrap(),
      base: 5,
    })
    .unwrap();
  let mut renamed = good.clone();
  renamed[4] = 0;
  check(&old, &old.r1cs(), &renamed, false);
  let zero = setup(0);
  let r1cs = zero.r1cs();
  check(&zero, &r1cs, &revision(input(&[V::Nat(vec![])])), true);
  check(&zero, &r1cs, &revision(input(&[V::Nat(vec![1])])), false);
}

#[test]
fn nat_input_crosses_physical_words_and_binds_every_derived_record() {
  let gate = setup(129);
  let r1cs = gate.r1cs();
  let mut data = vec![255; 17];
  data[16] = 1;
  let encoded = revision(input(&[V::Nat(data)]));
  check(&gate, &r1cs, &encoded, true);
  let input = advice(gate.capacity.bytes, &encoded);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
  for word in 0..gate.output_count() {
    for bit in [0, 7, 31, 32, 63, 64, 127] {
      let column = 128 * (gate.input_count() + word) + bit;
      bits[column] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[column] ^= true;
    }
  }
  let row = InputDecodeRow(input);
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
