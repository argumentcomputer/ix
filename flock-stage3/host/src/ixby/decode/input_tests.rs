use super::*;
use crate::ixby::decode::test_support::{Value, advice, input};

#[test]
fn canonical_input_scalar_tags_payloads_and_vector_order_are_derived_from_bytes()
 {
  let capacity = InputCapacities { bytes: 128, values: 6 };
  let gate = InputDecodeGate::new(3, capacity).unwrap();
  let r1cs = gate.r1cs();
  assert_eq!(
    input(&[Value::Word(0x1234_5678)]),
    crate::ixby::commitment::tests::GOLDEN_INPUT
  );
  let values = [
    Value::Bool(1),
    Value::Word(0x1234_5678),
    Value::Field(0xffff_ffff_0000_0000),
    Value::Ext(0, 0xffff_ffff_0000_0000),
    Value::Erased,
    Value::Bool(0),
  ];
  for count in 0..=values.len() {
    let bytes = input(&values[..count]);
    let inputs = advice(capacity.bytes, &bytes);
    let mut expected = vec![F128::new(count as u64, 0)];
    for value in &values[..count] {
      expected.extend(value.words());
    }
    expected.resize(gate.output_count(), F128::ZERO);
    assert_eq!(evaluate(gate.plan(), &inputs, gate.output_count()), expected);
    let mut bits = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&inputs, bits));
    assert!(r1cs.satisfies(&bits));
  }
}

fn rejected(gate: &InputDecodeGate, r1cs: &BlockR1cs, input: &[F128]) {
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(input, bits));
  let residual = (gate.input_count() + gate.decoded_words()) * 128;
  assert!(bits[residual]);
  assert!(r1cs.satisfies(&bits));
  bits[residual] = false;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn byte_input_decodes_every_partial_chunk_without_consuming_following_values() {
  use crate::ixby::{
    byte_value::{ByteCapacity, ByteDecodeLayout},
    decode::test_support::byte_record,
    value::BYTES_TAG,
  };
  let capacity = InputCapacities { bytes: 192, values: 3 };
  let bytes = ByteCapacity::new(65).unwrap();
  let gate = InputDecodeGate::new(3, capacity)
    .unwrap()
    .with_byte_values(ByteDecodeLayout { capacity: bytes, base: 7 })
    .unwrap();
  let r1cs = gate.r1cs();
  for length in 0..=65 {
    let data: Vec<_> = (0..length).map(|i| (i * 73 + 19) as u8).collect();
    let encoded = input(&[
      Value::Bytes(data.clone()),
      Value::Word(0xdead_beef),
      Value::Bytes(vec![]),
    ]);
    let inputs = advice(capacity.bytes, &encoded);
    let mut expected =
      vec![F128::new(3, 0), F128::new(BYTES_TAG, 0), F128::new(7, 0)];
    expected.extend(Value::Word(0xdead_beef).words());
    expected.extend([F128::new(BYTES_TAG, 0), F128::new(9, 0)]);
    expected.extend(byte_record(65, Some(&data)));
    expected.extend(byte_record(65, None));
    expected.extend(byte_record(65, Some(&[])));
    expected.push(F128::ZERO);
    assert_eq!(
      evaluate(gate.plan(), &inputs, gate.output_count()),
      expected,
      "length {length}"
    );
    let mut bits = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&inputs, bits));
    assert!(r1cs.satisfies(&bits));
  }
  let encoded = input(&[Value::Bytes(vec![1; 17]), Value::Word(42)]);
  for length in [66u32, 1 << 31, u32::MAX] {
    let mut bad = encoded.clone();
    bad[14..18].copy_from_slice(&length.to_le_bytes());
    rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
  }
  for end in 0..encoded.len() {
    rejected(&gate, &r1cs, &advice(capacity.bytes, &encoded[..end]));
  }
  let mut trailing = encoded.clone();
  trailing.push(0);
  rejected(&gate, &r1cs, &advice(capacity.bytes, &trailing));
  let row = InputDecodeRow(advice(capacity.bytes, &encoded));
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&row.0, bits));
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

#[test]
fn input_decoder_rejects_wide_counts_noncanonical_scalars_and_unconsumed_bytes()
{
  let capacity = InputCapacities { bytes: 64, values: 2 };
  let gate = InputDecodeGate::new(3, capacity).unwrap();
  let r1cs = gate.r1cs();
  let good = input(&[Value::Word(0x1234_5678)]);
  for end in 0..good.len() {
    rejected(&gate, &r1cs, &advice(capacity.bytes, &good[..end]));
  }
  for values in [
    vec![Value::Bool(2)],
    vec![Value::Field(0xffff_ffff_0000_0001)],
    vec![Value::Field(u64::MAX)],
    vec![Value::Ext(0xffff_ffff_0000_0001, 0)],
    vec![Value::Ext(0, 0xffff_ffff_0000_0001)],
    vec![Value::Erased; 3],
  ] {
    rejected(&gate, &r1cs, &advice(capacity.bytes, &input(&values)));
  }
  for (offset, tag) in [
    (0, 0),
    (3, b'O'),
    (4, 1),
    (12, 1),
    (12, 2),
    (12, 4),
    (12, 255),
    (13, 4),
    (13, 255),
  ] {
    let mut bad = good.clone();
    bad[offset] = tag;
    rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
  }
  for count in [0u32, 3, 1 << 31, u32::MAX] {
    let mut bad = good.clone();
    bad[8..12].copy_from_slice(&count.to_le_bytes());
    rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
  }
  let mut trailing = good.clone();
  trailing.push(0);
  rejected(&gate, &r1cs, &advice(capacity.bytes, &trailing));
  for bit in [0, 31, 63, 64, 95, 127] {
    let mut bad = advice(capacity.bytes, &good);
    if bit < 64 {
      bad[4].lo |= 1 << bit;
    } else {
      bad[4].hi |= 1 << (bit - 64);
    }
    rejected(&gate, &r1cs, &bad);
  }
  for bit in 32..128 {
    let mut bad = advice(capacity.bytes, &good);
    if bit < 64 {
      bad[0].lo |= 1 << bit;
    } else {
      bad[0].hi |= 1 << (bit - 64);
    }
    rejected(&gate, &r1cs, &bad);
  }
}

#[test]
fn input_decode_outputs_unused_columns_and_recycled_rows_are_constrained() {
  let capacity = InputCapacities { bytes: 64, values: 2 };
  let gate = InputDecodeGate::new(3, capacity).unwrap();
  let r1cs = gate.r1cs();
  let row =
    InputDecodeRow(advice(capacity.bytes, &input(&[Value::Ext(7, 11)])));
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&row.0, bits));
  for word in 0..gate.output_count() {
    for bit in [0, 31, 63, 64, 95, 127] {
      let column = (gate.input_count() + word) * 128 + bit;
      bits[column] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[column] ^= true;
    }
  }
  bits[gate.plan().k() - 1] = true;
  assert!(!r1cs.satisfies(&bits));
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  let zero =
    InputDecodeGate::new(3, InputCapacities { values: 0, ..capacity }).unwrap();
  assert_eq!(
    evaluate(
      zero.plan(),
      &advice(capacity.bytes, &input(&[])),
      zero.output_count()
    ),
    [F128::ZERO, F128::ZERO]
  );
  assert!(InputDecodeGate::new(2, capacity).is_err());
  assert!(
    InputDecodeGate::new(3, InputCapacities { bytes: usize::MAX, ..capacity })
      .is_err()
  );
  assert!(
    InputDecodeGate::new(3, InputCapacities { values: 17, ..capacity })
      .is_err()
  );
}
