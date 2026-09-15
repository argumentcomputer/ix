use super::*;
use crate::{
  ixby::bits::{fill_words, read_words},
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;

pub(super) fn input(source: &[u8], offset: usize, limit: F128) -> [F128; 4] {
  assert!(offset <= source.len());
  let mut lookahead = [0; 32];
  let end = source.len().min(offset + 32);
  lookahead[..end - offset].copy_from_slice(&source[offset..end]);
  [
    F128::new(offset as u64, source.len() as u64),
    limit,
    crate::hash::pack_bytes(&lookahead[..16]),
    crate::hash::pack_bytes(&lookahead[16..]),
  ]
}

fn encoded(length: &BigUint, payload: &[u8], following: &[u8]) -> Vec<u8> {
  let mut bytes = vec![6];
  bytes.extend(tests::natural_bytes(length));
  bytes.extend_from_slice(payload);
  bytes.extend_from_slice(following);
  bytes
}

pub(super) fn bits(gate: &ByteArraySpanGate, input: &[F128; 4]) -> Vec<bool> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| fill_words(input, bits));
  assert_eq!(read_words(&row, 4, 3), byte_span::evaluate(input));
  row
}

fn reject(gate: &ByteArraySpanGate, r1cs: &BlockR1cs, input: &[F128; 4]) {
  let mut row = bits(gate, input);
  assert!(tests::satisfies(r1cs, &row));
  assert!(row[768]);
  row[768] = false;
  assert!(!tests::satisfies(r1cs, &row));
}

#[test]
fn byte_array_headers_produce_exact_ranges_without_copying_payloads() {
  let gate = ByteArraySpanGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  for length in [0, 1, 15, 16, 17, 34, 127, 128, 744159, 9611064] {
    let mut scalar = vec![0; 3];
    scalar.extend(encoded(&BigUint::from(length), &[], &[]));
    let payload_start = scalar.len() as u64;
    // Only the fixed lookahead is witness input. The range relation is the
    // same at 9.6 MB as it is at one byte; this is not a payload membership proof.
    scalar.resize(35, 0);
    let mut input = input(&scalar, 3, F128::new(length, 0));
    input[0].hi = payload_start + length;
    let output = byte_span::evaluate(&input);
    assert_eq!(
      output,
      [
        F128::new(payload_start, length),
        F128::new(payload_start + length, payload_start + length),
        F128::ZERO
      ]
    );
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
  }
  // A zero-length value can end exactly at the largest u64 file position.
  let scalar = encoded(&BigUint::from(0u8), &[], &[]);
  let mut input = input(&scalar, 0, F128::ZERO);
  input[0] = F128::new(u64::MAX - 2, u64::MAX);
  assert_eq!(
    byte_span::evaluate(&input),
    [F128::new(u64::MAX, 0), F128::new(u64::MAX, u64::MAX), F128::ZERO]
  );
  assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
}

#[test]
fn byte_array_range_limit_truncation_overflow_and_noncanonical_lengths_reject()
{
  let gate = ByteArraySpanGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let data = encoded(&BigUint::from(3u8), &[9; 3], &[]);
  for end in 0..data.len() {
    reject(&gate, &r1cs, &input(&data[..end], 0, F128::new(3, 0)));
  }
  let row = input(&data, 0, F128::new(3, 0));
  let mut changed = row;
  changed[1] = F128::new(2, 0);
  reject(&gate, &r1cs, &changed);
  for tag in [0, 1, 2, 3, 4, 5, 7, 255] {
    let mut changed = data.clone();
    changed[0] = tag;
    reject(&gate, &r1cs, &input(&changed, 0, F128::new(3, 0)));
  }
  for natural in [
    vec![0x80, 0],
    vec![0x80; 19],
    tests::natural_bytes(&(BigUint::from(1u8) << 128usize)),
    tests::natural_bytes(&(BigUint::from(1u8) << 64usize)),
  ] {
    let mut changed = vec![6];
    changed.extend(natural);
    changed.resize(32, 0);
    let mut row = input(&changed, 0, F128::new(u64::MAX, u64::MAX));
    row[0].hi = u64::MAX;
    reject(&gate, &r1cs, &row);
  }
  for (offset, file_length) in [
    (6, 5),
    (u64::MAX, u64::MAX),
    (u64::MAX - 1, u64::MAX),
    (u64::MAX - 4, u64::MAX),
  ] {
    let mut changed = row;
    changed[0] = F128::new(offset, file_length);
    reject(&gate, &r1cs, &changed);
  }
}

#[test]
fn byte_array_u128_limits_and_following_data_remain_distinct_from_file_padding()
{
  let gate = ByteArraySpanGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let data = encoded(&BigUint::from(3u8), &[9; 3], &[0x81, 0xff, 0x11]);
  let mut row = input(&data, 0, F128::new(3, 0));
  let expected = byte_span::evaluate(&row);
  for bit in 0..64 {
    row[1] = F128::new(0, 1 << bit);
    assert_eq!(byte_span::evaluate(&row), expected);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &row)));
  }
  let mut changed = data.clone();
  *changed.last_mut().unwrap() ^= 0xff;
  let after = input(&changed, 0, F128::new(3, 0));
  assert_eq!(byte_span::evaluate(&after), expected);
  assert!(tests::satisfies(&r1cs, &bits(&gate, &after)));
  for byte in data.len()..32 {
    let mut changed = after;
    let word = 2 + byte / 16;
    if byte % 16 < 8 {
      changed[word].lo ^= 1 << (8 * (byte % 16));
    } else {
      changed[word].hi ^= 1 << (8 * (byte % 16 - 8));
    }
    reject(&gate, &r1cs, &changed);
  }
}

#[test]
fn byte_array_outputs_padding_and_count_emission_are_fully_bound() {
  use crate::sizing::{CircuitEmitter, CountingEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  let gate = ByteArraySpanGate::new(3).unwrap();
  let data = encoded(&BigUint::from(3u8), &[9; 3], &[]);
  let input = input(&data, 0, F128::new(3, 0));
  let r1cs = gate.r1cs();
  let mut row = bits(&gate, &input);
  tests::output_bits_are_bound(&r1cs, &mut row, 512, 384);
  row[gate.plan().k() - 1] = true;
  assert!(!tests::satisfies(&r1cs, &row));
  for rows in
    [vec![], vec![ByteArraySpanRow(input)], vec![ByteArraySpanRow(input); 5]]
  {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  fn emit(b: &mut impl CircuitEmitter, gate: ByteArraySpanGate) {
    let slot = ByteArraySpanSlot::declare(b, gate);
    for _ in 0..3 {
      let cursor = b.input();
      let limit = b.input();
      let data = [b.input(), b.input()];
      let output = slot.decode(b, cursor, limit, data);
      b.publish(output.range);
      b.publish(output.next);
    }
  }
  let gate = ByteArraySpanGate::new(3).unwrap();
  let mut count = CountingEmitter::new();
  emit(&mut count, gate.clone());
  assert!(gate.plan.get().is_none());
  let mut b = ShapeBuilder::new(3);
  emit(&mut b, gate.clone());
  let shape = b.finish().unwrap();
  count.ensure_matches(&shape).unwrap();
  assert_eq!(count.registry(3).1, shape.counts);
  assert_eq!(gate.input_count(), 4);
  assert_eq!(gate.output_count(), 3);
  assert!(ByteArraySpanGate::new(2).is_err());
  assert!(ByteArraySpanGate::new(21).is_err());
  eprintln!(
    "byte-span codec: k_log={}, useful_bits={}",
    gate.plan().k_log(),
    gate.plan().useful_bits()
  );
}
