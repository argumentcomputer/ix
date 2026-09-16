use super::*;
use crate::{
  ixby::bits::{fill_words, read_words},
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;

fn u128_word(value: u128) -> F128 {
  F128::new(value as u64, (value >> 64) as u64)
}

pub(super) fn input(bytes: &[u8], length: u64) -> Vec<F128> {
  let mut padded = vec![0; HEADER_PREFIX_BYTES];
  let copy = bytes.len().min(padded.len());
  padded[..copy].copy_from_slice(&bytes[..copy]);
  let mut input = vec![F128::new(length, 0)];
  input.extend(
    padded.as_chunks::<16>().0.iter().map(|word| crate::hash::pack_bytes(word)),
  );
  input
}

pub(super) fn bytes(fields: &[u128; HEADER_FIELDS], body: &[u8]) -> Vec<u8> {
  let mut bytes = b"IXBF\x01\0\0\0\x01\0\0\0".to_vec();
  for field in fields {
    bytes.extend(tests::natural_bytes(&BigUint::from(*field)));
  }
  bytes.extend_from_slice(body);
  bytes
}

pub(super) fn bits(gate: &HeaderDecodeGate, input: &[F128]) -> Vec<bool> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| fill_words(input, bits));
  assert_eq!(
    read_words(&row, gate.input_count(), gate.output_count()),
    header::evaluate(input)
  );
  row
}

fn reject(gate: &HeaderDecodeGate, r1cs: &BlockR1cs, input: &[F128]) {
  let mut row = bits(gate, input);
  assert!(tests::satisfies(r1cs, &row));
  let residual = (gate.input_count() + gate.output_count() - 1) * 128;
  assert!(row[residual]);
  row[residual] = false;
  assert!(!tests::satisfies(r1cs, &row));
}

pub(super) fn fixture() -> ([u128; HEADER_FIELDS], Vec<u8>) {
  // Includes wide limits, wide fuel and a wide entry reference. This is a
  // header-codec fixture, not a claim that the omitted program body is valid.
  let fields = [
    65536,
    4096,
    65536,
    8192,
    1024,
    65536,
    65536,
    4096,
    65536,
    16777216,
    (1 << 70) + 17,
    (1 << 65) + 3,
    2,
  ];
  let data = bytes(&fields, &[0x81, 0xff, 0, 0xaa, 0x11]);
  (fields, data)
}

#[test]
fn functional_header_preserves_u128_metadata_and_exact_constructor_cursor() {
  let gate = HeaderDecodeGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let (fields, data) = fixture();
  for length in [data.len() as u64, 1_002_355, 1 << 32, u64::MAX] {
    let row = input(&data, length);
    let bits = bits(&gate, &row);
    assert!(tests::satisfies(&r1cs, &bits));
    let outputs = header::evaluate(&row);
    assert_eq!(outputs[..HEADER_FIELDS], fields.map(u128_word));
    assert_eq!(outputs[HEADER_FIELDS], F128::new((data.len() - 5) as u64, 0));
    assert_eq!(outputs.last(), Some(&F128::ZERO));
  }
  for field in 0..HEADER_FIELDS - 1 {
    let mut wide = fields;
    wide[field] = u128::MAX;
    let bytes = bytes(&wide, &[3; 8]);
    let input = input(&bytes, bytes.len() as u64);
    assert!(tests::satisfies(&r1cs, &bits(&gate, &input)));
    assert_eq!(header::evaluate(&input)[field], u128_word(u128::MAX));
    assert_eq!(header::evaluate(&input).last(), Some(&F128::ZERO));
  }
  eprintln!(
    "functional header table: k_log={}, useful_bits={}, prefix_bytes={HEADER_PREFIX_BYTES}",
    gate.plan().k_log(),
    gate.plan().useful_bits()
  );
}

#[test]
fn functional_header_rejects_noncanonical_versions_truncation_wide_overflow_and_counts()
 {
  let gate = HeaderDecodeGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let (fields, data) = fixture();
  let end = data.len() - 5;
  for length in 0..end {
    reject(&gate, &r1cs, &input(&data[..length], length as u64));
  }
  for byte in 0..12 {
    let mut changed = data.clone();
    changed[byte] ^= 1;
    reject(&gate, &r1cs, &input(&changed, changed.len() as u64));
  }
  let mut nonminimal = data.clone();
  nonminimal.splice(12..15, [0x80, 0x80, 0x84, 0]);
  reject(&gate, &r1cs, &input(&nonminimal, nonminimal.len() as u64));
  let mut overflow = data.clone();
  overflow
    .splice(12..15, tests::natural_bytes(&(BigUint::from(1u8) << 128usize)));
  reject(&gate, &r1cs, &input(&overflow, overflow.len() as u64));
  let mut too_many = fields;
  too_many[12] = 4097;
  let overflow = bytes(&too_many, &[3; 5000]);
  reject(&gate, &r1cs, &input(&overflow, overflow.len() as u64));
  too_many[12] = 6;
  let short = bytes(&too_many, &[3; 5]);
  reject(&gate, &r1cs, &input(&short, short.len() as u64));
  let row = input(&data, data.len() as u64);
  for bit in 0..64 {
    let mut changed = row.clone();
    changed[0].hi = 1 << bit;
    reject(&gate, &r1cs, &changed);
  }
}

#[test]
fn header_padding_is_exact_but_following_body_bytes_are_not_padding() {
  let gate = HeaderDecodeGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let (fields, data) = fixture();
  let first = input(&data, data.len() as u64);
  let mut changed = data.clone();
  *changed.last_mut().unwrap() ^= 0xff;
  let second = input(&changed, changed.len() as u64);
  assert_eq!(header::evaluate(&first), header::evaluate(&second));
  assert!(tests::satisfies(&r1cs, &bits(&gate, &second)));
  for byte in [data.len(), 127, 128, HEADER_PREFIX_BYTES - 1] {
    let mut changed = first.clone();
    let word = 1 + byte / 16;
    if byte % 16 < 8 {
      changed[word].lo ^= 1 << (8 * (byte % 16));
    } else {
      changed[word].hi ^= 1 << (8 * (byte % 16 - 8));
    }
    reject(&gate, &r1cs, &changed);
  }
  let mut only_prefix = fields;
  only_prefix[12] = 0;
  let data = bytes(&only_prefix, &[]);
  // A header is not a whole program: a later whole-image gate must require
  // and validate the function vector even though this prefix itself is valid.
  let row = input(&data, data.len() as u64);
  assert_eq!(header::evaluate(&row).last(), Some(&F128::ZERO));
  assert!(tests::satisfies(&r1cs, &bits(&gate, &row)));
}

#[test]
fn every_header_output_and_unused_column_is_bound() {
  let gate = HeaderDecodeGate::new(3).unwrap();
  let (_, data) = fixture();
  let mut row = bits(&gate, &input(&data, data.len() as u64));
  let r1cs = gate.r1cs();
  tests::output_bits_are_bound(
    &r1cs,
    &mut row,
    gate.input_count() * 128,
    gate.output_count() * 128,
  );
  row[gate.plan().k() - 1] = true;
  assert!(!tests::satisfies(&r1cs, &row));
}
