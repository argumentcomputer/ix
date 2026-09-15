use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::bits::{fill_words, read_words},
};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;

pub(super) fn checked(
  plan: &BooleanR1csPlan,
  r1cs: &BlockR1cs,
  input: &[F128],
  expected: &[F128],
) -> Vec<bool> {
  let mut row = vec![false; plan.k()];
  plan.fill_row(&mut row, |bits| fill_words(input, bits));
  assert_eq!(
    read_words(&row, input.len(), expected.len()),
    expected,
    "input {input:?}"
  );
  assert!(tests::satisfies(r1cs, &row));
  if expected.last() != Some(&F128::ZERO) {
    let residual = (input.len() + expected.len() - 1) * 128;
    row[residual] = false;
    assert!(!tests::satisfies(r1cs, &row));
    row[residual] = true;
  }
  row
}

pub(super) fn utf8_input(
  source: &[u8],
  cursor: F128,
  state: F128,
  enabled: bool,
) -> [F128; 5] {
  let mut bytes = [0; 32];
  if enabled && state.lo != 0 {
    let offset = cursor.lo as usize;
    let end = source.len().min(offset.saturating_add(32));
    if offset < end {
      bytes[..end - offset].copy_from_slice(&source[offset..end]);
    }
  }
  [
    cursor,
    state,
    F128::new(u64::from(enabled), 0),
    crate::hash::pack_bytes(&bytes[..16]),
    crate::hash::pack_bytes(&bytes[16..]),
  ]
}

pub(super) fn magnitude(
  value: &BigUint,
  capacity: NaturalCapacity,
) -> Vec<F128> {
  let mut bytes = value.to_bytes_le();
  assert!(bytes.len() <= capacity.magnitude_words() * 16);
  bytes.resize(capacity.magnitude_words() * 16, 0);
  bytes
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| crate::hash::pack_bytes(word))
    .collect()
}

#[test]
fn payload_cursor_checks_all_u64_carries_lengths_and_control_padding() {
  let gate = PayloadCursorGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let mut rows = vec![
    [F128::ZERO, F128::ZERO, F128::ZERO],
    [F128::new(7, 10), F128::new(3, 0), F128::ONE],
    [F128::new(10, 10), F128::ZERO, F128::ONE],
    [F128::new(11, 10), F128::ZERO, F128::ONE],
    [F128::new(7, 10), F128::new(4, 0), F128::ONE],
    [F128::new(7, 10), F128::ONE, F128::ZERO],
  ];
  for bit in 0..64 {
    let n = 1u64 << bit;
    rows.push([F128::new(u64::MAX - n, u64::MAX), F128::new(n, 0), F128::ONE]);
    rows.push([
      F128::new(u64::MAX - n + 1, u64::MAX),
      F128::new(n, 0),
      F128::ONE,
    ]);
    rows.push([F128::new(0, u64::MAX), F128::new(0, n), F128::ONE]);
    rows.push([F128::ZERO, F128::ZERO, F128::new(0, n)]);
    if bit != 0 {
      rows.push([F128::ZERO, F128::ZERO, F128::new(n, 0)]);
    }
  }
  for input in rows {
    let output = payload::evaluate(&input);
    let [cursor, length, enabled] = input;
    let valid = cursor.lo <= cursor.hi
      && length.hi == 0
      && enabled.hi == 0
      && enabled.lo <= 1
      && (enabled.lo == 1 || length.lo == 0)
      && u128::from(cursor.lo) + u128::from(length.lo) <= u128::from(cursor.hi);
    assert_eq!(output[3] == F128::ZERO, valid);
    checked(gate.plan(), &r1cs, &input, &output);
  }
}

#[test]
fn natural_guest_bit_limit_checks_every_4096_basis_bit_and_full_u128_limits() {
  let cap = NaturalCapacity::new(4096).unwrap();
  let gate = NaturalLimitGate::new(3, cap).unwrap();
  let r1cs = gate.r1cs();
  for bit in 0usize..4096 {
    let value = BigUint::from(1u8) << bit;
    let mut input = vec![F128::new(value.bits(), 0), F128::ONE];
    input.extend(magnitude(&value, cap));
    assert_eq!(
      natural_limit::evaluate(cap, &input),
      [F128::new(bit as u64 + 1, 0), F128::ZERO]
    );
    checked(gate.plan(), &r1cs, &input, &natural_limit::evaluate(cap, &input));
    input[0].lo -= 1;
    let output = natural_limit::evaluate(cap, &input);
    assert_eq!(output[1], F128::ONE);
    checked(gate.plan(), &r1cs, &input, &output);
  }
  for width in [0, 1, 7, 64, 65, 127, 128, 129, 4095, 4096] {
    let cap = NaturalCapacity::new(width).unwrap();
    let gate = NaturalLimitGate::new(3, cap).unwrap();
    let r1cs = gate.r1cs();
    for value in [BigUint::from(0u8), (BigUint::from(1u8) << width) - 1u8] {
      for limit in [0, width as u128, u64::MAX as u128, 1u128 << 64, u128::MAX]
      {
        for enabled in [F128::ZERO, F128::ONE, F128::new(2, 0), F128::new(1, 1)]
        {
          let mut input =
            vec![F128::new(limit as u64, (limit >> 64) as u64), enabled];
          input.extend(magnitude(&value, cap));
          let output = natural_limit::evaluate(cap, &input);
          assert_eq!(output[0].lo, value.bits());
          assert_eq!(
            output[1] == F128::ZERO,
            enabled.hi == 0
              && enabled.lo <= 1
              && (enabled.lo == 1 || value.bits() == 0)
              && u128::from(value.bits()) <= limit
          );
          checked(gate.plan(), &r1cs, &input, &output);
        }
      }
    }
    for bit in width..cap.magnitude_words() * 128 {
      let mut input = vec![F128::new(u64::MAX, u64::MAX), F128::ONE];
      input.extend(magnitude(&(BigUint::from(1u8) << bit), cap));
      let output = natural_limit::evaluate(cap, &input);
      assert_eq!(output[1], F128::ONE);
      checked(gate.plan(), &r1cs, &input, &output);
    }
  }
}

fn stream(
  source: &[u8],
  payload_len: usize,
  circuit: Option<(&Utf8ChunkGate, &BlockR1cs)>,
) -> bool {
  let mut cursor = F128::new(0, source.len() as u64);
  let mut state = F128::new(payload_len as u64, 0);
  let mut valid = true;
  loop {
    let input = utf8_input(source, cursor, state, true);
    let output = utf8::evaluate(&input);
    if let Some((gate, r1cs)) = circuit {
      checked(gate.plan(), r1cs, &input, &output);
    }
    valid &= output[2] == F128::ZERO;
    cursor = output[0];
    state = output[1];
    if state.lo == 0 {
      break;
    }
  }
  assert_eq!(cursor.lo, payload_len as u64);
  valid
}

#[test]
fn utf8_every_dfa_transition_and_unicode_boundary_matches_strict_oracle() {
  let gate = Utf8ChunkGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  // All 2,048 state/byte combinations compare every output, including the
  // post-byte DFA even for an unfinished or rejected character.
  for dfa in 0..8 {
    for byte in 0..=255u8 {
      let input = utf8_input(&[byte], F128::new(0, 1), F128::new(1, dfa), true);
      checked(gate.plan(), &r1cs, &input, &utf8::evaluate(&input));
    }
  }
  for first in 0..=255u8 {
    for second in 0..=255u8 {
      let bytes = [first, second];
      assert_eq!(stream(&bytes, 2, None), std::str::from_utf8(&bytes).is_ok());
    }
    assert_eq!(
      stream(&[first], 1, None),
      std::str::from_utf8(&[first]).is_ok()
    );
  }
  for scalar in 0..=0x10ffff {
    if let Some(ch) = char::from_u32(scalar) {
      let mut bytes = [0; 4];
      let bytes = ch.encode_utf8(&mut bytes).as_bytes();
      assert!(stream(bytes, bytes.len(), None));
    }
  }
  let boundaries = [0, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xff];
  for first in
    [0xc0, 0xc1, 0xc2, 0xdf, 0xe0, 0xed, 0xef, 0xf0, 0xf1, 0xf4, 0xf5, 0xff]
  {
    for second in boundaries {
      for last in boundaries {
        let bytes = if first < 0xf0 {
          vec![first, second, last]
        } else {
          vec![first, second, 0x80, last]
        };
        assert_eq!(
          stream(&bytes, bytes.len(), Some((&gate, &r1cs))),
          std::str::from_utf8(&bytes).is_ok(),
          "{bytes:x?}"
        );
      }
    }
  }
}

#[test]
fn utf8_chunks_preserve_split_characters_extent_padding_and_disabled_state() {
  let gate = Utf8ChunkGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  for prefix in [0, 1, 28, 29, 30, 31, 32, 62, 63, 64] {
    for body in [
      vec![],
      vec![0],
      "¢€𐀀􏿿".as_bytes().to_vec(),
      vec![0xc0, 0x80],
      vec![0xed, 0xa0, 0x80],
      vec![0xf4, 0x90, 0x80, 0x80],
      vec![0xe0],
      vec![0xf0, 0x90, 0x80],
      vec![0x80],
    ] {
      let mut bytes = vec![b'a'; prefix];
      bytes.extend(body);
      let length = bytes.len();
      let expected = std::str::from_utf8(&bytes).is_ok();
      bytes.extend([0xff, 0xc0, 0x80, 0x11]); // Following records are not string padding.
      assert_eq!(stream(&bytes, length, Some((&gate, &r1cs))), expected);
    }
  }
  // Deterministic structured fuzz against the independent standard library.
  let mut seed = 0x5fa9_53d2_a71b_0831u64;
  for index in 0..1024 {
    let mut bytes = vec![b'a'; index % 96];
    for _ in 0..index % 9 {
      seed ^= seed << 13;
      seed ^= seed >> 7;
      seed ^= seed << 17;
      bytes.push(seed as u8);
    }
    assert_eq!(
      stream(&bytes, bytes.len(), Some((&gate, &r1cs))),
      std::str::from_utf8(&bytes).is_ok()
    );
  }
  let base =
    [F128::new(5, 50), F128::new(33, 6), F128::ZERO, F128::ZERO, F128::ZERO];
  assert_eq!(utf8::evaluate(&base), [base[0], base[1], F128::ZERO]);
  checked(gate.plan(), &r1cs, &base, &utf8::evaluate(&base));
  let mut bad = Vec::new();
  for bit in 0..64 {
    let mut row = base;
    row[1].hi |= 1u64 << bit;
    if bit >= 3 {
      bad.push(row);
    }
    let mut row = base;
    row[2].hi = 1u64 << bit;
    bad.push(row);
    if bit != 0 {
      let mut row = base;
      row[2].lo = 1u64 << bit;
      bad.push(row);
    }
    let mut row = base;
    row[0] = F128::new(u64::MAX, u64::MAX);
    row[1] = F128::new(1u64 << bit, 0);
    row[2] = F128::ONE;
    bad.push(row);
  }
  for word in 3..5 {
    for bit in 0..128 {
      let mut row = base;
      if bit < 64 {
        row[word].lo = 1 << bit;
      } else {
        row[word].hi = 1 << (bit - 64);
      }
      bad.push(row);
    }
  }
  for dfa in 1..8 {
    for enable in [F128::ZERO, F128::ONE] {
      let mut row = base;
      row[1] = F128::new(0, dfa);
      row[2] = enable;
      bad.push(row);
    }
  }
  let mut row = base;
  row[0] = F128::new(51, 50);
  bad.push(row);
  let mut row = base;
  row[1].lo = 46;
  bad.push(row);
  let small = utf8_input(b"ok", F128::new(0, 2), F128::new(2, 0), true);
  for byte in 2..32 {
    let mut row = small;
    if byte % 16 < 8 {
      row[3 + byte / 16].lo ^= 1 << (8 * (byte % 16));
    } else {
      row[3 + byte / 16].hi ^= 1 << (8 * (byte % 16 - 8));
    }
    bad.push(row);
  }
  for row in bad {
    let output = utf8::evaluate(&row);
    assert_eq!(output[2], F128::ONE, "{row:?}");
    checked(gate.plan(), &r1cs, &row, &output);
  }
  // Exact u64 endpoint with no carry remains valid.
  let mut row = utf8_input(b"a", F128::new(0, 1), F128::new(1, 0), true);
  row[0] = F128::new(u64::MAX - 1, u64::MAX);
  assert_eq!(utf8::evaluate(&row)[2], F128::ZERO);
  checked(gate.plan(), &r1cs, &row, &utf8::evaluate(&row));
}

#[test]
fn scalar_payload_outputs_recycled_padding_and_lazy_count_emission_are_bound() {
  use crate::sizing::{CircuitEmitter, CountingEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  let cap = NaturalCapacity::new(4096).unwrap();
  let payload = PayloadCursorGate::new(3).unwrap();
  let natural = NaturalLimitGate::new(3, cap).unwrap();
  let utf8 = Utf8ChunkGate::new(3).unwrap();
  let p = [F128::new(5, 10), F128::new(3, 0), F128::ONE];
  let mut n = vec![F128::new(4096, 0), F128::ONE];
  n.extend(magnitude(&((BigUint::from(1u8) << 4096usize) - 1u8), cap));
  let u = utf8_input("€".as_bytes(), F128::new(0, 3), F128::new(3, 0), true);
  for (plan, input, output) in [
    (payload.plan(), p.as_slice(), payload::evaluate(&p).to_vec()),
    (natural.plan(), n.as_slice(), natural_limit::evaluate(cap, &n).to_vec()),
    (utf8.plan(), u.as_slice(), utf8::evaluate(&u).to_vec()),
  ] {
    let r1cs = plan.block_r1cs(3);
    let mut row = checked(plan, &r1cs, input, &output);
    tests::output_bits_are_bound(
      &r1cs,
      &mut row,
      input.len() * 128,
      output.len() * 128,
    );
    row[plan.k() - 1] = true;
    assert!(!tests::satisfies(&r1cs, &row));
    eprintln!(
      "scalar payload: inputs={} outputs={} k_log={} useful_bits={}",
      input.len(),
      output.len(),
      plan.k_log(),
      plan.useful_bits()
    );
  }
  for count in [0, 1, 5] {
    let rows = vec![PayloadCursorRow(p); count];
    crate::ixby::test_support::padding(
      payload.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| payload.generate_witness_into(&rows, dst),
    );
    let rows = vec![NaturalLimitRow(n.clone()); count];
    crate::ixby::test_support::padding(
      natural.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| natural.generate_witness_into(&rows, dst),
    );
    let rows = vec![Utf8ChunkRow(u); count];
    crate::ixby::test_support::padding(
      utf8.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| utf8.generate_witness_into(&rows, dst),
    );
  }
  fn emit(
    b: &mut impl CircuitEmitter,
    p: PayloadCursorGate,
    n: NaturalLimitGate,
    u: Utf8ChunkGate,
  ) {
    let cap = n.capacity();
    let p = PayloadCursorSlot::declare(b, p);
    let n = NaturalLimitSlot::declare(b, n);
    let u = Utf8ChunkSlot::declare(b, u);
    for _ in 0..3 {
      let cursor = b.input();
      let length = b.input();
      let enabled = b.input();
      let range = p.advance(b, cursor, length, enabled);
      b.publish(range.natural_control);
      b.publish(range.range);
      b.publish(range.next);
      let limit = b.input();
      let magnitude: Vec<_> =
        (0..cap.magnitude_words()).map(|_| b.input()).collect();
      let length_bits = n.check(b, limit, enabled, &magnitude);
      b.publish(length_bits);
      let bytes = [b.input(), b.input()];
      let chunk = u.check(b, cursor, length, enabled, bytes);
      b.publish(chunk.next);
      b.publish(chunk.state);
    }
  }
  let p = PayloadCursorGate::new(3).unwrap();
  let n = NaturalLimitGate::new(3, cap).unwrap();
  let u = Utf8ChunkGate::new(3).unwrap();
  let mut count = CountingEmitter::new();
  emit(&mut count, p.clone(), n.clone(), u.clone());
  assert!(
    p.plan.get().is_none() && n.plan.get().is_none() && u.plan.get().is_none()
  );
  let mut b = ShapeBuilder::new(3);
  emit(&mut b, p, n, u);
  let shape = b.finish().unwrap();
  count.ensure_matches(&shape).unwrap();
  assert_eq!(count.registry(3).1, shape.counts);
  for nu in [2, 21] {
    assert!(PayloadCursorGate::new(nu).is_err());
    assert!(NaturalLimitGate::new(nu, cap).is_err());
    assert!(Utf8ChunkGate::new(nu).is_err());
  }
}
