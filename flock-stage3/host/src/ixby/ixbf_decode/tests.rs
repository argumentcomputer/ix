use super::*;
use crate::{boolean::write_f128, ixby::bits::read_words, sizing::CountedGate};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;

pub(super) fn natural_bytes(value: &BigUint) -> Vec<u8> {
  let digits = value.to_radix_le(128);
  digits
    .iter()
    .enumerate()
    .map(|(index, digit)| {
      digit | if index + 1 == digits.len() { 0 } else { 128 }
    })
    .collect()
}

pub(super) fn input(
  gate: &NaturalDecodeGate,
  bytes: &[u8],
  enabled: bool,
) -> Vec<F128> {
  assert!(bytes.len() <= 16 * gate.capacity().encoded_words());
  let mut result = vec![F128::new(bytes.len() as u64, u64::from(enabled))];
  let mut padded = vec![0; gate.capacity().encoded_words() * 16];
  padded[..bytes.len()].copy_from_slice(bytes);
  result.extend(
    padded.as_chunks::<16>().0.iter().map(|word| crate::hash::pack_bytes(word)),
  );
  result
}

#[test]
fn all_4096_magnitude_basis_bits_and_every_output_bit_are_constrained() {
  let gate =
    NaturalDecodeGate::new(3, NaturalCapacity::new(4096).unwrap()).unwrap();
  let r1cs = gate.r1cs();
  for bit in 0..4096 {
    let value = BigUint::from(1u8) << bit;
    let input = input(&gate, &natural_bytes(&value), true);
    let row = bits(&gate, &input);
    assert!(satisfies(&r1cs, &row));
    let output = read_words(&row, gate.input_count(), gate.output_count());
    assert_eq!(output.last(), Some(&F128::ZERO));
    let magnitude: Vec<_> = output[..gate.capacity().magnitude_words()]
      .iter()
      .flat_map(|word| {
        word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
      })
      .collect();
    assert_eq!(BigUint::from_bytes_le(&magnitude), value);
  }
  let input = input(
    &gate,
    &natural_bytes(&((BigUint::from(1u8) << 4096usize) - 1u8)),
    true,
  );
  let mut row = bits(&gate, &input);
  output_bits_are_bound(
    &r1cs,
    &mut row,
    gate.input_count() * 128,
    gate.output_count() * 128,
  );
  row[gate.plan().k() - 1] = true;
  assert!(!satisfies(&r1cs, &row));
  eprintln!(
    "4096-bit natural codec: k_log={}, useful_bits={}, encoded_bytes={}",
    gate.plan().k_log(),
    gate.plan().useful_bits(),
    gate.capacity().encoded_bytes()
  );
}

#[test]
fn natural_and_header_witness_drivers_clear_recycled_padding_and_constant_stripes()
 {
  use crate::ixby::bits::fill_words;
  for width in [0, 128, 4096] {
    let gate =
      NaturalDecodeGate::new(3, NaturalCapacity::new(width).unwrap()).unwrap();
    let good = NaturalDecodeRow(input(&gate, &[0], true));
    for rows in [vec![], vec![good.clone()], vec![good; 5]] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
  let gate = HeaderDecodeGate::new(3).unwrap();
  let (_, data) = header_tests::fixture();
  let good = HeaderDecodeRow(header_tests::input(&data, data.len() as u64));
  for rows in [vec![], vec![good.clone()], vec![good; 5]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}

#[test]
fn codec_count_pass_is_lazy_and_matches_capacity_only_emission() {
  use crate::sizing::{CircuitEmitter, CountingEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  fn emit(
    b: &mut impl CircuitEmitter,
    natural: NaturalDecodeGate,
    header: HeaderDecodeGate,
  ) {
    let cap = natural.capacity();
    let natural = NaturalDecodeSlot::declare(b, natural);
    let header = HeaderDecodeSlot::declare(b, header);
    for _ in 0..3 {
      let control = b.input();
      let words: Vec<_> = (0..cap.encoded_words()).map(|_| b.input()).collect();
      for value in natural.decode(b, control, &words) {
        b.publish(value);
      }
      let length = b.input();
      let prefix: Vec<_> =
        (0..HEADER_PREFIX_WORDS).map(|_| b.input()).collect();
      let fields = header.decode(b, length, &prefix);
      b.publish(fields.max_steps);
      b.publish(fields.constructors_offset);
    }
  }
  for width in [0, 65, 128, 4096] {
    let natural =
      NaturalDecodeGate::new(3, NaturalCapacity::new(width).unwrap()).unwrap();
    let header = HeaderDecodeGate::new(3).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, natural.clone(), header.clone());
    assert!(natural.plan.get().is_none());
    assert!(header.plan.get().is_none());
    let mut builder = ShapeBuilder::new(3);
    emit(&mut builder, natural, header);
    let shape = builder.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    assert_eq!(count.registry(3).1, shape.counts);
  }
  assert!(NaturalCapacity::new(4097).is_err());
  assert!(NaturalDecodeGate::new(2, NaturalCapacity::new(0).unwrap()).is_err());
  assert!(
    NaturalDecodeGate::new(21, NaturalCapacity::new(0).unwrap()).is_err()
  );
  assert!(HeaderDecodeGate::new(2).is_err());
  assert!(HeaderDecodeGate::new(21).is_err());
}

pub(super) fn satisfies(r1cs: &BlockR1cs, row: &[bool]) -> bool {
  r1cs.a_0.rows.iter().zip(&r1cs.b_0.rows).zip(row).all(|((a, b), out)| {
    let parity = |columns: &[usize]| {
      columns.iter().fold(false, |p, column| p ^ row[*column])
    };
    (parity(a) & parity(b)) == *out
  })
}

/// Each output has its own C=I constraint row. A changed output bit must
/// already fail that row; no repeated capacity-sized allocation is needed.
pub(super) fn output_bits_are_bound(
  r1cs: &BlockR1cs,
  bits: &mut [bool],
  start: usize,
  count: usize,
) {
  assert!(satisfies(r1cs, bits));
  for bit in start..start + count {
    bits[bit] ^= true;
    let parity = |columns: &[usize]| {
      columns.iter().fold(false, |value, column| value ^ bits[*column])
    };
    assert_ne!(
      parity(&r1cs.a_0.rows[bit]) & parity(&r1cs.b_0.rows[bit]),
      bits[bit],
      "unbound output bit {bit}"
    );
    bits[bit] ^= true;
  }
}

pub(super) fn bits(gate: &NaturalDecodeGate, input: &[F128]) -> Vec<bool> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| {
    for (word, value) in input.iter().enumerate() {
      write_f128(bits, 128 * word, *value);
    }
  });
  assert_eq!(
    read_words(&row, gate.input_count(), gate.output_count()),
    natural::evaluate(gate.capacity(), input)
  );
  row
}

#[test]
fn canonical_naturals_preserve_every_bit_through_the_explicit_capacity() {
  for width in [0, 1, 7, 8, 32, 64, 65, 112, 127, 128, 129, 256, 4096] {
    let gate =
      NaturalDecodeGate::new(3, NaturalCapacity::new(width).unwrap()).unwrap();
    let r1cs = gate.r1cs();
    let mut values = vec![BigUint::from(0u8)];
    if width != 0 {
      values.extend([
        BigUint::from(1u8) << (width - 1),
        (BigUint::from(1u8) << width) - 1u8,
      ]);
    }
    for value in values {
      let row = input(&gate, &natural_bytes(&value), true);
      let bits = bits(&gate, &row);
      assert!(satisfies(&r1cs, &bits));
      let outputs = natural::evaluate(gate.capacity(), &row);
      assert_eq!(outputs.last(), Some(&F128::ZERO));
      let decoded: Vec<_> = outputs[..outputs.len() - 1]
        .iter()
        .flat_map(|word| {
          word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
        })
        .collect();
      assert_eq!(BigUint::from_bytes_le(&decoded), value);
    }
  }
}

#[test]
fn natural_payload_lengths_continuations_minimality_overflow_and_padding_reject()
 {
  let gate =
    NaturalDecodeGate::new(3, NaturalCapacity::new(65).unwrap()).unwrap();
  let r1cs = gate.r1cs();
  let residual = 128 * (gate.input_count() + gate.output_count() - 1);
  let good = input(&gate, &[1], true);
  let mut cases = vec![
    input(&gate, &[], true),
    input(&gate, &[0x80, 0], true),
    input(&gate, &[1, 0], true),
    input(&gate, &[0x80; 10], true),
    input(&gate, &natural_bytes(&(BigUint::from(1u8) << 65usize)), true),
    input(&gate, &[1], false),
  ];
  for bit in 0..64 {
    let mut row = good.clone();
    row[0].lo ^= 1 << bit;
    cases.push(row);
  }
  for bit in 1..64 {
    let mut row = good.clone();
    row[0].hi |= 1 << bit;
    cases.push(row);
  }
  let mut extra = good.clone();
  extra[1].hi |= 1 << 63;
  cases.push(extra);
  for input in cases {
    let mut row = bits(&gate, &input);
    assert!(satisfies(&r1cs, &row));
    assert!(row[residual]);
    row[residual] = false;
    assert!(
      !satisfies(&r1cs, &row),
      "recomputed invalid advice bypassed the validity pin"
    );
  }
  let disabled = input(&gate, &[], false);
  assert!(
    natural::evaluate(gate.capacity(), &disabled)
      .iter()
      .all(|word| *word == F128::ZERO)
  );
  assert!(satisfies(&r1cs, &bits(&gate, &disabled)));
}
