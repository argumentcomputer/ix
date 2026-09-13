use super::*;
use crate::{
  ixby::{
    bits::{fill_words, read_words},
    byte_value::ByteCapacity,
    control::ControlCapacities,
    decode::{PrimitiveSet, test_support::meta},
    value::{BOOL_TAG, NAT_TAG, WORD32_TAG},
  },
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};

fn gate(bits: usize) -> NatDispatchGate {
  NatDispatchGate::new(
    3,
    (
      NatCapacity::new(bits).unwrap(),
      ByteCapacity::new(bits.div_ceil(8).max(1)).unwrap(),
    ),
    ControlCapacities { locals: 3, continuations: 1, arguments: 2 },
    2,
    4,
    PrimitiveSet::crypto_nat(),
  )
  .unwrap()
}

fn magnitude(value: u128) -> Vec<u8> {
  let mut bytes = value.to_le_bytes().to_vec();
  while bytes.last() == Some(&0) {
    bytes.pop();
  }
  bytes
}

fn buffer(g: &NatDispatchGate, bytes: &[u8]) -> Vec<F128> {
  let mut result = vec![F128::new(bytes.len() as u64, 0)];
  let mut padded = vec![0; 16 * g.bytes.data_words()];
  padded[..bytes.len()].copy_from_slice(bytes);
  result.extend(padded.chunks(16).map(crate::hash::pack_bytes));
  result
}

fn input(g: &NatDispatchGate, opcode: u8, a: &[u8], b: &[u8]) -> Vec<F128> {
  let mut input = vec![F128::ZERO; g.control.frame_words()];
  input.extend([
    meta(0, 2, 1, 0),
    meta(0, opcode.into(), 2, 0),
    F128::new(3, 0),
  ]);
  input.extend([
    F128::new(NAT_TAG, 0),
    F128::ZERO,
    F128::new(NAT_TAG, 0),
    F128::new(1, 0),
  ]);
  input.extend(buffer(g, a));
  input.extend(buffer(g, b));
  input
}

fn run(g: &NatDispatchGate, input: &[F128]) -> (Vec<bool>, Vec<F128>) {
  let mut bits = vec![false; g.plan().k()];
  g.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  let output = read_words(&bits, input.len(), g.output_count());
  (bits, output)
}

fn constraints(g: &NatDispatchGate, r1cs: &BlockR1cs, row: &[bool]) {
  let mut witness = row.to_vec();
  witness.resize(r1cs.n(), false);
  assert!(r1cs.satisfies(&witness));
  let residual = 128 * (g.input_count() + g.output_count() - 1);
  witness[residual] ^= true;
  assert!(
    !r1cs.satisfies(&witness),
    "recomputed advice cannot forge acceptance"
  );
}

fn result(g: &NatDispatchGate, output: &[F128]) -> u128 {
  let base = g.result_word();
  if output[base].lo == BOOL_TAG {
    return u128::from(output[base + 1].lo);
  }
  assert_eq!(output[base], F128::new(NAT_TAG, 0));
  assert_eq!(output[base + 1], F128::new(3, 0));
  let word = output[base + 3];
  u128::from(word.lo) | (u128::from(word.hi) << 64)
}

#[test]
fn nat_arithmetic_exhaustive_four_bit_oracle_and_real_constraints() {
  let g = gate(4);
  let r1cs = g.r1cs();
  for a in 0u128..16 {
    for b in 0u128..16 {
      let expected = [
        a + b,
        a.saturating_sub(b),
        a * b,
        a.checked_div(b).unwrap_or(0),
        if b == 0 { a } else { a % b },
        u128::from(a == b),
        u128::from(a < b),
      ];
      for (index, expected) in expected.into_iter().enumerate() {
        let input = input(&g, 35 + index as u8, &magnitude(a), &magnitude(b));
        let (bits, output) = run(&g, &input);
        assert_eq!(
          *output.last().unwrap(),
          F128::new(u64::from(expected >= 16), 0),
          "opcode {} a={a} b={b}",
          35 + index
        );
        if expected < 16 {
          assert_eq!(
            result(&g, &output),
            expected,
            "opcode {} a={a} b={b}",
            35 + index
          );
          if index < 5 {
            assert_eq!(
              output[g.result_word() + 2].lo,
              (1u64 << 32) | u64::from(expected != 0)
            );
          }
        }
        if matches!((a, b), (0, 0) | (15, 1) | (7, 3) | (15, 15)) {
          constraints(&g, &r1cs, &bits);
        }
      }
    }
  }
}

#[test]
fn nat_arithmetic_crosses_word_and_field_widths_without_wrapping() {
  let g = gate(96);
  let r1cs = g.r1cs();
  let a = (1u128 << 93) + (1u128 << 64) + 137;
  let b = (1u128 << 65) + 3;
  for (opcode, a, b, expected, valid) in [
    (35, a, b, a + b, true),
    (36, a, b, a - b, true),
    (36, b, a, 0, true),
    (37, (1 << 48) + 3, (1 << 40) + 7, ((1 << 48) + 3) * ((1 << 40) + 7), true),
    (38, a, b, a / b, true),
    (39, a, b, a % b, true),
    (38, a, 0, 0, true),
    (39, a, 0, a, true),
    (40, a, a, 1, true),
    (41, b, a, 1, true),
    (35, (1 << 96) - 1, 1, 0, false),
    (37, 1 << 64, 1 << 64, 0, false),
  ] {
    let input = input(&g, opcode, &magnitude(a), &magnitude(b));
    let (bits, output) = run(&g, &input);
    assert_eq!(*output.last().unwrap(), F128::new(u64::from(!valid), 0));
    if valid {
      assert_eq!(result(&g, &output), expected);
    }
    constraints(&g, &r1cs, &bits);
  }
  // A 192-bit product has nonzero data in the second physical magnitude word.
  let g = gate(192);
  let mut a = vec![0; 17];
  a[16] = 1;
  let mut b = vec![0; 8];
  b[7] = 1;
  let (bits, output) = run(&g, &input(&g, 37, &a, &b));
  assert_eq!(*output.last().unwrap(), F128::ZERO);
  let base = g.result_word() + 2;
  assert_eq!(output[base], F128::new((1 << 32) | 24, 0));
  assert_eq!(output[base + 1], F128::ZERO);
  assert_eq!(output[base + 2], F128::new(1 << 56, 0));
  constraints(&g, &g.r1cs(), &bits);
}

#[test]
fn nat_dispatch_rejects_noncanonical_magnitudes_types_and_recomputed_residuals()
{
  let g = gate(9);
  let r1cs = g.r1cs();
  let good = input(&g, 35, &[255, 1], &[]);
  let frame = g.control.frame_words();
  let first = frame + 7;
  let mut cases = Vec::new();
  let mut bad = good.clone();
  bad[first] = F128::new(3, 0);
  cases.push(bad);
  let mut bad = good.clone();
  bad[first + 1] = F128::new(0x200, 0);
  cases.push(bad);
  let mut bad = good.clone();
  bad[first + 1] = F128::new(0xff, 0);
  cases.push(bad);
  let mut bad = good.clone();
  bad[first] = F128::ZERO;
  cases.push(bad);
  let mut bad = good.clone();
  bad[first + 1].hi = 1;
  cases.push(bad);
  let mut bad = good.clone();
  bad[frame + 3] = F128::new(WORD32_TAG, 0);
  cases.push(bad);
  let mut bad = good.clone();
  bad[frame + 3].hi = 1;
  cases.push(bad);
  let mut bad = good.clone();
  bad[frame + 4] = F128::new(1 << 32, 0);
  cases.push(bad);
  let mut bad = good.clone();
  bad[frame + 1] = meta(0, 35, 1, 0);
  cases.push(bad);
  for bad in cases {
    let (bits, output) = run(&g, &bad);
    assert_eq!(*output.last().unwrap(), F128::ONE);
    constraints(&g, &r1cs, &bits);
  }
  let (bits, output) = run(&g, &good);
  assert_eq!(*output.last().unwrap(), F128::ZERO);
  let mut witness = bits.clone();
  witness.resize(r1cs.n(), false);
  for word in 0..g.output_count() {
    for bit in [0, 31, 32, 63, 64, 127] {
      let column = 128 * (g.input_count() + word) + bit;
      witness[column] ^= true;
      assert!(!r1cs.satisfies(&witness));
      witness[column] ^= true;
    }
  }
  let row = dispatch::NatDispatchRow(good);
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      g.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| g.generate_witness_into(&rows, dst),
    );
  }
}

#[test]
fn nat_case_preserves_zero_frame_and_appends_exact_successor_predecessor() {
  let g = gate(9);
  let r1cs = g.r1cs();
  let f = g.control.frame_words();
  for value in [0, 1, 256, 511] {
    let mut input = input(&g, 35, &magnitude(value), &[]);
    input[0] = meta(0, 0, 1, 0);
    input[1] = F128::new(BOOL_TAG, 0);
    input[2] = F128::ONE;
    input[f] = meta(1, 10, 2, 3);
    input[f + 1] = meta(0, 0, 1, 0);
    input[f + 5] = F128::ZERO;
    input[f + 6] = F128::ZERO;
    let (bits, output) = run(&g, &input);
    assert_eq!(*output.last().unwrap(), F128::ZERO);
    assert_eq!(output[0], meta(0, 0, if value == 0 { 1 } else { 2 }, 0));
    assert_eq!(output[1..3], input[1..3]);
    assert_eq!(output[f], meta(1, 6, 2, 3));
    assert_eq!(output[f + 4], F128::new(BOOL_TAG, 0));
    assert_eq!(output[f + 5], F128::new(u64::from(value == 0), 0));
    if value != 0 {
      assert_eq!(output[3..5], [F128::new(NAT_TAG, 0), F128::new(3, 0)]);
      assert_eq!(output[g.result_word() + 3], F128::new((value - 1) as u64, 0));
    }
    constraints(&g, &r1cs, &bits);
  }
  let zero = gate(0);
  let (bits, output) = run(&zero, &input(&zero, 35, &[], &[]));
  assert_eq!(*output.last().unwrap(), F128::ZERO);
  constraints(&zero, &zero.r1cs(), &bits);
}

#[test]
fn nat_arithmetic_differential_biguint_oracle_across_partial_and_multilimb_bounds()
 {
  use num_bigint::BigUint;
  let mut seed = 0x9164_abe2_5039_cd77u64;
  for bound in [0usize, 1, 7, 9, 32, 65, 96, 128, 129, 192, 255, 256, 257] {
    let g = gate(bound);
    let maximum = (BigUint::from(1u32) << bound) - 1u32;
    let mut pairs = vec![
      (BigUint::default(), BigUint::default()),
      (maximum.clone(), BigUint::default()),
      (maximum.clone(), maximum.clone()),
    ];
    for _ in 0..3 {
      let mut number = || {
        let bytes: Vec<_> = (0..bound.div_ceil(8))
          .map(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed as u8
          })
          .collect();
        BigUint::from_bytes_le(&bytes) & &maximum
      };
      pairs.push((number(), number()));
    }
    for (a, b) in pairs {
      let mut a_bytes = a.to_bytes_le();
      while a_bytes.last() == Some(&0) {
        a_bytes.pop();
      }
      let mut b_bytes = b.to_bytes_le();
      while b_bytes.last() == Some(&0) {
        b_bytes.pop();
      }
      let expected = [
        &a + &b,
        if a >= b { &a - &b } else { BigUint::default() },
        &a * &b,
        if b == BigUint::default() { BigUint::default() } else { &a / &b },
        if b == BigUint::default() { a.clone() } else { &a % &b },
        BigUint::from(u32::from(a == b)),
        BigUint::from(u32::from(a < b)),
      ];
      for (opcode, expected) in expected.into_iter().enumerate() {
        let (_, output) =
          run(&g, &input(&g, 35 + opcode as u8, &a_bytes, &b_bytes));
        let overflow = opcode < 5 && expected.bits() > bound as u64;
        assert_eq!(
          *output.last().unwrap(),
          F128::new(u64::from(overflow), 0),
          "bound {bound}, opcode {}, a={a}, b={b}",
          35 + opcode
        );
        if overflow {
          continue;
        }
        let base = g.result_word();
        let actual = if opcode >= 5 {
          assert_eq!(output[base], F128::new(BOOL_TAG, 0));
          BigUint::from(output[base + 1].lo)
        } else {
          let bytes: Vec<_> = output
            [base + 3..base + 2 + g.bytes.record_words()]
            .iter()
            .flat_map(|word| {
              word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
            })
            .collect();
          let value = BigUint::from_bytes_le(&bytes);
          assert_eq!(output[base + 2].lo, (1 << 32) | value.bits().div_ceil(8));
          value
        };
        assert_eq!(actual, expected, "bound {bound}, opcode {}", 35 + opcode);
      }
    }
  }
}
