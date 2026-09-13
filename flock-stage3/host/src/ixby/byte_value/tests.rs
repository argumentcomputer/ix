use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{
    bits::{fill_words, read_words},
    decode::{
      PrimitiveSet,
      test_support::{Value as V, meta},
    },
    value::BYTES_TAG,
  },
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};

fn flip(word: &mut F128, bit: usize) {
  if bit < 64 {
    word.lo ^= 1 << bit;
  } else {
    word.hi ^= 1 << (bit - 64);
  }
}

fn buffer(capacity: ByteCapacity, bytes: &[u8]) -> Vec<F128> {
  assert!(bytes.len() <= capacity.bytes());
  let mut result = vec![F128::new(bytes.len() as u64, 0)];
  let mut padded = vec![0; 16 * capacity.data_words()];
  padded[..bytes.len()].copy_from_slice(bytes);
  result.extend(padded.chunks(16).map(crate::hash::pack_bytes));
  result
}

fn record(capacity: ByteCapacity, bytes: &[u8]) -> Vec<F128> {
  let mut result = buffer(capacity, bytes);
  result[0].lo |= 1 << 32;
  result
}

fn check(
  plan: &BooleanR1csPlan,
  r1cs: &BlockR1cs,
  input: &[F128],
  outputs: usize,
  valid: bool,
) -> Vec<F128> {
  let mut bits = vec![false; r1cs.n()];
  plan.fill_row(&mut bits[..plan.k()], |bits| fill_words(input, bits));
  let result = read_words(&bits, input.len(), outputs);
  assert_eq!(
    result.last(),
    Some(&F128::new(u64::from(!valid), 0)),
    "invalid residual for {input:?}"
  );
  assert!(r1cs.satisfies(&bits));
  let residual = 128 * (input.len() + outputs - 1);
  bits[residual] ^= true;
  assert!(
    !r1cs.satisfies(&bits),
    "residual cannot be forged after recomputing all advice"
  );
  result
}

fn mutations(
  plan: &BooleanR1csPlan,
  r1cs: &BlockR1cs,
  input: &[F128],
  outputs: usize,
) {
  let mut bits = vec![false; r1cs.n()];
  plan.fill_row(&mut bits[..plan.k()], |bits| fill_words(input, bits));
  for word in 0..outputs {
    for bit in [0, 7, 31, 32, 63, 64, 95, 127] {
      let column = 128 * (input.len() + word) + bit;
      bits[column] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[column] ^= true;
    }
  }
  bits[plan.k() - 1] = true;
  assert!(!r1cs.satisfies(&bits), "unused column must be constrained zero");
}

#[test]
fn byte_read_authenticates_full_handles_presence_lengths_and_padding() {
  let capacity = ByteCapacity::new(33).unwrap();
  let gate = ByteReadGate::new(3, capacity, 4).unwrap();
  let r1cs = gate.r1cs();
  let data: Vec<_> = (0..33).map(|i| (i * 71 + 19) as u8).collect();
  let bank = [
    record(capacity, &data),
    record(capacity, &[]),
    vec![F128::ZERO; capacity.record_words()],
    record(capacity, &[0]),
  ]
  .concat();
  for (index, expected) in [(0, data.as_slice()), (1, &[][..]), (3, &[0][..])] {
    let input =
      [vec![F128::new(BYTES_TAG, 0), F128::new(index, 0)], bank.clone()]
        .concat();
    let result = check(gate.plan(), &r1cs, &input, gate.output_count(), true);
    assert_eq!(&result[..capacity.record_words()], buffer(capacity, expected));
  }
  let good = [vec![F128::new(BYTES_TAG, 0), F128::ZERO], bank].concat();
  for index in [2, 4, 1 << 31, u32::MAX.into()] {
    let mut bad = good.clone();
    bad[1] = F128::new(index, 0);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  for word in [0, 1] {
    for bit in 32..128 {
      let mut bad = good.clone();
      flip(&mut bad[word], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  for bit in 32..128 {
    let mut bad = good.clone();
    flip(&mut bad[2], bit);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  let mut too_long = good.clone();
  too_long[2].lo = (1 << 32) | 34;
  check(gate.plan(), &r1cs, &too_long, gate.output_count(), false);
  for bit in [8, 15, 31, 63, 64, 127] {
    let mut bad = good.clone();
    flip(&mut bad[5], bit);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  // Unselected records are owned by their producer, not falsely certified
  // here. Scalar and padding reads must expose no bytes from the bank.
  for cell in [V::Word(42).words(), V::Erased.words(), [F128::ZERO; 2]] {
    let mut input = good.clone();
    input[..2].copy_from_slice(&cell);
    assert_eq!(
      check(gate.plan(), &r1cs, &input, gate.output_count(), true),
      vec![F128::ZERO; gate.output_count()]
    );
  }
  mutations(gate.plan(), &r1cs, &good, gate.output_count());
  let row = ByteReadRow(good);
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
fn nat_reads_bind_distinct_tags_minimal_magnitudes_partial_bounds_and_full_indices()
 {
  use crate::ixby::{nat_value::NatCapacity, value::NAT_TAG};
  let capacity = ByteCapacity::new(4).unwrap();
  let gate = ByteReadGate::new(3, capacity, 2)
    .unwrap()
    .with_nat_capacity(NatCapacity::new(9).unwrap())
    .unwrap();
  let r1cs = gate.r1cs();
  let input = |tag, data: &[u8]| {
    [
      vec![F128::new(tag, 0), F128::ZERO],
      record(capacity, data),
      vec![F128::ZERO; capacity.record_words()],
    ]
    .concat()
  };
  for (data, valid) in [
    (&[][..], true),
    (&[1][..], true),
    (&[255, 1][..], true),
    (&[0][..], false),
    (&[1, 0][..], false),
    (&[0, 2][..], false),
    (&[1, 1, 1][..], false),
  ] {
    check(
      gate.plan(),
      &r1cs,
      &input(NAT_TAG, data),
      gate.output_count(),
      valid,
    );
    check(
      gate.plan(),
      &r1cs,
      &input(BYTES_TAG, data),
      gate.output_count(),
      true,
    );
  }
  let good = input(NAT_TAG, &[255, 1]);
  for word in [0, 1] {
    for bit in 32..128 {
      let mut bad = good.clone();
      flip(&mut bad[word], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  for index in [1, 2, u32::MAX as u64] {
    let mut bad = good.clone();
    bad[1].lo = index;
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  let mut missing = good.clone();
  missing[2].lo &= !(1 << 32);
  check(gate.plan(), &r1cs, &missing, gate.output_count(), false);
  mutations(gate.plan(), &r1cs, &good, gate.output_count());
}

fn primitive_input(
  capacity: ByteCapacity,
  opcode: u8,
  args: &[V],
) -> Vec<F128> {
  let mut input = vec![
    meta(args.len() as u32, 2, 1, 0),
    meta(0, opcode.into(), args.len() as u32, 0),
    F128::new(3, 0),
  ];
  for (index, arg) in args.iter().enumerate() {
    input.extend(match arg {
      V::Bytes(_) => [F128::new(BYTES_TAG, 0), F128::new(index as u64, 0)],
      _ => arg.words(),
    });
  }
  input.resize(9, F128::ZERO);
  for index in 0..2 {
    let data = match args.get(index) {
      Some(V::Bytes(data)) => data.as_slice(),
      _ => &[],
    };
    input.extend(buffer(capacity, data));
  }
  let data = match args.first() {
    Some(V::Bytes(data)) => data.as_slice(),
    _ => &[],
  };
  let digest = blake3::hash(data);
  input.extend(digest.as_bytes().chunks(16).map(crate::hash::pack_bytes));
  input
}

#[test]
fn byte_operations_constrain_results_and_reject_bounds_types_and_wrapped_indices()
 {
  let capacity = ByteCapacity::new(33).unwrap();
  let gate =
    BytePrimitiveGate::new(3, capacity, 4, 3, PrimitiveSet::crypto_bytes())
      .unwrap();
  let r1cs = gate.r1cs();
  let data: Vec<_> = (0..33).map(|i| (i * 71 + 19) as u8).collect();
  let cases = [
    (
      11,
      vec![V::Word(0xdead_beef)],
      V::Bytes(0xdead_beefu32.to_le_bytes().to_vec()),
    ),
    (12, vec![V::Bytes(vec![0xef, 0xbe, 0xad, 0xde])], V::Word(0xdead_beef)),
    (
      19,
      vec![V::Field(0xffff_ffff_0000_0000)],
      V::Bytes(0xffff_ffff_0000_0000u64.to_le_bytes().to_vec()),
    ),
    (
      20,
      vec![V::Bytes(0xffff_ffff_0000_0000u64.to_le_bytes().to_vec())],
      V::Field(0xffff_ffff_0000_0000),
    ),
    (29, vec![V::Bytes(data.clone())], V::Word(33)),
    (30, vec![V::Bytes(data.clone()), V::Word(32)], V::Word(data[32].into())),
    (
      31,
      vec![V::Bytes(data[..15].to_vec()), V::Bytes(data[15..].to_vec())],
      V::Bytes(data.clone()),
    ),
    (
      32,
      vec![V::Bytes(data.clone()), V::Word(16), V::Word(17)],
      V::Bytes(data[16..].to_vec()),
    ),
    (33, vec![V::Bytes(data.clone()), V::Bytes(data.clone())], V::Bool(1)),
    (
      34,
      vec![V::Bytes(data.clone())],
      V::Bytes(blake3::hash(&data).as_bytes().to_vec()),
    ),
  ];
  for (opcode, args, expected) in &cases {
    let input = primitive_input(capacity, *opcode, args);
    let result = check(gate.plan(), &r1cs, &input, gate.output_count(), true);
    assert_eq!(&result[..3], &[F128::new(1, 0), F128::ZERO, F128::ZERO]);
    match expected {
      V::Bytes(data) => {
        assert_eq!(&result[3..5], &[F128::new(BYTES_TAG, 0), F128::new(3, 0)]);
        assert_eq!(
          &result[5..5 + capacity.record_words()],
          record(capacity, data)
        );
      },
      _ => {
        assert_eq!(&result[3..5], &expected.words());
        assert!(result[5..].iter().all(|word| *word == F128::ZERO));
      },
    }
    for count in [0, args.len() as u32 + 1, 1 << 31] {
      let mut bad = input.clone();
      bad[1] = meta(0, (*opcode).into(), count, 0);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  for (opcode, args) in [
    (11, vec![V::Field(1)]),
    (12, vec![V::Bytes(vec![])]),
    (12, vec![V::Bytes(vec![0; 5])]),
    (20, vec![V::Bytes(vec![0; 7])]),
    (20, vec![V::Bytes(0xffff_ffff_0000_0001u64.to_le_bytes().to_vec())]),
    (20, vec![V::Bytes(u64::MAX.to_le_bytes().to_vec())]),
    (30, vec![V::Bytes(data.clone()), V::Word(33)]),
    (30, vec![V::Bytes(data.clone()), V::Word(1 << 31)]),
    (30, vec![V::Bytes(data.clone()), V::Word(u32::MAX)]),
    (31, vec![V::Bytes(data.clone()), V::Bytes(vec![1])]),
    (32, vec![V::Bytes(data.clone()), V::Word(33), V::Word(1)]),
    (32, vec![V::Bytes(data.clone()), V::Word(u32::MAX), V::Word(2)]),
    (33, vec![V::Bytes(vec![]), V::Word(0)]),
    (34, vec![V::Word(0)]),
  ] {
    check(
      gate.plan(),
      &r1cs,
      &primitive_input(capacity, opcode, &args),
      gate.output_count(),
      false,
    );
  }
  let good = primitive_input(capacity, 34, &[V::Bytes(data)]);
  for bit in 32..128 {
    for word in [2, 9] {
      let mut bad = good.clone();
      flip(&mut bad[word], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  for bit in [8, 15, 31, 63, 64, 127] {
    let mut bad = good.clone();
    flip(&mut bad[12], bit);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  mutations(gate.plan(), &r1cs, &good, gate.output_count());
  let row = BytePrimitiveRow(good);
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  // An operation's result bound applies even when its input is empty.
  let small = ByteCapacity::new(31).unwrap();
  let gate =
    BytePrimitiveGate::new(3, small, 4, 3, PrimitiveSet::crypto_bytes())
      .unwrap();
  check(
    gate.plan(),
    &gate.r1cs(),
    &primitive_input(small, 34, &[V::Bytes(vec![])]),
    gate.output_count(),
    false,
  );
}
