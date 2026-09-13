use super::{
  tests::{flip, inputs, reject, row_bits},
  *,
};
use crate::{
  ixby::{
    decode::{EXTRA_WORD_PRIMITIVES, PrimitiveSet, primitive_arity},
    io::LayoutEmitter,
    value::{bool_words, word32_words},
  },
  sizing::{CountedGate, CountingEmitter},
};
use flock_prover::circuit::builder::{GateType, ShapeBuilder};

fn oracle(opcode: u8, a: u32, b: u32) -> u32 {
  match opcode {
    1 => a.wrapping_sub(b),
    2 => a.wrapping_mul(b),
    6 => a.checked_shl(b).unwrap_or(0),
    7 => a.checked_shr(b).unwrap_or(0),
    8 => a.rotate_right(b),
    _ => unreachable!(),
  }
}

#[test]
fn complete_crypto_registry_is_explicit_and_all_arities_are_closed() {
  let crypto = PrimitiveSet::crypto();
  assert_eq!(crypto.opcodes().collect::<Vec<_>>(), (0..35).collect::<Vec<_>>());
  assert_eq!(crypto.crypto_scalar_subset().opcodes().count(), 25);
  assert_eq!(crypto.scalar_subset(), PrimitiveSet::scalar());
  assert_eq!(PrimitiveSet::crypto_bytes().opcodes().count(), 30);
  assert!(PrimitiveSet::with_crypto(&[1, 1]).is_err());
  assert!(PrimitiveSet::with_crypto(&[35]).is_err());
  assert!(PrimitiveSet::with_crypto(&[255]).is_err());
  for opcode in EXTRA_WORD_PRIMITIVES {
    assert!(!PrimitiveSet::scalar().contains(*opcode));
    assert!(!PrimitiveSet::crypto_bytes().contains(*opcode));
    assert!(PrimitiveSet::new(&[*opcode]).is_err());
    assert!(PrimitiveSet::with_bytes(&[*opcode]).is_err());
    assert_eq!(primitive_arity(*opcode), Some(2));
  }
  assert!((0..35).all(|op| primitive_arity(op).is_some()));
  // Nat arities exist in revision 1, but never extend the v0 registry.
  for opcode in 35..42 {
    assert!(!crypto.contains(opcode));
    assert!(PrimitiveSet::with_crypto(&[opcode]).is_err());
    assert_eq!(primitive_arity(opcode), Some(2));
  }
  assert_eq!(primitive_arity(42), None);
  assert_eq!(primitive_arity(255), None);
}

#[test]
fn remaining_word_ops_cover_carries_every_basis_bit_and_full_shift_counts() {
  let gate = PrimitivePrepareGate::new(
    3,
    2,
    PrimitiveSet::crypto().crypto_scalar_subset(),
  )
  .unwrap();
  let r1cs = gate.r1cs();
  for opcode in EXTRA_WORD_PRIMITIVES {
    let check = |a, b, matrix| {
      let input = inputs(*opcode, &[word32_words(a), word32_words(b)]);
      let mut output = Vec::new();
      let row = gate.eval(&input, &(), &mut output);
      assert_eq!(
        &output[..2],
        &word32_words(oracle(*opcode, a, b)),
        "opcode {opcode}, a={a:#x}, b={b:#x}"
      );
      assert!(output[2..].iter().all(|word| *word == F128::ZERO));
      if matrix {
        let bits =
          row_bits(gate.plan(), &r1cs, |bits| prepare::fill_free(&row, bits));
        assert!(r1cs.satisfies(&bits));
      }
    };
    for a in [0, 1, u32::MAX, 0x8000_0000, 0xdead_beef, 0xffff, 0x10001] {
      for b in
        [0, 1, 31, 32, 33, 63, 64, 0x8000_0000, u32::MAX, 0xffff, 0x10001]
      {
        check(a, b, true);
      }
    }
    for bit in 0..32 {
      for other in 0..32 {
        check(1 << bit, if *opcode <= 2 { 1 << other } else { other }, false);
      }
      // Every high count bit must zero shifts, including in combination with
      // low bits; rotate must ignore it without rejecting canonical words.
      check(0x89ab_cdef, (1 << bit) | 17, true);
    }
    let mut state = 0x6d2b_79f5u32;
    for _ in 0..128 {
      state ^= state << 13;
      state ^= state >> 17;
      state ^= state << 5;
      check(state, state.rotate_left(11), false);
    }
  }
}

#[test]
fn word_constraints_reject_bad_dispatch_cells_and_every_forged_result_bit() {
  let gate = PrimitivePrepareGate::new(
    3,
    3,
    PrimitiveSet::crypto().crypto_scalar_subset(),
  )
  .unwrap();
  let r1cs = gate.r1cs();
  for opcode in EXTRA_WORD_PRIMITIVES {
    let mut good =
      inputs(*opcode, &[word32_words(0x89ab_cdef), word32_words(17)]);
    good.resize(gate.input_count(), F128::ZERO);
    let row = gate.eval(&good, &(), &mut Vec::new());
    let bits =
      row_bits(gate.plan(), &r1cs, |bits| prepare::fill_free(&row, bits));
    assert!(r1cs.satisfies(&bits));
    // Both entire result cells, not only the significant 32 payload bits.
    for bit in 128 * gate.input_count()..128 * (gate.input_count() + 2) {
      let mut bad = bits.clone();
      bad[bit] = !bad[bit];
      assert!(!r1cs.satisfies(&bad), "opcode {opcode}, result bit {bit}");
    }
    for argument in 0..2 {
      let mut bad = good.clone();
      bad[2 + 2 * argument..4 + 2 * argument]
        .copy_from_slice(&bool_words(false));
      reject(&gate, &r1cs, &bad);
      for bit in [3, 31, 63, 64, 96, 127] {
        let mut bad = good.clone();
        flip(&mut bad[2 + 2 * argument], bit);
        reject(&gate, &r1cs, &bad);
      }
      for bit in 32..128 {
        let mut bad = good.clone();
        flip(&mut bad[3 + 2 * argument], bit);
        reject(&gate, &r1cs, &bad);
      }
    }
    for count in [0, 1, 3, 4, 1 << 31, u32::MAX] {
      let mut bad = good.clone();
      bad[1].hi = u64::from(count);
      reject(&gate, &r1cs, &bad);
    }
    for bit in 8..32 {
      let mut bad = good.clone();
      bad[1].lo ^= 1u64 << (32 + bit);
      reject(&gate, &r1cs, &bad);
    }
    for bit in [0, 63, 64, 127] {
      let mut bad = good.clone();
      flip(&mut bad[7], bit);
      reject(&gate, &r1cs, &bad);
    }
  }
  let only_sub =
    PrimitivePrepareGate::new(3, 2, PrimitiveSet::with_crypto(&[1]).unwrap())
      .unwrap();
  reject(
    &only_sub,
    &only_sub.r1cs(),
    &inputs(2, &[word32_words(2), word32_words(3)]),
  );
}

#[test]
fn extended_word_network_count_emit_and_recycled_padding_agree() {
  let gate = PrimitivePrepareGate::new(
    5,
    2,
    PrimitiveSet::crypto().crypto_scalar_subset(),
  )
  .unwrap();
  let mut count = CountingEmitter::new();
  let count_slots = ScalarPrimitiveSlots::declare(&mut count, gate.clone());
  let input: Vec<_> = (0..gate.input_count()).map(|_| count.input()).collect();
  for word in
    count_slots.evaluate(&mut count, &[input[0], input[1]], &input[2..])
  {
    count.publish(word);
  }
  count_slots.finish_canonical(&mut count);
  assert!(gate.plan.get().is_none());
  let mut builder = ShapeBuilder::new(5);
  let mut b = LayoutEmitter::new(&mut builder);
  let slots = ScalarPrimitiveSlots::declare(&mut b, gate.clone());
  let input: Vec<_> = (0..gate.input_count()).map(|_| b.input()).collect();
  for word in slots.evaluate(&mut b, &[input[0], input[1]], &input[2..]) {
    b.publish(word);
  }
  slots.finish_canonical(&mut b);
  let (input_layout, public) = b.finish();
  let shape = builder.finish().unwrap();
  count.ensure_matches(&shape).unwrap();
  for opcode in EXTRA_WORD_PRIMITIVES {
    let input = inputs(*opcode, &[word32_words(0x89ab_cdef), word32_words(17)]);
    let witness = shape.run(&input_layout.assign(&input).unwrap(), &[]);
    assert_eq!(
      witness.public,
      public
        .instantiate(&word32_words(oracle(*opcode, 0x89ab_cdef, 17)))
        .unwrap()
    );
  }
  let gate = PrimitivePrepareGate::new(
    3,
    2,
    PrimitiveSet::crypto().crypto_scalar_subset(),
  )
  .unwrap();
  let row = gate.eval(
    &inputs(2, &[word32_words(u32::MAX), word32_words(u32::MAX)]),
    &(),
    &mut Vec::new(),
  );
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      prepare::fill_free,
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
