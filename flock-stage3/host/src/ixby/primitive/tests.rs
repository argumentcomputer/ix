use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  goldilocks::GOLDILOCKS_MODULUS as P,
  ixby::{
    bits::{fill_words, read_words},
    io::LayoutEmitter,
    primitive::registry::{PrimitiveSet, scalar_primitive_arity},
    value::{EXT_TAG, FIELD_TAG, ValueWords, bool_words, word32_words},
  },
  sizing::{CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{GateType, ShapeBuilder},
  r1cs::BlockR1cs,
};
use p3_field::{
  BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64,
  extension::BinomialExtensionField,
};
use p3_goldilocks::Goldilocks;

fn meta(a: u32, b: u32, c: u32, d: u32) -> F128 {
  F128::new(
    u64::from(a) | (u64::from(b) << 32),
    u64::from(c) | (u64::from(d) << 32),
  )
}
fn field(a: u64) -> ValueWords {
  [F128::new(FIELD_TAG, 0), F128::new(a, 0)]
}
fn ext(a: u64, b: u64) -> ValueWords {
  [F128::new(EXT_TAG, 0), F128::new(a, b)]
}
pub(super) fn inputs(opcode: u8, values: &[ValueWords]) -> Vec<F128> {
  let mut input =
    vec![meta(1, 2, 1, 0), meta(0, u32::from(opcode), values.len() as u32, 0)];
  input.extend(values.iter().flatten().copied());
  input.resize(6, F128::ZERO);
  input
}
pub(super) fn row_bits(
  plan: &BooleanR1csPlan,
  r1cs: &BlockR1cs,
  fill: impl FnOnce(&mut [bool]),
) -> Vec<bool> {
  let mut bits = vec![false; r1cs.n()];
  plan.fill_row(&mut bits[..plan.k()], fill);
  bits
}

type Ext = BinomialExtensionField<Goldilocks, 2>;
pub(crate) fn oracle(
  opcode: u8,
  a: u32,
  b: u32,
  x: u64,
  y: u64,
) -> (Vec<ValueWords>, ValueWords) {
  let fa = Goldilocks::from_u64(x);
  let fb = Goldilocks::from_u64(y);
  let ea = Ext::from_basis_coefficients_slice(&[fa, fb]).unwrap();
  let eb =
    Ext::from_basis_coefficients_slice(&[fb, Goldilocks::from_u64(7)]).unwrap();
  let field_result = |z: Goldilocks| field(z.as_canonical_u64());
  let ext_result = |z: Ext| {
    let c: &[Goldilocks] = z.as_basis_coefficients_slice();
    ext(c[0].as_canonical_u64(), c[1].as_canonical_u64())
  };
  let (args, result) = match opcode {
    0 => {
      (vec![word32_words(a), word32_words(b)], word32_words(a.wrapping_add(b)))
    },
    3 => (vec![word32_words(a), word32_words(b)], word32_words(a & b)),
    4 => (vec![word32_words(a), word32_words(b)], word32_words(a | b)),
    5 => (vec![word32_words(a), word32_words(b)], word32_words(a ^ b)),
    9 => (vec![word32_words(a), word32_words(b)], bool_words(a == b)),
    10 => (vec![word32_words(a), word32_words(b)], bool_words(a < b)),
    13 => (vec![word32_words(a)], field(u64::from(a))),
    14 => (vec![field(x), field(y)], field_result(fa + fb)),
    15 => (vec![field(x), field(y)], field_result(fa - fb)),
    16 => (vec![field(x), field(y)], field_result(fa * fb)),
    17 => (
      vec![field(x)],
      field_result(fa.try_inverse().unwrap_or(Goldilocks::ZERO)),
    ),
    18 => (vec![field(x), field(y)], bool_words(fa == fb)),
    21 => (vec![ext(x, y), ext(y, 7)], ext_result(ea + eb)),
    22 => (vec![ext(x, y), ext(y, 7)], ext_result(ea - eb)),
    23 => (vec![ext(x, y), ext(y, 7)], ext_result(ea * eb)),
    24 => (vec![ext(x, y)], ext_result(ea.try_inverse().unwrap_or(Ext::ZERO))),
    25 => (vec![ext(x, y), ext(y, 7)], bool_words(ea == eb)),
    26 => (vec![field(x), field(y)], ext(x, y)),
    27 => (vec![ext(x, y)], field(x)),
    28 => (vec![ext(x, y)], field(y)),
    _ => unreachable!(),
  };
  assert_eq!(args.len(), scalar_primitive_arity(opcode).unwrap());
  (args, result)
}

#[test]
fn all_scalar_opcodes_and_boundary_values_use_one_fixed_arithmetic_network() {
  let gate = PrimitivePrepareGate::new(5, 2, PrimitiveSet::scalar()).unwrap();
  let finish = PrimitiveFinishGate::new(5).unwrap();
  let mut builder = ShapeBuilder::new(5);
  let mut b = LayoutEmitter::new(&mut builder);
  let slots = ScalarPrimitiveSlots::declare(&mut b, gate.clone());
  let input: Vec<_> = (0..gate.input_count()).map(|_| b.input()).collect();
  for word in slots.evaluate(&mut b, &[input[0], input[1]], &input[2..]) {
    b.publish(word);
  }
  slots.finish_canonical(&mut b);
  let (inputs_layout, public) = b.finish();
  let shape = builder.finish().unwrap();
  let r1cs = gate.r1cs();
  let finish_r1cs = finish.r1cs();
  for opcode in PrimitiveSet::scalar().opcodes() {
    for (a, b, x, y) in [
      (0, 0, 0, 0),
      (u32::MAX, 1, P - 1, 1),
      (1, u32::MAX, 1, P - 1),
      (17, 17, 7, 7),
      (0xdead_beef, 0x89ab_cdef, 0x1234_5678_90ab_cdef, 0xfedc_ba98_7654_3210),
    ] {
      let (args, expected) = oracle(opcode, a, b, x, y);
      let input = inputs(opcode, &args);
      let witness = shape.run(&inputs_layout.assign(&input).unwrap(), &[]);
      assert_eq!(
        witness.public,
        public.instantiate(&expected).unwrap(),
        "opcode {opcode}"
      );
      let row = &witness.rows::<PrimitivePrepareGate>(slots.prepare)[0];
      let bits =
        row_bits(gate.plan(), &r1cs, |bits| prepare::fill_free(row, bits));
      assert!(r1cs.satisfies(&bits));
      assert!(!bits[128 * (gate.input_count() + 7)]);
      let row = &witness.rows::<PrimitiveFinishGate>(slots.finish)[0];
      let bits =
        row_bits(finish.plan(), &finish_r1cs, |bits| fill_words(&row.0, bits));
      assert!(finish_r1cs.satisfies(&bits));
      assert!(!bits[1152]);
    }
  }
  // Return/copy/call/branch/halting operand values are not primitive inputs.
  for kind in [0, 1, 3, 4, 5, 6] {
    let mut input = inputs(0, &[bool_words(true), ext(23, 29)]);
    input[0] = meta(1, kind, 1, 0);
    let witness = shape.run(&inputs_layout.assign(&input).unwrap(), &[]);
    assert_eq!(witness.public, public.instantiate(&[F128::ZERO; 2]).unwrap());
  }
}

pub(super) fn reject(
  gate: &PrimitivePrepareGate,
  r1cs: &BlockR1cs,
  input: &[F128],
) {
  let row = gate.eval(input, &(), &mut Vec::new());
  let mut bits =
    row_bits(gate.plan(), r1cs, |bits| prepare::fill_free(&row, bits));
  let residual = 128 * (gate.input_count() + 7);
  assert!(bits[residual], "{input:?}");
  assert!(r1cs.satisfies(&bits));
  bits[residual] = false;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn runtime_dispatch_rejects_wrong_types_arity_registry_and_noncanonical_cells()
{
  let gate = PrimitivePrepareGate::new(3, 2, PrimitiveSet::scalar()).unwrap();
  let r1cs = gate.r1cs();
  for opcode in PrimitiveSet::scalar().opcodes() {
    let (args, _) = oracle(opcode, 11, 13, 17, 19);
    let good = inputs(opcode, &args);
    for index in 0..args.len() {
      let mut bad = good.clone();
      bad[2 + 2 * index..4 + 2 * index].copy_from_slice(&bool_words(false));
      reject(&gate, &r1cs, &bad);
      for bit in [3, 31, 63, 64, 96, 127] {
        let mut bad = good.clone();
        flip(&mut bad[2 + 2 * index], bit);
        reject(&gate, &r1cs, &bad);
      }
    }
    for count in [0, 3, 1 << 31, u32::MAX] {
      let mut bad = good.clone();
      bad[1] = meta(0, u32::from(opcode), count, 0);
      reject(&gate, &r1cs, &bad);
    }
    let mut bad = good.clone();
    bad[1] = meta(0, u32::from(opcode), if args.len() == 1 { 2 } else { 1 }, 0);
    reject(&gate, &r1cs, &bad);
    if args.len() == 1 {
      for bit in [0, 63, 64, 127] {
        let mut bad = good.clone();
        flip(&mut bad[5], bit);
        reject(&gate, &r1cs, &bad);
      }
    }
  }
  for opcode in [1, 2, 6, 8, 12, 19, 29, 255, 1 << 31, u32::MAX] {
    let mut bad = inputs(0, &[word32_words(11), word32_words(13)]);
    bad[1] = meta(0, opcode, 2, 0);
    reject(&gate, &r1cs, &bad);
  }
  for (opcode, values) in [
    (0, vec![word32_words(11), word32_words(13)]),
    (14, vec![field(11), field(13)]),
    (21, vec![ext(11, 13), ext(17, 19)]),
  ] {
    let good = inputs(opcode, &values);
    let mut bad = good.clone();
    bad[3].lo = P;
    reject(&gate, &r1cs, &bad);
    let mut bad = good;
    bad[3].hi = P;
    reject(&gate, &r1cs, &bad);
  }
  let only_add =
    PrimitivePrepareGate::new(3, 2, PrimitiveSet::new(&[0]).unwrap()).unwrap();
  reject(&only_add, &only_add.r1cs(), &inputs(16, &[field(2), field(3)]));
}

pub(super) fn flip(word: &mut F128, bit: usize) {
  if bit < 64 {
    word.lo ^= 1 << bit;
  } else {
    word.hi ^= 1 << (bit - 64);
  }
}

#[test]
fn recomputed_inverse_advice_requires_the_full_product_and_zero_convention() {
  let gate = PrimitivePrepareGate::new(3, 2, PrimitiveSet::scalar()).unwrap();
  let finish = PrimitiveFinishGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let fr = finish.r1cs();
  for (opcode, arg) in
    [(17, field(7)), (24, ext(7, 11)), (17, field(0)), (24, ext(0, 0))]
  {
    let input = inputs(opcode, &[arg]);
    let honest = gate.eval(&input, &(), &mut Vec::new());
    for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
      let mut row = honest.clone();
      flip(&mut row.inverse, bit);
      let mut bits =
        row_bits(gate.plan(), &r1cs, |bits| prepare::fill_free(&row, bits));
      assert!(r1cs.satisfies(&bits));
      let p = read_words(&bits, gate.input_count(), 8);
      if p[7] != F128::ZERO {
        bits[128 * (gate.input_count() + 7)] = false;
        assert!(!r1cs.satisfies(&bits));
        continue;
      }
      // The attacker also recomputes arithmetic with the forged candidate.
      // The finish relation still demands the correct full extension product.
      let sum = F128::new(
        crate::goldilocks::goldilocks_add(p[2].lo, p[3].lo),
        crate::goldilocks::goldilocks_add(p[2].hi, p[3].hi),
      );
      let product = crate::extension::goldilocks_ext2_mul(p[2], p[3]);
      let input = [p[0], p[1], p[6], sum, product, p[4], p[5]];
      let mut bits =
        row_bits(finish.plan(), &fr, |bits| fill_words(&input, bits));
      assert!(fr.satisfies(&bits));
      assert!(bits[1152]);
      bits[1152] = false;
      assert!(!fr.satisfies(&bits));
    }
  }
}

#[test]
fn primitive_count_emit_and_both_recycled_witness_drivers_agree() {
  let gate = PrimitivePrepareGate::new(5, 2, PrimitiveSet::scalar()).unwrap();
  fn emit(b: &mut impl CircuitEmitter, gate: PrimitivePrepareGate) {
    let input: Vec<_> = (0..gate.input_count()).map(|_| b.input()).collect();
    let slots = ScalarPrimitiveSlots::declare(b, gate);
    for word in slots.evaluate(b, &[input[0], input[1]], &input[2..]) {
      b.publish(word);
    }
    slots.finish_canonical(b);
  }
  let mut count = CountingEmitter::new();
  emit(&mut count, gate.clone());
  assert!(gate.plan.get().is_none());
  let mut builder = ShapeBuilder::new(5);
  emit(&mut builder, gate.clone());
  let shape = builder.finish().unwrap();
  count.ensure_matches(&shape).unwrap();
  let (registry, counts) = count.registry(5);
  assert_eq!(counts, shape.counts);
  for (counted, emitted) in registry.types().iter().zip(shape.registry.types())
  {
    assert_eq!(counted.a_0.rows, emitted.a_0.rows);
    assert_eq!(counted.b_0.rows, emitted.b_0.rows);
    assert_eq!(counted.io_schema, emitted.io_schema);
  }
  // The padding helper deliberately uses nu=3, independently of the network.
  let gate = PrimitivePrepareGate::new(3, 2, PrimitiveSet::scalar()).unwrap();
  let row = gate.eval(&inputs(24, &[ext(17, 19)]), &(), &mut Vec::new());
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      prepare::fill_free,
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  let finish = PrimitiveFinishGate::new(3).unwrap();
  let row = finish.eval(
    &[
      F128::new(2, 0),
      F128::new(42, 0),
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
    ],
    &(),
    &mut Vec::new(),
  );
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      finish.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| finish.generate_witness_into(&rows, dst),
    );
  }
}
