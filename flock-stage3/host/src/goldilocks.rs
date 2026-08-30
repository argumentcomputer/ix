//! Boolean R1CS gadgets for Goldilocks values carried as little-endian u64s.
//!
//! Flock's circuit wiring moves one `F128` word at a time. One gate therefore
//! checks two Goldilocks representatives at once and exposes a 128-bit
//! violation word. The circuit connects that output to a fixed zero wire.

use std::sync::OnceLock;

use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  lincheck::pack_z_lincheck,
  r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout},
  schedule::{IoWord, TableType},
};

use crate::boolean::{
  BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness,
  write_f128 as write_boolean_f128,
};

pub(crate) const GOLDILOCKS_MODULUS: u64 = 0xffff_ffff_0000_0001;
const K_LOG: usize = 9;
const K: usize = 1 << K_LOG;
const K_SKIP: usize = 6;
const INPUT_BASE: usize = 0;
const VIOLATION_BASE: usize = 128;
const FIRST_CHAIN_BASE: usize = 256;
const SECOND_CHAIN_BASE: usize = FIRST_CHAIN_BASE + 31;
const USEFUL_BITS: usize = SECOND_CHAIN_BASE + 31;

const ADD_K_LOG: usize = 11;
const ADD_LEFT_BASE: usize = 0;
const ADD_RIGHT_BASE: usize = 128;
const ADD_RESULT_BASE: usize = 256;
const ADD_VIOLATION_BASE: usize = 384;
const ADD_TOP_VIOLATION_BASE: usize = 512;
const ADD_RESERVED_COLUMNS: usize = 640;

/// One R1CS row record for a pair of little-endian Goldilocks candidates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CanonicalGoldilocksPairRow(F128);

/// A word-aligned Boolean gate that checks two canonical Goldilocks values.
///
/// Its sole output is zero exactly when both input u64 limbs are below
/// `2^64 - 2^32 + 1`. Callers must connect that output to a fixed zero wire;
/// the table alone intentionally exposes, rather than silently pins, the
/// violation bits.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CanonicalGoldilocksPairGate {
  pub(crate) nu: usize,
}

impl GateType for CanonicalGoldilocksPairGate {
  type Row = CanonicalGoldilocksPairRow;
  type Hint = ();

  fn table(&self) -> TableType {
    TableType::from_block_r1cs(&build_canonical_pair_r1cs(self.nu))
      .with_io_schema(vec![IoWord::input(0), IoWord::output(1)])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let value = inputs[0];
    outputs.push(violation_word(value));
    CanonicalGoldilocksPairRow(value)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

/// Build the Boolean relation used by [`CanonicalGoldilocksPairGate`].
pub(crate) fn build_canonical_pair_r1cs(nu: usize) -> BlockR1cs {
  assert!(nu >= 3, "Flock lincheck requires at least eight rows");

  let mut a_rows = vec![Vec::new(); K];
  let mut b_rows = vec![Vec::new(); K];

  // Input bits are free Boolean values: x * x = x over GF(2).
  for bit in 0..128 {
    a_rows[INPUT_BASE + bit].push(INPUT_BASE + bit);
    b_rows[INPUT_BASE + bit].push(INPUT_BASE + bit);
  }

  // Fold each limb's high 32 bits to one `high_is_all_ones` bit.
  add_and_chain(&mut a_rows, &mut b_rows, 32, FIRST_CHAIN_BASE);
  add_and_chain(&mut a_rows, &mut b_rows, 96, SECOND_CHAIN_BASE);

  // x >= p iff its high 32 bits are all one and at least one low bit is one.
  // Materialize all 32 products. Wiring pins the complete output word to zero.
  let first_high_all = FIRST_CHAIN_BASE + 30;
  let second_high_all = SECOND_CHAIN_BASE + 30;
  for low_bit in 0..32 {
    a_rows[VIOLATION_BASE + low_bit].push(first_high_all);
    b_rows[VIOLATION_BASE + low_bit].push(low_bit);
    a_rows[VIOLATION_BASE + 32 + low_bit].push(second_high_all);
    b_rows[VIOLATION_BASE + 32 + low_bit].push(64 + low_bit);
  }

  let identity_rows = (0..K).map(|row| vec![row]).collect();
  BlockR1cs {
    m: K_LOG + nu,
    k_log: K_LOG,
    k_skip: K_SKIP,
    useful_bits: USEFUL_BITS,
    a_0: sparse_matrix(a_rows),
    b_0: sparse_matrix(b_rows),
    c_0: sparse_matrix(identity_rows),
    layout: WitnessLayout::BatchMajor,
    const_pin: None,
    digest_cache: OnceLock::new(),
    csc_cache: OnceLock::new(),
  }
}

/// Produce Flock's batch-major `(z, A z, B z, lincheck stripe)` tuple.
pub(crate) fn generate_canonical_pair_witness(
  rows: &[CanonicalGoldilocksPairRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let capacity = 1usize << nu;
  assert!(rows.len() <= capacity);
  let r1cs = build_canonical_pair_r1cs(nu);
  let mut z = vec![false; r1cs.n()];
  for (outer, row) in rows.iter().enumerate() {
    let range = outer * K..(outer + 1) * K;
    fill_logical_row(&mut z[range], row.0);
  }
  let a = r1cs.apply_a(&z);
  let b = r1cs.apply_b(&z);
  debug_assert!(
    a.iter()
      .zip(&b)
      .zip(&z)
      .all(|((a_bit, b_bit), z_bit)| (*a_bit & *b_bit) == *z_bit)
  );
  let stripe = pack_z_lincheck(&z, r1cs.m, r1cs.k_log);
  (
    pack_batch_major(&z, nu),
    pack_batch_major(&a, nu),
    pack_batch_major(&b, nu),
    stripe,
  )
}

/// One row of two lane-wise Goldilocks additions packed into `F128` words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct GoldilocksAddPairRow {
  left: F128,
  right: F128,
}

/// Two independent canonical Goldilocks additions, one per u64 lane.
///
/// The gate exposes the result plus two zero-valued equation-residual words.
/// Callers connect both residuals to a fixed zero wire and pass every input
/// and result through [`CanonicalGoldilocksPairGate`]. Keeping canonicality a
/// shared table avoids duplicating its constraints in every arithmetic table.
#[derive(Clone, Copy, Debug)]
pub(crate) struct GoldilocksAddPairGate {
  pub(crate) nu: usize,
}

impl GateType for GoldilocksAddPairGate {
  type Row = GoldilocksAddPairRow;
  type Hint = ();

  fn table(&self) -> TableType {
    TableType::from_block_r1cs(&build_goldilocks_add_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::output(2),
        IoWord::output(3),
        IoWord::output(4),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let left = inputs[0];
    let right = inputs[1];
    outputs.extend_from_slice(&[
      F128::new(
        goldilocks_add(left.lo, right.lo),
        goldilocks_add(left.hi, right.hi),
      ),
      F128::ZERO,
      F128::ZERO,
    ]);
    GoldilocksAddPairRow { left, right }
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

struct GoldilocksAddPlan {
  boolean: BooleanR1csPlan,
  quotient_bits: [usize; 2],
}

pub(crate) fn build_goldilocks_add_r1cs(nu: usize) -> BlockR1cs {
  build_goldilocks_add_plan().boolean.block_r1cs(nu)
}

pub(crate) fn generate_goldilocks_add_witness(
  rows: &[GoldilocksAddPairRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let plan = build_goldilocks_add_plan();
  generate_boolean_witness(&plan.boolean, rows, nu, |row, bits| {
    fill_goldilocks_add_row(&plan, *row, bits)
  })
}

fn build_goldilocks_add_plan() -> GoldilocksAddPlan {
  let mut builder = BooleanR1csBuilder::new(ADD_K_LOG, ADD_RESERVED_COLUMNS);
  for column in ADD_LEFT_BASE..ADD_RESULT_BASE + 128 {
    builder.free_boolean_at(column);
  }
  let one = builder.alloc_constant_one();
  let quotient_bits =
    [builder.alloc_free_boolean(), builder.alloc_free_boolean()];

  for (lane, &quotient) in quotient_bits.iter().enumerate() {
    let lane_offset = lane * 64;
    let left: [usize; 64] =
      std::array::from_fn(|bit| ADD_LEFT_BASE + lane_offset + bit);
    let right: [usize; 64] =
      std::array::from_fn(|bit| ADD_RIGHT_BASE + lane_offset + bit);
    let result: [usize; 64] =
      std::array::from_fn(|bit| ADD_RESULT_BASE + lane_offset + bit);
    let right_terms = right.map(Some);
    let modulus_terms: [Option<usize>; 64] = std::array::from_fn(|bit| {
      (((GOLDILOCKS_MODULUS >> bit) & 1) == 1).then_some(quotient)
    });
    let (left_sum, left_carry) =
      ripple_add(&mut builder, &left, &right_terms, one);
    let (right_sum, right_carry) =
      ripple_add(&mut builder, &result, &modulus_terms, one);

    for bit in 0..64 {
      builder.write_xor(
        ADD_VIOLATION_BASE + lane_offset + bit,
        &[left_sum[bit], right_sum[bit]],
        one,
      );
    }
    builder.write_xor(
      ADD_TOP_VIOLATION_BASE + lane,
      &[left_carry, right_carry],
      one,
    );
  }

  GoldilocksAddPlan { boolean: builder.finish(), quotient_bits }
}

fn ripple_add(
  builder: &mut BooleanR1csBuilder,
  left: &[usize; 64],
  right: &[Option<usize>; 64],
  one: usize,
) -> (Vec<usize>, usize) {
  let mut sums = Vec::with_capacity(64);
  let mut carry = None;
  for bit in 0..64 {
    let xor_lr = right[bit]
      .map_or(left[bit], |right| builder.xor(&[left[bit], right], one));
    let sum = carry.map_or(xor_lr, |carry| builder.xor(&[xor_lr, carry], one));
    sums.push(sum);

    let left_and_right = right[bit].map(|right| builder.and(left[bit], right));
    let carry_and_xor = carry.map(|carry| builder.and(carry, xor_lr));
    carry = match (left_and_right, carry_and_xor) {
      (Some(first), Some(second)) => Some(builder.xor(&[first, second], one)),
      (Some(carry), None) | (None, Some(carry)) => Some(carry),
      (None, None) => None,
    };
  }
  (sums, carry.expect("addition has a carry variable from bit zero"))
}

fn fill_goldilocks_add_row(
  plan: &GoldilocksAddPlan,
  row: GoldilocksAddPairRow,
  bits: &mut [bool],
) {
  let result = F128::new(
    goldilocks_add(row.left.lo, row.right.lo),
    goldilocks_add(row.left.hi, row.right.hi),
  );
  write_boolean_f128(bits, ADD_LEFT_BASE, row.left);
  write_boolean_f128(bits, ADD_RIGHT_BASE, row.right);
  write_boolean_f128(bits, ADD_RESULT_BASE, result);
  for (lane, quotient) in plan.quotient_bits.iter().enumerate() {
    let (left, right) = if lane == 0 {
      (row.left.lo, row.right.lo)
    } else {
      (row.left.hi, row.right.hi)
    };
    bits[*quotient] =
      left as u128 + right as u128 >= GOLDILOCKS_MODULUS as u128;
  }
}

pub(crate) fn goldilocks_add(left: u64, right: u64) -> u64 {
  ((left as u128 + right as u128) % GOLDILOCKS_MODULUS as u128) as u64
}

fn add_and_chain(
  a_rows: &mut [Vec<usize>],
  b_rows: &mut [Vec<usize>],
  high_base: usize,
  chain_base: usize,
) {
  for step in 0..31 {
    let output = chain_base + step;
    let lhs = if step == 0 { high_base } else { output - 1 };
    let rhs = high_base + step + 1;
    a_rows[output].push(lhs);
    b_rows[output].push(rhs);
  }
}

fn sparse_matrix(rows: Vec<Vec<usize>>) -> SparseBinaryMatrix {
  SparseBinaryMatrix { num_rows: K, num_cols: K, rows }
}

fn fill_logical_row(bits: &mut [bool], value: F128) {
  assert_eq!(bits.len(), K);
  write_f128(bits, INPUT_BASE, value);
  write_f128(bits, VIOLATION_BASE, violation_word(value));
  fill_and_chain(bits, value.lo, FIRST_CHAIN_BASE);
  fill_and_chain(bits, value.hi, SECOND_CHAIN_BASE);
}

fn fill_and_chain(bits: &mut [bool], limb: u64, chain_base: usize) {
  let mut accumulator = bit(limb, 32);
  for step in 0..31 {
    accumulator &= bit(limb, 33 + step);
    bits[chain_base + step] = accumulator;
  }
}

fn violation_word(value: F128) -> F128 {
  let first = limb_violation_bits(value.lo) as u64;
  let second = limb_violation_bits(value.hi) as u64;
  F128::new(first | (second << 32), 0)
}

fn limb_violation_bits(value: u64) -> u32 {
  if value >= GOLDILOCKS_MODULUS { value as u32 } else { 0 }
}

fn write_f128(bits: &mut [bool], offset: usize, value: F128) {
  for local in 0..64 {
    bits[offset + local] = bit(value.lo, local);
    bits[offset + 64 + local] = bit(value.hi, local);
  }
}

fn bit(value: u64, index: usize) -> bool {
  (value >> index) & 1 == 1
}

fn pack_batch_major(bits: &[bool], nu: usize) -> Vec<F128> {
  let capacity = 1usize << nu;
  assert_eq!(bits.len(), capacity * K);
  let chunks = K / 128;
  let mut packed = vec![F128::ZERO; chunks * capacity];
  for chunk in 0..chunks {
    for outer in 0..capacity {
      let start = outer * K + chunk * 128;
      let mut lo = 0u64;
      let mut hi = 0u64;
      for local in 0..64 {
        lo |= u64::from(bits[start + local]) << local;
        hi |= u64::from(bits[start + 64 + local]) << local;
      }
      packed[(chunk << nu) + outer] = F128::new(lo, hi);
    }
  }
  packed
}

#[cfg(test)]
mod tests {
  use std::panic::{AssertUnwindSafe, catch_unwind};

  use flock_prover::circuit::builder::ShapeBuilder;
  use multi_stark::{
    p3_field::{PrimeCharacteristicRing, PrimeField64},
    p3_goldilocks::Goldilocks,
  };

  use super::*;

  #[test]
  fn canonicality_boundary_matches_goldilocks_modulus() {
    for value in [0, 1, GOLDILOCKS_MODULUS - 1] {
      assert_eq!(violation_word(F128::new(value, value)), F128::ZERO);
    }
    assert_ne!(violation_word(F128::new(GOLDILOCKS_MODULUS, 0)), F128::ZERO);
    assert_ne!(violation_word(F128::new(0, GOLDILOCKS_MODULUS)), F128::ZERO);
    assert_ne!(violation_word(F128::new(u64::MAX, 0)), F128::ZERO);
  }

  #[test]
  fn r1cs_recomputes_every_violation_bit() {
    let r1cs = build_canonical_pair_r1cs(3);
    for value in [
      F128::new(0, GOLDILOCKS_MODULUS - 1),
      F128::new(GOLDILOCKS_MODULUS, u64::MAX),
    ] {
      let mut row = vec![false; K];
      fill_logical_row(&mut row, value);
      let mut witness = vec![false; r1cs.n()];
      witness[..K].copy_from_slice(&row);
      assert!(r1cs.satisfies(&witness));

      if violation_word(value) != F128::ZERO {
        witness[VIOLATION_BASE..VIOLATION_BASE + 128].fill(false);
        assert!(!r1cs.satisfies(&witness));
      }
    }
  }

  #[test]
  fn circuit_wiring_pins_violation_output_to_zero() {
    let nu = 3;
    let mut builder = ShapeBuilder::new(nu);
    let slot = builder.slot(CanonicalGoldilocksPairGate { nu });
    let candidate = builder.input();
    let zero = builder.fixed_public_input(F128::ZERO);
    let violation = builder.gate(slot, &[candidate])[0];
    builder.connect(violation, zero);
    let shape = builder.finish().unwrap();

    shape.run(&[F128::new(GOLDILOCKS_MODULUS - 1, 0), F128::ZERO], &[]);
    let invalid = catch_unwind(AssertUnwindSafe(|| {
      shape.run(&[F128::new(GOLDILOCKS_MODULUS, 0), F128::ZERO], &[])
    }));
    assert!(invalid.is_err());
  }

  #[test]
  fn batch_major_witness_has_zero_dummy_rows() {
    let rows = [
      CanonicalGoldilocksPairRow(F128::new(1, 2)),
      CanonicalGoldilocksPairRow(F128::new(3, 4)),
    ];
    let (z, a, b, stripe) = generate_canonical_pair_witness(&rows, 3);
    assert_eq!(z.len(), 32);
    assert_eq!(a.len(), z.len());
    assert_eq!(b.len(), z.len());
    assert_eq!(stripe.len(), K);
    for chunk in 0..K / 128 {
      for outer in rows.len()..8 {
        assert_eq!(z[(chunk << 3) + outer], F128::ZERO);
        assert_eq!(a[(chunk << 3) + outer], F128::ZERO);
        assert_eq!(b[(chunk << 3) + outer], F128::ZERO);
      }
    }
  }

  #[test]
  fn modular_add_matches_reference_goldilocks() {
    let boundary = [
      0,
      1,
      2,
      (1u64 << 32) - 1,
      1u64 << 32,
      GOLDILOCKS_MODULUS - 2,
      GOLDILOCKS_MODULUS - 1,
    ];
    for &left in &boundary {
      for &right in &boundary {
        let expected = (Goldilocks::from_u64(left)
          + Goldilocks::from_u64(right))
        .as_canonical_u64();
        assert_eq!(goldilocks_add(left, right), expected);
      }
    }

    let mut state = 0x6a09_e667_f3bc_c909u64;
    for _ in 0..256 {
      state = state
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(0xbf58_476d_1ce4_e5b9);
      let left = state % GOLDILOCKS_MODULUS;
      state ^= state.rotate_left(29);
      let right = state % GOLDILOCKS_MODULUS;
      let expected = (Goldilocks::from_u64(left) + Goldilocks::from_u64(right))
        .as_canonical_u64();
      assert_eq!(goldilocks_add(left, right), expected);
    }
  }

  #[test]
  fn modular_add_r1cs_rejects_wrong_result_and_quotient() {
    let plan = build_goldilocks_add_plan();
    let r1cs = plan.boolean.block_r1cs(3);
    let cases = [
      GoldilocksAddPairRow {
        left: F128::new(0, GOLDILOCKS_MODULUS - 1),
        right: F128::new(0, 0),
      },
      GoldilocksAddPairRow {
        left: F128::new(GOLDILOCKS_MODULUS - 1, 1 << 32),
        right: F128::new(GOLDILOCKS_MODULUS - 1, u64::MAX >> 32),
      },
    ];
    for row in cases {
      let mut logical = vec![false; plan.boolean.k()];
      plan.boolean.fill_row(&mut logical, |bits| {
        fill_goldilocks_add_row(&plan, row, bits)
      });
      let mut witness = vec![false; r1cs.n()];
      witness[..plan.boolean.k()].copy_from_slice(&logical);
      assert!(r1cs.satisfies(&witness));

      let mut wrong_result = witness.clone();
      wrong_result[ADD_RESULT_BASE + 17] ^= true;
      assert!(!r1cs.satisfies(&wrong_result));

      let mut wrong_quotient = witness;
      wrong_quotient[plan.quotient_bits[0]] ^= true;
      assert!(!r1cs.satisfies(&wrong_quotient));
    }
  }

  #[test]
  fn modular_add_gate_pins_equation_residuals() {
    let nu = 3;
    let mut builder = ShapeBuilder::new(nu);
    let slot = builder.slot(GoldilocksAddPairGate { nu });
    let left = builder.input();
    let right = builder.input();
    let zero = builder.fixed_public_input(F128::ZERO);
    let outputs = builder.gate(slot, &[left, right]);
    builder.connect(outputs[1], zero);
    builder.connect(outputs[2], zero);
    builder.publish(outputs[0]);
    let shape = builder.finish().unwrap();

    let left = F128::new(GOLDILOCKS_MODULUS - 1, 7);
    let right = F128::new(2, GOLDILOCKS_MODULUS - 3);
    let witness = shape.run(&[left, right, F128::ZERO], &[]);
    assert_eq!(*witness.public.last().unwrap(), F128::new(1, 4));
    assert_eq!(
      witness.rows::<GoldilocksAddPairGate>(slot),
      &[GoldilocksAddPairRow { left, right }]
    );
  }

  #[test]
  fn modular_add_batch_witness_zeroes_dummy_rows() {
    let rows =
      [GoldilocksAddPairRow { left: F128::new(1, 2), right: F128::new(3, 4) }];
    let (z, a, b, stripe) = generate_goldilocks_add_witness(&rows, 3);
    let chunks = (1usize << ADD_K_LOG) / 128;
    assert_eq!(z.len(), chunks * 8);
    assert_eq!(a.len(), z.len());
    assert_eq!(b.len(), z.len());
    assert_eq!(stripe.len(), 1usize << ADD_K_LOG);
    for chunk in 0..chunks {
      for outer in rows.len()..8 {
        assert_eq!(z[(chunk << 3) + outer], F128::ZERO);
        assert_eq!(a[(chunk << 3) + outer], F128::ZERO);
        assert_eq!(b[(chunk << 3) + outer], F128::ZERO);
      }
    }
  }
}
