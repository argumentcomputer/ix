//! Degree-two Goldilocks extension arithmetic lowered to reusable base gates.
//!
//! Extension elements are packed as `F128::new(c0, c1)` and use
//! `X^2 = 7`, matching Plonky3's Goldilocks binomial extension. The lowering
//! deliberately composes the already checked base-field addition and
//! multiplication relations rather than introducing another large monolithic
//! arithmetic table.

use flock_prover::{
  circuit::builder::{GateType, ShapeBuilder, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};

use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness,
    generate_boolean_witness_into, write_f128,
  },
  goldilocks::{CanonicalGoldilocksPairGate, GoldilocksAddPairGate},
  multiplication::{GoldilocksMulPairGate, goldilocks_mul},
};

const REPACK_K_LOG: usize = 10;
const FIRST_BASE: usize = 0;
const SECOND_BASE: usize = 128;
const DUPLICATE_LOW_BASE: usize = 256;
const DUPLICATE_HIGH_BASE: usize = 384;
const SWAP_BASE: usize = 512;
const SELECT_BASE: usize = 640;
const REPACK_COLUMNS: usize = 768;

/// Fixed lane transforms used by the degree-two extension lowering.
///
/// For `first = [a,b]` and `second = [c,d]`, the outputs are
/// `[a,a]`, `[b,b]`, `[b,a]`, and `[a,d]`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct GoldilocksLaneRepackGate {
  pub(crate) nu: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct GoldilocksLaneRepackRow {
  first: F128,
  second: F128,
}

impl GateType for GoldilocksLaneRepackGate {
  type Row = GoldilocksLaneRepackRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_lane_repack_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::output(2),
        IoWord::output(3),
        IoWord::output(4),
        IoWord::output(5),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let first = inputs[0];
    let second = inputs[1];
    outputs.extend_from_slice(&[
      F128::new(first.lo, first.lo),
      F128::new(first.hi, first.hi),
      F128::new(first.hi, first.lo),
      F128::new(first.lo, second.hi),
    ]);
    GoldilocksLaneRepackRow { first, second }
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_lane_repack_r1cs(nu: usize) -> BlockR1cs {
  build_lane_repack_plan().block_r1cs(nu)
}

pub(crate) fn generate_lane_repack_witness(
  rows: &[GoldilocksLaneRepackRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let plan = build_lane_repack_plan();
  generate_boolean_witness(&plan, rows, nu, |row, bits| {
    write_f128(bits, FIRST_BASE, row.first);
    write_f128(bits, SECOND_BASE, row.second);
  })
}

pub(crate) fn generate_lane_repack_witness_into(
  rows: &[GoldilocksLaneRepackRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  let plan = build_lane_repack_plan();
  generate_boolean_witness_into(&plan, rows, nu, dst, |row, bits| {
    write_f128(bits, FIRST_BASE, row.first);
    write_f128(bits, SECOND_BASE, row.second);
  })
}

fn build_lane_repack_plan() -> BooleanR1csPlan {
  let mut builder = BooleanR1csBuilder::new(REPACK_K_LOG, REPACK_COLUMNS);
  for column in FIRST_BASE..SECOND_BASE + 128 {
    builder.free_boolean_at(column);
  }
  for bit in 0..64 {
    let first_low = FIRST_BASE + bit;
    let first_high = FIRST_BASE + 64 + bit;
    let second_high = SECOND_BASE + 64 + bit;
    for output in [DUPLICATE_LOW_BASE + bit, DUPLICATE_LOW_BASE + 64 + bit] {
      builder.write_product_of_parities(output, &[first_low], &[first_low]);
    }
    for output in [DUPLICATE_HIGH_BASE + bit, DUPLICATE_HIGH_BASE + 64 + bit] {
      builder.write_product_of_parities(output, &[first_high], &[first_high]);
    }
    builder.write_product_of_parities(
      SWAP_BASE + bit,
      &[first_high],
      &[first_high],
    );
    builder.write_product_of_parities(
      SWAP_BASE + 64 + bit,
      &[first_low],
      &[first_low],
    );
    builder.write_product_of_parities(
      SELECT_BASE + bit,
      &[first_low],
      &[first_low],
    );
    builder.write_product_of_parities(
      SELECT_BASE + 64 + bit,
      &[second_high],
      &[second_high],
    );
  }
  builder.finish()
}

/// The four table slots and fixed zero wire needed by Goldilocks arithmetic.
pub(crate) struct GoldilocksCircuitSlots {
  pub(crate) add: SlotId,
  pub(crate) mul: SlotId,
  pub(crate) canonical: SlotId,
  pub(crate) repack: SlotId,
  zero: Wire,
}

impl GoldilocksCircuitSlots {
  pub(crate) fn declare(builder: &mut ShapeBuilder, nu: usize) -> Self {
    let add = builder.slot(GoldilocksAddPairGate { nu });
    let mul = builder.slot(GoldilocksMulPairGate { nu });
    let canonical = builder.slot(CanonicalGoldilocksPairGate { nu });
    let repack = builder.slot(GoldilocksLaneRepackGate { nu });
    let zero = builder.fixed_public_input(F128::ZERO);
    Self { add, mul, canonical, repack, zero }
  }

  pub(crate) fn assert_canonical(
    &self,
    builder: &mut ShapeBuilder,
    value: Wire,
  ) {
    let violation = builder.gate(self.canonical, &[value])[0];
    builder.connect(violation, self.zero);
  }

  pub(crate) fn add(
    &self,
    builder: &mut ShapeBuilder,
    left: Wire,
    right: Wire,
  ) -> Wire {
    let outputs = builder.gate(self.add, &[left, right]);
    for &residual in &outputs[1..] {
      builder.connect(residual, self.zero);
    }
    self.assert_canonical(builder, outputs[0]);
    outputs[0]
  }

  pub(crate) fn mul(
    &self,
    builder: &mut ShapeBuilder,
    left: Wire,
    right: Wire,
  ) -> Wire {
    let outputs = builder.gate(self.mul, &[left, right]);
    for &residual in &outputs[1..] {
      builder.connect(residual, self.zero);
    }
    self.assert_canonical(builder, outputs[0]);
    outputs[0]
  }

  /// Multiply two packed extension values in `Goldilocks[X]/(X^2 - 7)`.
  pub(crate) fn ext2_mul(
    &self,
    builder: &mut ShapeBuilder,
    left: Wire,
    right: Wire,
  ) -> Wire {
    self.assert_canonical(builder, left);
    self.assert_canonical(builder, right);

    let left_lanes = builder.gate(self.repack, &[left, self.zero]);
    let products_low = self.mul(builder, left_lanes[0], right);
    let products_high = self.mul(builder, left_lanes[1], right);

    let high_repacked = builder.gate(self.repack, &[products_high, self.zero]);
    let reversed_high = high_repacked[2];
    let twice = self.add(builder, reversed_high, reversed_high);
    let four_times = self.add(builder, twice, twice);
    let six_times = self.add(builder, four_times, twice);
    let seven_times = self.add(builder, six_times, reversed_high);
    let selected = builder.gate(self.repack, &[seven_times, reversed_high])[3];
    self.add(builder, products_low, selected)
  }

  /// Embed the low `u64` lane as the constant-coordinate element `[lo, 0]`.
  pub(crate) fn embed_low_lane(
    &self,
    builder: &mut ShapeBuilder,
    value: Wire,
  ) -> Wire {
    builder.gate(self.repack, &[value, self.zero])[3]
  }

  /// Split `[c0, c1]` into the two base-coordinate embeddings `[c0, 0]`
  /// and `[c1, 0]` used by the coordinate-expanded AIR constraints.
  pub(crate) fn ext2_coordinates(
    &self,
    builder: &mut ShapeBuilder,
    value: Wire,
  ) -> [Wire; 2] {
    let lanes = builder.gate(self.repack, &[value, self.zero]);
    let low = lanes[3];
    let high_first = lanes[2];
    let high = builder.gate(self.repack, &[high_first, self.zero])[3];
    [low, high]
  }
}

pub(crate) fn goldilocks_ext2_mul(left: F128, right: F128) -> F128 {
  F128::new(
    crate::goldilocks::goldilocks_add(
      goldilocks_mul(left.lo, right.lo),
      goldilocks_mul(7, goldilocks_mul(left.hi, right.hi)),
    ),
    crate::goldilocks::goldilocks_add(
      goldilocks_mul(left.lo, right.hi),
      goldilocks_mul(left.hi, right.lo),
    ),
  )
}

#[cfg(test)]
mod tests {
  use multi_stark::{
    p3_field::{
      BasedVectorSpace, PrimeCharacteristicRing, PrimeField64,
      extension::BinomialExtensionField,
    },
    p3_goldilocks::Goldilocks,
  };

  use super::*;
  use crate::goldilocks::GOLDILOCKS_MODULUS;

  #[test]
  fn native_ext2_mul_matches_plonky3() {
    let cases = [
      ([0, 0], [0, 0]),
      ([1, 0], [0, 1]),
      ([GOLDILOCKS_MODULUS - 1, 17], [23, GOLDILOCKS_MODULUS - 2]),
      ([0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210], [7, 11]),
    ];
    for (left, right) in cases {
      let reference = BinomialExtensionField::<Goldilocks, 2>::new([
        Goldilocks::from_u64(left[0]),
        Goldilocks::from_u64(left[1]),
      ]) * BinomialExtensionField::<Goldilocks, 2>::new([
        Goldilocks::from_u64(right[0]),
        Goldilocks::from_u64(right[1]),
      ]);
      let reference: &[Goldilocks] = reference.as_basis_coefficients_slice();
      let actual = goldilocks_ext2_mul(
        F128::new(left[0], left[1]),
        F128::new(right[0], right[1]),
      );
      assert_eq!(actual.lo, reference[0].as_canonical_u64());
      assert_eq!(actual.hi, reference[1].as_canonical_u64());
    }
  }

  #[test]
  fn lane_repack_r1cs_matches_gate_semantics() {
    let row = GoldilocksLaneRepackRow {
      first: F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
      second: F128::new(9, 0x55aa_aa55_1234_5678),
    };
    let plan = build_lane_repack_plan();
    let r1cs = plan.block_r1cs(3);
    let mut logical = vec![false; plan.k()];
    plan.fill_row(&mut logical, |bits| {
      write_f128(bits, FIRST_BASE, row.first);
      write_f128(bits, SECOND_BASE, row.second);
    });
    let mut witness = vec![false; r1cs.n()];
    witness[..plan.k()].copy_from_slice(&logical);
    assert!(r1cs.satisfies(&witness));

    let outputs = [
      F128::new(row.first.lo, row.first.lo),
      F128::new(row.first.hi, row.first.hi),
      F128::new(row.first.hi, row.first.lo),
      F128::new(row.first.lo, row.second.hi),
    ];
    for (index, output) in outputs.into_iter().enumerate() {
      let mut encoded = vec![false; 128];
      write_f128(&mut encoded, 0, output);
      assert_eq!(
        &logical[DUPLICATE_LOW_BASE + index * 128
          ..DUPLICATE_LOW_BASE + (index + 1) * 128],
        encoded
      );
    }
  }
}
