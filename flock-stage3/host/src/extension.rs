//! Degree-two Goldilocks extension arithmetic lowered to reusable base gates.
//!
//! Extension elements are packed as `F128::new(c0, c1)` and use
//! `X^2 = 7`, matching Plonky3's Goldilocks binomial extension. The lowering
//! deliberately composes the already checked base-field addition and
//! multiplication relations rather than introducing another large monolithic
//! arithmetic table.

use std::cell::Cell;

use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
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
  goldilocks::{CanonicalGoldilocksQuadGate, GoldilocksAddPairGate},
  multiplication::{GoldilocksMulPairGate, goldilocks_mul},
  sizing::CircuitEmitter,
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
/// Call `finish_canonical` before finishing the emission, including a census.
pub(crate) struct GoldilocksCircuitSlots {
  pub(crate) add: SlotId,
  pub(crate) mul: SlotId,
  pub(crate) canonical: SlotId,
  pub(crate) repack: SlotId,
  zero: Wire,
  assertion_group: Cell<Option<(Wire, usize)>>,
  pending_canonical: Cell<Option<Wire>>,
}

impl GoldilocksCircuitSlots {
  pub(crate) fn declare(builder: &mut impl CircuitEmitter, nu: usize) -> Self {
    let add = builder.slot(GoldilocksAddPairGate { nu });
    let mul = builder.slot(GoldilocksMulPairGate { nu });
    let canonical = builder.slot(CanonicalGoldilocksQuadGate { nu });
    let repack = builder.slot(GoldilocksLaneRepackGate { nu });
    let zero = builder.fixed_public_input(F128::ZERO);
    Self {
      add,
      mul,
      canonical,
      repack,
      zero,
      assertion_group: Cell::new(None),
      pending_canonical: Cell::new(None),
    }
  }

  fn assert_zero(&self, builder: &mut impl CircuitEmitter, residual: Wire) {
    // Keep data zero input-only. Connecting residual outputs to that same
    // class creates producer -> consumer cycles. The pinned builder also
    // appends later gate inputs to the original wire, not its union-find
    // root, so merging data zero away could silently split its circuit cells.
    //
    // Each assertion class instead has its own canonical(0) output, which
    // the existing table constrains to zero. No member is used as data.
    // Bound the class size because the pinned dataflow checker scans every
    // class cell for every producer, even when there are no consumers.
    const GROUP_SIZE: usize = 256;
    let (zero, used) = match self.assertion_group.get() {
      Some((zero, used)) if used < GROUP_SIZE => (zero, used),
      _ => (builder.gate(self.canonical, &[self.zero, self.zero])[0], 0),
    };
    // connect moves the second class into the first; keep this anchor stable.
    builder.connect(zero, residual);
    self.assertion_group.set(Some((zero, used + 1)));
  }

  pub(crate) fn assert_canonical(
    &self,
    builder: &mut impl CircuitEmitter,
    value: Wire,
  ) {
    // Batch by emission order, never by wire identity: counting wires are
    // all the same opaque placeholder. Each requested check is retained.
    if let Some(first) = self.pending_canonical.take() {
      let violation = builder.gate(self.canonical, &[first, value])[0];
      self.assert_zero(builder, violation);
    } else {
      self.pending_canonical.set(Some(value));
    }
  }

  /// Flush an odd final check before finishing either a census or a circuit.
  /// The unused word is the fixed, input-only zero, not an assertion output.
  pub(crate) fn finish_canonical(&self, builder: &mut impl CircuitEmitter) {
    if let Some(value) = self.pending_canonical.take() {
      let violation = builder.gate(self.canonical, &[value, self.zero])[0];
      self.assert_zero(builder, violation);
    }
  }

  pub(crate) fn add(
    &self,
    builder: &mut impl CircuitEmitter,
    left: Wire,
    right: Wire,
  ) -> Wire {
    let outputs = builder.gate(self.add, &[left, right]);
    for &residual in &outputs[1..] {
      self.assert_zero(builder, residual);
    }
    self.assert_canonical(builder, outputs[0]);
    outputs[0]
  }

  pub(crate) fn mul(
    &self,
    builder: &mut impl CircuitEmitter,
    left: Wire,
    right: Wire,
  ) -> Wire {
    let outputs = builder.gate(self.mul, &[left, right]);
    for &residual in &outputs[1..] {
      self.assert_zero(builder, residual);
    }
    self.assert_canonical(builder, outputs[0]);
    outputs[0]
  }

  /// Multiply two packed extension values in `Goldilocks[X]/(X^2 - 7)`.
  pub(crate) fn ext2_mul(
    &self,
    builder: &mut impl CircuitEmitter,
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
    builder: &mut impl CircuitEmitter,
    value: Wire,
  ) -> Wire {
    builder.gate(self.repack, &[value, self.zero])[3]
  }

  /// Split `[c0, c1]` into the two base-coordinate embeddings `[c0, 0]`
  /// and `[c1, 0]` used by the coordinate-expanded AIR constraints.
  pub(crate) fn ext2_coordinates(
    &self,
    builder: &mut impl CircuitEmitter,
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
  use flock_prover::{
    circuit::{Cell as CircuitCell, CellSlot, builder::ShapeBuilder},
    schedule::IoDirection,
  };
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
  fn packed_canonical_checks_preserve_odd_tails_and_counting_parity() {
    use crate::sizing::CountingEmitter;
    fn emit(builder: &mut impl CircuitEmitter, nu: usize, checks: usize) {
      let slots = GoldilocksCircuitSlots::declare(builder, nu);
      for _ in 0..checks {
        let value = builder.input();
        slots.assert_canonical(builder, value);
      }
      slots.finish_canonical(builder);
      // Finalization is idempotent; no check is duplicated on a second call.
      slots.finish_canonical(builder);
    }
    for checks in [0usize, 1, 2, 3, 511, 512, 513] {
      let mut count = CountingEmitter::new();
      emit(&mut count, CountingEmitter::COUNT_NU, checks);
      let packed = checks.div_ceil(2);
      assert_eq!(
        count
          .table_rows()
          .find(|&(name, _)| name == "CanonicalGoldilocksQuadGate"),
        Some(("CanonicalGoldilocksQuadGate", packed + packed.div_ceil(256))),
      );
      let mut builder = ShapeBuilder::new(10);
      emit(&mut builder, 10, checks);
      let shape = builder.finish().unwrap();
      count.ensure_matches(&shape).unwrap();
      let mut inputs = vec![F128::new(17, GOLDILOCKS_MODULUS - 1); checks + 1];
      inputs[0] = F128::ZERO;
      shape.run(&inputs, &[]);
      for index in 1..=checks {
        for invalid in
          [F128::new(GOLDILOCKS_MODULUS, 0), F128::new(0, u64::MAX)]
        {
          let mut mutated = inputs.clone();
          mutated[index] = invalid;
          assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
              shape.run(&mutated, &[])
            }))
            .is_err(),
            "check {index} of {checks}"
          );
        }
      }
    }
  }

  #[test]
  fn assertion_groups_preserve_every_later_data_zero_cell() {
    const NU: usize = 10;
    const ROWS: usize = 600;
    let mut builder = ShapeBuilder::new(NU);
    let slots = GoldilocksCircuitSlots::declare(&mut builder, NU);
    let value = builder.public_input();
    let mut result = value;
    for _ in 0..ROWS {
      slots.assert_canonical(&mut builder, value);
      // The data-zero input is consumed AFTER residuals have been connected.
      result = slots.embed_low_lane(&mut builder, value);
    }
    builder.publish(result);
    slots.finish_canonical(&mut builder);
    let shape = builder.finish().unwrap();
    let inputs = [F128::ZERO, F128::new(17, 23)];
    let witness = shape.run(&inputs, &[]);
    assert_eq!(witness.public, [inputs[0], inputs[1], F128::new(17, 0)]);

    // Inspect the actual sigma classes, not just the native runner: the
    // pinned builder can resolve online inputs correctly while losing cells
    // appended to a wire that was previously merged into another root.
    let cells = shape.circuit.cells();
    let public_zero =
      cells.cell_index(CircuitCell::new(cells.num_gate_slots(), 0));
    let zero_class = shape
      .circuit
      .wires()
      .iter()
      .find(|class| class.contains(&public_zero))
      .expect("fixed data zero belongs to a wiring class");
    let repack = shape.registry_slot(slots.repack);
    let second_input = cells
      .slots()
      .iter()
      .position(|slot| {
        matches!(slot, CellSlot::Gate { ty, word }
          if *ty == repack && word.word_col == 1 && word.dir == IoDirection::In)
      })
      .unwrap();
    for row in 0..ROWS {
      assert!(
        zero_class
          .contains(&cells.cell_index(CircuitCell::new(second_input, row,)))
      );
    }
    assert!(zero_class.iter().all(|index| {
      !matches!(cells.slots()[index >> NU], CellSlot::Gate { word, .. }
        if word.dir == IoDirection::Out)
    }));

    let canonical = shape.registry_slot(slots.canonical);
    let assertion_classes: Vec<_> = shape
      .circuit
      .wires()
      .iter()
      .filter(|class| {
        class.iter().any(|index| {
          matches!(cells.slots()[index >> NU], CellSlot::Gate { ty, word }
            if ty == canonical && word.dir == IoDirection::Out)
        })
      })
      .collect();
    assert_eq!(assertion_classes.len(), ROWS.div_ceil(2).div_ceil(256));
    for class in assertion_classes {
      assert!(class.len() <= 257);
      assert!(class.iter().all(|index| {
        matches!(cells.slots()[index >> NU], CellSlot::Gate { word, .. }
          if word.dir == IoDirection::Out)
      }));
    }
    for bad in [F128::new(GOLDILOCKS_MODULUS, 0), F128::new(0, u64::MAX)] {
      assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
          shape.run(&[F128::ZERO, bad], &[])
        }))
        .is_err()
      );
    }
  }

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
