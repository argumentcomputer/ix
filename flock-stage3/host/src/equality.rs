//! A directed equality assertion for two `F128` wires.
//!
//! Flock wire connections merge producer classes, so connecting two values
//! that were independently computed can create a cyclic circuit graph. This
//! gate keeps the graph directed: it emits their bitwise XOR, which callers
//! pin to the fixed zero wire.

use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};

use crate::boolean::{
  BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  write_f128,
};

const K_LOG: usize = 9;
const LEFT_BASE: usize = 0;
const RIGHT_BASE: usize = 128;
const RESIDUAL_BASE: usize = 256;
const COLUMNS: usize = 384;
pub(crate) const F128_ZERO_BATCH_WIDTH: usize = 4;
const ZERO_K_LOG: usize = 9;
const ZERO_INPUT_BASE: usize = 0;
const ZERO_COLUMNS: usize = F128_ZERO_BATCH_WIDTH * 128;

#[derive(Clone, Copy, Debug)]
pub(crate) struct F128EqualityGate {
  pub(crate) nu: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct F128EqualityRow {
  left: F128,
  right: F128,
}

/// Directed assertion that four `F128` wires are zero.
///
/// Unlike merging every residual into one fixed-zero equivalence class, this
/// keeps each producer connected to a single consumer. Batching four
/// residuals also reduces the uniform row domain without making this table
/// wider in total than the four single-word assertions it replaces.
#[derive(Clone, Copy, Debug)]
pub(crate) struct F128ZeroGate {
  pub(crate) nu: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct F128ZeroRow([F128; F128_ZERO_BATCH_WIDTH]);

impl GateType for F128ZeroGate {
  type Row = F128ZeroRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_f128_zero_r1cs(self.nu))
      .with_io_schema((0..F128_ZERO_BATCH_WIDTH).map(IoWord::input).collect())
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    _outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let values: [F128; F128_ZERO_BATCH_WIDTH] =
      inputs.try_into().expect("F128 zero gate input width");
    assert!(
      values.iter().all(|&value| value == F128::ZERO),
      "F128 zero assertion failed"
    );
    F128ZeroRow(values)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

impl GateType for F128EqualityGate {
  type Row = F128EqualityRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_f128_equality_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::output(2),
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
    outputs.push(F128::new(left.lo ^ right.lo, left.hi ^ right.hi));
    F128EqualityRow { left, right }
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_f128_equality_r1cs(nu: usize) -> BlockR1cs {
  build_plan().block_r1cs(nu)
}

pub(crate) fn generate_f128_equality_witness_into(
  rows: &[F128EqualityRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  let plan = build_plan();
  generate_boolean_witness_into(&plan, rows, nu, dst, |row, bits| {
    write_f128(bits, LEFT_BASE, row.left);
    write_f128(bits, RIGHT_BASE, row.right);
  })
}

pub(crate) fn build_f128_zero_r1cs(nu: usize) -> BlockR1cs {
  build_zero_plan().block_r1cs(nu)
}

pub(crate) fn generate_f128_zero_witness_into(
  rows: &[F128ZeroRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  let plan = build_zero_plan();
  generate_boolean_witness_into(&plan, rows, nu, dst, |row, bits| {
    for (word, &value) in row.0.iter().enumerate() {
      write_f128(bits, ZERO_INPUT_BASE + word * 128, value);
    }
  })
}

fn build_plan() -> BooleanR1csPlan {
  let mut builder = BooleanR1csBuilder::new(K_LOG, COLUMNS);
  for column in LEFT_BASE..RIGHT_BASE + 128 {
    builder.free_boolean_at(column);
  }
  let one = builder.alloc_constant_one();
  for bit in 0..128 {
    builder.write_xor(
      RESIDUAL_BASE + bit,
      &[LEFT_BASE + bit, RIGHT_BASE + bit],
      one,
    );
  }
  builder.finish()
}

fn build_zero_plan() -> BooleanR1csPlan {
  // Block R1CS has C = I. Empty A and B rows enforce 0 * 0 = z_i,
  // pinning every supplied bit without a constant-one column.
  BooleanR1csBuilder::new(ZERO_K_LOG, ZERO_COLUMNS).finish()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn equality_r1cs_rejects_nonzero_residual() {
    let plan = build_plan();
    let r1cs = plan.block_r1cs(3);
    let left = F128::new(0x1234, 0x5678);
    let mut logical = vec![false; plan.k()];
    plan.fill_row(&mut logical, |bits| {
      write_f128(bits, LEFT_BASE, left);
      write_f128(bits, RIGHT_BASE, left);
    });
    let mut witness = vec![false; r1cs.n()];
    witness[..plan.k()].copy_from_slice(&logical);
    assert!(r1cs.satisfies(&witness));

    let mut wrong = witness;
    wrong[RIGHT_BASE + 7] ^= true;
    assert!(!r1cs.satisfies(&wrong));
  }

  #[test]
  fn zero_gate_r1cs_rejects_every_nonzero_bit() {
    let plan = build_zero_plan();
    let r1cs = plan.block_r1cs(3);
    let mut zero = vec![false; r1cs.n()];
    plan.fill_row(&mut zero[..plan.k()], |_| {});
    assert!(r1cs.satisfies(&zero));

    for bit in 0..ZERO_COLUMNS {
      let mut nonzero = zero.clone();
      nonzero[bit] = true;
      assert!(!r1cs.satisfies(&nonzero));
    }
  }
}
