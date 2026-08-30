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
};

use crate::boolean::{
  BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness, write_f128,
};

const K_LOG: usize = 9;
const LEFT_BASE: usize = 0;
const RIGHT_BASE: usize = 128;
const RESIDUAL_BASE: usize = 256;
const COLUMNS: usize = 384;

#[derive(Clone, Copy, Debug)]
pub(crate) struct F128EqualityGate {
  pub(crate) nu: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct F128EqualityRow {
  left: F128,
  right: F128,
}

impl GateType for F128EqualityGate {
  type Row = F128EqualityRow;
  type Hint = ();

  fn table(&self) -> TableType {
    TableType::from_block_r1cs(&build_f128_equality_r1cs(self.nu))
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

pub(crate) fn generate_f128_equality_witness(
  rows: &[F128EqualityRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  let plan = build_plan();
  generate_boolean_witness(&plan, rows, nu, |row, bits| {
    write_f128(bits, LEFT_BASE, row.left);
    write_f128(bits, RIGHT_BASE, row.right);
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
}
