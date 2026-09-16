//! Checked 64-bit global fuel for a future segmented execution path.
//!
//! The existing physical interpreter and IXBP wire retain their u32 fuel and
//! keys. This separate component neither upgrades those setups nor proves an
//! IXBF execution. A future interpreter must wire the actual pre-step control
//! metadata and the admitted program budget, and authenticate the complete
//! state at segment boundaries. Supplying a host-selected control kind or
//! checking this ledger alone is not an execution proof.

#[cfg(test)]
mod proof_tests;
#[cfg(test)]
mod tests;

use super::bits::{add, any, equal, equal_constant, not, subtract};
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
    write_f128,
  },
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

/// Both lanes are exact u64 integers, not field sums or wrapping counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fuel64 {
  pub remaining: u64,
  pub consumed: u64,
}

impl Fuel64 {
  pub fn initial(budget: u64) -> Self {
    Self { remaining: budget, consumed: 0 }
  }
  pub fn word(self) -> F128 {
    F128::new(self.remaining, self.consumed)
  }
}

#[derive(Clone, Debug)]
pub struct Fuel64StepGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Copy, Debug)]
pub struct Fuel64StepRow([F128; 3]);

impl Fuel64StepGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "wide-fuel row-domain admission");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(build_plan)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[Fuel64StepRow],
    dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| {
        for (word, value) in row.0.iter().enumerate() {
          write_f128(bits, word * 128, *value);
        }
      },
    )
  }
}

impl CountedGate for Fuel64StepGate {
  fn input_count(&self) -> usize {
    3
  }
  fn output_count(&self) -> usize {
    2
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for Fuel64StepGate {
  type Row = Fuel64StepRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(vec![
      IoWord::input(0),
      IoWord::input(1),
      IoWord::input(2),
      IoWord::output(3),
      IoWord::output(4),
    ])
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let row =
      Fuel64StepRow(inputs.try_into().expect("fixed wide-fuel input width"));
    outputs.extend(evaluate(&row));
    row
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

/// The residual is always connected to a verifier-owned zero. The control
/// input is the native metadata word: kind in low 32 bits (0 eval, 1 return,
/// 2 halted, 3 apply). Its other 96 bits belong to the separate control gate;
/// this component deliberately does not validate or alter them.
#[derive(Clone, Copy, Debug)]
pub struct Fuel64StepSlot {
  slot: SlotId,
  zero: Wire,
}

impl Fuel64StepSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: Fuel64StepGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    fuel: Wire,
    control: Wire,
    budget: Wire,
  ) -> Wire {
    let output = b.gate(self.slot, &[fuel, control, budget]);
    b.connect(output[1], self.zero);
    output[0]
  }
}

/// Total witness computation, including invalid rows. Gate satisfaction and
/// wiring—not this native evaluation—establish the component relation.
fn evaluate(row: &Fuel64StepRow) -> [F128; 2] {
  let [before, control, budget] = row.0;
  let kind = control.lo as u32;
  let active = u64::from(kind != 2);
  let total = u128::from(before.lo) + u128::from(before.hi);
  let (remaining, borrow) = before.lo.overflowing_sub(active);
  let (consumed, carry) = before.hi.overflowing_add(active);
  let violation = kind > 3
    || budget.hi != 0
    || total != u128::from(budget.lo)
    || borrow
    || carry;
  [F128::new(remaining, consumed), F128::new(u64::from(violation), 0)]
}

fn build_plan() -> BooleanR1csPlan {
  const OUTPUT: usize = 3 * 128;
  const RESIDUAL: usize = 4 * 128;
  let mut b = BooleanR1csBuilder::new(12, 5 * 128);
  for bit in 0..3 * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let remaining: Vec<_> = (0..64).collect();
  let consumed: Vec<_> = (64..128).collect();
  let kind: Vec<_> = (128..160).collect();
  let budget: Vec<_> = (256..320).collect();
  let halted = equal_constant(&mut b, one, &kind, 2);
  let active = not(&mut b, one, halted);
  let mut increment = vec![zero; 64];
  increment[0] = active;
  let (total, overflow) = add(&mut b, one, zero, &remaining, &consumed);
  let conserved = equal(&mut b, one, &total, &budget);
  let (next_remaining, borrow) =
    subtract(&mut b, one, zero, &remaining, &increment);
  let (next_consumed, carry) = add(&mut b, one, zero, &consumed, &increment);
  for (bit, source) in next_remaining.iter().chain(&next_consumed).enumerate() {
    b.write_xor(OUTPUT + bit, &[*source], one);
  }
  let mut violations: Vec<_> = (130..160).chain(320..384).collect();
  violations.extend([overflow, not(&mut b, one, conserved), borrow, carry]);
  let violation = any(&mut b, one, &violations);
  b.write_xor(RESIDUAL, &[violation], one);
  b.finish()
}
