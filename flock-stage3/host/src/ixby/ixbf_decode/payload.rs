//! Checked scalar-payload cursor advancement and codec-control packing.
//! The caller must share the length with the actual decoder and authenticate
//! the source at the returned range; this relation does not read payload bytes.

use super::synthesis::Builder;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{add, fill_words, subtract},
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

/// Inputs: `(offset, file length)` u64 lanes, a narrow u64 length (high
/// lane zero), and a narrow Boolean enable. A disabled row has zero length
/// and preserves the cursor. Empty enabled payloads are valid.
#[derive(Clone, Debug)]
pub struct PayloadCursorGate {
  pub(super) nu: usize,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Copy, Debug)]
pub struct PayloadCursorRow(pub(super) [F128; 3]);

impl PayloadCursorGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional payload cursor row domain");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(build_plan)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[PayloadCursorRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| fill_words(&row.0, bits),
    )
  }
}

impl CountedGate for PayloadCursorGate {
  fn input_count(&self) -> usize {
    3
  }
  fn output_count(&self) -> usize {
    4
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for PayloadCursorGate {
  type Row = PayloadCursorRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..3).map(IoWord::input).chain((3..7).map(IoWord::output)).collect(),
    )
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let input = inputs.try_into().expect("fixed payload cursor input width");
    outputs.extend(evaluate(&input));
    PayloadCursorRow(input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct PayloadCursorWires {
  /// NaturalDecodeGate control: `(exact encoded length, enable)` u64 lanes.
  pub natural_control: Wire,
  /// `(payload start, payload length)` u64 lanes, not an artifact identity.
  pub range: Wire,
  /// `(payload end, unchanged file length)` u64 lanes.
  pub next: Wire,
}

#[derive(Clone, Copy, Debug)]
pub struct PayloadCursorSlot {
  slot: SlotId,
  zero: Wire,
}

impl PayloadCursorSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: PayloadCursorGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn advance(
    &self,
    b: &mut impl CircuitEmitter,
    cursor: Wire,
    length: Wire,
    enabled: Wire,
  ) -> PayloadCursorWires {
    let output = b.gate(self.slot, &[cursor, length, enabled]);
    b.connect(output[3], self.zero);
    PayloadCursorWires {
      natural_control: output[0],
      range: output[1],
      next: output[2],
    }
  }
}

pub(super) fn evaluate(input: &[F128; 3]) -> [F128; 4] {
  let [cursor, length, enabled] = *input;
  let (next, carry) = cursor.lo.overflowing_add(length.lo);
  let violation = cursor.lo > cursor.hi
    || length.hi != 0
    || enabled.hi != 0
    || enabled.lo > 1
    || (enabled.lo & 1 == 0 && length.lo != 0)
    || carry
    || next > cursor.hi;
  [
    F128::new(length.lo, enabled.lo & 1),
    F128::new(cursor.lo, length.lo),
    F128::new(next, cursor.hi),
    F128::new(u64::from(violation), 0),
  ]
}

fn build_plan() -> BooleanR1csPlan {
  let mut b = Builder::new(3, 4, 1 << 12);
  let offset: Vec<_> = (0..64).collect();
  let file: Vec<_> = (64..128).collect();
  let length: Vec<_> = (128..192).collect();
  let enabled = 256;
  b.require_zero(b.one, &(192..256).collect::<Vec<_>>());
  b.require_zero(b.one, &(257..384).collect::<Vec<_>>());
  let disabled = b.not(enabled);
  b.require_zero(disabled, &length);
  let (_, borrow) = subtract(&mut b.b, b.one, b.zero, &file, &offset);
  b.violations.push(borrow);
  let (next, carry) = add(&mut b.b, b.one, b.zero, &offset, &length);
  b.violations.push(carry);
  let (_, borrow) = subtract(&mut b.b, b.one, b.zero, &file, &next);
  b.violations.push(borrow);
  b.write(3, &[length.clone(), vec![enabled]].concat());
  b.write(4, &[offset, length].concat());
  b.write(5, &[next, file].concat());
  b.finish(6)
}
