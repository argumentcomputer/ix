//! Exact magnitude bit length and the program's declared Nat bound.
//! Magnitude limbs must be the actual NaturalDecodeGate outputs; a host copy
//! of the header limit or of a decoded magnitude does not establish linkage.

use super::{NaturalCapacity, synthesis::Builder};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{fill_words, subtract},
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

/// Inputs: full u128 declared bit limit, narrow Boolean enable, and fixed
/// little-endian magnitude limbs. All bits beyond capacity are zero. Disabled
/// magnitudes are zero. Outputs: exact narrow bit length (zero has length 0),
/// then a validity residual that the slot pins to verifier-owned zero.
#[derive(Clone, Debug)]
pub struct NaturalLimitGate {
  pub(super) nu: usize,
  pub(super) capacity: NaturalCapacity,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct NaturalLimitRow(pub(super) Vec<F128>);

impl NaturalLimitGate {
  pub fn new(nu: usize, capacity: NaturalCapacity) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional natural limit row domain");
    Ok(Self { nu, capacity, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> NaturalCapacity {
    self.capacity
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.capacity))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[NaturalLimitRow],
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

impl CountedGate for NaturalLimitGate {
  fn input_count(&self) -> usize {
    2 + self.capacity.magnitude_words()
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

impl GateType for NaturalLimitGate {
  type Row = NaturalLimitRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let inputs = self.input_count();
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..inputs)
        .map(IoWord::input)
        .chain((inputs..inputs + 2).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(
      inputs.len(),
      self.input_count(),
      "fixed natural limit input width"
    );
    outputs.extend(evaluate(self.capacity, inputs));
    NaturalLimitRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct NaturalLimitSlot {
  slot: SlotId,
  zero: Wire,
  capacity: NaturalCapacity,
}

impl NaturalLimitSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: NaturalLimitGate) -> Self {
    Self {
      capacity: gate.capacity,
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    declared_limit: Wire,
    enabled: Wire,
    magnitude: &[Wire],
  ) -> Wire {
    assert_eq!(magnitude.len(), self.capacity.magnitude_words());
    let mut input = vec![declared_limit, enabled];
    input.extend_from_slice(magnitude);
    let output = b.gate(self.slot, &input);
    b.connect(output[1], self.zero);
    output[0]
  }
}

pub(super) fn evaluate(capacity: NaturalCapacity, input: &[F128]) -> [F128; 2] {
  let limit = u128::from(input[0].lo) | (u128::from(input[0].hi) << 64);
  let mut length = 0usize;
  let mut padding = false;
  let mut nonzero = false;
  for (word, value) in input[2..].iter().enumerate() {
    let value = u128::from(value.lo) | (u128::from(value.hi) << 64);
    nonzero |= value != 0;
    let width = capacity.bits().saturating_sub(word * 128).min(128);
    let mask = u128::MAX.checked_shr((128 - width) as u32).unwrap_or(0);
    padding |= value & !mask != 0;
    let value = value & mask;
    if value != 0 {
      length = word * 128 + 128 - value.leading_zeros() as usize;
    }
  }
  let enabled = input[1];
  let violation = padding
    || enabled.hi != 0
    || enabled.lo > 1
    || (enabled.lo & 1 == 0 && nonzero)
    || length as u128 > limit;
  [F128::new(length as u64, 0), F128::new(u64::from(violation), 0)]
}

fn build_plan(capacity: NaturalCapacity) -> BooleanR1csPlan {
  let inputs = 2 + capacity.magnitude_words();
  let mut b =
    Builder::new(inputs, 2, 128 * (inputs + 2) + 4 * capacity.bits() + 2048);
  b.require_zero(b.one, &(129..256).collect::<Vec<_>>());
  let disabled = b.not(128);
  b.require_zero(disabled, &(256..inputs * 128).collect::<Vec<_>>());
  b.require_zero(
    b.one,
    &(256 + capacity.bits()..inputs * 128).collect::<Vec<_>>(),
  );
  // Exactly one highest-set-bit flag, or none for zero. It is derived from
  // every magnitude bit, never a prover-supplied truncation or length hint.
  let mut none_above = b.one;
  let mut ends = vec![b.zero; capacity.bits()];
  for bit in (0..capacity.bits()).rev() {
    ends[bit] = b.b.and(none_above, 256 + bit);
    none_above = b.b.product_of_parities(&[none_above], &[256 + bit, b.one]);
  }
  let mut length = Vec::with_capacity(128);
  for bit in 0..13 {
    let set: Vec<_> = ends
      .iter()
      .enumerate()
      .filter_map(|(index, flag)| {
        ((index + 1) & (1 << bit) != 0).then_some(*flag)
      })
      .collect();
    length.push(b.sum(&set));
  }
  length.resize(128, b.zero);
  let limit: Vec<_> = (0..128).collect();
  let (_, borrow) = subtract(&mut b.b, b.one, b.zero, &limit, &length);
  b.violations.push(borrow);
  b.write(inputs, &length);
  b.finish(inputs + 1)
}
