use super::{MAX_NAT_BITS, synthesis::Builder};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::fill_words,
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

/// Magnitude width is setup-owned; zero bits admits precisely Nat zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NaturalCapacity(usize);

impl NaturalCapacity {
  pub fn new(bits: usize) -> Result<Self> {
    ensure!(bits <= MAX_NAT_BITS, "functional natural codec bit capacity");
    Ok(Self(bits))
  }
  pub fn bits(self) -> usize {
    self.0
  }
  pub fn encoded_bytes(self) -> usize {
    self.0.div_ceil(7).max(1)
  }
  pub fn encoded_words(self) -> usize {
    self.encoded_bytes().div_ceil(16)
  }
  pub fn magnitude_words(self) -> usize {
    self.0.div_ceil(128).max(1)
  }
}

/// Canonical LEB128 payload only, not a scalar tag or a whole artifact.
/// Input 0 packs exact u64 byte length in `lo` and a Boolean enable in `hi`.
/// Remaining inputs contain the padded little-endian encoding. Disabled rows
/// require length and every payload byte to be zero and produce zero.
#[derive(Clone, Debug)]
pub struct NaturalDecodeGate {
  pub(super) nu: usize,
  pub(super) capacity: NaturalCapacity,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct NaturalDecodeRow(pub(super) Vec<F128>);

impl NaturalDecodeGate {
  pub fn new(nu: usize, capacity: NaturalCapacity) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional natural codec row domain");
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
    rows: &[NaturalDecodeRow],
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

impl CountedGate for NaturalDecodeGate {
  fn input_count(&self) -> usize {
    1 + self.capacity.encoded_words()
  }
  fn output_count(&self) -> usize {
    self.capacity.magnitude_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for NaturalDecodeGate {
  type Row = NaturalDecodeRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let inputs = self.input_count();
    let schema = (0..inputs)
      .map(IoWord::input)
      .chain((inputs..inputs + self.output_count()).map(IoWord::output))
      .collect();
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
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
      "fixed natural codec input width"
    );
    outputs.extend(evaluate(self.capacity, inputs));
    NaturalDecodeRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

/// Always pins the validity residual to a verifier-owned zero.
#[derive(Clone, Copy, Debug)]
pub struct NaturalDecodeSlot {
  slot: SlotId,
  zero: Wire,
  capacity: NaturalCapacity,
}

impl NaturalDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: NaturalDecodeGate) -> Self {
    Self {
      capacity: gate.capacity,
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn decode(
    &self,
    b: &mut impl CircuitEmitter,
    control: Wire,
    encoded: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(encoded.len(), self.capacity.encoded_words());
    let mut inputs = vec![control];
    inputs.extend_from_slice(encoded);
    let mut output = b.gate(self.slot, &inputs);
    b.connect(output.pop().unwrap(), self.zero);
    output
  }
}

/// Independent integer witness computation; never a verifier admission.
pub(super) fn evaluate(capacity: NaturalCapacity, input: &[F128]) -> Vec<F128> {
  let control = input[0];
  let enabled = control.hi & 1 == 1;
  let mut bytes = Vec::with_capacity(capacity.encoded_words() * 16);
  for word in &input[1..] {
    bytes.extend_from_slice(&word.lo.to_le_bytes());
    bytes.extend_from_slice(&word.hi.to_le_bytes());
  }
  let mut result = vec![F128::ZERO; capacity.magnitude_words()];
  let mut consumed = 0;
  let mut violation = control.hi > 1;
  if enabled {
    for (index, byte) in bytes[..capacity.encoded_bytes()].iter().enumerate() {
      for bit in 0..7 {
        if byte & (1 << bit) != 0 {
          let target = index * 7 + bit;
          if target >= capacity.bits() {
            violation = true;
          } else if target % 128 < 64 {
            result[target / 128].lo |= 1 << (target % 128);
          } else {
            result[target / 128].hi |= 1 << (target % 128 - 64);
          }
        }
      }
      if byte & 128 == 0 {
        consumed = index + 1;
        violation |= index != 0 && *byte == 0;
        break;
      }
    }
    violation |= consumed == 0;
  }
  violation |= control.lo != consumed as u64;
  violation |= bytes.iter().skip(consumed).any(|byte| *byte != 0);
  result.push(F128::new(u64::from(violation), 0));
  result
}

fn build_plan(capacity: NaturalCapacity) -> BooleanR1csPlan {
  let inputs = 1 + capacity.encoded_words();
  let outputs = capacity.magnitude_words() + 1;
  let mut b = Builder::new(
    inputs,
    outputs,
    (inputs + outputs) * 128 + 36 * capacity.encoded_bytes() + 512,
  );
  let enabled = 64;
  b.violations.extend(65..128);
  let bytes: Vec<_> = (128..128 + capacity.encoded_bytes() * 8).collect();
  let decoded = b.natural(&bytes, enabled, capacity.bits());
  let exact = b.equal(&(0..64).collect::<Vec<_>>(), &decoded.consumed);
  b.require(b.one, exact);
  for (byte, live) in bytes.as_chunks::<8>().0.iter().zip(decoded.live) {
    let unused = b.not(live);
    b.require_zero(unused, byte);
  }
  b.require_zero(b.one, &(128 + bytes.len()..128 * inputs).collect::<Vec<_>>());
  for word in 0..capacity.magnitude_words() {
    let start = (128 * word).min(decoded.value.len());
    let end = (128 * (word + 1)).min(decoded.value.len());
    b.write(inputs + word, &decoded.value[start..end]);
  }
  b.finish(inputs + outputs - 1)
}
