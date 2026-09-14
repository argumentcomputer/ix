//! Canonical functional ByteArray scalar header and checked immutable range.
//! Payload bytes are not copied into this gate. Its two lookahead words must
//! be authenticated at the supplied cursor in the same original artifact.
//! The eventual byte-memory argument must authenticate payload reads there.

use super::synthesis::Builder;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{add, fill_words, or, subtract},
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

/// Inputs: `(scalar offset, file length)` as two u64 lanes, the exact u128
/// declared byte-array limit, and 32 bytes of lookahead starting at the scalar
/// tag. Source bytes after file EOF must be zero; following fields are not
/// padding. The scalar tag must be 6, not a String or an outer value tag.
#[derive(Clone, Debug)]
pub struct ByteArraySpanGate {
  pub(super) nu: usize,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Copy, Debug)]
pub struct ByteArraySpanRow(pub(super) [F128; 4]);

impl ByteArraySpanGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional byte-span row domain");
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
    rows: &[ByteArraySpanRow],
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

impl CountedGate for ByteArraySpanGate {
  fn input_count(&self) -> usize {
    4
  }
  fn output_count(&self) -> usize {
    3
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for ByteArraySpanGate {
  type Row = ByteArraySpanRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..4).map(IoWord::input).chain((4..7).map(IoWord::output)).collect(),
    )
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let input: [F128; 4] =
      inputs.try_into().expect("fixed byte-span input width");
    outputs.extend(evaluate(&input));
    ByteArraySpanRow(input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct ByteArraySpanWires {
  /// `(payload start, payload length)` as two exact u64 lanes. The artifact
  /// identity is a separate required part of an authenticated arena record.
  pub range: Wire,
  /// `(next scalar cursor, unchanged file length)` as two u64 lanes.
  pub next: Wire,
}

#[derive(Clone, Copy, Debug)]
pub struct ByteArraySpanSlot {
  slot: SlotId,
  zero: Wire,
}

impl ByteArraySpanSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: ByteArraySpanGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn decode(
    &self,
    b: &mut impl CircuitEmitter,
    cursor: Wire,
    declared_limit: Wire,
    lookahead: [Wire; 2],
  ) -> ByteArraySpanWires {
    let output =
      b.gate(self.slot, &[cursor, declared_limit, lookahead[0], lookahead[1]]);
    b.connect(output[2], self.zero);
    ByteArraySpanWires { range: output[0], next: output[1] }
  }
}

pub(super) fn evaluate(input: &[F128; 4]) -> [F128; 3] {
  let offset = input[0].lo;
  let file_length = input[0].hi;
  let limit = u128::from(input[1].lo) | (u128::from(input[1].hi) << 64);
  let bytes: Vec<_> = input[2..]
    .iter()
    .flat_map(|word| {
      word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
    })
    .collect();
  let mut violation = offset > file_length || bytes[0] != 6;
  violation |= bytes.iter().enumerate().any(|(index, byte)| {
    index as u64 >= file_length.saturating_sub(offset) && *byte != 0
  });
  let mut length = 0u128;
  let mut consumed = 0u64;
  for (index, byte) in bytes[1..20].iter().enumerate() {
    let digit = u128::from(byte & 127);
    if index == 18 {
      violation |= digit > 3;
    }
    length |= (digit & if index == 18 { 3 } else { 127 }) << (7 * index);
    if byte & 128 == 0 {
      consumed = index as u64 + 1;
      violation |= index != 0 && *byte == 0;
      break;
    }
  }
  violation |= consumed == 0 || length > limit || length > u128::from(u64::MAX);
  let (start, carry) = offset.overflowing_add(1 + consumed);
  violation |= carry;
  let (end, carry) = start.overflowing_add(length as u64);
  violation |= carry || end > file_length;
  [
    F128::new(start, length as u64),
    F128::new(end, file_length),
    F128::new(u64::from(violation), 0),
  ]
}

fn build_plan() -> BooleanR1csPlan {
  let mut b = Builder::new(4, 3, 1 << 13);
  let offset: Vec<_> = (0..64).collect();
  let file_length: Vec<_> = (64..128).collect();
  let (remaining, borrow) =
    subtract(&mut b.b, b.one, b.zero, &file_length, &offset);
  b.violations.push(borrow);
  let large = b.any(&remaining[5..]);
  for index in 0..32 {
    let at = b.constant(5, index as u64);
    let (_, within) = subtract(&mut b.b, b.one, b.zero, &at, &remaining[..5]);
    let live = or(&mut b.b, b.one, within, large);
    let padding = b.not(live);
    b.require_zero(
      padding,
      &(256 + index * 8..264 + index * 8).collect::<Vec<_>>(),
    );
  }
  let tag = b.eq_const(&(256..264).collect::<Vec<_>>(), 6);
  b.require(b.one, tag);
  let decoded = b.natural(&(264..416).collect::<Vec<_>>(), b.one, 128);
  b.require_zero(b.one, &decoded.value[64..]);
  let limit: Vec<_> = (128..256).collect();
  let (_, over_limit) =
    subtract(&mut b.b, b.one, b.zero, &limit, &decoded.value);
  b.violations.push(over_limit);
  let one = b.constant(64, 1);
  let (header, carry) = add(&mut b.b, b.one, b.zero, &decoded.consumed, &one);
  b.violations.push(carry);
  let (start, carry) = add(&mut b.b, b.one, b.zero, &offset, &header);
  b.violations.push(carry);
  let (next, carry) =
    add(&mut b.b, b.one, b.zero, &start, &decoded.value[..64]);
  b.violations.push(carry);
  let (_, overflow) = subtract(&mut b.b, b.one, b.zero, &file_length, &next);
  b.violations.push(overflow);
  b.write(4, &[start, decoded.value[..64].to_vec()].concat());
  b.write(5, &[next, file_length].concat());
  b.finish(6)
}
