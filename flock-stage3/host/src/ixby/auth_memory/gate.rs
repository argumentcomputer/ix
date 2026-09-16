use super::MemoryDepth;
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::bits::{add, any, equal, equal_constant, fill_words, subtract},
  sizing::CountedGate,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryGateKind {
  Address,
  Path,
  /// Inputs: address, allocated cell count, kind (0 read / 1 allocate).
  /// Outputs: exact new allocated count and a validity residual.
  Index,
}
#[derive(Clone)]
pub struct MemoryGate {
  nu: usize,
  depth: MemoryDepth,
  kind: MemoryGateKind,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct MemoryRow(pub(super) Vec<F128>);
impl MemoryGate {
  pub fn new(
    nu: usize,
    depth: MemoryDepth,
    kind: MemoryGateKind,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "memory row domain");
    Ok(Self { nu, depth, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> MemoryGateKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.depth, self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[MemoryRow],
    dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| fill_words(&row.0, bits),
    )
  }
  pub(super) fn evaluate(&self, input: &[F128]) -> Vec<F128> {
    if self.kind == MemoryGateKind::Index {
      let [address, count, mode] = <[F128; 3]>::try_from(input).unwrap();
      let allocate = mode.lo & 1;
      let (next, carry) = count.lo.overflowing_add(allocate);
      let bound =
        self.depth.bits() == 64 || count.lo <= 1u64 << self.depth.bits();
      let invalid = address.hi != 0
        || count.hi != 0
        || mode.hi != 0
        || mode.lo > 1
        || !self.depth.admits(address.lo)
        || !bound
        || carry
        || if allocate == 1 {
          address.lo != count.lo
        } else {
          address.lo >= count.lo
        };
      return vec![F128::new(next, 0), F128::new(u64::from(invalid), 0)];
    }
    let mut invalid = input[0].hi != 0 || !self.depth.admits(input[0].lo);
    let mut result = Vec::new();
    if self.kind == MemoryGateKind::Path {
      let level = input[1].lo & 63;
      invalid |= input[1].hi != 0 || input[1].lo >= self.depth.bits() as u64;
      let right = input[0].lo >> level & 1 != 0;
      result.extend(if right {
        [input[4], input[5], input[2], input[3]]
      } else {
        [input[2], input[3], input[4], input[5]]
      });
    }
    result.push(F128::new(u64::from(invalid), 0));
    result
  }
}
impl CountedGate for MemoryGate {
  fn input_count(&self) -> usize {
    match self.kind {
      MemoryGateKind::Address => 1,
      MemoryGateKind::Path => 6,
      MemoryGateKind::Index => 3,
    }
  }
  fn output_count(&self) -> usize {
    match self.kind {
      MemoryGateKind::Address => 1,
      MemoryGateKind::Path => 5,
      MemoryGateKind::Index => 2,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for MemoryGate {
  type Row = MemoryRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..self.input_count())
        .map(IoWord::input)
        .chain(
          (self.input_count()..self.input_count() + self.output_count())
            .map(IoWord::output),
        )
        .collect(),
    )
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), self.input_count());
    outputs.extend(self.evaluate(inputs));
    MemoryRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn build_plan(depth: MemoryDepth, kind: MemoryGateKind) -> BooleanR1csPlan {
  if kind == MemoryGateKind::Index {
    return build_index(depth);
  }
  let (inputs, outputs) =
    if kind == MemoryGateKind::Address { (1, 1) } else { (6, 5) };
  let mut b = BooleanR1csBuilder::new(
    if inputs == 1 { 10 } else { 14 },
    128 * (inputs + outputs),
  );
  for bit in 0..128 * inputs {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut bad = (depth.bits()..128).collect::<Vec<_>>();
  if kind == MemoryGateKind::Path {
    bad.extend(134..256);
    let level = (128..134).collect::<Vec<_>>();
    let choices = (0..64)
      .map(|i| equal_constant(&mut b, one, &level, i as u64))
      .collect::<Vec<_>>();
    let mut directions = Vec::new();
    for (i, &choice) in choices.iter().enumerate() {
      directions.push(b.and(choice, i));
      if i >= depth.bits() {
        bad.push(choice);
      }
    }
    let direction = b.xor(&directions, one);
    for bit in 0..256 {
      let current = 256 + bit;
      let sibling = 512 + bit;
      let delta = b.product_of_parities(&[direction], &[current, sibling]);
      b.write_xor(6 * 128 + bit, &[current, delta], one);
      b.write_xor(8 * 128 + bit, &[sibling, delta], one);
    }
  }
  let invalid = any(&mut b, one, &bad);
  let residual = (inputs + outputs - 1) * 128;
  b.write_xor(residual, &[invalid], one);
  for bit in 1..128 {
    b.write_xor(residual + bit, &[zero], one);
  }
  b.finish()
}

fn build_index(depth: MemoryDepth) -> BooleanR1csPlan {
  let mut b = BooleanR1csBuilder::new(13, 5 * 128);
  for bit in 0..3 * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let address = (0..64).collect::<Vec<_>>();
  let count = (128..192).collect::<Vec<_>>();
  let allocate = 256;
  let mut increment = vec![zero; 64];
  increment[0] = allocate;
  let (next, carry) = add(&mut b, one, zero, &count, &increment);
  let mut bad =
    (depth.bits()..128).chain(192..256).chain(257..384).collect::<Vec<_>>();
  bad.push(carry);
  if depth.bits() < 64 {
    bad.extend(129 + depth.bits()..192);
    let low = any(&mut b, one, &count[..depth.bits()]);
    bad.push(b.and(count[depth.bits()], low));
  }
  let same = equal(&mut b, one, &address, &count);
  let different = b.xor(&[same, one], one);
  bad.push(b.and(allocate, different));
  let (_, borrow) = subtract(&mut b, one, zero, &count, &address);
  let read = b.xor(&[allocate, one], one);
  bad.push(b.and(read, borrow));
  bad.push(b.and(read, same));
  for bit in 0..128 {
    b.write_xor(384 + bit, &[next.get(bit).copied().unwrap_or(zero)], one);
  }
  let invalid = any(&mut b, one, &bad);
  b.write_xor(512, &[invalid], one);
  for bit in 1..128 {
    b.write_xor(512 + bit, &[zero], one);
  }
  b.finish()
}
