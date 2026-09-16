use super::{super::MemoryDepth, CLAIM_WORDS};
use crate::{
  boolean::{
    BooleanR1csBuilder as Builder, BooleanR1csPlan,
    generate_boolean_witness_into,
  },
  ixby::bits::{
    any, equal_constant, evaluate_words, fill_words, not, require,
    require_zero, subtract,
  },
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
#[repr(usize)]
pub enum MultiKind {
  Leaf,
  Frontier,
  Parent,
  Equal,
}
impl MultiKind {
  pub const ALL: [Self; 4] =
    [Self::Leaf, Self::Frontier, Self::Parent, Self::Equal];
  fn inputs(self) -> usize {
    match self {
      Self::Leaf => 5,
      Self::Frontier => 4,
      Self::Parent => 14,
      Self::Equal => 2 * CLAIM_WORDS,
    }
  }
  fn outputs(self) -> usize {
    match self {
      Self::Leaf | Self::Frontier => CLAIM_WORDS + 1,
      Self::Parent => 3 * CLAIM_WORDS + 1,
      Self::Equal => 1,
    }
  }
}
#[derive(Clone)]
pub struct MultiGate {
  nu: usize,
  depth: MemoryDepth,
  kind: MultiKind,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct MultiRow(pub Vec<F128>);
impl MultiGate {
  pub fn new(nu: usize, depth: MemoryDepth, kind: MultiKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "memory multiproof row domain");
    Ok(Self { nu, depth, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> MultiKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self.depth, self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[MultiRow],
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
impl CountedGate for MultiGate {
  fn input_count(&self) -> usize {
    self.kind.inputs()
  }
  fn output_count(&self) -> usize {
    self.kind.outputs()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for MultiGate {
  type Row = MultiRow;
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
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> MultiRow {
    assert_eq!(input.len(), self.input_count());
    output.extend(evaluate_words(self.plan(), input, self.output_count()));
    MultiRow(input.to_vec())
  }
  fn witness(&self, _: &[MultiRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
fn word(i: usize) -> Vec<usize> {
  (128 * i..128 * (i + 1)).collect()
}
fn emit_claim(
  b: &mut Builder,
  [one, zero]: [usize; 2],
  at: usize,
  enabled: usize,
  position: &[usize],
  old: &[Vec<usize>; 2],
  new: &[Vec<usize>; 2],
) {
  let mut flag = vec![zero; 128];
  flag[0] = enabled;
  for (i, bits) in [
    flag,
    position.to_vec(),
    old[0].clone(),
    old[1].clone(),
    new[0].clone(),
    new[1].clone(),
  ]
  .iter()
  .enumerate()
  {
    for (bit, &value) in bits.iter().enumerate() {
      let value = b.and(enabled, value);
      b.write_xor((at + i) * 128 + bit, &[value], one);
    }
  }
}
fn build(depth: MemoryDepth, kind: MultiKind) -> BooleanR1csPlan {
  let ni = kind.inputs();
  let no = kind.outputs();
  let k = match kind {
    MultiKind::Leaf | MultiKind::Equal => 12,
    MultiKind::Frontier => 13,
    MultiKind::Parent => 14,
  };
  let mut b = Builder::new(k, (ni + no) * 128);
  for bit in 0..ni * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut bad = Vec::new();
  if kind == MultiKind::Equal {
    for bit in 0..CLAIM_WORDS * 128 {
      bad.push(b.xor(&[bit, bit + CLAIM_WORDS * 128], one));
    }
  } else if kind == MultiKind::Leaf {
    bad.extend(depth.bits()..128);
    let mut position = vec![zero; 64];
    position.extend(0..64);
    emit_claim(
      &mut b,
      [one, zero],
      ni,
      one,
      &position,
      &[word(1), word(2)],
      &[word(3), word(4)],
    );
  } else {
    let enabled = 0;
    bad.extend(1..128);
    let disabled = not(&mut b, one, enabled);
    // Parent digest inputs are actual compression outputs, also on inactive
    // rows. Only the caller-supplied child data must be zero when inactive.
    let end = if kind == MultiKind::Parent { 10 } else { ni };
    for i in 1..end {
      require_zero(&mut b, one, &mut bad, disabled, &word(i));
    }
    let position = word(1);
    require_zero(&mut b, one, &mut bad, enabled, &position[7..64]);
    let levels = (0..=depth.bits())
      .map(|level| equal_constant(&mut b, one, &position[..7], level as u64))
      .collect::<Vec<_>>();
    let valid = b.xor(&levels, one);
    require(&mut b, one, &mut bad, enabled, valid);
    for bit in 0..64 {
      let high = if bit >= depth.bits() {
        one
      } else {
        any(&mut b, one, &levels[depth.bits() - bit..])
      };
      let active = b.and(enabled, high);
      require_zero(&mut b, one, &mut bad, active, &[position[64 + bit]]);
    }
    if kind == MultiKind::Frontier {
      emit_claim(
        &mut b,
        [one, zero],
        ni,
        enabled,
        &position,
        &[word(2), word(3)],
        &[word(2), word(3)],
      );
    } else {
      bad.push(b.and(enabled, levels[0]));
      emit_claim(
        &mut b,
        [one, zero],
        ni,
        enabled,
        &position,
        &[word(10), word(11)],
        &[word(12), word(13)],
      );
      let decrement = [vec![one], vec![zero; 6]].concat();
      let level = subtract(&mut b, one, zero, &position[..7], &decrement).0;
      let mut child = level;
      child.resize(64, zero);
      child.push(zero);
      child.extend(&position[64..127]);
      emit_claim(
        &mut b,
        [one, zero],
        ni + CLAIM_WORDS,
        enabled,
        &child,
        &[word(2), word(3)],
        &[word(6), word(7)],
      );
      child[64] = one;
      emit_claim(
        &mut b,
        [one, zero],
        ni + 2 * CLAIM_WORDS,
        enabled,
        &child,
        &[word(4), word(5)],
        &[word(8), word(9)],
      );
    }
  }
  let invalid = any(&mut b, one, &bad);
  let residual = (ni + no - 1) * 128;
  b.write_xor(residual, &[invalid], one);
  for bit in 1..128 {
    b.write_xor(residual + bit, &[zero], one);
  }
  b.finish()
}
