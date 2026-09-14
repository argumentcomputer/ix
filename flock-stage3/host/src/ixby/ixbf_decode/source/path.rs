use super::super::synthesis::Builder;
use super::{SourceCapacity, file_bits, last_index, require_index};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  hash::{PARENT, ROOT, pack_params},
  ixby::bits::{fill_words, subtract},
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

/// Inputs: narrow u64 file length, narrow u64 leaf index, fixed level,
/// current CV (two words), sibling CV (two words). Outputs: four ordered
/// parent message words, compression parameters, active flag, residual.
/// Missing right subtrees are promoted, never duplicated or zero-hashed.
/// Siblings for inactive levels must be zero. The final active parent gets
/// ROOT; its position is derived from file length, not from the witness.
#[derive(Clone, Debug)]
pub struct SourcePathGate {
  pub(super) nu: usize,
  pub(super) depth: usize,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct SourcePathRow(pub(super) [F128; 7]);

impl SourcePathGate {
  pub fn new(nu: usize, depth: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "source path row domain");
    SourceCapacity::new(depth, 0)?;
    Ok(Self { nu, depth, plan: Arc::new(OnceLock::new()) })
  }
  pub fn depth(&self) -> usize {
    self.depth
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.depth))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[SourcePathRow],
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
impl CountedGate for SourcePathGate {
  fn input_count(&self) -> usize {
    7
  }
  fn output_count(&self) -> usize {
    7
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for SourcePathGate {
  type Row = SourcePathRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..7).map(IoWord::input).chain((7..14).map(IoWord::output)).collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    let input = input.try_into().expect("source path input width");
    output.extend(evaluate(self.depth, &input));
    SourcePathRow(input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(super) fn evaluate(depth: usize, input: &[F128; 7]) -> [F128; 7] {
  let last = last_index(input[0].lo);
  let index = input[1].lo;
  let level = (input[2].lo & 63) as usize;
  let valid_level = level < depth;
  let width = 1u64 << level;
  let right = valid_level && index & width != 0;
  let sibling = (index ^ width) & !(width - 1);
  let active = valid_level && sibling <= last;
  let root = valid_level && last != 0 && last.ilog2() as usize == level;
  let bad = input[..3].iter().any(|w| w.hi != 0)
    || input[2].lo >= depth as u64
    || last >> depth != 0
    || index > last
    || (!active && input[5..].iter().any(|w| *w != F128::ZERO));
  let [a, b, c, d] = if right {
    [input[5], input[6], input[3], input[4]]
  } else {
    [input[3], input[4], input[5], input[6]]
  };
  [
    a,
    b,
    c,
    d,
    pack_params(0, 64, PARENT | if root { ROOT } else { 0 }),
    F128::new(u64::from(active), 0),
    F128::new(u64::from(bad), 0),
  ]
}

fn build_plan(depth: usize) -> BooleanR1csPlan {
  let mut b = Builder::new(7, 7, 8192 + 256 * depth);
  b.require_zero(b.one, &(64..128).collect::<Vec<_>>());
  b.require_zero(b.one, &(192..256).collect::<Vec<_>>());
  b.require_zero(b.one, &(262..384).collect::<Vec<_>>());
  let length: Vec<_> = (0..64).collect();
  let index: Vec<_> = (128..192).collect();
  let level: Vec<_> = (256..262).collect();
  let file = file_bits(&mut b, &length, depth);
  require_index(&mut b, &index, &file.last);
  let levels: Vec<_> =
    (0..depth).map(|i| b.eq_const(&level, i as u64)).collect();
  let valid_level = b.sum(&levels);
  b.require(b.one, valid_level);
  let directions: Vec<_> =
    levels.iter().zip(&index).map(|(&s, &bit)| b.b.and(s, bit)).collect();
  let right = b.sum(&directions);
  let mut sibling = Vec::with_capacity(64);
  for (bit, &index_bit) in index.iter().enumerate() {
    let mut choices = Vec::new();
    for (level, &flag) in levels.iter().enumerate().take(bit + 1) {
      let source = if bit == level { b.not(index_bit) } else { index_bit };
      choices.push(b.b.and(flag, source));
    }
    sibling.push(b.sum(&choices));
  }
  let (_, outside) = subtract(&mut b.b, b.one, b.zero, &file.last, &sibling);
  let present = b.not(outside);
  let active = b.b.and(valid_level, present);
  let inactive = b.not(active);
  b.require_zero(inactive, &(640..896).collect::<Vec<_>>());
  let mut no_higher = b.one;
  let mut roots = vec![b.zero; depth];
  for level in (0..depth).rev() {
    let highest = b.b.and(no_higher, file.last[level]);
    roots[level] = b.b.and(levels[level], highest);
    no_higher =
      b.b.product_of_parities(&[no_higher], &[file.last[level], b.one]);
  }
  // High last-index bits are rejected, but they still influence deterministic
  // output on invalid wide lengths just as the native evaluator does.
  let high = b.any(&file.last[depth..]);
  let no_high = b.not(high);
  let low_root = b.sum(&roots);
  let root = b.b.and(no_high, low_root);
  let mut left = Vec::with_capacity(256);
  let mut right_words = Vec::with_capacity(256);
  for bit in 0..256 {
    let current = 384 + bit;
    let sibling = 640 + bit;
    let delta = b.b.product_of_parities(&[right], &[current, sibling]);
    left.push(b.sum(&[current, delta]));
    right_words.push(b.sum(&[sibling, delta]));
  }
  for word in 0..2 {
    b.write(7 + word, &left[word * 128..word * 128 + 128]);
  }
  for word in 0..2 {
    b.write(9 + word, &right_words[word * 128..word * 128 + 128]);
  }
  let mut params = b.constant(128, 0);
  params[70] = b.one;
  params[98] = b.one;
  params[99] = root;
  b.write(11, &params);
  b.write(12, &[active]);
  b.finish(13)
}
