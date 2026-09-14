use super::super::synthesis::Builder;
use super::{
  SourceCapacity, choose_bits, file_bits, last_index, prefix, require_index,
};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  hash::{CHUNK_END, CHUNK_START, ROOT, pack_params},
  ixby::bits::{fill_words, or, subtract},
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

/// Seven inputs: narrow u64 file length, narrow u64 chunk index, narrow
/// block index 0..15, and four message words. Outputs: exact BLAKE3 parameters,
/// canonical active flag, residual. The source reader pins residual zero and
/// supplies setup-owned block positions, then selects the last active CV.
#[derive(Clone, Debug)]
pub struct SourceBlockGate {
  pub(super) nu: usize,
  pub(super) depth: usize,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct SourceBlockRow(pub(super) [F128; 7]);

impl SourceBlockGate {
  pub fn new(nu: usize, depth: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "source block row domain");
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
    rows: &[SourceBlockRow],
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

impl CountedGate for SourceBlockGate {
  fn input_count(&self) -> usize {
    7
  }
  fn output_count(&self) -> usize {
    3
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}

impl GateType for SourceBlockGate {
  type Row = SourceBlockRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..7).map(IoWord::input).chain((7..10).map(IoWord::output)).collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    let input = input.try_into().expect("source block input width");
    output.extend(evaluate(self.depth, &input));
    SourceBlockRow(input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(super) fn evaluate(depth: usize, input: &[F128; 7]) -> [F128; 3] {
  let length = input[0].lo;
  let index = input[1].lo;
  let block = input[2].lo & 15;
  let last = last_index(length);
  let chunk_len = if index == last {
    if length == 0 { 0 } else { (length - 1) % 1024 + 1 }
  } else {
    1024
  };
  let remaining = chunk_len.saturating_sub(block * 64);
  let block_len = remaining.min(64);
  let active = block == 0 || remaining > 0;
  let end = active && remaining <= 64;
  let flags = if block == 0 { CHUNK_START } else { 0 }
    | if end { CHUNK_END } else { 0 }
    | if end && last == 0 { ROOT } else { 0 };
  let mut bad = input[..3].iter().any(|w| w.hi != 0)
    || input[2].lo > 15
    || last >> depth != 0
    || index > last;
  let bytes = input[3..]
    .iter()
    .flat_map(|w| w.lo.to_le_bytes().into_iter().chain(w.hi.to_le_bytes()));
  bad |= bytes.enumerate().any(|(i, byte)| i as u64 >= block_len && byte != 0);
  [
    pack_params(index, block_len as u32, flags),
    F128::new(u64::from(active), 0),
    F128::new(u64::from(bad), 0),
  ]
}

fn build_plan(depth: usize) -> BooleanR1csPlan {
  let mut b = Builder::new(7, 3, 1 << 13);
  b.require_zero(b.one, &(64..128).collect::<Vec<_>>());
  b.require_zero(b.one, &(192..256).collect::<Vec<_>>());
  b.require_zero(b.one, &(260..384).collect::<Vec<_>>());
  let length: Vec<_> = (0..64).collect();
  let index: Vec<_> = (128..192).collect();
  let block: Vec<_> = (256..260).collect();
  let file = file_bits(&mut b, &length, depth);
  require_index(&mut b, &index, &file.last);
  let last = b.equal(&index, &file.last);
  let full = b.constant(11, 1024);
  let chunk_len = choose_bits(&mut b, last, &file.tail, &full);
  let mut offset = vec![b.zero; 6];
  offset.extend(&block);
  offset.push(b.zero);
  let (remaining, borrow) =
    subtract(&mut b.b, b.one, b.zero, &chunk_len, &offset);
  let within = b.not(borrow);
  let nonzero = b.any(&remaining);
  let positive = b.b.and(within, nonzero);
  let first = b.eq_const(&block, 0);
  let active = or(&mut b.b, b.one, first, positive);
  let large = b.any(&remaining[6..]);
  let small = b.not(large);
  let small = b.b.and(within, small);
  let mut size: Vec<_> =
    remaining[..6].iter().map(|&v| b.b.and(small, v)).collect();
  size.push(b.b.and(within, large));
  let sixty_four = b.constant(11, 64);
  let (_, above) = subtract(&mut b.b, b.one, b.zero, &sixty_four, &remaining);
  let short = b.not(above);
  let end = b.b.and(active, short);
  let root = b.b.and(end, file.single);
  let lives = prefix(&mut b, &size, 64);
  for (byte, live) in lives.into_iter().enumerate() {
    let pad = b.not(live);
    b.require_zero(pad, &(384 + byte * 8..392 + byte * 8).collect::<Vec<_>>());
  }
  let mut params = index;
  params.extend(size);
  params.resize(96, b.zero);
  params.extend([first, end, b.zero, root]);
  b.write(7, &params);
  b.write(8, &[active]);
  b.finish(9)
}
