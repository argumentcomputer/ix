use super::*;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::{add, fill_words, read_words},
    ixbf_decode::{
      source::{choose_bits, file_bits, require_index},
      synthesis::{Bits, Builder},
    },
  },
  sizing::CountedGate,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceBytesOp {
  Control,
  Copy,
}
#[derive(Clone, Debug)]
pub struct SourceBytesGate {
  bank: SourceBank,
  nu: usize,
  op: SourceBytesOp,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct SourceBytesRow(pub(super) Vec<F128>);
impl SourceBytesGate {
  pub fn new(bank: SourceBank, nu: usize, op: SourceBytesOp) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "source bytes row domain");
    Ok(Self { bank, nu, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn op(&self) -> SourceBytesOp {
    self.op
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| plan(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[SourceBytesRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
}
impl CountedGate for SourceBytesGate {
  fn input_count(&self) -> usize {
    match self.op {
      SourceBytesOp::Control => 2,
      SourceBytesOp::Copy => 130,
    }
  }
  fn output_count(&self) -> usize {
    match self.op {
      SourceBytesOp::Control => 5,
      SourceBytesOp::Copy => 193,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for SourceBytesGate {
  type Row = SourceBytesRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let n = self.input_count();
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..n)
        .map(IoWord::input)
        .chain((n..n + self.output_count()).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count());
    let mut row = vec![false; self.plan().k()];
    self.plan().fill_row(&mut row, |bits| fill_words(input, bits));
    output.extend(read_words(&row, input.len(), self.output_count()));
    SourceBytesRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
fn word(at: usize) -> Bits {
  (at * 128..(at + 1) * 128).collect()
}
fn plan(g: &SourceBytesGate) -> BooleanR1csPlan {
  let n = g.input_count();
  let mut b = Builder::new(
    n,
    g.output_count(),
    if g.op == SourceBytesOp::Control { 1 << 12 } else { 1 << 16 },
  );
  match g.op {
    SourceBytesOp::Control => {
      b.require_zero(b.one, &word(0)[64..]);
      b.require_zero(b.one, &word(1)[SOURCE_DEPTH..]);
      let file = file_bits(&mut b, &word(0)[..64], SOURCE_DEPTH);
      let first = word(1)[..64].to_vec();
      require_index(&mut b, &first, &file.last);
      let same = b.equal(&first, &file.last);
      let live = b.not(same);
      let one = b.constant(64, 1);
      let (successor, _) = add(&mut b.b, b.one, b.zero, &first, &one);
      let next = choose_bits(&mut b, live, &successor, &file.last);
      let (last_plus_one, _) = add(&mut b.b, b.one, b.zero, &file.last, &one);
      let two = b.constant(64, 2);
      let (two_after, _) = add(&mut b.b, b.one, b.zero, &first, &two);
      let end = choose_bits(&mut b, live, &two_after, &last_plus_one);
      b.write(n, &next);
      b.write(n + 1, &file.last);
      b.write(n + 2, &[live]);
      b.write(n + 3, &end);
    },
    SourceBytesOp::Copy => {
      b.require_zero(b.one, &word(0)[SOURCE_DEPTH..]);
      b.require_zero(b.one, &word(1)[1..]);
      let live = word(1)[0];
      let mut chunk = word(0)[..SOURCE_DEPTH].to_vec();
      chunk.push(b.zero);
      let one = b.constant(SOURCE_DEPTH + 1, 1);
      let (next, _) = add(&mut b.b, b.one, b.zero, &chunk, &one);
      for cell in 0..CELLS {
        let mut address = b.constant(5, (cell % 32) as u64);
        address.extend(if cell < 32 { &chunk } else { &next });
        address.resize(36, b.zero);
        address.extend(b.constant(28, g.bank.address() >> 36));
        b.write(n + 3 * cell, &address);
        for part in 0..2 {
          let value = word(2 + 2 * cell + part);
          let value = if cell < CELLS / 2 {
            value
          } else {
            value.iter().map(|&bit| b.b.and(live, bit)).collect()
          };
          b.write(n + 3 * cell + 1 + part, &value);
        }
      }
    },
  }
  b.finish(n + g.output_count() - 1)
}
