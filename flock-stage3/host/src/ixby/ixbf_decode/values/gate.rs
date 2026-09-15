use super::super::synthesis::Builder;
use super::*;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::fill_words,
  sizing::CountedGate,
};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueOp {
  Link,
  Node,
  Capture,
  Finish,
  ReadNode,
  ReadChild,
  ReadRoot,
}
impl ValueOp {
  pub const ALL: [Self; 7] = [
    Self::Link,
    Self::Node,
    Self::Capture,
    Self::Finish,
    Self::ReadNode,
    Self::ReadChild,
    Self::ReadRoot,
  ];
}
#[derive(Clone, Debug)]
pub struct ValueGate {
  nu: usize,
  pub(super) config: ValueConfig,
  pub(super) op: ValueOp,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct ValueRow(pub(super) Vec<F128>);
impl ValueGate {
  pub fn new(nu: usize, config: ValueConfig, op: ValueOp) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "value arena row domain");
    config.validate()?;
    Ok(Self { nu, config, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn config(&self) -> ValueConfig {
    self.config
  }
  pub fn op(&self) -> ValueOp {
    self.op
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let mut b = self.builder();
      match self.op {
        ValueOp::Link => link::build(&mut b, self),
        ValueOp::Node => node::build(&mut b, self),
        ValueOp::Capture => bank::capture(&mut b, self),
        ValueOp::Finish => bank::finish(&mut b, self),
        _ => bank::read(&mut b, self),
      }
      b.finish(self.input_count() + self.output_count() - 1)
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ValueRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
  fn builder(&self) -> Builder {
    let cells = match self.op {
      ValueOp::Link => self.config.registry.words(),
      ValueOp::Node => self.config.arena.record_words(),
      _ => self.config.arena.finished_bank_words(),
    };
    Builder::new(
      self.input_count(),
      self.output_count(),
      128 * (self.input_count() + self.output_count()) + 1024 * cells + 65536,
    )
  }
}
impl CountedGate for ValueGate {
  fn input_count(&self) -> usize {
    let a = self.config.arena;
    match self.op {
      ValueOp::Link => LINK_BANK + self.config.registry.words(),
      ValueOp::Node => NAT + a.natural.magnitude_words() + ACC_WORDS,
      ValueOp::Capture => 2 + a.record_words() + a.bank_words(),
      ValueOp::Finish => 28 + ACC_WORDS + 1 + a.bank_words(),
      _ => 3 + a.finished_bank_words(),
    }
  }
  fn output_count(&self) -> usize {
    let a = self.config.arena;
    match self.op {
      ValueOp::Link => 2,
      ValueOp::Node => PACKET_RECORD + a.record_words() + 1,
      ValueOp::Capture => 1 + a.bank_words() + 1,
      ValueOp::Finish => 3 + a.finished_bank_words() + 1,
      _ => 1 + a.finished_record_words() + 1,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for ValueGate {
  type Row = ValueRow;
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
  fn eval(&self, input: &[F128], _: &(), out: &mut Vec<F128>) -> ValueRow {
    assert_eq!(input.len(), self.input_count(), "value table input width");
    out.extend(evaluate::evaluate(self.config, self.op, input));
    ValueRow(input.to_vec())
  }
  fn witness(&self, _: &[ValueRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
