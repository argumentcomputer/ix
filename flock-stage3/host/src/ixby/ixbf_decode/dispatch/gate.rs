use super::*;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::fill_words,
    ixbf_decode::{GrammarKind, NaturalCapacity},
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
pub struct DispatchConfig {
  pub kind: GrammarKind,
  pub natural: NaturalCapacity,
}
impl DispatchConfig {
  pub fn window_words(self) -> usize {
    super::super::HEADER_PREFIX_WORDS.max(self.natural.encoded_words())
  }
  pub fn window_bytes(self) -> usize {
    self.window_words() * 16
  }
}

/// Setup-owned, distinct table schemas. No row can choose its own operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DispatchOp {
  Initialize,
  Request,
  Route,
  NaturalLookahead,
  Merge,
  Finish,
}
impl DispatchOp {
  pub const ALL: [Self; 6] = [
    Self::Initialize,
    Self::Request,
    Self::Route,
    Self::NaturalLookahead,
    Self::Merge,
    Self::Finish,
  ];
}

#[derive(Clone, Debug)]
pub struct DispatchGate {
  pub(super) nu: usize,
  pub(super) config: DispatchConfig,
  pub(super) op: DispatchOp,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct DispatchRow(pub(super) Vec<F128>);

impl DispatchGate {
  pub fn new(
    nu: usize,
    config: DispatchConfig,
    op: DispatchOp,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional dispatch row domain");
    Ok(Self { nu, config, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn config(&self) -> DispatchConfig {
    self.config
  }
  pub fn op(&self) -> DispatchOp {
    self.op
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| match self.op {
      DispatchOp::Initialize => control::initialize_plan(self),
      DispatchOp::Request => control::request_plan(self),
      DispatchOp::Finish => control::finish_plan(self),
      DispatchOp::Route => routing::route_plan(self),
      DispatchOp::NaturalLookahead => routing::natural_plan(self),
      DispatchOp::Merge => routing::merge_plan(self),
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[DispatchRow],
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
  pub(super) fn builder(&self, columns: usize) -> Builder {
    Builder::new(self.input_count(), self.output_count(), columns)
  }
}
impl CountedGate for DispatchGate {
  fn input_count(&self) -> usize {
    match self.op {
      DispatchOp::Initialize => 1 + DISPATCH_CONTEXT_WORDS,
      DispatchOp::Request => DISPATCH_STATE_WORDS,
      DispatchOp::Route => REQUEST_WORDS + self.config.window_words(),
      DispatchOp::NaturalLookahead => 1 + self.config.natural.encoded_words(),
      DispatchOp::Merge => 110,
      DispatchOp::Finish => 62,
    }
  }
  fn output_count(&self) -> usize {
    match self.op {
      DispatchOp::Initialize => DISPATCH_STATE_WORDS + 1,
      DispatchOp::Request => REQUEST_WORDS + 1,
      DispatchOp::Route => 157 + self.config.natural.encoded_words(),
      DispatchOp::NaturalLookahead => 2 + self.config.natural.encoded_words(),
      DispatchOp::Merge => 15,
      DispatchOp::Finish => DISPATCH_STATE_WORDS + 2,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for DispatchGate {
  type Row = DispatchRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let inputs = self.input_count();
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..inputs)
        .map(IoWord::input)
        .chain((inputs..inputs + self.output_count()).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count(), "fixed dispatch input width");
    output.extend(match self.op {
      DispatchOp::Initialize => control::initialize(self.config, input),
      DispatchOp::Request => control::request(self.config, input),
      DispatchOp::Finish => control::finish(input),
      DispatchOp::Route => routing::route(self.config, input),
      DispatchOp::NaturalLookahead => routing::natural(self.config, input),
      DispatchOp::Merge => routing::merge(input),
    });
    DispatchRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
