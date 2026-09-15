use super::*;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{bits::fill_words, ixbf_decode::source::SourceCapacity},
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
pub enum StreamOp {
  Cache,
  Read,
  Prepare,
}
impl StreamOp {
  pub const ALL: [Self; 3] = [Self::Cache, Self::Read, Self::Prepare];
}

#[derive(Clone, Debug)]
pub struct StreamGate {
  nu: usize,
  capacity: SourceCapacity,
  op: StreamOp,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct StreamRow(pub(super) Vec<F128>);

impl StreamGate {
  pub fn new(
    nu: usize,
    capacity: SourceCapacity,
    op: StreamOp,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "streaming parser row domain");
    Ok(Self { nu, capacity, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> SourceCapacity {
    self.capacity
  }
  pub fn op(&self) -> StreamOp {
    self.op
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| relation::plan(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[StreamRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
}
impl CountedGate for StreamGate {
  fn input_count(&self) -> usize {
    match self.op {
      StreamOp::Cache => 2,
      StreamOp::Read => 4,
      StreamOp::Prepare => 31,
    }
  }
  fn output_count(&self) -> usize {
    match self.op {
      StreamOp::Cache | StreamOp::Read => 3,
      StreamOp::Prepare => 33,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for StreamGate {
  type Row = StreamRow;
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
    output.extend(relation::evaluate(self, input));
    StreamRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
