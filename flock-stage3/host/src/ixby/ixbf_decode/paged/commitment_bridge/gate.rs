use super::*;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{evaluate_words, fill_words},
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
pub enum CommitmentBridgeOp {
  Control,
  Copy,
}
impl CommitmentBridgeOp {
  pub fn inputs(self) -> usize {
    match self {
      Self::Control => 2,
      Self::Copy => 132,
    }
  }
  pub fn outputs(self) -> usize {
    match self {
      Self::Control => 8,
      Self::Copy => 65,
    }
  }
}
#[derive(Clone, Debug)]
pub struct CommitmentBridgeGate {
  nu: usize,
  op: CommitmentBridgeOp,
  domain: ArtifactDomain,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct CommitmentBridgeRow(pub(super) Vec<F128>);
impl CommitmentBridgeGate {
  pub fn new(
    nu: usize,
    domain: ArtifactDomain,
    op: CommitmentBridgeOp,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "commitment bridge row domain");
    Ok(Self { nu, op, domain, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| relation::plan(self.domain, self.op))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[CommitmentBridgeRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
}
impl CountedGate for CommitmentBridgeGate {
  fn input_count(&self) -> usize {
    self.op.inputs()
  }
  fn output_count(&self) -> usize {
    self.op.outputs()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for CommitmentBridgeGate {
  type Row = CommitmentBridgeRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..self.op.inputs())
        .map(IoWord::input)
        .chain(
          (self.op.inputs()..self.op.inputs() + self.op.outputs())
            .map(IoWord::output),
        )
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.op.inputs());
    output.extend(evaluate_words(self.plan(), input, self.op.outputs()));
    CommitmentBridgeRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
