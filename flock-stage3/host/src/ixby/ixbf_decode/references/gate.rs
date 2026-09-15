use super::{super::synthesis::Builder, *};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::fill_words,
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
pub enum ReferenceOp {
  Request,
  Check,
}
impl ReferenceOp {
  pub const ALL: [Self; 2] = [Self::Request, Self::Check];
}

#[derive(Clone, Debug)]
pub struct ReferenceGate {
  nu: usize,
  pub(super) capacity: RegistryCapacity,
  pub(super) op: ReferenceOp,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct ReferenceRow(pub(super) Vec<F128>);

impl ReferenceGate {
  pub fn new(
    nu: usize,
    capacity: RegistryCapacity,
    op: ReferenceOp,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional reference row domain");
    Ok(Self { nu, capacity, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn op(&self) -> ReferenceOp {
    self.op
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| relation::build(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ReferenceRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| {
        fill_words(&row.0, bits);
      },
    )
  }
  pub(super) fn builder(&self) -> Builder {
    Builder::new(self.input_count(), self.output_count(), 1 << 16)
  }
}
impl CountedGate for ReferenceGate {
  fn input_count(&self) -> usize {
    match self.op {
      ReferenceOp::Request => REQUEST_INPUTS,
      ReferenceOp::Check => CHECK_INPUTS,
    }
  }
  fn output_count(&self) -> usize {
    match self.op {
      ReferenceOp::Request => STATE_WORDS + FACTS + 1,
      ReferenceOp::Check => 1,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for ReferenceGate {
  type Row = ReferenceRow;
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
    assert_eq!(input.len(), self.input_count(), "fixed reference input width");
    output.extend(evaluate::evaluate(self.capacity, self.op, input));
    ReferenceRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
