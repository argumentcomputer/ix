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

#[derive(Clone, Debug)]
pub struct FrameGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct FrameRow(pub(super) Vec<F128>);
impl FrameGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "paged frame row domain");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(super::synthesis::build)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[FrameRow],
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
}
impl CountedGate for FrameGate {
  fn input_count(&self) -> usize {
    13
  }
  fn output_count(&self) -> usize {
    19
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for FrameGate {
  type Row = FrameRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..13).map(IoWord::input).chain((13..32).map(IoWord::output)).collect(),
    )
  }
  fn eval(&self, inputs: &[F128], _: &(), outputs: &mut Vec<F128>) -> FrameRow {
    assert_eq!(inputs.len(), 13);
    outputs.extend(
      super::witness::evaluate(inputs)
        .unwrap_or_else(|| evaluate_words(self.plan(), inputs, 19)),
    );
    FrameRow(inputs.to_vec())
  }
  fn witness(&self, _: &[FrameRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
