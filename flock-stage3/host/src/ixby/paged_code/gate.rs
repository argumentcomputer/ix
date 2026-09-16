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
pub enum CodeGateKind {
  Block,
  Operand,
  Function,
  Alternative,
  Constructor,
}
#[derive(Clone, Debug)]
pub struct CodeGate {
  nu: usize,
  kind: CodeGateKind,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct CodeRow(pub(super) Vec<F128>);
impl CodeGate {
  pub fn new(nu: usize, kind: CodeGateKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "paged code row domain");
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> CodeGateKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| super::synthesis::build(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[CodeRow],
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
impl CountedGate for CodeGate {
  fn input_count(&self) -> usize {
    match self.kind {
      CodeGateKind::Operand => 8,
      CodeGateKind::Alternative => 6,
      _ => 4,
    }
  }
  fn output_count(&self) -> usize {
    if self.kind == CodeGateKind::Operand { 11 } else { 5 }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for CodeGate {
  type Row = CodeRow;
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
  fn eval(&self, inputs: &[F128], _: &(), outputs: &mut Vec<F128>) -> CodeRow {
    assert_eq!(inputs.len(), self.input_count());
    outputs.extend(evaluate_words(self.plan(), inputs, self.output_count()));
    CodeRow(inputs.to_vec())
  }
  fn witness(&self, _: &[CodeRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
