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
pub enum ConstructorIdKind {
  Source,
  Audit,
}
impl ConstructorIdKind {
  pub fn inputs(self) -> usize {
    match self {
      Self::Source => 6,
      Self::Audit => 11,
    }
  }
  pub fn outputs(self) -> usize {
    match self {
      Self::Source => 6,
      Self::Audit => 1,
    }
  }
}
#[derive(Clone, Debug)]
pub struct ConstructorIdGate {
  nu: usize,
  pub(super) kind: ConstructorIdKind,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct ConstructorIdRow(pub(super) Vec<F128>);
impl ConstructorIdGate {
  pub fn new(nu: usize, kind: ConstructorIdKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "constructor ID row domain");
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| relation::build(self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ConstructorIdRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
}
impl CountedGate for ConstructorIdGate {
  fn input_count(&self) -> usize {
    self.kind.inputs()
  }
  fn output_count(&self) -> usize {
    self.kind.outputs()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for ConstructorIdGate {
  type Row = ConstructorIdRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..self.kind.inputs())
        .map(IoWord::input)
        .chain(
          (self.kind.inputs()..self.kind.inputs() + self.kind.outputs())
            .map(IoWord::output),
        )
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.kind.inputs());
    output.extend(evaluate_words(self.plan(), input, self.kind.outputs()));
    ConstructorIdRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
