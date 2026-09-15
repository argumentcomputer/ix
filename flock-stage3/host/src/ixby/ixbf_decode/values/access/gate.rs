use super::{ValueKind, ValueLayout, relation};
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
pub enum ValueAccessOp {
  Request,
  Record,
}
#[derive(Clone, Debug)]
pub struct ValueAccessGate {
  nu: usize,
  pub(super) layout: ValueLayout,
  pub(super) kind: ValueKind,
  pub(super) op: ValueAccessOp,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct ValueAccessRow(pub(super) Vec<F128>);
impl ValueAccessGate {
  pub fn new(
    nu: usize,
    layout: ValueLayout,
    kind: ValueKind,
    op: ValueAccessOp,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "value access row domain");
    Ok(Self { nu, layout, kind, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn layout(&self) -> ValueLayout {
    self.layout
  }
  pub fn kind(&self) -> ValueKind {
    self.kind
  }
  pub fn op(&self) -> ValueAccessOp {
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
    rows: &[ValueAccessRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
}
impl CountedGate for ValueAccessGate {
  fn input_count(&self) -> usize {
    match self.op {
      ValueAccessOp::Request => 4,
      ValueAccessOp::Record => 4 + self.layout.window_words(),
    }
  }
  fn output_count(&self) -> usize {
    match self.op {
      ValueAccessOp::Request => 5,
      ValueAccessOp::Record => 2 + self.layout.record_words(self.kind),
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for ValueAccessGate {
  type Row = ValueAccessRow;
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
  fn eval(
    &self,
    input: &[F128],
    _: &(),
    out: &mut Vec<F128>,
  ) -> ValueAccessRow {
    assert_eq!(input.len(), self.input_count());
    out.extend(relation::evaluate(self, input));
    ValueAccessRow(input.to_vec())
  }
  fn witness(&self, _: &[ValueAccessRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
