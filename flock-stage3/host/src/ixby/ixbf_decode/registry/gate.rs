use super::{super::synthesis::Builder, *};
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

/// These are setup-owned table operations, never prover-selected read types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistryOp {
  Capture,
  Finish,
  Constructor,
  Function,
  Block,
}
impl RegistryOp {
  pub const ALL: [Self; 5] = [
    Self::Capture,
    Self::Finish,
    Self::Constructor,
    Self::Function,
    Self::Block,
  ];
  pub(super) fn bank(self) -> usize {
    match self {
      Self::Capture => CAPTURE_BANK,
      Self::Finish => FINISH_BANK,
      _ => READ_BANK,
    }
  }
}

#[derive(Clone, Debug)]
pub struct RegistryGate {
  pub(super) nu: usize,
  pub(super) capacity: RegistryCapacity,
  pub(super) op: RegistryOp,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct RegistryRow(pub(super) Vec<F128>);
impl RegistryGate {
  pub fn new(
    nu: usize,
    capacity: RegistryCapacity,
    op: RegistryOp,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional registry row domain");
    Ok(Self { nu, capacity, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> RegistryCapacity {
    self.capacity
  }
  pub fn op(&self) -> RegistryOp {
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
    rows: &[RegistryRow],
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
  pub(super) fn builder(&self) -> Builder {
    // Explicit headroom for full-width selectors, all canonical cells, and
    // per-function block/entry checks. Counting never builds this plan.
    let columns = 128 * (self.input_count() + self.output_count())
      + 2048 * self.capacity.words()
      + 32768;
    Builder::new(self.input_count(), self.output_count(), columns)
  }
}
impl CountedGate for RegistryGate {
  fn input_count(&self) -> usize {
    self.op.bank() + self.capacity.words()
  }
  fn output_count(&self) -> usize {
    match self.op {
      RegistryOp::Capture => self.capacity.words() + 1,
      RegistryOp::Finish => 1,
      _ => 7, // five zero-padded fields, header range, validity residual
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for RegistryGate {
  type Row = RegistryRow;
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
    assert_eq!(input.len(), self.input_count(), "fixed registry input width");
    output.extend(evaluate::evaluate(self.capacity, self.op, input));
    RegistryRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
