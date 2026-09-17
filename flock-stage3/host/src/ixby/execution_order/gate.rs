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

#[derive(Clone, Copy, Debug)]
pub enum OrderKind {
  /// [enabled, clock, before[N], after[N]] -> [before clock/kind, after clock/kind, residual]
  Prepare(usize),
  /// Same preparation, with a positive setup-selected clock increment.
  PrepareSpan(usize, u8),
  /// [previous[N+2], current[N+2], first, last] -> residual
  Audit(usize),
  /// [initial clock, final clock] -> residual; both are u64 and initial < final.
  Endpoints,
  /// [left[N+2], right[N+2]] -> one XOR residual per complete field word.
  Match(usize),
  /// [enabled, clock, ordinal, address, write, value[2]] -> [memory record[5], residual]
  Access,
}
#[derive(Clone)]
pub struct OrderGate {
  nu: usize,
  kind: OrderKind,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct OrderRow(pub(crate) Vec<F128>);
impl OrderGate {
  pub fn new(nu: usize, kind: OrderKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "execution order row domain");
    if let OrderKind::Prepare(n)
    | OrderKind::PrepareSpan(n, _)
    | OrderKind::Audit(n)
    | OrderKind::Match(n) = kind
    {
      ensure!((1..=30).contains(&n), "execution state words");
    }
    if let OrderKind::PrepareSpan(_, span) = kind {
      ensure!((2..=10).contains(&span), "execution clock span");
    }
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub(crate) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| super::synthesis::build(self.kind))
  }
  pub fn kind(&self) -> OrderKind {
    self.kind
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[OrderRow],
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
impl CountedGate for OrderGate {
  fn input_count(&self) -> usize {
    match self.kind {
      OrderKind::Prepare(n) | OrderKind::PrepareSpan(n, _) => 2 + 2 * n,
      OrderKind::Audit(n) => 2 * (n + 2) + 2,
      OrderKind::Endpoints => 2,
      OrderKind::Match(n) => 2 * (n + 2),
      OrderKind::Access => 7,
    }
  }
  fn output_count(&self) -> usize {
    match self.kind {
      OrderKind::Prepare(_) | OrderKind::PrepareSpan(_, _) => 5,
      OrderKind::Audit(_) | OrderKind::Endpoints => 1,
      OrderKind::Match(n) => n + 2,
      OrderKind::Access => 6,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for OrderGate {
  type Row = OrderRow;
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
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> OrderRow {
    assert_eq!(input.len(), self.input_count());
    output.extend(evaluate_words(self.plan(), input, self.output_count()));
    OrderRow(input.to_vec())
  }
  fn witness(&self, _: &[OrderRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
