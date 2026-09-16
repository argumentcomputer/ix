use super::STATE_WORDS;
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
pub enum MicroKind {
  Parameters,
  Fetch,
  ResolveRequest,
  ResolveFinish,
  Scratch(usize),
  NumericAction,
  ControlAction,
  CallReference,
  CallAction,
  Resume,
  FrameRequest,
  Complete,
}
impl MicroKind {
  pub const ALL: [Self; 13] = [
    Self::Parameters,
    Self::Fetch,
    Self::ResolveRequest,
    Self::ResolveFinish,
    Self::Scratch(1),
    Self::Scratch(3),
    Self::NumericAction,
    Self::ControlAction,
    Self::CallReference,
    Self::CallAction,
    Self::Resume,
    Self::FrameRequest,
    Self::Complete,
  ];
  pub fn inputs(self) -> usize {
    match self {
      Self::Parameters => 3,
      Self::Fetch
      | Self::ResolveFinish
      | Self::NumericAction
      | Self::ControlAction
      | Self::CallAction => 1 + STATE_WORDS + 2,
      Self::Scratch(n) => 1 + STATE_WORDS + 2 * n,
      Self::FrameRequest => 1 + STATE_WORDS + 1,
      Self::Complete => 1 + STATE_WORDS + 6,
      _ => 1 + STATE_WORDS,
    }
  }
  pub fn outputs(self) -> usize {
    match self {
      Self::Parameters | Self::Resume => 1,
      Self::Fetch | Self::Complete => STATE_WORDS + 1,
      Self::ResolveRequest => 3,
      Self::ResolveFinish => STATE_WORDS + 5,
      Self::Scratch(n) => 4 * n + 1,
      Self::NumericAction | Self::ControlAction | Self::CallAction => 6,
      Self::CallReference => 2,
      Self::FrameRequest => 7,
    }
  }
}
#[derive(Clone)]
pub struct MicroGate {
  nu: usize,
  kind: MicroKind,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct MicroRow(pub(super) Vec<F128>);
impl MicroGate {
  pub fn new(nu: usize, kind: MicroKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "paged execution row domain");
    if let MicroKind::Scratch(n) = kind {
      ensure!([1, 3].contains(&n), "scratch operand quota");
    }
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> MicroKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| super::synthesis::build(self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[MicroRow],
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
}
impl CountedGate for MicroGate {
  fn input_count(&self) -> usize {
    self.kind.inputs()
  }
  fn output_count(&self) -> usize {
    self.kind.outputs()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for MicroGate {
  type Row = MicroRow;
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
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> MicroRow {
    assert_eq!(input.len(), self.input_count());
    output.extend(evaluate_words(self.plan(), input, self.output_count()));
    MicroRow(input.to_vec())
  }
  fn witness(&self, _: &[MicroRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
