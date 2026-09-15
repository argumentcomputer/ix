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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyOp {
  Step,
  Capture,
  Finish,
  ReadFunction,
  ReadBlock,
  ReadOperand,
  ReadAlternative,
}
impl BodyOp {
  pub const ALL: [Self; 7] = [
    Self::Step,
    Self::Capture,
    Self::Finish,
    Self::ReadFunction,
    Self::ReadBlock,
    Self::ReadOperand,
    Self::ReadAlternative,
  ];
}
#[derive(Clone, Debug)]
pub struct BodyGate {
  nu: usize,
  pub(super) capacity: BodyCapacity,
  pub(super) op: BodyOp,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct BodyRow(pub(super) Vec<F128>);
impl BodyGate {
  pub fn new(nu: usize, capacity: BodyCapacity, op: BodyOp) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "body row domain");
    Ok(Self { nu, capacity, op, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> BodyCapacity {
    self.capacity
  }
  pub fn op(&self) -> BodyOp {
    self.op
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let cells = if self.op == BodyOp::Step {
        self.capacity.block_words()
      } else {
        self.capacity.finished_words()
      };
      // Conservative scratch budgets for each construction. The rows still
      // pin every padded column; this only selects their physical width.
      let scratch = match self.op {
        BodyOp::Step => 640 * cells + 80_000,
        BodyOp::Finish => 640 * cells + 262_144,
        _ => 512 * cells + 16_384,
      };
      let mut b = Builder::new(
        self.input_count(),
        self.output_count(),
        128 * (self.input_count() + self.output_count()) + scratch,
      );
      match self.op {
        BodyOp::Step => step::build(&mut b, self),
        BodyOp::Capture => bank::capture(&mut b, self),
        BodyOp::Finish => finish::build(&mut b, self),
        _ => read::build(&mut b, self),
      }
      b.finish(self.input_count() + self.output_count() - 1)
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[BodyRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, bits| {
      fill_words(&r.0, bits)
    })
  }
}
impl CountedGate for BodyGate {
  fn input_count(&self) -> usize {
    let c = self.capacity;
    match self.op {
      BodyOp::Step => c.state() + c.state_words(),
      BodyOp::Capture => 2 + c.block_words() + c.bank_words(),
      BodyOp::Finish => {
        28 + c.state_words() + c.registry.words() + c.bank_words()
      },
      _ => 4 + c.finished_words(),
    }
  }
  fn output_count(&self) -> usize {
    let c = self.capacity;
    match self.op {
      BodyOp::Step => c.state_words() + 2 + c.block_words() + 1,
      BodyOp::Capture => c.bank_words() + 1,
      BodyOp::Finish => c.finished_words() + 1,
      BodyOp::ReadFunction => FUNCTION_WORDS + 1,
      BodyOp::ReadBlock => HEADER_WORDS + 1,
      BodyOp::ReadOperand => c.operand_words() + 1,
      BodyOp::ReadAlternative => ALT_WORDS + 1,
    }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for BodyGate {
  type Row = BodyRow;
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
  fn eval(&self, input: &[F128], _: &(), out: &mut Vec<F128>) -> BodyRow {
    assert_eq!(input.len(), self.input_count());
    out.extend(evaluate::evaluate(self.capacity, self.op, input));
    BodyRow(input.to_vec())
  }
  fn witness(&self, _: &[BodyRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
