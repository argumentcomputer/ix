use super::super::synthesis::*;
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
pub enum EndpointOp {
  Parser,
  Source,
  Bridge,
  Bytes,
  References,
  Clock,
}
#[derive(Clone, Debug)]
pub struct EndpointGate {
  pub op: EndpointOp,
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct EndpointRow(pub(super) Vec<F128>);
impl EndpointGate {
  pub fn new(nu: usize, op: EndpointOp) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "endpoint row domain");
    Ok(Self { op, nu, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| plan(self.op))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[EndpointRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, b| {
      fill_words(&r.0, b)
    })
  }
}
impl CountedGate for EndpointGate {
  fn input_count(&self) -> usize {
    4
  }
  fn output_count(&self) -> usize {
    1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for EndpointGate {
  type Row = EndpointRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..4).map(IoWord::input).chain([IoWord::output(4)]).collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), out: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), 4);
    out.extend(evaluate_words(self.plan(), input, 1));
    EndpointRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
fn plan(op: EndpointOp) -> BooleanR1csPlan {
  let mut builder = Builder::new(4, 1, 1 << 12);
  let b = &mut builder;
  if op != EndpointOp::Parser {
    b.require_zero(b.one, &[word(2), word(3)].concat());
  }
  match op {
    EndpointOp::Parser => {
      bound(b, b.one, &word(0), 1 << 24);
      b.require_zero(b.one, &word(1)[..64]);
      same(b, b.one, &word(1)[64..], &word(0)[..64]);
      same(b, b.one, &word(2)[..64], &word(0)[..64]);
      same(b, b.one, &word(2)[64..], &word(0)[..64]);
      same(b, b.one, &word(3)[..8], &b.constant(8, 20));
    },
    EndpointOp::Source | EndpointOp::Bridge | EndpointOp::Bytes => {
      let length =
        if op == EndpointOp::Bytes { word(0)[64..].to_vec() } else { word(0) };
      bound(b, b.one, &length, 1 << 24);
      let extra = match op {
        EndpointOp::Bridge => 48 + 1023,
        EndpointOp::Source => 1023,
        _ => 31,
      };
      let sum = plus(b, b.one, &length, &b.constant(length.len(), extra));
      let shift = if op == EndpointOp::Bytes { 5 } else { 10 };
      let mut count = sum[shift..].to_vec();
      count.resize(128, b.zero);
      if op != EndpointOp::Bridge {
        let empty = eqc(b, &length, 0);
        count = choose(b, empty, &b.constant(128, 1), &count);
      }
      same(b, b.one, &word(1), &count);
    },
    EndpointOp::References => {
      bound(b, b.one, &word(0), 1024);
      let expected = [b.constant(8, 3), word(0)[..120].to_vec()].concat();
      same(b, b.one, &word(1), &expected);
    },
    EndpointOp::Clock => {
      b.require_zero(b.one, &word(0)[59..]);
      b.require_zero(b.one, &word(1)[59..]);
      let progress = lt(b, &word(0), &word(1));
      b.require(b.one, progress);
    },
  }
  builder.finish(4)
}
