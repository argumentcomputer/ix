use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, equal, evaluate_words, fill_words, not, require, require_zero,
      select,
    },
    value::scalar_cell,
  },
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
pub struct PrimitiveFinishGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct PrimitiveFinishRow(pub(super) Vec<F128>);

impl PrimitiveFinishGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "primitive-result row-domain admission");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(build)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[PrimitiveFinishRow],
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
impl CountedGate for PrimitiveFinishGate {
  fn input_count(&self) -> usize {
    7
  }
  fn output_count(&self) -> usize {
    3
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for PrimitiveFinishGate {
  type Row = PrimitiveFinishRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> = (0..7).map(IoWord::input).collect();
    schema.extend((7..10).map(IoWord::output));
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(&self, input: &[F128], _: &(), outputs: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), 7);
    outputs.extend(evaluate_words(self.plan(), input, 3));
    PrimitiveFinishRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn build() -> BooleanR1csPlan {
  let mut b = BooleanR1csBuilder::new(12, 128 * 10);
  for bit in 0..128 * 7 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut violations: Vec<_> = (259..384).collect();
  for (a, c) in [(256, 257), (256, 258), (257, 258)] {
    violations.push(b.and(a, c));
  }
  let arithmetic = b.xor(&[256, 257, 258], one);
  let direct = not(&mut b, one, arithmetic);
  require_zero(
    &mut b,
    one,
    &mut violations,
    arithmetic,
    &(128..256).collect::<Vec<_>>(),
  );
  let product_correct = equal(
    &mut b,
    one,
    &(512..640).collect::<Vec<_>>(),
    &(768..896).collect::<Vec<_>>(),
  );
  require(&mut b, one, &mut violations, 258, product_correct);
  let payload = select(
    &mut b,
    one,
    zero,
    &[(direct, 128), (256, 384), (257, 512), (258, 640)],
    128,
  );
  let mut value: Vec<_> = (0..128).collect();
  value.extend_from_slice(&payload);
  let enabled = any(&mut b, one, &value[..128]);
  scalar_cell(&mut b, one, &mut violations, enabled, &value);
  for (bit, source) in value.iter().enumerate() {
    b.write_xor(896 + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(1152, &[violation], one);
  b.finish()
}
