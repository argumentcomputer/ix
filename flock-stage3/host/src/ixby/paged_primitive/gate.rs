use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, equal_constant, evaluate_words, fill_words, not, require,
      require_zero,
    },
    ixbf::Primitive,
    paged_value,
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
pub struct PrimitiveRouteGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct PrimitiveRouteRow(pub(super) Vec<F128>);
impl PrimitiveRouteGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional primitive row domain");
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
    rows: &[PrimitiveRouteRow],
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
impl CountedGate for PrimitiveRouteGate {
  fn input_count(&self) -> usize {
    8
  }
  fn output_count(&self) -> usize {
    20
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for PrimitiveRouteGate {
  type Row = PrimitiveRouteRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..8).map(IoWord::input).chain((8..28).map(IoWord::output)).collect(),
    )
  }
  fn eval(
    &self,
    input: &[F128],
    _: &(),
    output: &mut Vec<F128>,
  ) -> PrimitiveRouteRow {
    assert_eq!(input.len(), 8);
    output.extend(evaluate_words(self.plan(), input, 20));
    PrimitiveRouteRow(input.to_vec())
  }
  fn witness(&self, _: &[PrimitiveRouteRow], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
pub(super) fn numeric(p: Primitive) -> bool {
  matches!(p.opcode(), 0..=6 | 10..=20 | 23..=28 | 31..=38)
}
fn range(start: usize, length: usize) -> Vec<usize> {
  (start..start + length).collect()
}
fn build() -> BooleanR1csPlan {
  let mut b = BooleanR1csBuilder::new(15, 28 * 128);
  for bit in 0..8 * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let enabled = 0;
  let disabled = not(&mut b, one, enabled);
  let mut bad = range(1, 127);
  require_zero(&mut b, one, &mut bad, disabled, &range(128, 896));
  let instruction = equal_constant(&mut b, one, &range(136, 8), 0);
  let operation = equal_constant(&mut b, one, &range(144, 8), 1);
  require(&mut b, one, &mut bad, enabled, instruction);
  require(&mut b, one, &mut bad, enabled, operation);
  let mut flags = Vec::new();
  for p in Primitive::ALL {
    let equal =
      equal_constant(&mut b, one, &range(152, 8), u64::from(p.opcode()));
    flags.push(b.and(enabled, equal));
  }
  let valid = b.xor(&flags, one);
  require(&mut b, one, &mut bad, enabled, valid);
  // No String primitive is admitted in this physical execution component yet.
  bad.extend_from_slice(&flags[7..10]);
  let nat = b.xor(&flags[..7], one);
  let scalar_flags = Primitive::ALL
    .iter()
    .filter(|p| numeric(**p) && p.opcode() >= 10)
    .map(|p| flags[p.opcode() as usize])
    .collect::<Vec<_>>();
  let scalar = b.xor(&scalar_flags, one);
  let byte_flags = Primitive::ALL
    .iter()
    .filter(|p| !numeric(**p) && p.opcode() >= 10)
    .map(|p| flags[p.opcode() as usize])
    .collect::<Vec<_>>();
  let bytes = b.xor(&byte_flags, one);
  let mut arity = vec![zero; 8];
  for (p, &flag) in Primitive::ALL.iter().zip(&flags) {
    for (bit, target) in arity.iter_mut().enumerate() {
      if p.arity() & (1 << bit) != 0 {
        *target = b.xor(&[*target, flag], one);
      }
    }
  }
  for count_start in [160, 168] {
    let same =
      crate::ixby::bits::equal(&mut b, one, &range(count_start, 8), &arity);
    require(&mut b, one, &mut bad, enabled, same);
  }
  for index in 0..3 {
    let used = b.xor(
      &Primitive::ALL
        .iter()
        .filter(|p| p.arity() > index)
        .map(|p| flags[p.opcode() as usize])
        .collect::<Vec<_>>(),
      one,
    );
    paged_value::cell(
      &mut b,
      one,
      &mut bad,
      used,
      &range(256 + 256 * index, 256),
      false,
    );
  }
  let mut out = vec![zero; 20 * 128];
  out[0] = nat;
  for (opcode, &flag) in flags[..7].iter().enumerate() {
    for bit in 0..3 {
      if (opcode + 1) & (1 << bit) != 0 {
        out[128 + bit] = b.xor(&[out[128 + bit], flag], one);
      }
    }
  }
  for bit in 0..512 {
    out[256 + bit] = b.and(nat, 256 + bit);
  }
  out[6 * 128 + 33] = scalar; // Existing scalar table's instruction kind = 2.
  for p in Primitive::ALL.iter().filter(|p| numeric(**p) && p.opcode() >= 10) {
    let flag = flags[p.opcode() as usize];
    let code = p.native_opcode().unwrap();
    for bit in 0..8 {
      if code & (1 << bit) != 0 {
        let at = 7 * 128 + 32 + bit;
        out[at] = b.xor(&[out[at], flag], one);
      }
    }
  }
  for (bit, &source) in arity.iter().enumerate() {
    out[7 * 128 + 64 + bit] = b.and(scalar, source);
  }
  for bit in 0..512 {
    out[8 * 128 + bit] = b.and(scalar, 256 + bit);
  }
  for p in Primitive::ALL.iter().filter(|p| !numeric(**p) && p.opcode() >= 10) {
    let flag = flags[p.opcode() as usize];
    let code = p.opcode() + 1;
    for bit in 0..8 {
      if code & (1 << bit) != 0 {
        let at = 12 * 128 + bit;
        out[at] = b.xor(&[out[at], flag], one);
      }
    }
  }
  for bit in 0..768 {
    out[13 * 128 + bit] = b.and(bytes, 256 + bit);
  }
  out[19 * 128] = any(&mut b, one, &bad);
  for (bit, source) in out.into_iter().enumerate() {
    b.write_xor(8 * 128 + bit, &[source], one);
  }
  b.finish()
}
