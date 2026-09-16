//! Check the actual halted machine state and derive its Bytes result and exact
//! consumed fuel. The enclosing relation must use the execution endpoint wires.
use super::synthesis::*;
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{evaluate_words, fill_words},
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};
pub const INPUTS: usize = 29;
pub const OUTPUTS: usize = 4;
#[derive(Clone, Debug)]
pub struct FinalizeGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct FinalizeRow(Vec<F128>);
impl FinalizeGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "paged finalization row domain");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(plan)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[FinalizeRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, b| {
      fill_words(&r.0, b)
    })
  }
}
impl CountedGate for FinalizeGate {
  fn input_count(&self) -> usize {
    INPUTS
  }
  fn output_count(&self) -> usize {
    OUTPUTS
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for FinalizeGate {
  type Row = FinalizeRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..INPUTS)
        .map(IoWord::input)
        .chain((INPUTS..INPUTS + OUTPUTS).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), out: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), INPUTS);
    out.extend(evaluate_words(self.plan(), input, OUTPUTS));
    FinalizeRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
pub struct FinalizeSlots {
  gate: (SlotId, FinalizeGate),
  zero: Wire,
}
pub struct FinalizedWires {
  pub result: [Wire; 2],
  pub consumed: Wire,
}
impl FinalizeSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let g = FinalizeGate::new(nu)?;
    Ok(Self {
      gate: (b.slot(g.clone()), g),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn gate(&self) -> (SlotId, &FinalizeGate) {
    (self.gate.0, &self.gate.1)
  }
  pub fn derive(
    &self,
    b: &mut impl CircuitEmitter,
    parameters: [Wire; 3],
    state: [Wire; 24],
    source_lengths: [Wire; 2],
  ) -> FinalizedWires {
    let out = b.gate(
      self.gate.0,
      &parameters
        .into_iter()
        .chain(state)
        .chain(source_lengths)
        .collect::<Vec<_>>(),
    );
    b.connect(out[3], self.zero);
    FinalizedWires { result: [out[0], out[1]], consumed: out[2] }
  }
}
fn plan() -> BooleanR1csPlan {
  let mut builder = Builder::new(INPUTS, OUTPUTS, 1 << 15);
  let b = &mut builder;
  same(b, b.one, &word(3), &b.constant(128, 2));
  for i in [4, 7].into_iter().chain(11..27) {
    b.require_zero(b.one, &word(i));
  }
  b.require_zero(b.one, &word(1)[64..]);
  let total = plus(b, b.one, &word(8)[..64], &word(8)[64..]);
  same(b, b.one, &total, &word(1)[..64]);
  for i in [9, 10] {
    bound(b, b.one, &word(i), 1 << 36);
  }
  for i in [27, 28] {
    bound(b, b.one, &word(i), 1 << 24);
  }
  let value = [word(5), word(6)].concat();
  crate::ixby::paged_value::cell(
    &mut b.b,
    b.one,
    &mut b.violations,
    b.one,
    &value,
    false,
  );
  same(b, b.one, &word(5), &b.constant(128, 6));
  le(b, b.one, &word(6)[64..], &word(2)[64..]);
  let empty = eqc(b, &word(6)[64..], 0);
  let live = b.not(empty);
  let mut offset = word(6)[..41].to_vec();
  offset.resize(64, b.zero);
  let end = plus(b, b.one, &offset, &word(6)[64..]);
  for (bank, limit) in [
    (8, word(27)[..64].to_vec()),
    (9, word(28)[..64].to_vec()),
    (10, [vec![b.zero; 5], word(10)[..59].to_vec()].concat()),
  ] {
    let selected = eqc(b, &word(6)[41..45], bank);
    let on = b.b.and(live, selected);
    le(b, on, &end, &limit);
  }
  b.write(INPUTS, &word(5));
  b.write(INPUTS + 1, &word(6));
  b.write(INPUTS + 2, &word(8)[64..]);
  builder.finish(INPUTS + OUTPUTS - 1)
}
#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixby::bits::{fill_words, read_words};
  #[test]
  fn finalization_requires_halt_exact_fuel_and_the_actual_allocated_bytes() {
    let g = FinalizeGate::new(3).unwrap();
    let t = g.r1cs();
    let mut rows = Vec::new();
    for (bank, offset, length, budget, used) in [
      (8, 100, 34, 3000000000, 2268502805),
      (9, 0, 4096, 4096, 4096),
      (10, 31, 34, u64::MAX, 1),
      (0, 0, 0, 0, 0),
    ] {
      let mut input = vec![F128::ZERO; INPUTS];
      input[0] = F128::new(128, 1024);
      input[1] = F128::new(budget, 0);
      input[2] = F128::new(4096, 1 << 24);
      input[3] = F128::new(2, 0);
      input[5] = F128::new(6, 0);
      input[6] = F128::new((bank << 41) + offset, length);
      input[8] = F128::new(budget - used, used);
      input[9] = F128::new(17, 0);
      input[10] = F128::new(3, 0);
      input[27] = F128::new(8192, 0);
      input[28] = F128::new(4096, 0);
      let mut out = Vec::new();
      let row = g.eval(&input, &(), &mut out);
      assert_eq!(out, vec![input[5], input[6], F128::new(used, 0), F128::ZERO]);
      let mut bits = vec![false; t.n()];
      g.plan().fill_row(&mut bits[..g.plan().k()], |b| fill_words(&input, b));
      assert!(t.satisfies(&bits));
      assert_eq!(read_words(&bits, INPUTS, OUTPUTS), out);
      for at in INPUTS..INPUTS + OUTPUTS {
        for bit in [0, 63, 64, 127] {
          bits[128 * at + bit] ^= true;
          assert!(!t.satisfies(&bits));
          bits[128 * at + bit] ^= true;
        }
      }
      for at in [1, 3, 4, 5, 6, 7, 8, 9, 10, 27, 28].into_iter().chain(11..27) {
        let mut bad = input.clone();
        bad[at].hi ^= 1 << 63;
        let mut out = Vec::new();
        g.eval(&bad, &(), &mut out);
        assert_eq!(out[3], F128::ONE, "alias {at}");
      }
      for phase in [0, 1, 3, 4] {
        let mut bad = input.clone();
        bad[3] = F128::new(phase, 0);
        let mut out = Vec::new();
        g.eval(&bad, &(), &mut out);
        assert_eq!(out[3], F128::ONE);
      }
      if length > 0 {
        let mut bad = input.clone();
        bad[2].hi = length - 1;
        let mut out = Vec::new();
        g.eval(&bad, &(), &mut out);
        assert_eq!(out[3], F128::ONE);
        let mut bad = input.clone();
        bad[match bank {
          8 => 27,
          9 => 28,
          _ => 10,
        }] = F128::ZERO;
        let mut out = Vec::new();
        g.eval(&bad, &(), &mut out);
        assert_eq!(out[3], F128::ONE);
      }
      rows.push(row);
    }
    crate::ixby::test_support::padding(
      g.plan(),
      &rows,
      |r, b| fill_words(&r.0, b),
      |dst| g.generate_witness_into(&rows, dst),
    );
  }
}
