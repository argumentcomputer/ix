//! Derive the exact paged execution parameters and initial machine state from
//! admitted Program context and completed Input capture. The caller must wire
//! those actual child statement fields and carry the input's final memory root.
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
pub const INPUTS: usize = 20;
pub const OUTPUTS: usize = 28;
#[derive(Clone, Debug)]
pub struct InitializeGate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct InitializeRow(Vec<F128>);
impl InitializeGate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "paged initialization row domain");
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
    rows: &[InitializeRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, |r, b| {
      fill_words(&r.0, b)
    })
  }
}
impl CountedGate for InitializeGate {
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
impl GateType for InitializeGate {
  type Row = InitializeRow;
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
    InitializeRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
pub struct InitializeSlots {
  gate: (SlotId, InitializeGate),
  zero: Wire,
}
pub struct InitializedWires {
  pub parameters: [Wire; 3],
  pub state: [Wire; 24],
  pub clock: Wire,
}
impl InitializeSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let g = InitializeGate::new(nu)?;
    Ok(Self {
      gate: (b.slot(g.clone()), g),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn gate(&self) -> (SlotId, &InitializeGate) {
    (self.gate.0, &self.gate.1)
  }
  pub fn derive(
    &self,
    b: &mut impl CircuitEmitter,
    context: [Wire; 15],
    capture: [Wire; 5],
  ) -> InitializedWires {
    let out = b.gate(
      self.gate.0,
      &context.into_iter().chain(capture).collect::<Vec<_>>(),
    );
    b.connect(out[27], self.zero);
    InitializedWires {
      parameters: out[..3].try_into().unwrap(),
      state: out[3..27].try_into().unwrap(),
      clock: self.zero,
    }
  }
}
fn plan() -> BooleanR1csPlan {
  let mut builder = Builder::new(INPUTS, OUTPUTS, 1 << 15);
  let b = &mut builder;
  bound(b, b.one, &word(0), 256);
  bound(b, b.one, &word(1), 1024);
  let entry = lt(b, &word(12), &word(1));
  b.require(b.one, entry);
  bound(b, b.one, &word(13), 64);
  le(b, b.one, &word(13), &word(5));
  for i in [5, 7, 9, 11, 14] {
    b.require_zero(b.one, &word(i)[64..]);
  }
  le(b, b.one, &b.constant(128, 128), &word(9));
  for i in [15, 17, 18] {
    b.require_zero(b.one, &word(i));
  }
  bound(b, b.one, &word(16), 1 << 36);
  let decl = word(19);
  b.require_zero(b.one, &decl[32..]);
  bound(b, b.one, &decl[16..32], 256);
  let mut arity = decl[..8].to_vec();
  arity.resize(128, b.zero);
  same(b, b.one, &arity, &word(13));
  let mut block = decl[8..16].to_vec();
  block.resize(16, b.zero);
  let good = lt(b, &block, &decl[16..32]);
  b.require(b.one, good);
  let parameters = [
    [word(5)[..64].to_vec(), word(7)[..64].to_vec()].concat(),
    word(14),
    [word(9)[..64].to_vec(), word(11)[..64].to_vec()].concat(),
  ];
  for (i, v) in parameters.iter().enumerate() {
    b.write(INPUTS + i, v);
  }
  let mut frame = b.constant(128, 0);
  frame[8..24].copy_from_slice(&word(12)[..16]);
  frame[24..32].copy_from_slice(&decl[8..16]);
  frame[32..40].copy_from_slice(&decl[..8]);
  for i in 0..24 {
    let v = match i {
      0 => frame.clone(),
      5 => word(14),
      6 => word(16),
      _ => b.constant(128, 0),
    };
    b.write(INPUTS + 3 + i, &v);
  }
  builder.finish(INPUTS + OUTPUTS - 1)
}
#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixby::{
    bits::{fill_words, read_words},
    paged_exec,
    paged_frame::FrameState,
  };
  #[test]
  fn exact_initial_state_parameters_and_limits_are_constrained() {
    let g = InitializeGate::new(3).unwrap();
    let table = g.r1cs();
    let mut rows = Vec::new();
    for (entry, arity, block, heap, budget) in [
      (0, 0, 0, 0, 0),
      (1023, 64, 255, 1 << 36, u64::MAX),
      (681, 2, 93, 129, 3000000000),
    ] {
      let mut input = vec![F128::ZERO; INPUTS];
      for (i, v) in [
        (0, 256),
        (1, 1024),
        (5, 128),
        (7, 1024),
        (9, 4096),
        (11, 16777216),
        (12, entry),
        (13, arity),
        (14, budget),
        (16, heap),
      ] {
        input[i] = F128::new(v, 0);
      }
      input[19] = F128::new(arity | block << 8 | 256 << 16, 0);
      let mut out = Vec::new();
      let row = g.eval(&input, &(), &mut out);
      assert_eq!(out[27], F128::ZERO);
      assert_eq!(
        &out[..3],
        &[
          F128::new(128, 1024),
          F128::new(budget, 0),
          F128::new(4096, 16777216)
        ]
      );
      let mut state = paged_exec::initial_state(
        FrameState::eval(entry as u16, block as u8, arity as u8, 0).words(),
        budget,
      );
      state[paged_exec::HEAP_COUNT] = F128::new(heap, 0);
      assert_eq!(out[3..27], state);
      let mut bits = vec![false; table.n()];
      g.plan().fill_row(&mut bits[..g.plan().k()], |b| fill_words(&input, b));
      assert!(table.satisfies(&bits));
      assert_eq!(read_words(&bits, INPUTS, OUTPUTS), out);
      for at in INPUTS..INPUTS + OUTPUTS {
        for bit in [0, 63, 64, 127] {
          bits[at * 128 + bit] ^= true;
          assert!(!table.satisfies(&bits));
          bits[at * 128 + bit] ^= true;
        }
      }
      for at in [0, 1, 5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19] {
        let mut bad = input.clone();
        bad[at].hi |= 1 << 63;
        let mut out = Vec::new();
        g.eval(&bad, &(), &mut out);
        assert_eq!(out[27], F128::ONE, "alias at={at}");
      }
      let mut bad = input.clone();
      bad[9] = F128::new(127, 0);
      let mut out = Vec::new();
      g.eval(&bad, &(), &mut out);
      assert_eq!(out[27], F128::ONE);
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
