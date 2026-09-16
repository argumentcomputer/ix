//! A constrained conditional on a fixed-width immutable record. The selector
//! is a canonical 0/1 F128 word, not an unchecked native branch or one-hot hint.

use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
    write_f128,
  },
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

#[derive(Clone, Debug)]
pub struct SelectWordsGate {
  nu: usize,
  width: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct SelectWordsRow(Vec<F128>);

impl SelectWordsGate {
  pub fn new(nu: usize, width: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "record selector row-domain admission");
    ensure!((1..=32).contains(&width), "record selector width admission");
    Ok(Self { nu, width, plan: Arc::new(OnceLock::new()) })
  }

  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let reserved = (3 * self.width + 2) * 128;
      let columns = reserved + 128 * self.width + 1;
      let mut b = BooleanR1csBuilder::new(
        columns.next_power_of_two().ilog2() as usize,
        reserved,
      );
      for bit in 0..(1 + 2 * self.width) * 128 {
        b.free_boolean_at(bit);
      }
      let one = b.alloc_constant_one();
      let result = (1 + 2 * self.width) * 128;
      for bit in 0..128 * self.width {
        let yes = 128 + bit;
        let no = 128 + 128 * self.width + bit;
        let delta = b.product_of_parities(&[0], &[yes, no]);
        b.write_xor(result + bit, &[no, delta], one);
      }
      let violation = (1 + 3 * self.width) * 128;
      for bit in 0..127 {
        b.write_xor(violation + bit, &[bit + 1], one);
      }
      b.finish()
    })
  }

  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }

  pub fn generate_witness_into(
    &self,
    rows: &[SelectWordsRow],
    dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| {
        for (word, value) in row.0.iter().enumerate() {
          write_f128(bits, word * 128, *value);
        }
      },
    )
  }
}

impl CountedGate for SelectWordsGate {
  fn input_count(&self) -> usize {
    1 + 2 * self.width
  }
  fn output_count(&self) -> usize {
    1 + self.width
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for SelectWordsGate {
  type Row = SelectWordsRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> =
      (0..self.input_count()).map(IoWord::input).collect();
    schema.extend(
      (self.input_count()..self.input_count() + self.output_count())
        .map(IoWord::output),
    );
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), self.input_count());
    let choice = inputs[0];
    let start = if choice.lo & 1 != 0 { 1 } else { 1 + self.width };
    outputs.extend_from_slice(&inputs[start..start + self.width]);
    outputs
      .push(F128::new((choice.lo >> 1) | (choice.hi << 63), choice.hi >> 1));
    SelectWordsRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct SelectWordsSlot {
  slot: SlotId,
  width: usize,
  zero: Wire,
}

impl SelectWordsSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: SelectWordsGate) -> Self {
    let width = gate.width;
    Self { slot: b.slot(gate), width, zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn select(
    &self,
    b: &mut impl CircuitEmitter,
    choice: Wire,
    yes: &[Wire],
    no: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(yes.len(), self.width);
    assert_eq!(no.len(), self.width);
    let mut inputs = vec![choice];
    inputs.extend_from_slice(yes);
    inputs.extend_from_slice(no);
    let output = b.gate(self.slot, &inputs);
    b.connect(output[self.width], self.zero);
    output[..self.width].to_vec()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn logical(gate: &SelectWordsGate, choice: F128) -> Vec<bool> {
    let mut input = vec![choice];
    input
      .extend((0..2 * gate.width).map(|i| F128::new(i as u64 * 17, !i as u64)));
    let mut output = Vec::new();
    gate.eval(&input, &(), &mut output);
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| {
      for (word, value) in input.iter().enumerate() {
        write_f128(bits, word * 128, *value);
      }
    });
    let start = gate.input_count() * 128;
    let mut expected = vec![false; gate.output_count() * 128];
    for (word, value) in output.iter().enumerate() {
      write_f128(&mut expected, word * 128, *value);
    }
    assert_eq!(&bits[start..start + expected.len()], expected);
    bits
  }

  fn satisfies(r1cs: &BlockR1cs, bits: &[bool]) -> bool {
    let mut full = vec![false; r1cs.n()];
    full[..bits.len()].copy_from_slice(bits);
    r1cs.satisfies(&full)
  }

  #[test]
  fn widths_and_both_choices_match_the_constrained_record() {
    for width in [1, 2, 9, 16, 32] {
      let gate = SelectWordsGate::new(3, width).unwrap();
      let r1cs = gate.r1cs();
      for choice in [F128::ZERO, F128::new(1, 0)] {
        let good = logical(&gate, choice);
        assert!(satisfies(&r1cs, &good));
        for word in 0..width {
          for bit in [0, 31, 64, 127] {
            let mut bad = good.clone();
            bad[(gate.input_count() + word) * 128 + bit] ^= true;
            assert!(!satisfies(&r1cs, &bad));
          }
        }
      }
    }
  }

  #[test]
  fn every_noncanonical_selector_bit_is_rejected_after_recomputing_advice() {
    let gate = SelectWordsGate::new(3, 9).unwrap();
    let r1cs = gate.r1cs();
    for low in [0, 1] {
      for bit in 1..128 {
        let choice = if bit < 64 {
          F128::new(low | (1 << bit), 0)
        } else {
          F128::new(low, 1 << (bit - 64))
        };
        let mut bits = logical(&gate, choice);
        assert!(satisfies(&r1cs, &bits));
        let error = (1 + 3 * gate.width) * 128;
        bits[error..error + 128].fill(false);
        assert!(!satisfies(&r1cs, &bits));
      }
    }
    assert!(SelectWordsGate::new(3, 0).is_err());
    assert!(SelectWordsGate::new(3, 33).is_err());
    assert!(SelectWordsGate::new(2, 9).is_err());
    assert!(SelectWordsGate::new(21, 9).is_err());
  }

  #[test]
  fn record_selection_driver_clears_recycled_padding_and_constant_stripes() {
    for width in [1, 9, 32] {
      let gate = SelectWordsGate::new(3, width).unwrap();
      let mut input = vec![F128::ZERO; gate.input_count()];
      input[0] = F128::new(1, 0);
      input[1] = F128::new(17, 29);
      let row = SelectWordsRow(input);
      for rows in [vec![], vec![row.clone()], vec![row; 3]] {
        crate::ixby::test_support::padding(
          gate.plan(),
          &rows,
          |row, bits| {
            for (word, value) in row.0.iter().enumerate() {
              write_f128(bits, word * 128, *value);
            }
          },
          |dst| gate.generate_witness_into(&rows, dst),
        );
      }
    }
  }
}
