//! Canonical u32 byte-length adjustment by a setup constant. The low word is
//! accompanied by a constrained residual for wide inputs or carry overflow;
//! callers must not use modular wrapping to bypass a byte-capacity check.

use super::bits::{add, any, constant_bits};
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
pub struct CheckedLengthAddGate {
  nu: usize,
  increment: u32,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Copy, Debug)]
pub struct CheckedLengthAddRow(F128);

impl CheckedLengthAddGate {
  pub fn new(nu: usize, increment: u32) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "length addition row-domain admission");
    Ok(Self { nu, increment, plan: Arc::new(OnceLock::new()) })
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let mut b = BooleanR1csBuilder::new(10, 384);
      for bit in 0..128 {
        b.free_boolean_at(bit);
      }
      let one = b.alloc_constant_one();
      let zero = b.xor(&[one, one], one);
      let increment = constant_bits(one, zero, self.increment);
      let (sum, carry) =
        add(&mut b, one, zero, &(0..32).collect::<Vec<_>>(), &increment);
      for (bit, source) in sum.iter().enumerate() {
        b.write_xor(128 + bit, &[*source], one);
      }
      let mut violations: Vec<_> = (32..128).collect();
      violations.push(carry);
      let violation = any(&mut b, one, &violations);
      b.write_xor(256, &[violation], one);
      b.finish()
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[CheckedLengthAddRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| write_f128(bits, 0, row.0),
    )
  }
}

impl CountedGate for CheckedLengthAddGate {
  fn input_count(&self) -> usize {
    1
  }
  fn output_count(&self) -> usize {
    2
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for CheckedLengthAddGate {
  type Row = CheckedLengthAddRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(vec![
      IoWord::input(0),
      IoWord::output(1),
      IoWord::output(2),
    ])
  }
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), 1);
    let input = inputs[0];
    let sum = u64::from(input.lo as u32) + u64::from(self.increment);
    outputs.push(F128::new(sum & u64::from(u32::MAX), 0));
    outputs.push(F128::new(
      u64::from(input.hi != 0 || input.lo >> 32 != 0 || sum >> 32 != 0),
      0,
    ));
    CheckedLengthAddRow(input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct CheckedLengthAddSlot {
  slot: SlotId,
  zero: Wire,
}

impl CheckedLengthAddSlot {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    gate: CheckedLengthAddGate,
  ) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn add(&self, b: &mut impl CircuitEmitter, length: Wire) -> Wire {
    let output = b.gate(self.slot, &[length]);
    b.connect(output[1], self.zero);
    output[0]
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn bits(gate: &CheckedLengthAddGate, input: F128) -> Vec<bool> {
    let mut output = Vec::new();
    gate.eval(&[input], &(), &mut output);
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| write_f128(bits, 0, input));
    let mut expected = vec![false; 256];
    for (word, value) in output.iter().enumerate() {
      write_f128(&mut expected, word * 128, *value);
    }
    assert_eq!(&bits[128..384], expected);
    bits
  }
  fn satisfies(r1cs: &BlockR1cs, bits: &[bool]) -> bool {
    let mut full = vec![false; r1cs.n()];
    full[..bits.len()].copy_from_slice(bits);
    r1cs.satisfies(&full)
  }

  #[test]
  fn addition_is_checked_not_wrapped_and_all_output_bits_are_bound() {
    for increment in [0, 1, 16, 48, 65536, 1 << 31, u32::MAX] {
      let gate = CheckedLengthAddGate::new(3, increment).unwrap();
      let r1cs = gate.r1cs();
      for input in
        [0, 1, 16, 48, 65536, 1 << 31, u32::MAX - increment, u32::MAX]
      {
        let good = bits(&gate, F128::new(u64::from(input), 0));
        assert!(satisfies(&r1cs, &good));
        assert_eq!(
          good[256],
          u64::from(input) + u64::from(increment) > u64::from(u32::MAX)
        );
        for bit in 128..384 {
          let mut bad = good.clone();
          bad[bit] ^= true;
          assert!(!satisfies(&r1cs, &bad));
        }
      }
    }
  }

  #[test]
  fn each_high_input_bit_cannot_bypass_canonical_length_admission() {
    let gate = CheckedLengthAddGate::new(3, 48).unwrap();
    let r1cs = gate.r1cs();
    for bit in 32..128 {
      let input = if bit < 64 {
        F128::new(1 << bit, 0)
      } else {
        F128::new(0, 1 << (bit - 64))
      };
      let mut bad = bits(&gate, input);
      assert!(satisfies(&r1cs, &bad));
      assert!(bad[256]);
      bad[256] = false;
      assert!(!satisfies(&r1cs, &bad));
    }
    assert!(CheckedLengthAddGate::new(2, 48).is_err());
    assert!(CheckedLengthAddGate::new(21, 48).is_err());
  }

  #[test]
  fn length_driver_clears_recycled_padding_and_constant_stripes() {
    let gate = CheckedLengthAddGate::new(3, 48).unwrap();
    for rows in [
      vec![],
      vec![CheckedLengthAddRow(F128::ZERO)],
      vec![CheckedLengthAddRow(F128::new(u64::from(u32::MAX), 0)); 3],
    ] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| write_f128(bits, 0, row.0),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
}
