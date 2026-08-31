//! A fixed-selector 16-byte window over two adjacent transcript words.
//!
//! Stage 2 starts its challenger seed with the 14-byte `multi-stark/v0` tag,
//! so later commitment digests are not necessarily aligned to the Flock
//! circuit's 16-byte `F128` words. This Boolean table selects one of the 16
//! possible byte offsets and returns the exact next 16 bytes. The selector is
//! always a relation-fixed one-hot word at call sites.

use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};

use crate::boolean::{
  BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  write_f128,
};

const K_LOG: usize = 12;
const FIRST_BASE: usize = 0;
const SECOND_BASE: usize = 128;
const SELECTOR_BASE: usize = 256;
const OUTPUT_BASE: usize = 384;
const RESERVED_COLUMNS: usize = 512;

#[derive(Clone, Copy, Debug)]
pub(crate) struct ByteWindowGate {
  pub(crate) nu: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ByteWindowRow {
  first: F128,
  second: F128,
  selector: F128,
}

impl GateType for ByteWindowGate {
  type Row = ByteWindowRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_byte_window_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::input(2),
        IoWord::output(3),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let first = inputs[0];
    let second = inputs[1];
    let selector = inputs[2];
    assert_eq!(selector.hi, 0, "byte-window selector high lane must be zero");
    assert_eq!(
      selector.lo.count_ones(),
      1,
      "byte-window selector must be one-hot"
    );
    let offset = selector.lo.trailing_zeros() as usize;
    assert!(offset < 16, "byte-window offset exceeds one F128 word");
    outputs.push(byte_window(first, second, offset));
    ByteWindowRow { first, second, selector }
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_byte_window_r1cs(nu: usize) -> BlockR1cs {
  byte_window_plan().block_r1cs(nu)
}

pub(crate) fn generate_byte_window_witness_into(
  rows: &[ByteWindowRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  generate_boolean_witness_into(
    byte_window_plan(),
    rows,
    nu,
    dst,
    |row, bits| {
      write_f128(bits, FIRST_BASE, row.first);
      write_f128(bits, SECOND_BASE, row.second);
      write_f128(bits, SELECTOR_BASE, row.selector);
    },
  )
}

fn byte_window_plan() -> &'static BooleanR1csPlan {
  static PLAN: std::sync::OnceLock<BooleanR1csPlan> =
    std::sync::OnceLock::new();
  PLAN.get_or_init(|| {
    let mut builder = BooleanR1csBuilder::new(K_LOG, RESERVED_COLUMNS);
    for column in FIRST_BASE..SELECTOR_BASE + 128 {
      builder.free_boolean_at(column);
    }
    let one = builder.alloc_constant_one();
    for output_bit in 0..128 {
      let products: Vec<_> = (0..16)
        .map(|offset| {
          let source_bit = offset * 8 + output_bit;
          let source = if source_bit < 128 {
            FIRST_BASE + source_bit
          } else {
            SECOND_BASE + source_bit - 128
          };
          builder.and(SELECTOR_BASE + offset, source)
        })
        .collect();
      builder.write_xor(OUTPUT_BASE + output_bit, &products, one);
    }
    builder.finish()
  })
}

fn byte_window(first: F128, second: F128, offset: usize) -> F128 {
  let mut bytes = [0u8; 32];
  bytes[..8].copy_from_slice(&first.lo.to_le_bytes());
  bytes[8..16].copy_from_slice(&first.hi.to_le_bytes());
  bytes[16..24].copy_from_slice(&second.lo.to_le_bytes());
  bytes[24..].copy_from_slice(&second.hi.to_le_bytes());
  F128::new(
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap()),
    u64::from_le_bytes(bytes[offset + 8..offset + 16].try_into().unwrap()),
  )
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn every_byte_offset_matches_native_slice() {
    let first = F128::new(0x0706_0504_0302_0100, 0x0f0e_0d0c_0b0a_0908);
    let second = F128::new(0x1716_1514_1312_1110, 0x1f1e_1d1c_1b1a_1918);
    let plan = byte_window_plan();
    let r1cs = plan.block_r1cs(3);
    for offset in 0..16 {
      let selector = F128::new(1 << offset, 0);
      let mut logical = vec![false; plan.k()];
      plan.fill_row(&mut logical, |bits| {
        write_f128(bits, FIRST_BASE, first);
        write_f128(bits, SECOND_BASE, second);
        write_f128(bits, SELECTOR_BASE, selector);
      });
      let mut witness = vec![false; r1cs.n()];
      witness[..plan.k()].copy_from_slice(&logical);
      assert!(r1cs.satisfies(&witness));
      let expected = byte_window(first, second, offset);
      let mut output = vec![false; 128];
      write_f128(&mut output, 0, expected);
      assert_eq!(&logical[OUTPUT_BASE..OUTPUT_BASE + 128], output);
    }
  }
}
