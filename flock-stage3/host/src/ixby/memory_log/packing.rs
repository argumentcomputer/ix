//! An injective bit layout for routing canonical records. Removed input bits
//! are constrained to zero; unpacking constrains all unused packed bits too.
//! This is a change of representation, with no hash or random compression.
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_packed_rows_into,
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

#[cfg(test)]
#[path = "packing_tests.rs"]
mod tests;

#[derive(Clone)]
pub struct RecordLayout {
  masks: Vec<u128>,
  bits: Vec<usize>,
}
impl RecordLayout {
  pub fn new(masks: Vec<u128>) -> Result<Self> {
    ensure!(!masks.is_empty() && masks.len() <= 32, "record layout width");
    let bits = masks
      .iter()
      .enumerate()
      .flat_map(|(word, &mask)| {
        (0..128)
          .filter(move |&bit| mask >> bit & 1 != 0)
          .map(move |bit| word * 128 + bit)
      })
      .collect::<Vec<_>>();
    ensure!(!bits.is_empty(), "empty record bit layout");
    Ok(Self { masks, bits })
  }
  pub fn low_bits(width: usize) -> u128 {
    assert!(width <= 128);
    u128::MAX.checked_shr((128 - width) as u32).unwrap_or(0)
  }
  pub fn words(&self) -> usize {
    self.masks.len()
  }
  pub fn packed_words(&self) -> usize {
    self.bits.len().div_ceil(128)
  }
}

#[derive(Clone)]
pub struct RecordPackingGate {
  nu: usize,
  layout: Arc<RecordLayout>,
  unpack: bool,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct RecordPackingRow(Vec<F128>);
impl RecordPackingGate {
  pub fn new(nu: usize, layout: RecordLayout, unpack: bool) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "record packing row domain");
    Ok(Self {
      nu,
      layout: Arc::new(layout),
      unpack,
      plan: Arc::new(OnceLock::new()),
    })
  }
  fn mapping(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
    self.layout.bits.iter().enumerate().map(|(packed, &full)| {
      if self.unpack { (packed, full) } else { (full, packed) }
    })
  }
  fn input_masks(&self) -> Vec<u128> {
    if self.unpack {
      (0..self.input_count())
        .map(|word| {
          RecordLayout::low_bits(
            self.layout.bits.len().saturating_sub(word * 128).min(128),
          )
        })
        .collect()
    } else {
      self.layout.masks.clone()
    }
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let reserved = (self.input_count() + self.output_count()) * 128;
      let mut b = BooleanR1csBuilder::new(
        (reserved + 1).next_power_of_two().ilog2() as usize,
        reserved,
      );
      let one = b.alloc_constant_one();
      for (word, mask) in self.input_masks().into_iter().enumerate() {
        for bit in 0..128 {
          let at = word * 128 + bit;
          if mask >> bit & 1 != 0 {
            b.free_boolean_at(at);
          } else {
            b.assert_zero_at(at, one);
          }
        }
      }
      let mut source = vec![None; self.output_count() * 128];
      for (input, output) in self.mapping() {
        source[output] = Some(input);
      }
      for (bit, source) in source.into_iter().enumerate() {
        let terms = source.map_or_else(|| vec![one, one], |bit| vec![bit]);
        b.write_xor(self.input_count() * 128 + bit, &terms, one);
      }
      b.finish()
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  fn output(&self, input: &[F128]) -> Vec<F128> {
    assert_eq!(input.len(), self.input_count());
    let mut output = vec![0u128; self.output_count()];
    for (from, to) in self.mapping() {
      let v = input[from / 128];
      let v = u128::from(v.lo) | u128::from(v.hi) << 64;
      output[to / 128] |= ((v >> (from % 128)) & 1) << (to % 128);
    }
    output.into_iter().map(|v| F128::new(v as u64, (v >> 64) as u64)).collect()
  }
  pub fn generate_witness_into(
    &self,
    rows: &[RecordPackingRow],
    dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    let input = self.input_count();
    let output = self.output_count();
    let masks = self.input_masks();
    generate_boolean_packed_rows_into(
      self.plan().k_log(),
      (input + output) * 128 + 1,
      rows,
      self.nu,
      dst,
      |row, z, a, b| {
        let all = F128::new(u64::MAX, u64::MAX);
        z[..input].copy_from_slice(&row.0);
        a[..input].copy_from_slice(&row.0);
        for (at, (&value, &mask)) in row.0.iter().zip(&masks).enumerate() {
          b[at] = value + F128::new(!mask as u64, (!mask >> 64) as u64);
        }
        let values = self.output(&row.0);
        z[input..input + output].copy_from_slice(&values);
        a[input..input + output].copy_from_slice(&values);
        b[input..input + output].fill(all);
        for words in [z, a, b] {
          words[input + output] = F128::ONE;
        }
      },
    )
  }
}
impl CountedGate for RecordPackingGate {
  fn input_count(&self) -> usize {
    if self.unpack { self.layout.packed_words() } else { self.layout.words() }
  }
  fn output_count(&self) -> usize {
    if self.unpack { self.layout.words() } else { self.layout.packed_words() }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for RecordPackingGate {
  type Row = RecordPackingRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..self.input_count())
        .map(IoWord::input)
        .chain(
          (self.input_count()..self.input_count() + self.output_count())
            .map(IoWord::output),
        )
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    output.extend(self.output(input));
    RecordPackingRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
