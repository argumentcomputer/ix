use super::super::synthesis::Builder;
use super::{SourceCapacity, choose_bits, file_bits, last_index, prefix};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  hash::pack_bytes,
  ixby::bits::{add, fill_words, subtract},
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

/// Inputs: (offset, file_length), narrow u64 take, first chunk (64 words),
/// next chunk (64 words). Outputs: narrow file length, first/next/last chunk
/// indices, the exact zero-padded window, residual. The reader hashes these
/// SAME chunk wires at these SAME derived indices against its expected root.
/// `take` can mask a payload's following bytes; it cannot exceed capacity.
#[derive(Clone, Debug)]
pub struct SourceWindowGate {
  pub(super) nu: usize,
  capacity: SourceCapacity,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct SourceWindowRow(pub(super) Vec<F128>);

#[cfg(test)]
impl SourceWindowRow {
  /// Malicious-witness conformance below the honest runner's copy checks.
  pub(in crate::ixby::ixbf_decode) fn test_inputs_mut(
    &mut self,
  ) -> &mut [F128] {
    &mut self.0
  }
}

impl SourceWindowGate {
  pub fn new(nu: usize, capacity: SourceCapacity) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "source window row domain");
    Ok(Self { nu, capacity, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> SourceCapacity {
    self.capacity
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.capacity))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[SourceWindowRow],
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
impl CountedGate for SourceWindowGate {
  fn input_count(&self) -> usize {
    130
  }
  fn output_count(&self) -> usize {
    5 + self.capacity.window_words()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut g = self.clone();
    g.nu = nu;
    g.table()
  }
}
impl GateType for SourceWindowGate {
  type Row = SourceWindowRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..130)
        .map(IoWord::input)
        .chain((130..130 + self.output_count()).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), 130);
    output.extend(evaluate(self.capacity, input));
    SourceWindowRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(super) fn evaluate(capacity: SourceCapacity, input: &[F128]) -> Vec<F128> {
  let offset = input[0].lo;
  let length = input[0].hi;
  let take = input[1].lo;
  let last = last_index(length);
  let first = (offset >> 10).min(last);
  let next = (first + 1).min(last);
  let bad = offset > length
    || !capacity.admits_length(length)
    || input[1].hi != 0
    || take > capacity.window_bytes() as u64;
  let source: Vec<_> = input[2..]
    .iter()
    .flat_map(|w| w.lo.to_le_bytes().into_iter().chain(w.hi.to_le_bytes()))
    .collect();
  let mut window = vec![0; capacity.window_words() * 16];
  // Wrapping only defines deterministic output for rejected offset > length.
  let available = length.wrapping_sub(offset);
  for (i, byte) in window.iter_mut().enumerate().take(capacity.window_bytes()) {
    if (i as u64) < take && (i as u64) < available {
      *byte = source[(offset as usize & 1023) + i];
    }
  }
  let mut output =
    [length, first, next, last].map(|v| F128::new(v, 0)).to_vec();
  output.extend(window.as_chunks::<16>().0.iter().map(|w| pack_bytes(w)));
  output.push(F128::new(u64::from(bad), 0));
  output
}

fn build_plan(capacity: SourceCapacity) -> BooleanR1csPlan {
  let count = capacity.window_bytes();
  let outputs = 5 + capacity.window_words();
  let columns = 128 * (130 + outputs)
    + 16 * (10 * count + 1013)
    + 8 * count
    + 16 * count.max(1).next_power_of_two()
    + 4096;
  let mut b = Builder::new(130, outputs, columns);
  let offset: Vec<_> = (0..64).collect();
  let length: Vec<_> = (64..128).collect();
  let take: Vec<_> = (128..192).collect();
  b.require_zero(b.one, &(192..256).collect::<Vec<_>>());
  let max_take = b.constant(64, count as u64);
  let (_, too_much) = subtract(&mut b.b, b.one, b.zero, &max_take, &take);
  b.violations.push(too_much);
  let (available, past_end) =
    subtract(&mut b.b, b.one, b.zero, &length, &offset);
  b.violations.push(past_end);
  let file = file_bits(&mut b, &length, capacity.depth());
  let mut index = offset[10..].to_vec();
  index.resize(64, b.zero);
  let (_, clamp) = subtract(&mut b.b, b.one, b.zero, &file.last, &index);
  let first = choose_bits(&mut b, clamp, &file.last, &index);
  let one = b.constant(64, 1);
  let (successor, _) = add(&mut b.b, b.one, b.zero, &first, &one);
  let (_, clamp) = subtract(&mut b.b, b.one, b.zero, &file.last, &successor);
  let next = choose_bits(&mut b, clamp, &file.last, &successor);
  b.write(130, &length);
  b.write(131, &first);
  b.write(132, &next);
  b.write(133, &file.last);

  // A shrinking barrel selector: only retain the prefix needed by the
  // remaining offset bits. No witness-selected host slice participates.
  let mut bytes: Vec<_> = (256..130 * 128).collect();
  for bit in (0..10).rev() {
    let shift = 1 << bit;
    let needed = count + shift - 1;
    let mut selected = Vec::with_capacity(8 * needed);
    for i in 0..8 * needed {
      selected.push(super::choose(
        &mut b,
        offset[bit],
        bytes[i + 8 * shift],
        bytes[i],
      ));
    }
    bytes = selected;
  }
  let file_live = prefix(&mut b, &available, count);
  let take_live = prefix(&mut b, &take, count);
  for byte in 0..count {
    let live = b.b.and(file_live[byte], take_live[byte]);
    for bit in 0..8 {
      bytes[8 * byte + bit] = b.b.and(live, bytes[8 * byte + bit]);
    }
  }
  for word in 0..capacity.window_words() {
    b.write(134 + word, &bytes[128 * word..bytes.len().min(128 * (word + 1))]);
  }
  b.finish(134 + capacity.window_words())
}
