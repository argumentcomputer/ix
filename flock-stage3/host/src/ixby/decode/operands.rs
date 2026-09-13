//! Constrained oldest-first local lookup and literal/erased resolution. The
//! instruction record is wired from ProgramFetchSlot; its argument count and
//! every full-width local selector are circuit-derived. Even unread locals
//! and inactive operand cells have their canonical representation checked.

use super::{evaluate, fill_words};
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, bounded_prefix, equal_constant, not, require, require_zero, select,
      subtract,
    },
    value::{
      cell_with_byte_handles, cell_with_nat_handles, cell_with_object_handles,
      scalar_cell,
    },
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
pub struct OperandResolveGate {
  nu: usize,
  locals: usize,
  operands: usize,
  byte_entries: Option<usize>,
  object_entries: Option<usize>,
  nat_values: bool,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct OperandResolveRow(Vec<F128>);

impl OperandResolveGate {
  pub fn new(nu: usize, locals: usize, operands: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "operand row-domain admission");
    ensure!((1..=16).contains(&locals), "operand local capacity");
    ensure!((1..=4).contains(&operands), "operand capacity");
    Ok(Self {
      nu,
      locals,
      operands,
      byte_entries: None,
      object_entries: None,
      nat_values: false,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn with_byte_handles(mut self, entries: usize) -> Result<Self> {
    crate::ixby::byte_value::validate_entries(entries)?;
    self.byte_entries = Some(entries);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub(crate) fn with_object_handles(mut self, entries: usize) -> Result<Self> {
    ensure!(
      self.byte_entries.is_some() && (1..=128).contains(&entries),
      "object operand arena capacity"
    );
    self.object_entries = Some(entries);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  fn frame_words(&self) -> usize {
    1 + 2 * self.locals
  }
  pub(crate) fn with_nat_handles(mut self) -> Result<Self> {
    ensure!(
      self.byte_entries.is_some(),
      "Nat operands require a magnitude arena"
    );
    self.nat_values = true;
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  fn block_words(&self) -> usize {
    2 + 3 * self.operands
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[OperandResolveRow],
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

impl CountedGate for OperandResolveGate {
  fn input_count(&self) -> usize {
    self.frame_words() + self.block_words()
  }
  fn output_count(&self) -> usize {
    2 * self.operands + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for OperandResolveGate {
  type Row = OperandResolveRow;
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
    outputs.extend(evaluate(self.plan(), inputs, self.output_count()));
    OperandResolveRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct OperandResolveSlot {
  slot: SlotId,
  zero: Wire,
  locals: usize,
  operands: usize,
}

impl OperandResolveSlot {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    gate: OperandResolveGate,
  ) -> Self {
    let (locals, operands) = (gate.locals, gate.operands);
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      locals,
      operands,
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn resolve(
    &self,
    b: &mut impl CircuitEmitter,
    frame: &[Wire],
    block: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(frame.len(), 1 + 2 * self.locals);
    assert_eq!(block.len(), 2 + 3 * self.operands);
    let mut input = frame.to_vec();
    input.extend_from_slice(block);
    let output = b.gate(self.slot, &input);
    b.connect(output[2 * self.operands], self.zero);
    output[..2 * self.operands].to_vec()
  }
}

fn build(gate: &OperandResolveGate) -> BooleanR1csPlan {
  let reserved = 128 * (gate.input_count() + gate.output_count());
  let columns = reserved
    + if gate.nat_values {
      2048 * (gate.locals + gate.operands + 4)
    } else {
      0
    }
    + 1024 * (gate.locals + gate.operands + 4)
    + 384 * gate.operands * (gate.locals + 2)
    + gate
      .object_entries
      .map_or(0, |_| 1024 * (gate.locals + gate.operands + 4));
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..128 * gate.input_count() {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut violations: Vec<_> = (96..128).collect();
  let locals: Vec<_> = (64..96).collect();
  let live = bounded_prefix(&mut b, one, &mut violations, &locals, gate.locals);
  for (index, flag) in live.iter().enumerate() {
    let base = 128 * (1 + 2 * index);
    let value: Vec<_> = (base..base + 256).collect();
    match (gate.byte_entries, gate.object_entries) {
      (Some(entries), objects) if gate.nat_values => {
        cell_with_nat_handles(
          &mut b,
          one,
          &mut violations,
          *flag,
          &value,
          entries,
          objects,
        );
      },
      (None, _) => {
        scalar_cell(&mut b, one, &mut violations, *flag, &value);
      },
      (Some(entries), None) => {
        cell_with_byte_handles(
          &mut b,
          one,
          &mut violations,
          *flag,
          &value,
          entries,
        );
      },
      (Some(bytes), Some(objects)) => {
        cell_with_object_handles(
          &mut b,
          one,
          &mut violations,
          *flag,
          &value,
          bytes,
          objects,
        );
      },
    }
  }
  let block = 128 * gate.frame_words();
  let count: Vec<_> = (block + 192..block + 224).collect();
  let used =
    bounded_prefix(&mut b, one, &mut violations, &count, gate.operands);
  for (index, enabled) in used.iter().enumerate() {
    let base = block + 128 * (2 + 3 * index);
    let header: Vec<_> = (base..base + 128).collect();
    let value: Vec<_> = (base + 128..base + 384).collect();
    let disabled = not(&mut b, one, *enabled);
    require_zero(&mut b, one, &mut violations, disabled, &header);
    require_zero(&mut b, one, &mut violations, one, &header[64..]);
    let local = equal_constant(&mut b, one, &header[..32], 1);
    let constant = equal_constant(&mut b, one, &header[..32], 2);
    let valid = b.xor(&[local, constant], one);
    require(&mut b, one, &mut violations, *enabled, valid);
    let local = b.and(*enabled, local);
    let constant = b.and(*enabled, constant);
    require_zero(&mut b, one, &mut violations, constant, &header[32..64]);
    match (gate.byte_entries, gate.object_entries) {
      (Some(entries), objects) if gate.nat_values => {
        cell_with_nat_handles(
          &mut b,
          one,
          &mut violations,
          constant,
          &value,
          entries,
          objects,
        );
      },
      (None, _) => {
        scalar_cell(&mut b, one, &mut violations, constant, &value);
      },
      (Some(entries), None) => {
        cell_with_byte_handles(
          &mut b,
          one,
          &mut violations,
          constant,
          &value,
          entries,
        );
      },
      (Some(bytes), Some(objects)) => {
        cell_with_object_handles(
          &mut b,
          one,
          &mut violations,
          constant,
          &value,
          bytes,
          objects,
        );
      },
    }
    let in_range = subtract(&mut b, one, zero, &header[32..64], &locals).1;
    require(&mut b, one, &mut violations, local, in_range);
    let mut sources: Vec<_> = (0..gate.locals)
      .map(|index| {
        let matched =
          equal_constant(&mut b, one, &header[32..64], index as u64);
        (b.and(local, matched), 128 * (1 + 2 * index))
      })
      .collect();
    sources.push((constant, base + 128));
    let resolved = select(&mut b, one, zero, &sources, 256);
    for (bit, source) in resolved.iter().enumerate() {
      b.write_xor(
        128 * (gate.input_count() + 2 * index) + bit,
        &[*source],
        one,
      );
    }
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(
    128 * (gate.input_count() + 2 * gate.operands),
    &[violation],
    one,
  );
  b.finish()
}

#[cfg(test)]
#[path = "operand_tests.rs"]
mod tests;
