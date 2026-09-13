//! Capacity-only instruction fetch from a decoder-derived program table.
//! The table inputs must be wired to ProgramDecodeSlot, not supplied as free
//! prover advice in an execution circuit. This gate checks dynamic function,
//! block, frame-size and callee accesses; it is not whole-image admission.

use super::{ProgramLayout, evaluate, fill_words};
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::bits::{any, equal, equal_constant, not, require, select, subtract},
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
pub struct ProgramFetchGate {
  nu: usize,
  layout: ProgramLayout,
  objects: bool,
  nats: bool,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct ProgramFetchRow(Vec<F128>);

impl ProgramFetchGate {
  pub fn new(nu: usize, layout: ProgramLayout) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "program fetch row-domain admission");
    layout.capacity().validate()?;
    Ok(Self {
      nu,
      layout,
      objects: false,
      nats: false,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn with_objects(mut self) -> Self {
    self.objects = true;
    self.plan = Arc::new(OnceLock::new());
    self
  }
  pub fn layout(&self) -> ProgramLayout {
    self.layout
  }
  pub(crate) fn with_nats(mut self) -> Self {
    self.nats = true;
    self.plan = Arc::new(OnceLock::new());
    self
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self.layout, self.objects, self.nats))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ProgramFetchRow],
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

impl CountedGate for ProgramFetchGate {
  fn input_count(&self) -> usize {
    2 + self.layout.words()
  }
  /// Selected block record, called function header (zero unless calling),
  /// then the constrained validity residual.
  fn output_count(&self) -> usize {
    self.layout.block_words() + 2
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for ProgramFetchGate {
  type Row = ProgramFetchRow;
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
    ProgramFetchRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct ProgramFetchSlot {
  slot: SlotId,
  zero: Wire,
  layout: ProgramLayout,
}

impl ProgramFetchSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: ProgramFetchGate) -> Self {
    let layout = gate.layout;
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO), layout }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn fetch(
    &self,
    b: &mut impl CircuitEmitter,
    state: Wire,
    frame: Wire,
    program: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(program.len(), self.layout.words());
    let mut input = vec![state, frame];
    input.extend_from_slice(program);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.layout.block_words() + 1], self.zero);
    output[..self.layout.block_words() + 1].to_vec()
  }
}

fn build(layout: ProgramLayout, objects: bool, nats: bool) -> BooleanR1csPlan {
  let c = layout.capacity();
  let input_words = 2 + layout.words();
  let output_words = layout.block_words() + 2;
  let reserved = 128 * (input_words + output_words);
  let columns = reserved
    + 128 * (c.functions * (c.blocks + 2) * (layout.block_words() + 2) + 10)
    + 4096;
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..input_words * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let kind: Vec<_> = (0..32).collect();
  let active = equal_constant(&mut b, one, &kind, 0);
  let returning = equal_constant(&mut b, one, &kind, 1);
  let halted = equal_constant(&mut b, one, &kind, 2);
  let valid_kind = b.xor(&[active, returning, halted], one);
  let mut violations: Vec<_> = (96..128).chain(224..256).collect();
  require(&mut b, one, &mut violations, one, valid_kind);
  let inactive = not(&mut b, one, active);
  let frame_nonzero = any(&mut b, one, &(128..256).collect::<Vec<_>>());
  violations.push(b.and(inactive, frame_nonzero));
  let function: Vec<_> = (128..160).collect();
  let block: Vec<_> = (160..192).collect();
  let locals: Vec<_> = (192..224).collect();
  let function_count: Vec<_> = (288..320).collect();
  let function_valid =
    subtract(&mut b, one, zero, &function, &function_count).1;
  require(&mut b, one, &mut violations, active, function_valid);
  let functions: Vec<_> = (0..c.functions)
    .map(|index| {
      let matched = equal_constant(&mut b, one, &function, index as u64);
      let selected = b.and(active, matched);
      (selected, (2 + layout.function_word(index)) * 128)
    })
    .collect();
  let function_header = select(&mut b, one, zero, &functions, 128);
  let block_valid =
    subtract(&mut b, one, zero, &block, &function_header[64..96]).1;
  require(&mut b, one, &mut violations, active, block_valid);
  let mut blocks = Vec::new();
  for (function, (flag, _)) in functions.iter().enumerate() {
    for index in 0..c.blocks {
      let matched = equal_constant(&mut b, one, &block, index as u64);
      let selected = b.and(*flag, matched);
      blocks.push((selected, (2 + layout.block_word(function, index)) * 128));
    }
  }
  let record = select(&mut b, one, zero, &blocks, 128 * layout.block_words());
  let locals_match = equal(&mut b, one, &locals, &record[..32]);
  require(&mut b, one, &mut violations, active, locals_match);
  let mut valid_opcodes: Vec<_> = (1..=if objects { 9 } else { 6 })
    .map(|opcode| equal_constant(&mut b, one, &record[32..64], opcode))
    .collect();
  if nats {
    valid_opcodes.push(equal_constant(&mut b, one, &record[32..64], 10));
  }
  let valid = b.xor(&valid_opcodes, one);
  require(&mut b, one, &mut violations, active, valid);
  let entering = b.xor(&[valid_opcodes[2], valid_opcodes[4]], one);
  let callee_valid =
    subtract(&mut b, one, zero, &record[128..160], &function_count).1;
  require(&mut b, one, &mut violations, entering, callee_valid);
  let callees: Vec<_> = (0..c.functions)
    .map(|index| {
      let matched =
        equal_constant(&mut b, one, &record[128..160], index as u64);
      let selected = b.and(entering, matched);
      (selected, (2 + layout.function_word(index)) * 128)
    })
    .collect();
  let callee_header = select(&mut b, one, zero, &callees, 128);
  for (bit, source) in record.iter().chain(&callee_header).enumerate() {
    b.write_xor(input_words * 128 + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(
    (input_words + layout.block_words() + 1) * 128,
    &[violation],
    one,
  );
  b.finish()
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixby::decode::{
    OperandResolveGate, OperandResolveSlot, PrimitiveSet, ProgramCapacities,
    ProgramDecodeGate, ProgramDecodeSlot,
    test_support::{
      FunctionImage, Instruction as I, Operand as O, advice, meta, program,
    },
  };
  use crate::ixby::{control::ControlCapacities, io::LayoutEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;

  #[test]
  fn decoded_program_wires_select_live_instructions_and_callees_in_fixed_shape()
  {
    let capacity =
      ProgramCapacities { bytes: 128, functions: 2, blocks: 2, operands: 1 };
    let control =
      ControlCapacities { locals: 2, continuations: 2, arguments: 1 };
    let decode_gate =
      ProgramDecodeGate::new(3, capacity, control, PrimitiveSet::scalar())
        .unwrap();
    let fetch_gate = ProgramFetchGate::new(3, capacity.layout()).unwrap();
    let mut builder = ShapeBuilder::new(3);
    let mut b = LayoutEmitter::new(&mut builder);
    let decoder = ProgramDecodeSlot::declare(&mut b, decode_gate);
    let fetcher = ProgramFetchSlot::declare(&mut b, fetch_gate.clone());
    let resolver = OperandResolveSlot::declare(
      &mut b,
      OperandResolveGate::new(3, control.locals, capacity.operands).unwrap(),
    );
    let length = b.input();
    let data: Vec<_> = (0..capacity.data_words()).map(|_| b.input()).collect();
    let table = decoder.decode(&mut b, length, &data);
    let state = b.input();
    let frame: Vec<_> = (0..control.frame_words()).map(|_| b.input()).collect();
    let fetched = fetcher.fetch(&mut b, state, frame[0], &table);
    for word in &fetched {
      b.publish(*word);
    }
    for word in resolver.resolve(
      &mut b,
      &frame,
      &fetched[..capacity.layout().block_words()],
    ) {
      b.publish(word);
    }
    let (inputs, public) = b.finish();
    let shape = builder.finish().unwrap();
    let functions = [
      FunctionImage {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::Call(Some(1), vec![O::Local(0)], 1)),
          (2, I::Ret(O::Local(1))),
        ],
      },
      FunctionImage {
        arity: 1,
        entry: 0,
        blocks: vec![(1, I::Tail(None, vec![O::Local(0)]))],
      },
    ];
    let bytes = program(0, &functions);
    let table =
      crate::ixby::decode::test_support::program_table(capacity, 0, &functions);
    let r1cs = fetch_gate.r1cs();
    for (state, frame, block, callee) in [
      (meta(0, 8, 0, 0), meta(0, 0, 1, 0), Some((0, 0)), Some(1)),
      (meta(0, 7, 1, 0), meta(1, 0, 1, 0), Some((1, 0)), Some(1)),
      (meta(0, 3, 0, 0), meta(0, 1, 2, 0), Some((0, 1)), None),
      (meta(1, 2, 1, 0), F128::ZERO, None, None),
      (meta(2, 0, 0, 0), F128::ZERO, None, None),
    ] {
      let mut private = advice(capacity.bytes, &bytes);
      private.extend([state, frame]);
      for index in 0..control.locals {
        private.extend(if index < frame.hi as u32 as usize {
          crate::ixby::value::word32_words(41 + index as u32)
        } else {
          [F128::ZERO; 2]
        });
      }
      let witness = shape.run(&inputs.assign(&private).unwrap(), &[]);
      let mut expected = vec![F128::ZERO; capacity.layout().block_words() + 1];
      if let Some((function, block)) = block {
        let start = capacity.layout().block_word(function, block);
        expected[..capacity.layout().block_words()].copy_from_slice(
          &table[start..start + capacity.layout().block_words()],
        );
      }
      if let Some(callee) = callee {
        *expected.last_mut().unwrap() =
          table[capacity.layout().function_word(callee)];
      }
      let mut all_expected = expected.clone();
      all_expected.extend(if let Some((_, block)) = block {
        crate::ixby::value::word32_words(if block == 1 { 42 } else { 41 })
      } else {
        [F128::ZERO; 2]
      });
      assert_eq!(witness.public, public.instantiate(&all_expected).unwrap());
      let row = &witness.rows::<ProgramFetchGate>(fetcher.slot())[0];
      let mut bits = vec![false; r1cs.n()];
      fetch_gate.plan().fill_row(&mut bits[..fetch_gate.plan().k()], |bits| {
        fill_words(&row.0, bits)
      });
      assert!(r1cs.satisfies(&bits));
      let mut outputs =
        evaluate(fetch_gate.plan(), &row.0, fetch_gate.output_count());
      assert_eq!(outputs.pop(), Some(F128::ZERO));
      assert_eq!(outputs, expected);
    }
  }

  #[test]
  fn malformed_dynamic_fetches_fail_constraints_after_recomputing_all_advice() {
    let capacity =
      ProgramCapacities { bytes: 128, functions: 2, blocks: 2, operands: 1 };
    let gate = ProgramFetchGate::new(3, capacity.layout()).unwrap();
    let functions = [FunctionImage {
      arity: 1,
      entry: 0,
      blocks: vec![(1, I::Ret(O::Local(0)))],
    }];
    let table =
      crate::ixby::decode::test_support::program_table(capacity, 0, &functions);
    let mut good = vec![meta(0, 8, 0, 0), meta(0, 0, 1, 0)];
    good.extend(table);
    let r1cs = gate.r1cs();
    let check = |input: &[F128], accepted: bool| {
      let mut bits = vec![false; r1cs.n()];
      gate
        .plan()
        .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(input, bits));
      let residual = 128 * (gate.input_count() + gate.layout.block_words() + 1);
      assert_eq!(bits[residual], !accepted);
      assert!(r1cs.satisfies(&bits));
      if !accepted {
        bits[residual] = false;
        assert!(!r1cs.satisfies(&bits));
      }
    };
    check(&good, true);
    for index in [1, 2, 1 << 16, 1 << 31, u32::MAX] {
      for frame in [meta(index, 0, 1, 0), meta(0, index, 1, 0)] {
        let mut bad = good.clone();
        bad[1] = frame;
        check(&bad, false);
      }
    }
    for locals in [0, 2, 1 << 31, u32::MAX] {
      let mut bad = good.clone();
      bad[1] = meta(0, 0, locals, 0);
      check(&bad, false);
    }
    for kind in [1, 2, 3, 1 << 31, u32::MAX] {
      let mut bad = good.clone();
      bad[0] = meta(kind, 8, 0, 0);
      check(&bad, false);
    }
    for word in [0, 1] {
      for bit in 96..128 {
        let mut bad = good.clone();
        bad[word].hi |= 1 << (bit - 64);
        check(&bad, false);
      }
    }
    let block = 2 + capacity.layout().block_word(0, 0);
    for kind in [0, 7, 1 << 31, u32::MAX] {
      let mut bad = good.clone();
      bad[block] = meta(1, kind, 0, 0);
      check(&bad, false);
    }
    for callee in [1, 2, 1 << 31, u32::MAX] {
      for kind in [3, 5] {
        let mut bad = good.clone();
        bad[block] = meta(1, kind, 0, 0);
        bad[block + 1] = meta(callee, 0, 1, 0);
        check(&bad, false);
      }
    }
    // This table is not admitted as a whole image: the fetch component can
    // only check accesses. The execution compiler must retain decoder wiring.
    let mut bits = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&good, bits));
    for word in 0..gate.output_count() {
      for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
        let index = 128 * (gate.input_count() + word) + bit;
        bits[index] ^= true;
        assert!(!r1cs.satisfies(&bits));
        bits[index] ^= true;
      }
    }
    bits[gate.plan().k() - 1] = true;
    assert!(!r1cs.satisfies(&bits));
    let row = ProgramFetchRow(good);
    for rows in [vec![], vec![row.clone()], vec![row; 3]] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
}
