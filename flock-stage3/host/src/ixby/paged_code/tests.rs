use super::*;
use crate::{
  ixby::{
    bits::{fill_words, read_words},
    paged_frame::{FrameState, HEAP, LOCALS},
    paged_value::{INPUT_BYTES, PROGRAM_BYTES},
  },
  sizing::CountedGate,
};
use flock_prover::{circuit::builder::GateType, field::F128};

fn checked(gate: &CodeGate, input: &[F128]) -> Vec<F128> {
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  let output = read_words(&bits, gate.input_count(), gate.output_count());
  let table = gate.r1cs();
  bits.resize(table.n(), false);
  assert!(table.satisfies(&bits));
  let mut native = Vec::new();
  gate.eval(input, &(), &mut native);
  assert_eq!(native, output);
  output
}
fn accept(gate: &CodeGate, input: &[F128]) -> Vec<F128> {
  let out = checked(gate, input);
  assert_eq!(out.last(), Some(&F128::ZERO));
  out
}
fn reject(gate: &CodeGate, input: &[F128]) {
  assert_eq!(checked(gate, input).last(), Some(&F128::ONE));
}
fn frame() -> F128 {
  FrameState::eval(680, 184, 73, 647).words()[0]
}

#[test]
fn block_fetch_derives_address_and_checks_the_complete_instruction_header() {
  let gate = CodeGate::new(3, CodeGateKind::Block).unwrap();
  let h = Header {
    locals: 73,
    operation: 1,
    primitive: 4,
    operands: 2,
    arguments: 2,
    target: 183,
    ..Header::default()
  };
  let mut input = vec![F128::ONE, frame()];
  input.extend(h.words());
  let out = accept(&gate, &input);
  assert_eq!(
    &out[..4],
    &[
      F128::new(block_address(680, 184), 0),
      F128::ZERO,
      h.words()[0],
      F128::ZERO
    ]
  );
  for primitive in crate::ixby::ixbf::Primitive::ALL {
    let mut header = h;
    header.primitive = primitive.opcode();
    header.arguments = primitive.arity() as u8;
    header.operands = primitive.arity() as u8;
    let mut input = vec![F128::ONE, frame()];
    input.extend(header.words());
    accept(&gate, &input);
    if primitive.is_conversion() {
      for count in [0, 2, 3] {
        header.arguments = count;
        header.operands = count;
        let mut wrong = vec![F128::ONE, frame()];
        wrong.extend(header.words());
        reject(&gate, &wrong);
      }
    }
  }
  for primitive in [58, 127, 255] {
    let mut header = h;
    header.primitive = primitive;
    let mut wrong = vec![F128::ONE, frame()];
    wrong.extend(header.words());
    reject(&gate, &wrong);
  }
  for (at, low, high) in [
    (0, 2, 0),
    (0, 0, 1),
    (1, 1 << 18, 0),
    (1, 0, 1),
    (2, 1, 0),
    (2, 1 << 56, 0),
    (2, 1 << 32, 0),
    (2, 1 << 40, 0),
    (2, 1 << 48, 0),
    (2, 0, 1),
    (2, 0, 1 << 24),
    (2, 0, 1 << 32),
    (2, 0, 1 << 48),
    (3, 1, 0),
    (3, 0, 1),
  ] {
    let mut changed = input.clone();
    changed[at] += F128::new(low, high);
    reject(&gate, &changed);
  }
  for instruction in 0..8 {
    for operation in 0..if instruction == 0 { 8 } else { 1 } {
      let has_args = instruction == 2
        || instruction == 3
        || instruction == 4
        || (instruction == 0 && matches!(operation, 1 | 2 | 4 | 5 | 6 | 7));
      let has_main = matches!(instruction, 1 | 4 | 5 | 6 | 7)
        || (instruction == 0 && matches!(operation, 0 | 3 | 7));
      let arguments = if has_args { 2 } else { 0 };
      let h = Header {
        locals: 73,
        instruction,
        operation,
        arguments,
        operands: arguments + u8::from(has_main),
        ..Header::default()
      };
      let mut input = vec![F128::ONE, frame()];
      input.extend(h.words());
      accept(&gate, &input);
    }
  }
  accept(
    &gate,
    &[F128::ZERO, F128::new(u64::MAX, u64::MAX), F128::ZERO, F128::ZERO],
  );
}

#[test]
fn operand_reads_bind_code_position_local_prefix_and_full_128_bit_values() {
  let gate = CodeGate::new(3, CodeGateKind::Operand).unwrap();
  let value = [F128::new(8, 0), F128::new(0, 1)];
  let input = [
    F128::ONE,
    frame(),
    F128::ONE,
    F128::new(2, 0),
    F128::ZERO,
    F128::new(72, 0),
    value[0],
    value[1],
  ];
  let out = accept(&gate, &input);
  assert_eq!(
    &out[..4],
    &[
      F128::new(block_address(680, 184) + 2, 0),
      F128::ZERO,
      F128::ZERO,
      F128::new(72, 0)
    ]
  );
  assert_eq!(
    &out[4..8],
    &[F128::new(LOCALS + (647 << 7) + 72, 0), F128::ZERO, value[0], value[1]]
  );
  assert_eq!(&out[8..10], &value);
  for at in [0, 1, 2, 3, 4, 5] {
    let mut changed = input;
    changed[at].hi ^= 1 << 63;
    reject(&gate, &changed);
  }
  for (at, value) in [
    (2, F128::new(2, 0)),
    (3, F128::new(66, 0)),
    (5, F128::new(73, 0)),
    (5, F128::new(128, 0)),
  ] {
    let mut changed = input;
    changed[at] = value;
    reject(&gate, &changed);
  }
  for value in [
    [F128::new(1, 0), F128::ZERO],
    [F128::new(2, 0), F128::new(u32::MAX as u64, 0)],
    [F128::new(3, 0), F128::new(0xffffffff00000000, 0)],
    [F128::new(4, 0), F128::new(0xffffffff00000000, 0xffffffff00000000)],
    [F128::new(5, 0), F128::ZERO],
    [F128::new(8, 0), F128::new(u64::MAX, u64::MAX)],
    [F128::new(6, 0), F128::new((PROGRAM_BYTES << 5) + 65535, 4813182)],
    [F128::new(10, 0), F128::new((INPUT_BYTES << 5) + 123, 123)],
  ] {
    let input = [
      F128::ONE,
      frame(),
      F128::ZERO,
      F128::ONE,
      value[0],
      value[1],
      F128::ZERO,
      F128::ZERO,
    ];
    let out = accept(&gate, &input);
    assert_eq!(&out[8..10], &value);
    assert_eq!(&out[4..8], &[F128::ZERO; 4]);
  }
  for value in [
    [F128::new(1, 0), F128::new(2, 0)],
    [F128::new(2, 0), F128::new(1 << 32, 0)],
    [F128::new(3, 0), F128::new(0xffffffff00000001, 0)],
    [F128::new(4, 0), F128::new(0, 0xffffffff00000001)],
    [F128::new(5, 0), F128::ONE],
    [F128::new(8, 1), F128::ZERO],
    [F128::new(6, 0), F128::new(HEAP << 5, 1)],
    [F128::new(6, 0), F128::new(PROGRAM_BYTES << 5, 0)],
    [F128::new(6, 0), F128::new((PROGRAM_BYTES << 5) + (1 << 41) - 1, 2)],
    [F128::new(7, 145), F128::new(HEAP + 123, 9)],
    [F128::new(9, 680), F128::new(HEAP + 456, 3)],
  ] {
    let input = [
      F128::ONE,
      frame(),
      F128::ZERO,
      F128::ONE,
      value[0],
      value[1],
      F128::ZERO,
      F128::ZERO,
    ];
    reject(&gate, &input);
  }
  for (tag, id, count) in [(7, 145, 9), (9, 680, 3)] {
    let mut input = input;
    input[6] = F128::new(tag, id);
    input[7] = F128::new(HEAP + 123, count);
    accept(&gate, &input);
    input[7].hi = 65;
    reject(&gate, &input);
  }
}

#[test]
fn declaration_and_alternative_fetches_check_full_indices_and_ranges() {
  let gate = CodeGate::new(3, CodeGateKind::Function).unwrap();
  let meta = F128::new(55 | (184 << 8) | (185 << 16), 0);
  let input = [F128::ONE, F128::new(680, 0), meta, F128::ZERO];
  let out = accept(&gate, &input);
  assert_eq!(out[0], F128::new(FUNCTIONS + 680, 0));
  for meta in [
    F128::ZERO,
    F128::new(65 | (1 << 16), 0),
    F128::new(185 << 8 | 185 << 16, 0),
    F128::new(257 << 16, 0),
  ] {
    let mut changed = input;
    changed[2] = meta;
    reject(&gate, &changed);
  }
  for index in [F128::new(1024, 0), F128::new(680, 1)] {
    let mut changed = input;
    changed[1] = index;
    reject(&gate, &changed);
  }
  let gate = CodeGate::new(3, CodeGateKind::Constructor).unwrap();
  let input = [F128::ONE, F128::new(145, 0), F128::new(9, 0), F128::ZERO];
  let out = accept(&gate, &input);
  assert_eq!(out[0], F128::new(CONSTRUCTORS + 3 * 145 + 2, 0));
  let gate = CodeGate::new(3, CodeGateKind::Alternative).unwrap();
  let input = [
    F128::ONE,
    frame(),
    F128::new(127, 0),
    F128::new(128, 0),
    F128::new(145 | 184 << 8, 0),
    F128::ZERO,
  ];
  let out = accept(&gate, &input);
  assert_eq!(out[0], F128::new(block_address(680, 184) + 255, 0));
  let mut changed = input;
  changed[2].lo = 128;
  reject(&gate, &changed);
}

#[test]
#[ignore = "full original CSLib native packing census; this does not prove source-to-code admission"]
fn original_cslib_native_packing_fits_consumers_not_source_admission() {
  use crate::ixby::ixbf::{self, DecodeLimits};
  let source = std::fs::read(
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
  )
  .unwrap();
  let artifact =
    ixbf::decode_program(&source, DecodeLimits::default()).unwrap();
  let packed = PackedProgram::from_artifact(&artifact).unwrap();
  let cells =
    packed.cells.iter().copied().collect::<std::collections::BTreeMap<_, _>>();
  assert_eq!(cells.len(), packed.cells.len());
  let gate = CodeGate::new(3, CodeGateKind::Block).unwrap();
  let operand_gate = CodeGate::new(3, CodeGateKind::Operand).unwrap();
  let mut operands = 0;
  for (function, definition) in artifact.functions().iter().enumerate() {
    for (block, definition) in definition.blocks.iter().enumerate() {
      let locals =
        definition.locals.to_u64_digits().first().copied().unwrap_or(0) as u8;
      let frame =
        FrameState::eval(function as u16, block as u8, locals, 0).words()[0];
      let address = block_address(function as u16, block as u8);
      let cell = cells[&address];
      let mut out = Vec::new();
      gate.eval(&[F128::ONE, frame, cell[0], cell[1]], &(), &mut out);
      assert_eq!(out[4], F128::ZERO, "block {function}/{block}");
      let count = (cell[0].lo >> 32) as u8;
      for index in 0..count {
        let cell = cells[&(address + 1 + u64::from(index))];
        let reply = if cell[0] == F128::ZERO {
          [F128::new(5, 0), F128::ZERO]
        } else {
          [F128::ZERO; 2]
        };
        out.clear();
        operand_gate.eval(
          &[
            F128::ONE,
            frame,
            F128::new(u64::from(index), 0),
            F128::new(u64::from(count), 0),
            cell[0],
            cell[1],
            reply[0],
            reply[1],
          ],
          &(),
          &mut out,
        );
        assert_eq!(out[10], F128::ZERO, "operand {function}/{block}/{index}");
        operands += 1;
      }
    }
  }
  eprintln!(
    "native packed original IXBF: {} bytes, {} functions, {} blocks, {operands} operand cells, {} total cells; source binding remains unproved",
    source.len(),
    artifact.functions().len(),
    artifact.inventory().blocks,
    cells.len()
  );
}
