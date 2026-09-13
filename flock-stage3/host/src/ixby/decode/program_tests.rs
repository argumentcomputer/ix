use super::*;
use crate::ixby::decode::scalar_primitive_arity;
use crate::ixby::decode::test_support::{
  FunctionImage, Instruction as I, Operand as O, Value as V, advice, program,
  program_table,
};

const CAPACITY: ProgramCapacities =
  ProgramCapacities { bytes: 256, functions: 2, blocks: 3, operands: 2 };
const CONTROL: ControlCapacities =
  ControlCapacities { locals: 4, continuations: 2, arguments: 2 };

fn accepted(
  gate: &ProgramDecodeGate,
  r1cs: &BlockR1cs,
  entry: u32,
  functions: &[FunctionImage],
) {
  let bytes = program(entry, functions);
  let mut expected = program_table(gate.capacity, entry, functions);
  expected.push(F128::ZERO);
  let inputs = advice(gate.capacity.bytes, &bytes);
  assert_eq!(
    evaluate(gate.plan(), &inputs, gate.output_count()),
    expected,
    "{functions:?}"
  );
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&inputs, bits));
  assert!(r1cs.satisfies(&bits));
}

#[test]
fn canonical_programs_decode_every_instruction_and_untouched_padding() {
  let gate =
    ProgramDecodeGate::new(3, CAPACITY, CONTROL, PrimitiveSet::scalar())
      .unwrap();
  let r1cs = gate.r1cs();
  let identity = FunctionImage {
    arity: 1,
    entry: 0,
    blocks: vec![(1, I::Ret(O::Local(0)))],
  };
  assert_eq!(
    program(0, std::slice::from_ref(&identity)),
    crate::ixby::commitment::tests::GOLDEN_PROGRAM
  );
  accepted(&gate, &r1cs, 0, std::slice::from_ref(&identity));
  for operand in [
    O::Local(0),
    O::Literal(V::Bool(0)),
    O::Literal(V::Bool(1)),
    O::Literal(V::Word(u32::MAX)),
    O::Literal(V::Field(0xffff_ffff_0000_0000)),
    O::Literal(V::Ext(0x1234_5678_9abc_def0, 0xffff_ffff_0000_0000)),
    O::Literal(V::Erased),
  ] {
    accepted(
      &gate,
      &r1cs,
      0,
      &[FunctionImage {
        arity: 1,
        entry: 0,
        blocks: vec![(1, I::Copy(operand, 1)), (2, I::Ret(O::Local(1)))],
      }],
    );
  }
  for primitive in PrimitiveSet::scalar().opcodes() {
    let operands =
      vec![O::Local(0); scalar_primitive_arity(primitive).unwrap()];
    accepted(
      &gate,
      &r1cs,
      0,
      &[FunctionImage {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::Primitive(primitive, operands, 1)),
          (2, I::Ret(O::Local(1))),
        ],
      }],
    );
  }
  for callee in [Some(1), None] {
    accepted(
      &gate,
      &r1cs,
      0,
      &[
        FunctionImage {
          arity: 1,
          entry: 0,
          blocks: vec![
            (1, I::Call(callee, vec![O::Local(0)], 1)),
            (2, I::Ret(O::Local(1))),
          ],
        },
        identity.clone(),
      ],
    );
    accepted(
      &gate,
      &r1cs,
      1,
      &[
        identity.clone(),
        FunctionImage {
          arity: 1,
          entry: 0,
          blocks: vec![(1, I::Tail(callee.map(|_| 0), vec![O::Local(0)]))],
        },
      ],
    );
  }
  accepted(
    &gate,
    &r1cs,
    0,
    &[FunctionImage {
      arity: 1,
      entry: 2,
      blocks: vec![
        (1, I::Ret(O::Literal(V::Word(11)))),
        (1, I::Ret(O::Literal(V::Word(13)))),
        (1, I::Branch(O::Local(0), 0, 1)),
      ],
    }],
  );
}

fn rejected(gate: &ProgramDecodeGate, r1cs: &BlockR1cs, input: &[F128]) {
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(input, bits));
  let residual = (gate.input_count() + gate.decoded_words()) * 128;
  assert!(bits[residual], "malformed program was accepted");
  assert!(r1cs.satisfies(&bits));
  // Recompute every internal and output bit, then forge the zero required
  // by the actual slot wrapper. No host rejection or stale advice is used.
  bits[residual] = false;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn byte_literals_have_setup_fixed_handles_and_exact_independent_records() {
  use crate::ixby::{
    byte_value::{ByteCapacity, ByteDecodeLayout},
    decode::test_support::{byte_record, meta},
    value::BYTES_TAG,
  };
  let capacity =
    ProgramCapacities { bytes: 192, functions: 2, blocks: 2, operands: 3 };
  let bytes = ByteCapacity::new(33).unwrap();
  let gate =
    ProgramDecodeGate::new(3, capacity, CONTROL, PrimitiveSet::crypto_bytes())
      .unwrap()
      .with_byte_values(ByteDecodeLayout { capacity: bytes, base: 0 })
      .unwrap();
  let r1cs = gate.r1cs();
  let data: Vec<_> = (0..33).map(|i| (i * 73 + 19) as u8).collect();
  let code = program(
    0,
    &[
      FunctionImage {
        arity: 0,
        entry: 0,
        blocks: vec![
          (
            0,
            I::Primitive(
              31,
              vec![
                O::Literal(V::Bytes(data.clone())),
                O::Literal(V::Bytes(vec![])),
              ],
              1,
            ),
          ),
          (1, I::Ret(O::Local(0))),
        ],
      },
      FunctionImage {
        arity: 0,
        entry: 0,
        blocks: vec![(0, I::Ret(O::Literal(V::Bytes(vec![7, 8, 9]))))],
      },
    ],
  );
  let inputs = advice(capacity.bytes, &code);
  let result = evaluate(gate.plan(), &inputs, gate.output_count());
  assert_eq!(result.last(), Some(&F128::ZERO));
  for (function, block, operand, allocation) in
    [(0, 0, 0, 0), (0, 0, 1, 1), (1, 0, 0, 6)]
  {
    let at = capacity.layout().block_word(function, block) + 2 + 3 * operand;
    assert_eq!(
      &result[at..at + 3],
      &[meta(2, 0, 0, 0), F128::new(BYTES_TAG, 0), F128::new(allocation, 0)]
    );
  }
  let mut records = Vec::new();
  for index in 0..12 {
    records.extend(byte_record(
      33,
      match index {
        0 => Some(data.as_slice()),
        1 => Some(&[]),
        6 => Some(&[7, 8, 9]),
        _ => None,
      },
    ));
  }
  assert_eq!(&result[capacity.layout().words()..gate.decoded_words()], records);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&inputs, bits));
  assert!(r1cs.satisfies(&bits));
  for word in capacity.layout().words()..gate.decoded_words() {
    for bit in [0, 31, 32, 63, 64, 127] {
      let at = 128 * (gate.input_count() + word) + bit;
      bits[at] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[at] ^= true;
    }
  }
  for end in [0, 8, 20, 47, code.len() - 1] {
    rejected(&gate, &r1cs, &advice(capacity.bytes, &code[..end]));
  }
  let oversized = program(
    0,
    &[FunctionImage {
      arity: 0,
      entry: 0,
      blocks: vec![(0, I::Ret(O::Literal(V::Bytes(vec![0; 34]))))],
    }],
  );
  rejected(&gate, &r1cs, &advice(capacity.bytes, &oversized));
  let row = ProgramDecodeRow(inputs);
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}

#[test]
fn malformed_headers_full_width_counts_and_all_bytes_are_constrained() {
  let capacity =
    ProgramCapacities { bytes: 64, functions: 1, blocks: 1, operands: 1 };
  let control = ControlCapacities { locals: 1, continuations: 0, arguments: 1 };
  let gate =
    ProgramDecodeGate::new(3, capacity, control, PrimitiveSet::scalar())
      .unwrap();
  let r1cs = gate.r1cs();
  let code = crate::ixby::commitment::tests::GOLDEN_PROGRAM;
  for end in 0..code.len() {
    rejected(&gate, &r1cs, &advice(capacity.bytes, &code[..end]));
  }
  for byte in 0..8 {
    let mut bad = code.to_vec();
    bad[byte] ^= 1;
    rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
  }
  for (offset, values) in [
    (8, vec![1, 2, 1 << 31, u32::MAX]),
    (12, vec![1, 1 << 31, u32::MAX]),
    (16, vec![0, 2, 1 << 31, u32::MAX]),
    (20, vec![0, 2, 1 << 31, u32::MAX]),
    (24, vec![1, 1 << 31, u32::MAX]),
    (28, vec![0, 2, 1 << 31, u32::MAX]),
    (32, vec![0, 2, 1 << 31, u32::MAX]),
    (38, vec![1, 1 << 31, u32::MAX]),
  ] {
    for value in values {
      let mut bad = code.to_vec();
      bad[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
      rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
    }
  }
  for (offset, tag) in [(36, 4), (36, 5), (36, 255), (37, 3), (37, 255)] {
    let mut bad = code.to_vec();
    bad[offset] = tag;
    rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
  }
  for suffix in [0, 1, 255] {
    let mut bad = code.to_vec();
    bad.push(suffix);
    rejected(&gate, &r1cs, &advice(capacity.bytes, &bad));
  }
  let good = advice(capacity.bytes, code);
  for bit in 32..128 {
    let mut bad = good.clone();
    if bit < 64 {
      bad[0].lo |= 1 << bit;
    } else {
      bad[0].hi |= 1 << (bit - 64);
    }
    rejected(&gate, &r1cs, &bad);
  }
  for length in [65, 1 << 31, u32::MAX] {
    let mut bad = good.clone();
    bad[0] = F128::new(u64::from(length), 0);
    rejected(&gate, &r1cs, &bad);
  }
  for bit in 0..128 {
    let mut bad = good.clone();
    let last = bad.last_mut().unwrap();
    if bit < 64 {
      last.lo |= 1 << bit;
    } else {
      last.hi |= 1 << (bit - 64);
    }
    rejected(&gate, &r1cs, &bad);
  }
}

#[test]
fn whole_image_admission_checks_unreachable_blocks_unused_functions_and_registry()
 {
  let gate =
    ProgramDecodeGate::new(3, CAPACITY, CONTROL, PrimitiveSet::scalar())
      .unwrap();
  let r1cs = gate.r1cs();
  let identity = FunctionImage {
    arity: 1,
    entry: 0,
    blocks: vec![(1, I::Ret(O::Local(0)))],
  };
  let bad_instructions = [
    I::Ret(O::Local(1)),
    I::Ret(O::Literal(V::Bool(2))),
    I::Ret(O::Literal(V::Field(0xffff_ffff_0000_0001))),
    I::Ret(O::Literal(V::Field(u64::MAX))),
    I::Ret(O::Literal(V::Ext(1, 0xffff_ffff_0000_0001))),
    I::Primitive(0, vec![O::Local(0)], 0),
    I::Primitive(17, vec![O::Local(0); 2], 0),
    I::Primitive(20, vec![O::Local(0)], 0),
    I::Primitive(255, vec![O::Local(0); 2], 0),
    I::Primitive(0, vec![O::Local(0); 3], 0),
    I::Copy(O::Local(0), 0), // destination needs two locals, not one
    I::Copy(O::Local(0), 2), // outside this function's live block count
    I::Call(Some(2), vec![O::Local(0)], 0),
    I::Tail(Some(2), vec![O::Local(0)]),
    I::Tail(Some(0), vec![]), // valid callee, wrong arity
    I::Tail(None, vec![]),
    I::Branch(O::Local(0), 0, 2),
  ];
  for bad in bad_instructions {
    // An unused function and an unvisited second block must both be checked.
    for in_unused_function in [false, true] {
      let mut functions = vec![identity.clone(), identity.clone()];
      if in_unused_function {
        functions[1].blocks = vec![(1, bad.clone())];
      } else {
        functions[0].blocks.push((1, bad.clone()));
      }
      let bytes = program(0, &functions);
      rejected(&gate, &r1cs, &advice(CAPACITY.bytes, &bytes));
    }
  }
  let mut mismatch = identity.clone();
  mismatch.blocks.push((2, I::Ret(O::Local(0))));
  mismatch.blocks[0].1 = I::Branch(O::Local(0), 0, 1);
  rejected(&gate, &r1cs, &advice(CAPACITY.bytes, &program(0, &[mismatch])));
  // Isolate primitive arity from destination admission: the successor is
  // valid and declares exactly one more local than the primitive block.
  for (opcode, count) in [(0, 1), (17, 2)] {
    let image = FunctionImage {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Primitive(opcode, vec![O::Local(0); count], 1)),
        (2, I::Ret(O::Local(1))),
      ],
    };
    rejected(&gate, &r1cs, &advice(CAPACITY.bytes, &program(0, &[image])));
  }
  for malformed in [
    FunctionImage { arity: 0, ..identity.clone() },
    FunctionImage { entry: 1, ..identity.clone() },
    FunctionImage { blocks: vec![], ..identity.clone() },
  ] {
    rejected(
      &gate,
      &r1cs,
      &advice(CAPACITY.bytes, &program(0, &[identity.clone(), malformed])),
    );
  }
  let only_add = ProgramDecodeGate::new(
    3,
    CAPACITY,
    CONTROL,
    PrimitiveSet::new(&[0]).unwrap(),
  )
  .unwrap();
  let only_add_r1cs = only_add.r1cs();
  let field_mul = FunctionImage {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Primitive(16, vec![O::Local(0); 2], 1)),
      (2, I::Ret(O::Local(1))),
    ],
  };
  let bytes = program(0, &[identity, field_mul]);
  rejected(&only_add, &only_add_r1cs, &advice(CAPACITY.bytes, &bytes));
}

#[test]
fn program_tables_outputs_and_inner_padding_cannot_be_forged() {
  let capacity =
    ProgramCapacities { bytes: 64, functions: 1, blocks: 1, operands: 1 };
  let control = ControlCapacities { locals: 1, continuations: 0, arguments: 1 };
  let gate =
    ProgramDecodeGate::new(3, capacity, control, PrimitiveSet::scalar())
      .unwrap();
  let r1cs = gate.r1cs();
  let input =
    advice(capacity.bytes, crate::ixby::commitment::tests::GOLDEN_PROGRAM);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
  assert!(r1cs.satisfies(&bits));
  for word in 0..gate.output_count() {
    for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
      let column = (gate.input_count() + word) * 128 + bit;
      bits[column] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[column] ^= true;
    }
  }
  bits[gate.plan().k() - 1] = true;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn program_count_emit_setup_is_capacity_only_and_witness_padding_is_initialized()
 {
  use crate::sizing::CountingEmitter;
  use flock_prover::circuit::builder::ShapeBuilder;
  let capacity =
    ProgramCapacities { bytes: 64, functions: 1, blocks: 1, operands: 1 };
  let control = ControlCapacities { locals: 1, continuations: 0, arguments: 1 };
  let gate =
    ProgramDecodeGate::new(3, capacity, control, PrimitiveSet::scalar())
      .unwrap();
  fn emit(b: &mut impl CircuitEmitter, gate: ProgramDecodeGate) {
    let capacity = gate.capacity;
    let slot = ProgramDecodeSlot::declare(b, gate);
    let length = b.input();
    let data: Vec<_> = (0..capacity.data_words()).map(|_| b.input()).collect();
    for word in slot.decode(b, length, &data) {
      b.publish(word);
    }
  }
  let mut count = CountingEmitter::new();
  emit(&mut count, gate.clone());
  assert!(gate.plan.get().is_none());
  let mut b = ShapeBuilder::new(3);
  emit(&mut b, gate.clone());
  let shape = b.finish().unwrap();
  count.ensure_matches(&shape).unwrap();
  let (registry, counts) = count.registry(3);
  assert_eq!(counts, shape.counts);
  assert_eq!(registry.types()[0].a_0.rows, shape.registry.types()[0].a_0.rows);
  assert_eq!(registry.types()[0].b_0.rows, shape.registry.types()[0].b_0.rows);
  assert_eq!(
    registry.types()[0].io_schema,
    shape.registry.types()[0].io_schema
  );
  let row = ProgramDecodeRow(advice(
    capacity.bytes,
    crate::ixby::commitment::tests::GOLDEN_PROGRAM,
  ));
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  assert!(PrimitiveSet::new(&[0, 0]).is_err());
  assert!(PrimitiveSet::new(&[255]).is_err());
  assert!(
    ProgramDecodeGate::new(2, capacity, control, PrimitiveSet::scalar())
      .is_err()
  );
  assert!(
    ProgramDecodeGate::new(
      3,
      ProgramCapacities { bytes: usize::MAX, ..capacity },
      control,
      PrimitiveSet::scalar()
    )
    .is_err()
  );
  assert!(
    ProgramDecodeGate::new(
      3,
      ProgramCapacities { functions: 0, ..capacity },
      control,
      PrimitiveSet::scalar()
    )
    .is_err()
  );
  assert!(
    ProgramDecodeGate::new(
      3,
      ProgramCapacities { blocks: 9, ..capacity },
      control,
      PrimitiveSet::scalar()
    )
    .is_err()
  );
}
