use super::*;
use crate::ixby::{
  byte_value::ByteCapacity,
  decode::test_support::{
    CtorId, FunctionImage as F, Instruction as I, Operand as O, Value as V,
    advice, meta, object_program,
  },
  object_value::test_support::{CAPACITY, declarations, id, layout},
};

fn setup() -> ProgramDecodeGate {
  ProgramDecodeGate::new(
    3,
    CAPACITY.program,
    CAPACITY.control,
    PrimitiveSet::crypto(),
  )
  .unwrap()
  .with_byte_values(ByteDecodeLayout {
    capacity: ByteCapacity::new(17).unwrap(),
    base: 0,
  })
  .unwrap()
  .with_objects(layout())
  .unwrap()
}

fn constructors() -> Vec<(CtorId, u32)> {
  vec![(id(false), 0), (id(true), 2)]
}

fn case() -> F {
  F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::CaseCtor(O::Local(0), vec![(1, 1), (0, 2)])),
      (3, I::Ret(O::Local(2))),
      (1, I::Ret(O::Literal(V::Word(9)))),
    ],
  }
}

fn check(gate: &ProgramDecodeGate, r1cs: &BlockR1cs, bytes: &[u8], good: bool) {
  let inputs = advice(CAPACITY.program.bytes, bytes);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&inputs, bits));
  let residual = 128 * (gate.input_count() + gate.decoded_words());
  assert_eq!(bits[residual], !good);
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn constructor_program_checks_all_declarations_and_alternative_frame_arities() {
  let gate = setup();
  let r1cs = gate.r1cs();
  let code = object_program(0, &constructors(), &[case()]);
  check(&gate, &r1cs, &code, true);
  let inputs = advice(CAPACITY.program.bytes, &code);
  let result = evaluate(gate.plan(), &inputs, gate.output_count());
  let mut expected = declarations();
  expected.extend([F128::new(2, 0), meta(1, 1, 0, 0), meta(0, 2, 0, 0)]);
  expected.resize(layout().program_words(), F128::ZERO);
  assert_eq!(&result[gate.object_data_word()..gate.decoded_words()], expected);
  for bad in [
    vec![(id(true), 0), (id(true), 2)], // duplicate, even unused
    vec![(id(false), 0), (id(true), 3)], // fields over physical capacity
    vec![(id(false), 0)],               // referenced constructor missing
  ] {
    check(&gate, &r1cs, &object_program(0, &bad, &[case()]), false);
  }
  for alternatives in [
    vec![(1, 1), (1, 1)],
    vec![(2, 1)],
    vec![(1, 2)],
    vec![(0, 1)],
    vec![(0, u32::MAX)],
  ] {
    let mut bad = case();
    bad.blocks[0].1 = I::CaseCtor(O::Local(0), alternatives);
    check(&gate, &r1cs, &object_program(0, &constructors(), &[bad]), false);
  }
  for (ctor, args) in
    [(0, vec![O::Local(0)]), (1, vec![]), (2, vec![]), (u32::MAX, vec![])]
  {
    // Malformed but unreachable construction must still reject.
    let bad = F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Ret(O::Local(0))),
        (1, I::Construct(ctor, args, 2)),
        (2, I::Ret(O::Local(1))),
      ],
    };
    check(&gate, &r1cs, &object_program(0, &constructors(), &[bad]), false);
  }
  for end in 0..code.len() {
    check(&gate, &r1cs, &code[..end], false);
  }
}

#[test]
fn constructor_program_full_identity_is_guest_data_and_all_outputs_are_bound() {
  let gate = setup();
  let r1cs = gate.r1cs();
  let base = object_program(0, &constructors(), &[case()]);
  for byte in [16, 31, 47, 48, 51, 52, 55, 60, 91, 92, 96] {
    let mut code = base.clone();
    code[byte] ^= 0x80;
    check(&gate, &r1cs, &code, true);
  }
  let row = ProgramDecodeRow(advice(CAPACITY.program.bytes, &base));
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&row.0, bits));
  assert!(r1cs.satisfies(&bits));
  for word in gate.object_data_word()..gate.output_count() {
    for bit in [0, 7, 31, 32, 63, 64, 95, 127] {
      let at = 128 * (gate.input_count() + word) + bit;
      bits[at] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[at] ^= true;
    }
  }
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
