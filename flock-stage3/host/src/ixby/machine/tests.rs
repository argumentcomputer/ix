use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{
    bits::fill_words,
    control::{
      CallTarget, Control, ControlFrame, ControlState, ResolvedAction,
    },
    decode::test_support::{
      FunctionImage as F, Instruction as I, Operand as O, Value as V, advice,
      input, meta, output, program, program_table,
    },
    io::LayoutEmitter,
  },
  sizing::{CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{GateType, ShapeBuilder},
  field::F128,
  r1cs::BlockR1cs,
};

const CONTROL: ControlCapacities =
  ControlCapacities { locals: 4, continuations: 2, arguments: 2 };
const CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 2,
    blocks: 4,
    operands: 2,
  },
  control: CONTROL,
  input: InputCapacities { bytes: 64, values: 2 },
  output_bytes: 64,
  steps: 24,
};

fn check(
  plan: &BooleanR1csPlan,
  r1cs: &BlockR1cs,
  input: &[F128],
  outputs: usize,
  good: bool,
) {
  let mut bits = vec![false; r1cs.n()];
  plan.fill_row(&mut bits[..plan.k()], |bits| fill_words(input, bits));
  let error = 128 * (input.len() + outputs - 1);
  assert_eq!(bits[error], !good, "{input:?}");
  assert!(r1cs.satisfies(&bits));
  if !good {
    bits[error] = false;
    assert!(!r1cs.satisfies(&bits));
  }
}
fn mutations(
  plan: &BooleanR1csPlan,
  r1cs: &BlockR1cs,
  input: &[F128],
  outputs: usize,
) {
  let mut bits = vec![false; r1cs.n()];
  plan.fill_row(&mut bits[..plan.k()], |bits| fill_words(input, bits));
  assert!(r1cs.satisfies(&bits));
  for word in 0..outputs {
    for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
      let column = 128 * (input.len() + word) + bit;
      bits[column] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[column] ^= true;
    }
  }
  bits[plan.k() - 1] = true;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn initializer_derives_entry_arity_fuel_and_zero_stack_from_both_decoders() {
  let gate = InitialStateGate::new(3, CONTROL, 2, 2, 16).unwrap();
  let r1cs = gate.r1cs();
  let input = [
    meta(1, 2, 0, 0),
    meta(1, 0, 1, 0),
    meta(2, 1, 2, 0),
    F128::new(2, 0),
    V::Word(41).words()[0],
    V::Word(41).words()[1],
    V::Ext(17, 19).words()[0],
    V::Ext(17, 19).words()[1],
  ];
  let expected = ControlState {
    control: Control::Eval(ControlFrame {
      function: 1,
      block: 1,
      locals: vec![V::Word(41).words(), V::Ext(17, 19).words()],
    }),
    continuation: vec![],
    remaining: 16,
  }
  .words(CONTROL)
  .unwrap();
  let mut result = Vec::new();
  gate.eval(&input, &(), &mut result);
  assert_eq!(&result[..CONTROL.state_words()], expected);
  check(gate.plan(), &r1cs, &input, gate.output_count(), true);
  for entry in [2, 1 << 31, u32::MAX] {
    let mut bad = input;
    bad[0] = meta(entry, 2, 0, 0);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  for count in [0, 1, 3, 1 << 31, u32::MAX] {
    for word in [0, 3] {
      let mut bad = input;
      bad[word] = if word == 0 {
        meta(1, count, 0, 0)
      } else {
        F128::new(count.into(), 0)
      };
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  for header in [
    meta(1, 1, 2, 0),
    meta(2, 2, 2, 0),
    meta(2, 1 << 31, 2, 0),
    meta(2, 1, 0, 0),
  ] {
    let mut bad = input;
    bad[2] = header;
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  for (word, start) in [(0, 64), (2, 96), (3, 32)] {
    for bit in start..128 {
      let mut bad = input;
      flip(&mut bad[word], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  let empty_gate = InitialStateGate::new(3, CONTROL, 1, 0, 16).unwrap();
  let empty = [meta(0, 1, 0, 0), meta(0, 0, 1, 0), F128::ZERO];
  check(
    empty_gate.plan(),
    &empty_gate.r1cs(),
    &empty,
    empty_gate.output_count(),
    true,
  );
  mutations(gate.plan(), &r1cs, &input, gate.output_count());
  let row = InitialStateRow(input.to_vec());
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
fn action_assembly_is_exact_for_all_instruction_kinds_and_idle_padding() {
  let gate = ActionAssembleGate::new(3, CONTROL, 2).unwrap();
  let r1cs = gate.r1cs();
  let literal = V::Word(42).words();
  let extra = V::Ext(17, 19).words();
  for kind in 0..=6 {
    let mut input = vec![F128::ZERO; gate.input_count()];
    if kind != 0 {
      input[0] = meta(
        1,
        kind,
        if matches!(kind, 1 | 2 | 3 | 6) { 7 } else { 0 },
        if kind == 6 { 11 } else { 0 },
      );
      input[1] = meta(
        if matches!(kind, 3 | 5) { 13 } else { 0 },
        0,
        if matches!(kind, 3 | 5) { 2 } else { 1 },
        0,
      );
      input[5..7].copy_from_slice(&literal);
      if kind == 2 {
        input[3..5].copy_from_slice(&extra);
      }
      if matches!(kind, 3 | 5) {
        input[2] = meta(2, 17, 23, 0);
        input[7..9].copy_from_slice(&extra);
      }
    }
    let callee = CallTarget { function: 13, entry: 17, arity: 2 };
    let action = match kind {
      0 => ResolvedAction::Idle,
      1 => ResolvedAction::Bind { target: 7, value: literal },
      2 => ResolvedAction::Bind { target: 7, value: extra },
      3 => {
        ResolvedAction::Call { target: 7, callee, args: vec![literal, extra] }
      },
      4 => ResolvedAction::Return { value: literal },
      5 => ResolvedAction::TailCall { callee, args: vec![literal, extra] },
      6 => ResolvedAction::Branch { condition: literal, yes: 7, no: 11 },
      _ => unreachable!(),
    };
    let mut result = Vec::new();
    gate.eval(&input, &(), &mut result);
    assert_eq!(
      &result[..CONTROL.action_words()],
      action.words(CONTROL).unwrap()
    );
    check(gate.plan(), &r1cs, &input, gate.output_count(), true);
    mutations(gate.plan(), &r1cs, &input, gate.output_count());
  }
  let mut bad = vec![F128::ZERO; gate.input_count()];
  for kind in [7, 1 << 31, u32::MAX] {
    bad[0] = meta(0, kind, 0, 0);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  for count in [3, 1 << 31, u32::MAX] {
    bad[0] = meta(0, 3, 1, 0);
    bad[1] = meta(1, 0, count, 0);
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
  }
  for word in 0..gate.input_count() {
    for bit in [0, 31, 63, 64, 95, 127] {
      let mut bad = vec![F128::ZERO; gate.input_count()];
      flip(&mut bad[word], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
  }
  let row = ActionAssembleRow(vec![F128::ZERO; gate.input_count()]);
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}

fn flip(word: &mut F128, bit: usize) {
  if bit < 64 {
    word.lo ^= 1 << bit;
  } else {
    word.hi ^= 1 << (bit - 64);
  }
}

#[test]
fn output_bytes_are_canonical_and_require_a_genuine_empty_stack_terminal_state()
{
  let gate = OutputEncodeGate::new(3, CONTROL, 64).unwrap();
  let r1cs = gate.r1cs();
  for value in [
    V::Bool(0),
    V::Bool(1),
    V::Word(u32::MAX),
    V::Field(0xffff_ffff_0000_0000),
    V::Ext(0x1234_5678_9abc_def0, 0xffff_ffff_0000_0000),
    V::Erased,
  ] {
    let state = ControlState {
      control: Control::Halted(value.words()),
      continuation: vec![],
      remaining: 7,
    }
    .words(CONTROL)
    .unwrap();
    let mut expected = advice(64, &output(&value));
    expected.push(F128::ZERO);
    let mut result = Vec::new();
    gate.eval(&state, &(), &mut result);
    assert_eq!(result, expected);
    check(gate.plan(), &r1cs, &state, gate.output_count(), true);
    for kind in [0, 1, 3, 1 << 31, u32::MAX] {
      let mut bad = state.clone();
      bad[0] = meta(kind, 7, 0, 0);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
    for bit in 64..128 {
      let mut bad = state.clone();
      flip(&mut bad[0], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
    let value_word = 1 + CONTROL.frame_words();
    for word in (1..value_word).chain(value_word + 2..CONTROL.state_words()) {
      let mut bad = state.clone();
      bad[word] = F128::new(1, 0);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
    let mut bad = state.clone();
    bad[value_word] = F128::ZERO;
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    let size = output(&value).len();
    let narrow = OutputEncodeGate::new(3, CONTROL, size - 1).unwrap();
    check(narrow.plan(), &narrow.r1cs(), &state, narrow.output_count(), false);
    let exact = OutputEncodeGate::new(3, CONTROL, size).unwrap();
    check(exact.plan(), &exact.r1cs(), &state, exact.output_count(), true);
    mutations(gate.plan(), &r1cs, &state, gate.output_count());
  }
  let row = OutputEncodeRow(
    ControlState {
      control: Control::Halted(V::Word(42).words()),
      continuation: vec![],
      remaining: 0,
    }
    .words(CONTROL)
    .unwrap(),
  );
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
fn byte_output_binds_the_complete_buffer_and_enforces_terminal_and_capacity_checks()
 {
  use crate::ixby::{byte_value::ByteCapacity, value::BYTES_TAG};
  let capacity = ByteCapacity::new(65).unwrap();
  let gate = OutputEncodeGate::new(3, CONTROL, 96)
    .unwrap()
    .with_byte_values(capacity, 7)
    .unwrap();
  let r1cs = gate.r1cs();
  for length in [0, 1, 15, 16, 17, 31, 32, 33, 64, 65] {
    let data: Vec<_> = (0..length).map(|i| (i * 73 + 19) as u8).collect();
    let mut state = ControlState {
      control: Control::Halted([F128::new(BYTES_TAG, 0), F128::new(6, 0)]),
      continuation: vec![],
      remaining: 2,
    }
    .words(CONTROL)
    .unwrap();
    state.extend(advice(65, &data));
    let mut result = Vec::new();
    gate.eval(&state, &(), &mut result);
    let mut expected = advice(96, &output(&V::Bytes(data.clone())));
    expected.push(F128::ZERO);
    assert_eq!(result, expected);
    check(gate.plan(), &r1cs, &state, gate.output_count(), true);
    let exact = OutputEncodeGate::new(3, CONTROL, 14 + length)
      .unwrap()
      .with_byte_values(capacity, 7)
      .unwrap();
    check(exact.plan(), &exact.r1cs(), &state, exact.output_count(), true);
    let narrow = OutputEncodeGate::new(3, CONTROL, 13 + length)
      .unwrap()
      .with_byte_values(capacity, 7)
      .unwrap();
    check(narrow.plan(), &narrow.r1cs(), &state, narrow.output_count(), false);
    for bit in [0, 31, 63, 64, 127] {
      let mut bad = state.clone();
      flip(&mut bad[1], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
    for bit in 32..128 {
      let mut bad = state.clone();
      flip(&mut bad[CONTROL.state_words()], bit);
      check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    }
    let padding_byte = length;
    let mut bad = state.clone();
    flip(
      &mut bad[CONTROL.state_words() + 1 + padding_byte / 16],
      8 * (padding_byte % 16),
    );
    check(gate.plan(), &r1cs, &bad, gate.output_count(), false);
    mutations(gate.plan(), &r1cs, &state, gate.output_count());
  }
  let mut scalar = ControlState {
    control: Control::Halted(V::Word(42).words()),
    continuation: vec![],
    remaining: 2,
  }
  .words(CONTROL)
  .unwrap();
  scalar.extend(advice(65, &[]));
  check(gate.plan(), &r1cs, &scalar, gate.output_count(), true);
  scalar[CONTROL.state_words()] = F128::new(1, 0);
  check(gate.plan(), &r1cs, &scalar, gate.output_count(), false);
}

pub(crate) fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let mut cases = Vec::new();
  let identity =
    F { arity: 1, entry: 0, blocks: vec![(1, I::Ret(O::Local(0)))] };
  for value in [
    V::Bool(0),
    V::Bool(1),
    V::Word(42),
    V::Field(0xffff_ffff_0000_0000),
    V::Ext(17, 19),
    V::Erased,
  ] {
    cases.push((
      program(0, std::slice::from_ref(&identity)),
      input(std::slice::from_ref(&value)),
      output(&value),
    ));
  }
  for condition in [0, 1] {
    let image = F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Branch(O::Local(0), 1, 2)),
        (1, I::Ret(O::Literal(V::Word(11)))),
        (1, I::Ret(O::Literal(V::Word(13)))),
      ],
    };
    cases.push((
      program(0, &[image]),
      input(&[V::Bool(condition)]),
      output(&V::Word(if condition == 0 { 13 } else { 11 })),
    ));
  }
  let increment = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Primitive(0, vec![O::Local(0), O::Literal(V::Word(1))], 1)),
      (2, I::Ret(O::Local(1))),
    ],
  };
  let caller = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Call(Some(1), vec![O::Local(0)], 1)),
      (2, I::Ret(O::Local(1))),
    ],
  };
  cases.push((
    program(0, &[caller, increment.clone()]),
    input(&[V::Word(41)]),
    output(&V::Word(42)),
  ));
  let tail = F {
    arity: 1,
    entry: 0,
    blocks: vec![(1, I::Tail(Some(1), vec![O::Local(0)]))],
  };
  cases.push((
    program(0, &[tail, increment]),
    input(&[V::Word(0)]),
    output(&V::Word(1)),
  ));
  // Mutual tail recursion varies the number of iterations without changing
  // the physical continuation depth or circuit geometry.
  let recurse = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Primitive(10, vec![O::Local(0), O::Literal(V::Word(1))], 1)),
      (2, I::Branch(O::Local(1), 2, 3)),
      (2, I::Ret(O::Literal(V::Word(0)))),
      // Tail recursion uses a second helper to stay within four blocks per fn.
      (2, I::Tail(Some(1), vec![O::Local(0)])),
    ],
  };
  let decrement = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Primitive(0, vec![O::Local(0), O::Literal(V::Word(u32::MAX))], 1)),
      (2, I::Tail(Some(0), vec![O::Local(1)])),
    ],
  };
  for n in [0, 1, 2] {
    cases.push((
      program(0, &[recurse.clone(), decrement.clone()]),
      input(&[V::Word(n)]),
      output(&V::Word(0)),
    ));
  }
  // Now retain a continuation per recursive descent; n=0/1/2 visits distinct
  // stack depths under the same setup. The deepest case takes 18 transitions.
  let decrement_call = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Primitive(0, vec![O::Local(0), O::Literal(V::Word(u32::MAX))], 1)),
      (2, I::Call(Some(0), vec![O::Local(1)], 2)),
      (3, I::Ret(O::Local(2))),
    ],
  };
  for n in [0, 1, 2] {
    cases.push((
      program(0, &[recurse.clone(), decrement_call.clone()]),
      input(&[V::Word(n)]),
      output(&V::Word(0)),
    ));
  }
  // CallSelf pushes once, takes a different branch, and returns through both
  // saved frames. This also tests a nonzero entry function and ordered locals.
  let self_call = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::Branch(O::Local(0), 1, 2)),
      (1, I::Call(None, vec![O::Literal(V::Bool(0))], 3)),
      (1, I::Ret(O::Literal(V::Word(37)))),
      (2, I::Ret(O::Local(1))),
    ],
  };
  for condition in [0, 1] {
    cases.push((
      program(1, &[identity.clone(), self_call.clone()]),
      input(&[V::Bool(condition)]),
      output(&V::Word(37)),
    ));
  }
  let no_args =
    F { arity: 0, entry: 0, blocks: vec![(0, I::Ret(O::Literal(V::Erased)))] };
  cases.push((program(0, &[no_args]), input(&[]), output(&V::Erased)));
  cases
}

#[test]
fn different_byte_programs_inputs_branches_calls_and_recursion_execute_in_one_shape()
 {
  let mut builder = ShapeBuilder::new(8);
  let mut b = LayoutEmitter::new(&mut builder);
  let slots =
    ScalarMachineSlots::declare(&mut b, 8, CAPACITY, PrimitiveSet::scalar())
      .unwrap();
  let code: Vec<_> =
    (0..1 + CAPACITY.program.data_words()).map(|_| b.input()).collect();
  let input: Vec<_> =
    (0..1 + CAPACITY.input.data_words()).map(|_| b.input()).collect();
  for word in slots.execute(&mut b, &code, &input) {
    b.publish(word);
  }
  let (layout, public) = b.finish();
  let shape = builder.finish().unwrap();
  let identity = shape.circuit.digest();
  let action_r1cs = slots.action_gate.r1cs();
  let initial_r1cs = slots.initial_gate.r1cs();
  let output_r1cs = slots.output_gate.r1cs();
  for (code, input, output) in cases() {
    let private = [
      advice(CAPACITY.program.bytes, &code),
      advice(CAPACITY.input.bytes, &input),
    ]
    .concat();
    let witness = shape.run(&layout.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      public.instantiate(&advice(CAPACITY.output_bytes, &output)).unwrap(),
      "code {code:?} input {input:?}"
    );
    assert_eq!(shape.circuit.digest(), identity);
    for row in witness.rows::<ActionAssembleGate>(slots.action_slot.slot()) {
      check(
        slots.action_gate.plan(),
        &action_r1cs,
        &row.0,
        slots.action_gate.output_count(),
        true,
      );
    }
    for row in witness.rows::<InitialStateGate>(slots.initial_slot.slot()) {
      check(
        slots.initial_gate.plan(),
        &initial_r1cs,
        &row.0,
        slots.initial_gate.output_count(),
        true,
      );
    }
    for row in witness.rows::<OutputEncodeGate>(slots.output_slot.slot()) {
      check(
        slots.output_gate.plan(),
        &output_r1cs,
        &row.0,
        slots.output_gate.output_count(),
        true,
      );
    }
  }
  let mut count = CountingEmitter::new();
  let mut b = LayoutEmitter::new(&mut count);
  let slots =
    ScalarMachineSlots::declare(&mut b, 8, CAPACITY, PrimitiveSet::scalar())
      .unwrap();
  let code: Vec<_> =
    (0..1 + CAPACITY.program.data_words()).map(|_| b.input()).collect();
  let input: Vec<_> =
    (0..1 + CAPACITY.input.data_words()).map(|_| b.input()).collect();
  for word in slots.execute(&mut b, &code, &input) {
    b.publish(word);
  }
  let (counted_input, counted_public) = b.finish();
  count.ensure_matches(&shape).unwrap();
  assert_eq!(counted_input, layout);
  assert_eq!(counted_public, public);
  assert!(slots.initial_gate.plan.get().is_none());
  assert!(slots.action_gate.plan.get().is_none());
  assert!(slots.output_gate.plan.get().is_none());
  let mut builder = ShapeBuilder::new(3);
  assert!(
    ScalarMachineSlots::declare(
      &mut builder,
      3,
      MachineCapacities { steps: 0, ..CAPACITY },
      PrimitiveSet::scalar()
    )
    .is_err()
  );
  assert!(
    ScalarMachineSlots::declare(
      &mut builder,
      3,
      MachineCapacities { steps: usize::MAX, ..CAPACITY },
      PrimitiveSet::scalar()
    )
    .is_err()
  );
  // Independent codec-table helper agrees on the identity used above.
  assert_eq!(
    program_table(
      CAPACITY.program,
      0,
      &[F {
        arity: 0,
        entry: 0,
        blocks: vec![(0, I::Ret(O::Literal(V::Erased)))]
      }]
    )[0],
    meta(0, 1, 0, 0)
  );
}
