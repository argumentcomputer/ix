use super::*;
use crate::ixby::value::{bool_words, word32_words};

const CAPACITY: ControlCapacities =
  ControlCapacities { locals: 4, continuations: 3, arguments: 3 };

fn frame(function: u32, block: u32, locals: &[u32]) -> ControlFrame {
  ControlFrame {
    function,
    block,
    locals: locals.iter().map(|value| word32_words(*value)).collect(),
  }
}

fn initial() -> ControlState {
  ControlState {
    control: Control::Eval(frame(2, 3, &[11, 13])),
    continuation: vec![frame(7, 9, &[17])],
    remaining: 7,
  }
}

fn logical(gate: &ControlStepGate, input: &[F128]) -> Vec<bool> {
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| {
    fill_free(&ControlStepRow(input.to_vec()), bits)
  });
  let output = evaluate(gate.capacity, input);
  let mut expected = vec![false; output.len() * 128];
  for (word, value) in output.iter().enumerate() {
    write_f128(&mut expected, word * 128, *value);
  }
  let start = gate.input_count() * 128;
  assert_eq!(&bits[start..start + expected.len()], expected);
  bits
}

fn satisfies(r1cs: &BlockR1cs, bits: &[bool]) -> bool {
  let mut full = vec![false; r1cs.n()];
  full[..bits.len()].copy_from_slice(bits);
  r1cs.satisfies(&full)
}

fn transition(
  state: ControlState,
  action: ResolvedAction,
  expected: ControlState,
) {
  let gate = ControlStepGate::new(3, CAPACITY).unwrap();
  let input = gate.inputs(&state, &action).unwrap();
  let output = evaluate(CAPACITY, &input);
  assert_eq!(
    &output[..CAPACITY.state_words()],
    expected.words(CAPACITY).unwrap()
  );
  assert_eq!(output[CAPACITY.state_words()], F128::ZERO);
  assert!(satisfies(&gate.r1cs(), &logical(&gate, &input)));
}

#[test]
fn calls_returns_tail_calls_branches_and_binding_preserve_cek_frames() {
  let state = initial();
  transition(
    state.clone(),
    ResolvedAction::Bind { target: 5, value: word32_words(19) },
    ControlState {
      control: Control::Eval(frame(2, 5, &[11, 13, 19])),
      remaining: 6,
      ..state.clone()
    },
  );
  let callee = CallTarget { function: 4, entry: 6, arity: 2 };
  let args = vec![word32_words(23), word32_words(29)];
  transition(
    state.clone(),
    ResolvedAction::Call {
      target: 8,
      callee: callee.clone(),
      args: args.clone(),
    },
    ControlState {
      control: Control::Eval(frame(4, 6, &[23, 29])),
      continuation: vec![frame(7, 9, &[17]), frame(2, 8, &[11, 13])],
      remaining: 6,
    },
  );
  transition(
    state.clone(),
    ResolvedAction::TailCall { callee, args },
    ControlState {
      control: Control::Eval(frame(4, 6, &[23, 29])),
      remaining: 6,
      ..state.clone()
    },
  );
  transition(
    state.clone(),
    ResolvedAction::Return { value: word32_words(31) },
    ControlState {
      control: Control::Ret(word32_words(31)),
      remaining: 6,
      ..state.clone()
    },
  );
  for condition in [false, true] {
    transition(
      state.clone(),
      ResolvedAction::Branch {
        condition: bool_words(condition),
        yes: 37,
        no: 41,
      },
      ControlState {
        control: Control::Eval(frame(
          2,
          if condition { 37 } else { 41 },
          &[11, 13],
        )),
        remaining: 6,
        ..state.clone()
      },
    );
  }
  transition(
    ControlState { control: Control::Ret(word32_words(31)), ..state },
    ResolvedAction::Idle,
    ControlState {
      control: Control::Eval(frame(7, 9, &[17, 31])),
      continuation: vec![],
      remaining: 6,
    },
  );
}

#[test]
fn terminal_return_consumes_fuel_but_halting_padding_does_not() {
  let state = ControlState {
    control: Control::Ret(word32_words(43)),
    continuation: vec![],
    remaining: 1,
  };
  let halted = ControlState {
    control: Control::Halted(word32_words(43)),
    continuation: vec![],
    remaining: 0,
  };
  transition(state, ResolvedAction::Idle, halted.clone());
  transition(halted.clone(), ResolvedAction::Idle, halted);
}

#[test]
fn layout_bounds_and_maximum_synthesis_are_admitted_without_witness_values() {
  for (locals, continuations, arguments) in
    [(1, 0, 0), (1, 8, 1), (4, 3, 3), (16, 0, 16), (16, 8, 16)]
  {
    let gate = ControlStepGate::new(
      3,
      ControlCapacities { locals, continuations, arguments },
    )
    .unwrap();
    assert!(gate.plan.get().is_none());
    assert!(gate.plan().useful_bits() <= gate.plan().k());
  }
  assert!(ControlStepGate::new(2, CAPACITY).is_err());
  assert!(ControlStepGate::new(21, CAPACITY).is_err());
  assert!(
    ControlStepGate::new(3, ControlCapacities { locals: 0, ..CAPACITY })
      .is_err()
  );
  assert!(
    ControlStepGate::new(3, ControlCapacities { locals: 17, ..CAPACITY })
      .is_err()
  );
  assert!(
    ControlStepGate::new(3, ControlCapacities { continuations: 9, ..CAPACITY })
      .is_err()
  );
  assert!(
    ControlStepGate::new(3, ControlCapacities { arguments: 5, ..CAPACITY })
      .is_err()
  );
}

fn set_lane(input: &mut [F128], word: usize, lane: usize, value: u32) {
  let mut fields = lanes(input[word]);
  fields[lane] = value;
  input[word] = meta(fields[0], fields[1], fields[2], fields[3]);
}

fn mask(bit: usize) -> F128 {
  if bit < 64 { F128::new(1 << bit, 0) } else { F128::new(0, 1 << (bit - 64)) }
}

/// Bypass every typed witness helper, recompute ALL intermediate advice and
/// outputs, then forge the zero residual required by ControlStepSlot. Checking
/// only a host rejection or an unchanged stale output would be insufficient.
fn rejected(gate: &ControlStepGate, r1cs: &BlockR1cs, input: &[F128]) {
  let mut bits = logical(gate, input);
  let residual = (gate.input_count() + gate.capacity.state_words()) * 128;
  assert!(bits[residual], "malformed control row did not report a violation");
  assert!(satisfies(r1cs, &bits));
  bits[residual] = false;
  assert!(!satisfies(r1cs, &bits), "forged zero residual was unconstrained");
}

#[test]
fn raw_metadata_counts_fuel_and_state_kinds_cannot_bypass_admission() {
  let gate = ControlStepGate::new(3, CAPACITY).unwrap();
  let r1cs = gate.r1cs();
  let state = initial();
  let good = gate
    .inputs(
      &state,
      &ResolvedAction::Bind { target: 5, value: word32_words(19) },
    )
    .unwrap();
  let mut mutations = Vec::new();
  for (word, lane, values) in [
    (0, 0, vec![3, 4, 1 << 31, u32::MAX]),
    (0, 1, vec![0]),
    (0, 2, vec![4, 1 << 16, 1 << 31, u32::MAX]),
    (CAPACITY.state_words(), 0, vec![0, 6, 1 << 31, u32::MAX]),
  ] {
    for value in values {
      let mut bad = good.clone();
      set_lane(&mut bad, word, lane, value);
      mutations.push(bad);
    }
  }
  for word in [0, 1, CAPACITY.stack_word(0), CAPACITY.state_words() + 1] {
    for bit in 0..32 {
      let mut bad = good.clone();
      set_lane(&mut bad, word, 3, 1 << bit);
      mutations.push(bad);
    }
  }
  for index in 0..=CAPACITY.continuations {
    let word = if index == 0 { 1 } else { CAPACITY.stack_word(index - 1) };
    for value in [5, 32, 1 << 16, 1 << 31, u32::MAX] {
      let mut bad = good.clone();
      set_lane(&mut bad, word, 2, value);
      mutations.push(bad);
    }
  }
  let call = gate
    .inputs(
      &state,
      &ResolvedAction::Call {
        target: 5,
        callee: CallTarget { function: 6, entry: 7, arity: 1 },
        args: vec![word32_words(23)],
      },
    )
    .unwrap();
  for lane in [1, 2] {
    for value in [0, 2, 4, 1 << 31, u32::MAX] {
      let mut bad = call.clone();
      set_lane(&mut bad, CAPACITY.state_words() + 1, lane, value);
      mutations.push(bad);
    }
  }
  for kind in
    [Control::Ret(word32_words(31)), Control::Halted(word32_words(31))]
  {
    let mut state =
      ControlState { control: kind, continuation: vec![], remaining: 7 };
    let good = gate.inputs(&state, &ResolvedAction::Idle).unwrap();
    for word in 0..CAPACITY.action_words() {
      let mut bad = good.clone();
      bad[CAPACITY.state_words() + word] = F128::ONE;
      mutations.push(bad);
    }
    for word in 1..1 + CAPACITY.frame_words() {
      let mut bad = good.clone();
      bad[word] = F128::ONE;
      mutations.push(bad);
    }
    if matches!(state.control, Control::Ret(_)) {
      state.remaining = 0;
    } else {
      state.continuation.push(frame(3, 4, &[5]));
    }
    mutations.push(gate.inputs(&state, &ResolvedAction::Idle).unwrap());
  }
  for bad in mutations {
    rejected(&gate, &r1cs, &bad);
  }
}

#[test]
fn live_prefix_padding_unused_action_fields_and_typed_branch_are_constrained() {
  let gate = ControlStepGate::new(3, CAPACITY).unwrap();
  let r1cs = gate.r1cs();
  let good = gate
    .inputs(
      &initial(),
      &ResolvedAction::Bind { target: 5, value: word32_words(19) },
    )
    .unwrap();
  let mut padding: Vec<_> = (6..1 + CAPACITY.frame_words())
    .chain(CAPACITY.value_word()..CAPACITY.value_word() + 2)
    .chain(
      CAPACITY.stack_word(0) + 3
        ..CAPACITY.stack_word(0) + CAPACITY.frame_words(),
    )
    .chain(CAPACITY.stack_word(1)..CAPACITY.state_words())
    .chain(CAPACITY.state_words() + 4..gate.input_count())
    .collect();
  padding.sort_unstable();
  padding.dedup();
  for word in padding {
    for bit in [0, 31, 64, 95, 127] {
      let mut bad = good.clone();
      bad[word] = mask(bit);
      rejected(&gate, &r1cs, &bad);
    }
  }
  let action = CAPACITY.state_words();
  for (word, lane) in [
    (action, 2),
    (action, 3),
    (action + 1, 0),
    (action + 1, 1),
    (action + 1, 2),
  ] {
    let mut bad = good.clone();
    set_lane(&mut bad, word, lane, 1);
    rejected(&gate, &r1cs, &bad);
  }
  for condition in [false, true] {
    let branch = gate
      .inputs(
        &initial(),
        &ResolvedAction::Branch {
          condition: bool_words(condition),
          yes: 5,
          no: 6,
        },
      )
      .unwrap();
    for bit in 0..128 {
      let mut bad = branch.clone();
      bad[action + 2] = xor(bad[action + 2], mask(bit));
      rejected(&gate, &r1cs, &bad);
    }
    for bit in 1..128 {
      let mut bad = branch.clone();
      bad[action + 3] = xor(bad[action + 3], mask(bit));
      rejected(&gate, &r1cs, &bad);
    }
  }
  for action_value in [
    ResolvedAction::Call {
      target: 5,
      callee: CallTarget { function: 6, entry: 7, arity: 0 },
      args: vec![],
    },
    ResolvedAction::TailCall {
      callee: CallTarget { function: 6, entry: 7, arity: 0 },
      args: vec![],
    },
  ] {
    let good = gate.inputs(&initial(), &action_value).unwrap();
    for word in action + 2..gate.input_count() {
      let mut bad = good.clone();
      bad[word] = F128::ONE;
      rejected(&gate, &r1cs, &bad);
    }
    if matches!(action_value, ResolvedAction::TailCall { .. }) {
      let mut bad = good;
      set_lane(&mut bad, action, 1, 1);
      rejected(&gate, &r1cs, &bad);
    }
  }
}

#[test]
fn full_banks_reject_append_and_push_but_allow_tail_calls() {
  let gate = ControlStepGate::new(3, CAPACITY).unwrap();
  let r1cs = gate.r1cs();
  let full = frame(2, 3, &[11, 13, 17, 19]);
  let mut state = ControlState {
    control: Control::Eval(full.clone()),
    continuation: vec![full.clone(); CAPACITY.continuations],
    remaining: 7,
  };
  let bind = ResolvedAction::Bind { target: 5, value: word32_words(23) };
  rejected(&gate, &r1cs, &gate.inputs(&state, &bind).unwrap());
  let callee = CallTarget { function: 4, entry: 6, arity: 0 };
  let call =
    ResolvedAction::Call { target: 5, callee: callee.clone(), args: vec![] };
  rejected(&gate, &r1cs, &gate.inputs(&state, &call).unwrap());
  transition(
    state.clone(),
    ResolvedAction::TailCall { callee, args: vec![] },
    ControlState {
      control: Control::Eval(frame(4, 6, &[])),
      remaining: 6,
      ..state.clone()
    },
  );
  state.control = Control::Ret(word32_words(23));
  rejected(&gate, &r1cs, &gate.inputs(&state, &ResolvedAction::Idle).unwrap());
  // A call saves the caller before the result is appended. Even a full
  // caller frame can take that one step; its eventual resume is rejected.
  state.control = Control::Eval(full.clone());
  state.continuation.clear();
  transition(
    state,
    call,
    ControlState {
      control: Control::Eval(frame(4, 6, &[])),
      continuation: vec![ControlFrame { block: 5, ..full }],
      remaining: 6,
    },
  );
}

#[test]
fn every_next_state_word_and_unused_inner_column_is_constrained() {
  let gate = ControlStepGate::new(3, CAPACITY).unwrap();
  let r1cs = gate.r1cs();
  let cases = [
    (
      initial(),
      ResolvedAction::Call {
        target: 5,
        callee: CallTarget { function: 6, entry: 7, arity: 1 },
        args: vec![word32_words(23)],
      },
    ),
    (
      ControlState { control: Control::Ret(word32_words(29)), ..initial() },
      ResolvedAction::Idle,
    ),
    (
      ControlState {
        control: Control::Halted(word32_words(31)),
        continuation: vec![],
        remaining: 2,
      },
      ResolvedAction::Idle,
    ),
  ];
  for (state, action) in cases {
    let good = logical(&gate, &gate.inputs(&state, &action).unwrap());
    assert!(satisfies(&r1cs, &good));
    for word in 0..gate.output_count() {
      for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
        let mut bad = good.clone();
        bad[(gate.input_count() + word) * 128 + bit] ^= true;
        assert!(!satisfies(&r1cs, &bad));
      }
    }
    let mut bad = good;
    bad[gate.plan().k() - 1] = true;
    assert!(!satisfies(&r1cs, &bad));
  }
}

#[test]
fn control_count_emit_geometry_and_tables_depend_only_on_capacity() {
  use crate::sizing::CountingEmitter;
  use flock_prover::circuit::builder::ShapeBuilder;
  fn emit(b: &mut impl CircuitEmitter, gate: ControlStepGate) {
    let capacity = gate.capacity;
    let slot = ControlStepSlot::declare(b, gate);
    let mut state: Vec<_> =
      (0..capacity.state_words()).map(|_| b.input()).collect();
    for _ in 0..3 {
      let action: Vec<_> =
        (0..capacity.action_words()).map(|_| b.input()).collect();
      state = slot.step(b, &state, &action);
    }
    for word in state {
      b.publish(word);
    }
  }
  for capacity in
    [ControlCapacities { locals: 1, continuations: 0, arguments: 0 }, CAPACITY]
  {
    let gate = ControlStepGate::new(3, capacity).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, gate.clone());
    assert!(gate.plan.get().is_none(), "count pass allocated control table");
    let mut b = ShapeBuilder::new(3);
    emit(&mut b, gate.clone());
    let shape = b.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    let (registry, counts) = count.registry(3);
    assert_eq!(counts, shape.counts);
    assert_eq!(
      registry.types()[0].a_0.rows,
      shape.registry.types()[0].a_0.rows
    );
    assert_eq!(
      registry.types()[0].b_0.rows,
      shape.registry.types()[0].b_0.rows
    );
    assert_eq!(
      registry.types()[0].io_schema,
      shape.registry.types()[0].io_schema
    );
    let mut b = ShapeBuilder::new(3);
    emit(&mut b, ControlStepGate::new(3, capacity).unwrap());
    assert_eq!(shape.circuit.digest(), b.finish().unwrap().circuit.digest());
  }
}

#[test]
fn control_witness_overwrites_poison_and_all_absent_rows() {
  let gate = ControlStepGate::new(3, CAPACITY).unwrap();
  let row = ControlStepRow(
    gate
      .inputs(&initial(), &ResolvedAction::Return { value: word32_words(31) })
      .unwrap(),
  );
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(gate.plan(), &rows, fill_free, |dst| {
      gate.generate_witness_into(&rows, dst)
    });
  }
}
