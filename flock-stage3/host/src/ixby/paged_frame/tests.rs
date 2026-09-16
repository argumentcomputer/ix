use super::*;
use crate::ixby::bits::{fill_words, read_words};
use flock_prover::circuit::builder::GateType;

fn checked(gate: &FrameGate, input: &[F128]) -> Vec<F128> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| fill_words(input, bits));
  let output = read_words(&row, 13, 19);
  let table = gate.r1cs();
  row.resize(table.n(), false);
  assert!(table.satisfies(&row));
  let mut native = Vec::new();
  gate.eval(input, &(), &mut native);
  assert_eq!(native, output);
  output
}
fn input(
  state: FrameState,
  action: Option<Action>,
  reply: [F128; 2],
) -> Vec<F128> {
  state
    .words()
    .into_iter()
    .chain(action.map_or([F128::ZERO; 5], Action::words))
    .chain(reply)
    .chain([F128::new(128, 1024)])
    .collect()
}
fn value(n: u64) -> [F128; 2] {
  [F128::new(8, 0), F128::new(n, 1)]
}
fn accepted(gate: &FrameGate, input: &[F128]) -> Vec<F128> {
  let out = checked(gate, input);
  assert_eq!(out[18], F128::ZERO);
  out
}
fn rejected(gate: &FrameGate, input: &[F128]) {
  assert_eq!(checked(gate, input)[18], F128::ONE);
}
#[test]
fn bind_call_copy_return_and_terminal_use_actual_frame_addresses() {
  let gate = FrameGate::new(3).unwrap();
  let mut action = Action::new(ActionKind::Bind);
  action.target = 42;
  action.value = value(11);
  let start = FrameState::eval(680, 184, 72, 647);
  let out = accepted(&gate, &input(start, Some(action), [F128::ZERO; 2]));
  assert_eq!(&out[..5], &FrameState::eval(680, 42, 73, 647).words());
  assert_eq!(
    &out[13..17],
    &[
      F128::new(LOCALS + (647 << 7) + 72, 0),
      F128::ONE,
      action.value[0],
      action.value[1]
    ]
  );
  assert_eq!(out[17], F128::ZERO);
  action = Action::new(ActionKind::Call);
  action.target = 43;
  action.callee = 671;
  action.entry = 180;
  action.arity = 2;
  action.arguments = Vector { pointer: SCRATCH, count: 2 };
  let out = accepted(&gate, &input(start, Some(action), [F128::ZERO; 2]));
  let mut copying = FrameState::eval(671, 180, 2, 648);
  copying.phase = Phase::Copy;
  copying.copy_count = 2;
  copying.copy_pointer = SCRATCH;
  assert_eq!(&out[..5], &copying.words());
  let saved = F128::new(1 | (680 << 8) | (43 << 24) | (72 << 32), 0);
  assert_eq!(
    &out[9..13],
    &[F128::new(CONTINUATIONS + 647, 0), F128::ONE, saved, F128::ZERO]
  );
  let out = accepted(&gate, &input(copying, None, value(12)));
  assert_eq!(
    &out[5..9],
    &[F128::new(SCRATCH, 0), F128::ZERO, value(12)[0], value(12)[1]]
  );
  assert_eq!(
    &out[13..17],
    &[F128::new(LOCALS + (648 << 7), 0), F128::ONE, value(12)[0], value(12)[1]]
  );
  assert_eq!(out[17], F128::new(2, 0));
  copying.copy_index = 1;
  assert_eq!(&out[..5], &copying.words());
  let out = accepted(&gate, &input(copying, None, value(13)));
  assert_eq!(&out[..5], &FrameState::eval(671, 180, 2, 648).words());
  let mut returning = FrameState::eval(0, 0, 0, 648);
  returning.phase = Phase::Return;
  returning.value = value(14);
  let out = accepted(&gate, &input(returning, None, [saved, F128::ZERO]));
  assert_eq!(&out[..5], &FrameState::eval(680, 43, 73, 647).words());
  assert_eq!(
    &out[5..9],
    &[F128::new(CONTINUATIONS + 647, 0), F128::ZERO, saved, F128::ZERO]
  );
  assert_eq!(
    &out[13..17],
    &[
      F128::new(LOCALS + (647 << 7) + 72, 0),
      F128::ONE,
      value(14)[0],
      value(14)[1]
    ]
  );
  returning.depth = 0;
  let out = accepted(&gate, &input(returning, None, [F128::ZERO; 2]));
  returning.phase = Phase::Halted;
  assert_eq!(&out[..5], &returning.words());
  assert_eq!(out[17], F128::ONE);
  let out = accepted(&gate, &input(returning, None, [F128::ZERO; 2]));
  assert_eq!(&out[..5], &returning.words());
  assert_eq!(out[17], F128::new(2, 0));
}

#[test]
fn apply_continuations_restore_arguments_and_caller_at_distinct_depths() {
  let gate = FrameGate::new(3).unwrap();
  let start = FrameState::eval(680, 184, 73, 647);
  let mut action = Action::new(ActionKind::Apply);
  action.target = 42;
  action.value = value(10);
  action.arguments = Vector { pointer: HEAP + 123, count: 2 };
  let out = accepted(&gate, &input(start, Some(action), [F128::ZERO; 2]));
  let saved = [out[11], out[12]];
  let mut applying = FrameState::eval(0, 0, 0, 648);
  applying.phase = Phase::Apply;
  applying.value = action.value;
  applying.arguments = action.arguments;
  assert_eq!(&out[..5], &applying.words());
  action = Action::new(ActionKind::ApplyEnter);
  action.callee = 671;
  action.entry = 180;
  action.arity = 2;
  action.arguments = Vector { pointer: SCRATCH, count: 2 };
  action.rest = Vector { pointer: HEAP + 456, count: 1 };
  let out = accepted(&gate, &input(applying, Some(action), [F128::ZERO; 2]));
  let mut copying = FrameState::eval(671, 180, 2, 649);
  copying.phase = Phase::Copy;
  copying.copy_count = 2;
  copying.copy_pointer = SCRATCH;
  assert_eq!(&out[..5], &copying.words());
  assert_eq!(
    &out[9..13],
    &[
      F128::new(CONTINUATIONS + 648, 0),
      F128::ONE,
      F128::new(2, 0),
      action.rest.word()
    ]
  );
  let mut returning = FrameState::eval(0, 0, 0, 649);
  returning.phase = Phase::Return;
  returning.value = value(999);
  let out = accepted(
    &gate,
    &input(returning, None, [F128::new(2, 0), action.rest.word()]),
  );
  applying.value = returning.value;
  applying.arguments = action.rest;
  assert_eq!(&out[..5], &applying.words());
  let mut action = Action::new(ActionKind::ApplyReturn);
  action.value = [F128::new(5, 0), F128::ZERO];
  let out = accepted(&gate, &input(applying, Some(action), [F128::ZERO; 2]));
  returning.depth = 648;
  returning.value = action.value;
  assert_eq!(&out[..5], &returning.words());
  let out = accepted(&gate, &input(returning, None, saved));
  assert_eq!(&out[..5], &FrameState::eval(680, 42, 74, 647).words());
  // With no rest arguments ApplyEnter must not push a continuation.
  let mut action = Action::new(ActionKind::ApplyEnter);
  action.callee = 1023;
  action.entry = 255;
  let out = accepted(&gate, &input(applying, Some(action), [F128::ZERO; 2]));
  assert_eq!(&out[..5], &FrameState::eval(1023, 255, 0, 648).words());
  assert_eq!(&out[9..13], &[F128::ZERO; 4]);
}

#[test]
fn transfers_enforce_full_width_bounds_and_exact_copy_completion() {
  let gate = FrameGate::new(3).unwrap();
  for (depth, locals, count) in [(0, 0, 0), (647, 73, 9), (1024, 64, 64)] {
    let start = FrameState::eval(1023, 255, locals, depth);
    let mut a = Action::new(ActionKind::Append);
    a.target = 184;
    a.arguments =
      Vector { pointer: if count == 0 { 0 } else { HEAP + (1 << 35) }, count };
    let out = accepted(&gate, &input(start, Some(a), [F128::ZERO; 2]));
    let mut expected = FrameState::eval(1023, 184, locals + count, depth);
    if count != 0 {
      expected.phase = Phase::Copy;
      expected.copy_pointer = a.arguments.pointer;
      expected.copy_count = count;
      expected.copy_base = locals;
    }
    assert_eq!(&out[..5], &expected.words());
    for index in 0..count {
      expected.copy_index = index;
      let out =
        accepted(&gate, &input(expected, None, value(u64::from(index))));
      assert_eq!(
        out[13].lo,
        LOCALS + (u64::from(depth) << 7) + u64::from(locals + index)
      );
      if index + 1 == count {
        assert_eq!(
          &out[..5],
          &FrameState::eval(1023, 184, locals + count, depth).words()
        );
      } else {
        let mut next = expected;
        next.copy_index += 1;
        assert_eq!(&out[..5], &next.words());
      }
    }
    a = Action::new(ActionKind::TailCall);
    a.callee = 680;
    a.entry = 184;
    let out = accepted(&gate, &input(start, Some(a), [F128::ZERO; 2]));
    assert_eq!(&out[..5], &FrameState::eval(680, 184, 0, depth).words());
  }
  let mut a = Action::new(ActionKind::Bind);
  a.value = value(1);
  rejected(
    &gate,
    &input(FrameState::eval(0, 0, 128, 0), Some(a), [F128::ZERO; 2]),
  );
  a = Action::new(ActionKind::Call);
  rejected(
    &gate,
    &input(FrameState::eval(0, 0, 0, 1024), Some(a), [F128::ZERO; 2]),
  );
  a = Action::new(ActionKind::Append);
  a.arguments = Vector { pointer: HEAP, count: 64 };
  rejected(
    &gate,
    &input(FrameState::eval(0, 0, 65, 0), Some(a), [F128::ZERO; 2]),
  );
  for vector in [
    Vector { pointer: LOCALS, count: 1 },
    Vector { pointer: SCRATCH + 1, count: 1 },
    Vector { pointer: HEAP, count: 65 },
    Vector { pointer: HEAP + (1 << 36) - 1, count: 2 },
    Vector { pointer: 1 << 40, count: 1 },
    Vector { pointer: HEAP, count: 0 },
  ] {
    a.arguments = vector;
    rejected(
      &gate,
      &input(FrameState::eval(0, 0, 0, 0), Some(a), [F128::ZERO; 2]),
    );
  }
}

#[test]
fn state_padding_limits_and_saved_continuation_fields_are_constrained() {
  let gate = FrameGate::new(3).unwrap();
  let mut action = Action::new(ActionKind::Bind);
  action.value = value(77);
  let honest =
    input(FrameState::eval(680, 184, 72, 647), Some(action), [F128::ZERO; 2]);
  for (at, lo, hi) in [
    (0, 1 << 40, 0),
    (0, 1 << 18, 0),
    (0, 0, 1 << 24),
    (1, 0, 1),
    (2, 1, 0),
    (4, 0, 1),
    (5, 0, 1),
    (6, 0, 1),
    (9, 0, 1),
    (10, 1, 0),
    (11, 0, 1),
  ] {
    let mut changed = honest.clone();
    changed[at] += F128::new(lo, hi);
    rejected(&gate, &changed);
  }
  for limits in [F128::new(72, 1024), F128::new(128, 646)] {
    let mut changed = honest.clone();
    changed[12] = limits;
    rejected(&gate, &changed);
  }
  let mut returning = FrameState::eval(0, 0, 0, 648);
  returning.phase = Phase::Return;
  returning.value = value(88);
  let saved = F128::new(1 | (680 << 8) | (42 << 24) | (73 << 32), 0);
  let honest = input(returning, None, [saved, F128::ZERO]);
  for bit in 40..128 {
    let mut changed = honest.clone();
    if bit < 64 {
      changed[10].lo ^= 1 << bit;
    } else {
      changed[10].hi ^= 1 << (bit - 64);
    }
    rejected(&gate, &changed);
  }
  for reply in [
    [F128::new(3, 0), F128::ZERO],
    [F128::new(2, 0), F128::ZERO],
    [F128::new(2, 0), Vector { pointer: SCRATCH, count: 1 }.word()],
    [saved, F128::ONE],
  ] {
    rejected(&gate, &input(returning, None, reply));
  }
  // Every input bit gets an independent native / Boolean differential check.
  for at in 0..13 {
    for bit in 0..128 {
      let mut changed = honest.clone();
      if bit < 64 {
        changed[at].lo ^= 1 << bit;
      } else {
        changed[at].hi ^= 1 << (bit - 64);
      }
      checked(&gate, &changed);
    }
  }
}
