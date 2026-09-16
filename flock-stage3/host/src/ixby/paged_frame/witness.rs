//! Fast, untrusted witness advice for valid rows. Invalid encodings fall back
//! to total Boolean-plan evaluation; no native verdict is used by a verifier.
use super::*;
use flock_prover::field::F128;

fn vector(word: F128, persistent: bool) -> Option<Vector> {
  if word.hi > 64 || word.lo >> 40 != 0 {
    return None;
  }
  let v = Vector { pointer: word.lo, count: word.hi as u8 };
  if v.count == 0 {
    return (v.pointer == 0).then_some(v);
  }
  let heap = v.pointer >> 36 == HEAP >> 36;
  let scratch = !persistent && v.pointer == SCRATCH;
  let offset = v.pointer & ((1 << 36) - 1);
  (heap || scratch).then_some(())?;
  (offset + u64::from(v.count) <= 1 << 36).then_some(v)
}

fn state(words: &[F128]) -> Option<FrameState> {
  let h = words[0];
  let phase = match h.lo as u8 {
    0 => Phase::Eval,
    1 => Phase::Return,
    2 => Phase::Halted,
    3 => Phase::Apply,
    4 => Phase::Copy,
    _ => return None,
  };
  let s = FrameState {
    phase,
    function: (h.lo >> 8) as u16,
    block: (h.lo >> 24) as u8,
    locals: (h.lo >> 32) as u8,
    depth: (h.lo >> 48) as u16,
    copy_index: h.hi as u8,
    copy_count: (h.hi >> 8) as u8,
    copy_base: (h.hi >> 16) as u8,
    copy_pointer: words[1].lo,
    value: [words[2], words[3]],
    arguments: vector(words[4], true)?,
  };
  (s.words() == words
    && s.function < 1024
    && s.locals <= 128
    && s.depth <= 1024)
    .then_some(())?;
  let framed = matches!(phase, Phase::Eval | Phase::Copy);
  if !framed && (s.function != 0 || s.block != 0 || s.locals != 0) {
    return None;
  }
  if framed && s.value != [F128::ZERO; 2] {
    return None;
  }
  if phase != Phase::Apply && s.arguments != Vector::default() {
    return None;
  }
  if phase == Phase::Halted && s.depth != 0 {
    return None;
  }
  if phase == Phase::Copy {
    if s.copy_index >= s.copy_count
      || u16::from(s.copy_base) + u16::from(s.copy_count) != u16::from(s.locals)
    {
      return None;
    }
    vector(F128::new(s.copy_pointer, u64::from(s.copy_count)), false)?;
  } else if s.copy_index != 0
    || s.copy_count != 0
    || s.copy_base != 0
    || s.copy_pointer != 0
  {
    return None;
  }
  Some(s)
}

fn action(words: &[F128], phase: Phase) -> Option<Action> {
  let h = words[0];
  let kind = match h.lo as u8 {
    1 => ActionKind::Bind,
    2 => ActionKind::Call,
    3 => ActionKind::TailCall,
    4 => ActionKind::Return,
    5 => ActionKind::Jump,
    6 => ActionKind::Append,
    7 => ActionKind::Apply,
    8 => ActionKind::TailApply,
    9 => ActionKind::ApplyReturn,
    10 => ActionKind::ApplyEnter,
    _ => return None,
  };
  let a = Action {
    kind,
    target: (h.lo >> 8) as u8,
    callee: (h.lo >> 16) as u16,
    entry: (h.lo >> 32) as u8,
    arity: (h.lo >> 40) as u8,
    arguments: vector(
      words[1],
      matches!(kind, ActionKind::Apply | ActionKind::TailApply),
    )?,
    value: [words[2], words[3]],
    rest: vector(words[4], true)?,
  };
  if a.words() != words || ((a.kind as u8 <= 8) != (phase == Phase::Eval)) {
    return None;
  }
  let targeted = matches!(
    kind,
    ActionKind::Bind
      | ActionKind::Call
      | ActionKind::Jump
      | ActionKind::Append
      | ActionKind::Apply
  );
  if !targeted && a.target != 0 {
    return None;
  }
  let entering = matches!(
    kind,
    ActionKind::Call | ActionKind::TailCall | ActionKind::ApplyEnter
  );
  if entering {
    if a.callee >= 1024 || a.arity > 64 || a.arguments.count != a.arity {
      return None;
    }
  } else if a.callee != 0 || a.entry != 0 || a.arity != 0 {
    return None;
  }
  let uses_args = entering
    || matches!(
      kind,
      ActionKind::Append | ActionKind::Apply | ActionKind::TailApply
    );
  if !uses_args && a.arguments != Vector::default() {
    return None;
  }
  let uses_value = matches!(
    kind,
    ActionKind::Bind
      | ActionKind::Return
      | ActionKind::Apply
      | ActionKind::TailApply
      | ActionKind::ApplyReturn
  );
  if !uses_value && a.value != [F128::ZERO; 2] {
    return None;
  }
  if kind != ActionKind::ApplyEnter && a.rest != Vector::default() {
    return None;
  }
  Some(a)
}

fn start_copy(next: &mut FrameState, source: Vector, base: u8) -> Option<()> {
  next.locals = base.checked_add(source.count)?;
  if next.locals > 128 {
    return None;
  }
  if source.count != 0 {
    next.phase = Phase::Copy;
    next.copy_pointer = source.pointer;
    next.copy_count = source.count;
    next.copy_base = base;
  }
  Some(())
}
fn continuation(state: FrameState, target: u8) -> [F128; 2] {
  [
    F128::new(
      1 | u64::from(state.function) << 8
        | u64::from(target) << 24
        | u64::from(state.locals) << 32,
      0,
    ),
    F128::ZERO,
  ]
}
fn local_address(depth: u16, slot: u8) -> u64 {
  LOCALS + (u64::from(depth) << 7) + u64::from(slot)
}
fn access(address: u64, write: bool, value: [F128; 2]) -> [F128; 4] {
  [F128::new(address, 0), F128::new(u64::from(write), 0), value[0], value[1]]
}

pub(super) fn evaluate(input: &[F128]) -> Option<Vec<F128>> {
  let before = state(&input[..5])?;
  let limits = input[12];
  if u64::from(before.locals) > limits.lo || u64::from(before.depth) > limits.hi
  {
    return None;
  }
  let reply = [input[10], input[11]];
  let mut next = FrameState::eval(0, 0, 0, before.depth);
  let mut accesses = [[F128::ZERO; 4]; 3];
  let control = match before.phase {
    Phase::Eval => 0,
    Phase::Return => 1,
    Phase::Apply => 3,
    Phase::Halted | Phase::Copy => 2,
  };
  if matches!(before.phase, Phase::Eval | Phase::Apply) {
    if reply != [F128::ZERO; 2] {
      return None;
    }
    let a = action(&input[5..10], before.phase)?;
    use ActionKind::*;
    match a.kind {
      Bind => {
        next = FrameState::eval(
          before.function,
          a.target,
          before.locals.checked_add(1)?,
          before.depth,
        );
        accesses[2] =
          access(local_address(before.depth, before.locals), true, a.value);
      },
      Call | TailCall | ApplyEnter => {
        let push =
          a.kind == Call || (a.kind == ApplyEnter && a.rest.count != 0);
        let depth = before.depth + u16::from(push);
        next = FrameState::eval(a.callee, a.entry, 0, depth);
        start_copy(&mut next, a.arguments, 0)?;
        if push {
          let value = if a.kind == Call {
            continuation(before, a.target)
          } else {
            [F128::new(2, 0), a.rest.word()]
          };
          accesses[1] =
            access(CONTINUATIONS + u64::from(before.depth), true, value);
        }
      },
      Return | ApplyReturn => {
        next.phase = Phase::Return;
        next.value = a.value;
      },
      Jump => {
        next = FrameState::eval(
          before.function,
          a.target,
          before.locals,
          before.depth,
        );
      },
      Append => {
        next = FrameState::eval(before.function, a.target, 0, before.depth);
        start_copy(&mut next, a.arguments, before.locals)?;
      },
      Apply | TailApply => {
        next.phase = Phase::Apply;
        next.value = a.value;
        next.arguments = a.arguments;
        if a.kind == Apply {
          next.depth += 1;
          accesses[1] = access(
            CONTINUATIONS + u64::from(before.depth),
            true,
            continuation(before, a.target),
          );
        }
      },
    }
  } else {
    if input[5..10] != [F128::ZERO; 5] {
      return None;
    }
    match before.phase {
      Phase::Copy => {
        next = before;
        accesses[0] = access(
          before.copy_pointer + u64::from(before.copy_index),
          false,
          reply,
        );
        accesses[2] = access(
          local_address(before.depth, before.copy_base + before.copy_index),
          true,
          reply,
        );
        next.copy_index += 1;
        if next.copy_index == next.copy_count {
          next.phase = Phase::Eval;
          next.copy_index = 0;
          next.copy_count = 0;
          next.copy_base = 0;
          next.copy_pointer = 0;
        }
      },
      Phase::Return => {
        if before.depth == 0 {
          if reply != [F128::ZERO; 2] {
            return None;
          }
          next.phase = Phase::Halted;
          next.value = before.value;
        } else {
          next.depth -= 1;
          accesses[0] =
            access(CONTINUATIONS + u64::from(next.depth), false, reply);
          match reply[0].lo as u8 {
            1 => {
              let function = (reply[0].lo >> 8) as u16;
              let block = (reply[0].lo >> 24) as u8;
              let locals = (reply[0].lo >> 32) as u8;
              let saved = FrameState::eval(function, block, locals, 0);
              if continuation(saved, block) != reply || function >= 1024 {
                return None;
              }
              next = FrameState::eval(
                function,
                block,
                locals.checked_add(1)?,
                next.depth,
              );
              accesses[2] =
                access(local_address(next.depth, locals), true, before.value);
            },
            2 => {
              if reply[0] != F128::new(2, 0) {
                return None;
              }
              next.phase = Phase::Apply;
              next.value = before.value;
              next.arguments = vector(reply[1], true)?;
              if next.arguments.count == 0 {
                return None;
              }
            },
            _ => return None,
          }
        }
      },
      Phase::Halted => {
        if reply != [F128::ZERO; 2] {
          return None;
        }
        next = before;
      },
      Phase::Eval | Phase::Apply => unreachable!(),
    }
  }
  if next.locals > 128
    || next.depth > 1024
    || u64::from(next.locals) > limits.lo
    || u64::from(next.depth) > limits.hi
  {
    return None;
  }
  Some(
    next
      .words()
      .into_iter()
      .chain(accesses.into_iter().flatten())
      .chain([F128::new(control, 0), F128::ZERO])
      .collect(),
  )
}
