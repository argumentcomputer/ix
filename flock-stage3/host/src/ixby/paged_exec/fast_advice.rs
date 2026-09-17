//! Direct native calculations for common advice operations. These functions
//! are not validators. They never participate in gate evaluation, circuit
//! checking or proof verification; those retain the complete Boolean plans.
use super::{CONTROL, FUEL, HEADER, MicroKind, STATE_WORDS};
use crate::ixby::{
  paged_code::{CONSTRUCTORS, CodeGateKind, FUNCTIONS, block_address},
  paged_frame::{ActionKind, LOCALS, SCRATCH},
};
use flock_prover::field::F128;

pub(super) fn micro(kind: MicroKind, input: &[F128]) -> Option<Vec<F128>> {
  if input.len() != kind.inputs() || input.first() != Some(&F128::ONE) {
    return None;
  }
  if let MicroKind::Collection(kind) = kind {
    return super::collection_native::evaluate(
      kind,
      &input[1..1 + STATE_WORDS],
      &input[1 + STATE_WORDS..],
    );
  }
  if matches!(
    kind,
    MicroKind::Parameters
      | MicroKind::Object(_)
      | MicroKind::Byte(_)
      | MicroKind::Collection(_)
  ) {
    return None;
  }
  let state = &input[1..1 + STATE_WORDS];
  let extra = &input[1 + STATE_WORDS..];
  let header = state[HEADER];
  let count = (header.lo >> 32) & 255;
  let index = (state[CONTROL].lo >> 8) & 255;
  let target = (header.hi >> 16) & 255;
  let other = (header.hi >> 24) & 255;
  let instruction = (header.lo >> 8) & 255;
  let operation = (header.lo >> 16) & 255;
  Some(match kind {
    MicroKind::Fetch => {
      let mut out = state.to_vec();
      out[HEADER] = extra[0];
      out[CONTROL] =
        F128::new(if (extra[0].lo >> 32) & 255 == 0 { 2 } else { 1 }, 0);
      out
    },
    MicroKind::ResolveRequest => vec![F128::new(index, 0), F128::new(count, 0)],
    MicroKind::ResolveFinish => {
      let mut out = state.to_vec();
      out[CONTROL] =
        F128::new(if index + 1 == count { 2 } else { 1 | (index + 1) << 8 }, 0);
      out.extend([
        F128::new(SCRATCH + index, 0),
        F128::ONE,
        extra[0],
        extra[1],
      ]);
      out
    },
    MicroKind::Scratch(n) => (0..n)
      .flat_map(|i| {
        let address = if u64::try_from(i).unwrap() < count {
          SCRATCH + u64::try_from(i).unwrap()
        } else {
          0
        };
        [F128::new(address, 0), F128::ZERO, extra[2 * i], extra[2 * i + 1]]
      })
      .collect(),
    MicroKind::NumericAction | MicroKind::ControlAction => {
      let value = [extra[0], extra[1]];
      let zero = [F128::ZERO; 2];
      let (kind, destination, result) = if kind == MicroKind::NumericAction
        || (instruction == 0 && operation == 0)
      {
        (ActionKind::Bind, target, value)
      } else {
        match instruction {
          1 => (ActionKind::Return, 0, value),
          6 if value[1] == F128::ZERO => (ActionKind::Jump, target, zero),
          6 => {
            let n = (u128::from(value[1].lo) | u128::from(value[1].hi) << 64)
              .wrapping_sub(1);
            (
              ActionKind::Bind,
              other,
              [
                F128::new(8, 0),
                F128::new(
                  u64::try_from(n & u128::from(u64::MAX)).unwrap(),
                  u64::try_from(n >> 64).unwrap(),
                ),
              ],
            )
          },
          7 => (
            ActionKind::Jump,
            if value[1].lo & 1 != 0 { target } else { other },
            zero,
          ),
          _ => return None,
        }
      };
      vec![
        F128::new(kind as u64 | destination << 8, 0),
        F128::ZERO,
        result[0],
        result[1],
        F128::ZERO,
      ]
    },
    MicroKind::CallReference | MicroKind::CallAction => {
      let reference =
        if (instruction == 0 && operation == 6) || instruction == 3 {
          (state[0].lo >> 8) & 65535
        } else {
          header.hi & 65535
        };
      if kind == MicroKind::CallReference {
        vec![F128::new(reference, 0)]
      } else {
        let arity = extra[0].lo & 255;
        let entry = (extra[0].lo >> 8) & 255;
        let tail = instruction == 2 || instruction == 3;
        let action = if tail { ActionKind::TailCall } else { ActionKind::Call };
        vec![
          F128::new(
            action as u64
              | if tail { 0 } else { target << 8 }
              | reference << 16
              | entry << 32
              | arity << 40,
            0,
          ),
          F128::new(if arity == 0 { 0 } else { SCRATCH }, arity),
          F128::ZERO,
          F128::ZERO,
          F128::ZERO,
        ]
      }
    },
    MicroKind::Resume => Vec::new(),
    MicroKind::FrameRequest => {
      state[..5].iter().copied().chain([state[FUEL]]).collect()
    },
    MicroKind::Complete => {
      let mut out = state.to_vec();
      out[..6].copy_from_slice(extra);
      out[CONTROL] = F128::ZERO;
      out[HEADER] = F128::ZERO;
      out[10..].fill(F128::ZERO);
      out
    },
    MicroKind::Parameters
    | MicroKind::Object(_)
    | MicroKind::Byte(_)
    | MicroKind::Collection(_) => {
      unreachable!()
    },
  })
}

pub(super) fn code(kind: CodeGateKind, input: &[F128]) -> Option<Vec<F128>> {
  let width = match kind {
    CodeGateKind::Operand => 8,
    CodeGateKind::Alternative => 6,
    _ => 4,
  };
  if input.len() != width || input[0] != F128::ONE {
    return None;
  }
  let address = match kind {
    CodeGateKind::Function => FUNCTIONS + (input[1].lo & 1023),
    CodeGateKind::Constructor => CONSTRUCTORS + 3 * (input[1].lo & 255) + 2,
    _ => {
      let frame = input[1].lo;
      let base = block_address(
        u16::try_from((frame >> 8) & 65535).unwrap(),
        u8::try_from((frame >> 24) & 255).unwrap(),
      );
      base
        + match kind {
          CodeGateKind::Operand => (input[2].lo & 255) + 1,
          CodeGateKind::Alternative => (input[2].lo & 255) + 128,
          _ => 0,
        }
    },
  };
  let at = if matches!(kind, CodeGateKind::Operand | CodeGateKind::Alternative)
  {
    4
  } else {
    2
  };
  let mut out =
    vec![F128::new(address, 0), F128::ZERO, input[at], input[at + 1]];
  if kind == CodeGateKind::Operand {
    let local = input[4] == F128::ZERO;
    let address =
      if local { LOCALS + (input[1].lo >> 48) * 128 + input[5].lo } else { 0 };
    out.extend([F128::new(address, 0), F128::ZERO, input[6], input[7]]);
    out.extend(if local { [input[6], input[7]] } else { [input[4], input[5]] });
  }
  Some(out)
}
