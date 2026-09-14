//! Independent checked-integer model used only by tests. It neither calls the
//! Boolean plan nor participates in proving/verification or source admission.
use super::{grammar::*, *};
use anyhow::{Result, bail, ensure};
use flock_prover::field::F128;

fn integer(word: F128) -> u128 {
  u128::from(word.lo) | (u128::from(word.hi) << 64)
}
fn phase(value: u8) -> Result<Phase> {
  Ok(match value {
    0 => Phase::Start,
    1 => Phase::Constructor,
    2 => Phase::FunctionCount,
    3 => Phase::Function,
    4 => Phase::Block,
    5 => Phase::Operation,
    6 => Phase::Operand,
    7 => Phase::OperandCount,
    8 => Phase::Target,
    9 => Phase::Projection,
    10 => Phase::FunctionIndex,
    11 => Phase::AlternativeCount,
    12 => Phase::Alternative,
    13 => Phase::Scalar,
    14 => Phase::Natural,
    15 => Phase::StringCount,
    16 => Phase::StringPayload,
    17 => Phase::BytesCount,
    18 => Phase::BytesPayload,
    19 => Phase::Value,
    20 => Phase::Done,
    21 => Phase::FinishBlock,
    22 => Phase::FinishValue,
    23 => Phase::NextArgument,
    _ => bail!("invalid control phase"),
  })
}
fn sub(a: u128, z: u128) -> Result<u128> {
  a.checked_sub(z).ok_or_else(|| anyhow::anyhow!("counter underflow"))
}
fn add(a: u128, z: u128) -> Result<u128> {
  a.checked_add(z).ok_or_else(|| anyhow::anyhow!("counter overflow"))
}

pub(super) fn step(
  kind: GrammarKind,
  input: &[F128; GRAMMAR_INPUTS],
) -> Result<[F128; GRAMMAR_STATE_WORDS]> {
  let mut s: [u128; GRAMMAR_STATE_WORDS] = input[..GRAMMAR_STATE_WORDS]
    .iter()
    .copied()
    .map(integer)
    .collect::<Vec<_>>()
    .try_into()
    .unwrap();
  let f = input[GRAMMAR_STATE_WORDS + 4..GRAMMAR_INPUTS - 1]
    .iter()
    .copied()
    .map(integer)
    .collect::<Vec<_>>();
  let mut control = s[1].to_le_bytes();
  ensure!(control[5..].iter().all(|b| *b == 0), "reserved control bits");
  let p = phase(control[0])?;
  ensure!((p as u8) <= Phase::Done as u8, "unresolved phase");
  for byte in &control[1..4] {
    phase(*byte)?;
  }
  ensure!(control[4] <= 2, "target count");
  if kind == GrammarKind::Program {
    ensure!(p != Phase::Value, "program value phase");
  } else {
    ensure!(!(1..=12).contains(&(p as u8)), "transport program phase");
  }
  let cursor = input[0];
  let next = input[GRAMMAR_INPUTS - 1];
  ensure!(cursor.lo <= cursor.hi && next.lo <= cursor.hi, "cursor bounds");
  let header = kind == GrammarKind::Program && p == Phase::Start;
  ensure!(next.hi == if header { 0 } else { cursor.hi }, "file identity");
  if p == Phase::Done {
    ensure!(next == cursor, "padding cursor");
  } else {
    ensure!(next.lo > cursor.lo, "strict progress");
  }
  let next_offset = next.lo;
  let delta = next.lo.saturating_sub(cursor.lo) as u128;
  let mut event = GrammarEvent::Done;
  let mut bounds = [0u128; 3];
  let mut used = 6;
  let mut next_phase = p;
  match p {
    Phase::Start => {
      ensure!(cursor.lo == 0, "initial cursor");
      for (index, value) in s.iter().enumerate().skip(1) {
        let context = kind != GrammarKind::Program
          && (index == CTORS
            || index == FUNCTIONS
            || (LIMITS..=ENTRY_ARITY).contains(&index)
            || index == FUEL);
        ensure!(context || *value == 0, "initial state");
      }
      match kind {
        GrammarKind::Program => {
          event = GrammarEvent::Header;
          used = 13;
          bounds[0] = cursor.hi.into();
          s[LIMITS..LIMITS + 10].copy_from_slice(&f[..10]);
          s[FUEL] = f[10];
          s[ENTRY] = f[11];
          s[CTORS] = f[12];
          s[CTORS_LEFT] = f[12];
          next_phase =
            if f[12] == 0 { Phase::FunctionCount } else { Phase::Constructor };
        },
        GrammarKind::Input | GrammarKind::Output => {
          let input = kind == GrammarKind::Input;
          event = GrammarEvent::Record(if input {
            RecordKind::Input
          } else {
            RecordKind::Output
          });
          bounds = if input {
            [s[LIMITS + 4], s[ENTRY_ARITY], s[LIMITS + 6]]
          } else {
            [s[LIMITS + 6], 0, 0]
          };
          ensure!(f[0] <= s[LIMITS + 6], "root budget");
          s[PENDING] = f[0];
          next_phase = Phase::FinishValue;
        },
      }
    },
    Phase::Constructor => {
      event = GrammarEvent::Record(RecordKind::Constructor);
      bounds[0] = s[LIMITS + 4];
      s[CTORS_LEFT] = sub(s[CTORS_LEFT], 1)?;
      next_phase = if s[CTORS_LEFT] == 0 {
        Phase::FunctionCount
      } else {
        Phase::Constructor
      };
    },
    Phase::FunctionCount => {
      event = GrammarEvent::Record(RecordKind::Count);
      bounds[0] = s[LIMITS];
      ensure!(s[ENTRY] < f[0], "entry index");
      s[FUNCTIONS] = f[0];
      s[FUNCTIONS_LEFT] = f[0];
      next_phase = Phase::Function;
    },
    Phase::Function => {
      event = GrammarEvent::Record(RecordKind::Function);
      bounds = [s[LIMITS + 4], s[LIMITS + 3], s[LIMITS + 2]];
      s[FUNCTIONS_LEFT] = sub(s[FUNCTIONS_LEFT], 1)?;
      if s[FUNCTION_INDEX] == s[ENTRY] {
        s[ENTRY_ARITY] = f[0];
      }
      s[FUNCTION_INDEX] = add(s[FUNCTION_INDEX], 1)?;
      s[ARITY] = f[0];
      s[BLOCKS] = f[2];
      s[BLOCKS_LEFT] = f[2];
      ensure!(f[2] != 0, "empty function");
      next_phase = Phase::Block;
    },
    Phase::Block => {
      event = GrammarEvent::Record(RecordKind::Block);
      bounds[0] = s[LIMITS + 3];
      s[BLOCKS_LEFT] = sub(s[BLOCKS_LEFT], 1)?;
      s[LOCALS] = f[0];
      control[1] = Phase::FinishBlock as u8;
      control[2] = Phase::FinishBlock as u8;
      control[3] = 0;
      control[4] = 0;
      next_phase = match f[1] {
        0 => {
          control[2] = Phase::Target as u8;
          control[4] = 1;
          Phase::Operation
        },
        1 => Phase::Operand,
        2 => Phase::FunctionIndex,
        3 => Phase::OperandCount,
        4 => {
          control[1] = Phase::OperandCount as u8;
          Phase::Operand
        },
        5 => {
          control[1] = Phase::AlternativeCount as u8;
          Phase::Operand
        },
        6 | 7 => {
          control[1] = Phase::Target as u8;
          control[4] = 2;
          Phase::Operand
        },
        _ => bail!("instruction tag"),
      };
    },
    Phase::Operation => {
      event = GrammarEvent::Record(RecordKind::Operation);
      bounds = [s[LIMITS + 4], s[CTORS], s[FUNCTIONS]];
      next_phase = match f[0] {
        0 | 3 | 7 => {
          control[1] = match f[0] {
            0 => Phase::Target,
            3 => Phase::Projection,
            _ => Phase::OperandCount,
          } as u8;
          Phase::Operand
        },
        1 | 2 | 4 | 5 | 6 => {
          s[ITEMS] = f[3];
          control[1] = Phase::NextArgument as u8;
          if f[3] == 0 { phase(control[2])? } else { Phase::Operand }
        },
        _ => bail!("operation tag"),
      };
    },
    Phase::FunctionIndex => {
      event = GrammarEvent::Record(RecordKind::Index);
      bounds[0] = s[FUNCTIONS];
      next_phase = Phase::OperandCount;
    },
    Phase::OperandCount => {
      event = GrammarEvent::Record(RecordKind::Count);
      bounds[0] = s[LIMITS + 4];
      s[ITEMS] = f[0];
      control[1] = Phase::NextArgument as u8;
      next_phase = if f[0] == 0 { phase(control[2])? } else { Phase::Operand };
    },
    Phase::Operand => {
      event = GrammarEvent::Record(RecordKind::Operand);
      bounds[0] = s[LOCALS];
      ensure!(f[0] < 3, "operand tag");
      let after = if control[1] == Phase::NextArgument as u8 {
        s[ITEMS] = sub(s[ITEMS], 1)?;
        if s[ITEMS] != 0 { Phase::Operand } else { phase(control[2])? }
      } else {
        phase(control[1])?
      };
      next_phase = if f[0] == 1 {
        control[3] = after as u8;
        Phase::Scalar
      } else {
        after
      };
    },
    Phase::Projection => {
      event = GrammarEvent::Record(RecordKind::Metadata);
      next_phase = Phase::Target;
    },
    Phase::Target => {
      event = GrammarEvent::Record(RecordKind::Index);
      bounds[0] = s[BLOCKS];
      ensure!((1..=2).contains(&control[4]), "target underflow");
      control[4] -= 1;
      next_phase =
        if control[4] == 0 { Phase::FinishBlock } else { Phase::Target };
    },
    Phase::AlternativeCount => {
      event = GrammarEvent::Record(RecordKind::Count);
      bounds[0] = s[LIMITS + 1];
      s[ITEMS] = f[0];
      next_phase =
        if f[0] == 0 { Phase::FinishBlock } else { Phase::Alternative };
    },
    Phase::Alternative => {
      event = GrammarEvent::Record(RecordKind::Alternative);
      bounds = [s[CTORS], s[BLOCKS], 0];
      s[ITEMS] = sub(s[ITEMS], 1)?;
      next_phase =
        if s[ITEMS] == 0 { Phase::FinishBlock } else { Phase::Alternative };
    },
    Phase::Scalar => {
      event = GrammarEvent::Record(RecordKind::Scalar);
      next_phase = match f[0] {
        0 => Phase::Natural,
        1 => Phase::StringCount,
        2..=5 => phase(control[3])?,
        6 => Phase::BytesCount,
        _ => bail!("scalar tag"),
      };
    },
    Phase::Natural => {
      event = GrammarEvent::Natural;
      used = 1;
      ensure!(
        (1..=4096u128.div_ceil(7)).contains(&f[0]) && delta == f[0],
        "natural extent"
      );
      next_phase = phase(control[3])?;
    },
    Phase::StringCount | Phase::BytesCount => {
      event = GrammarEvent::Record(RecordKind::Count);
      let string = p == Phase::StringCount;
      bounds[0] = s[LIMITS + if string { 8 } else { 9 }];
      s[PAYLOAD] = f[0];
      next_phase = if f[0] == 0 {
        phase(control[3])?
      } else if string {
        Phase::StringPayload
      } else {
        Phase::BytesPayload
      };
    },
    Phase::StringPayload | Phase::BytesPayload => {
      event = if p == Phase::StringPayload {
        GrammarEvent::StringPayload
      } else {
        GrammarEvent::BytesPayload
      };
      used = 0;
      ensure!(delta == s[PAYLOAD], "payload extent");
      s[PAYLOAD] = 0;
      next_phase = phase(control[3])?;
    },
    Phase::Value => {
      event = GrammarEvent::Record(RecordKind::Value);
      ensure!(f[0] < 4, "value tag");
      s[SEEN] = add(s[SEEN], 1)?;
      bounds = [s[LIMITS + 4], s[FUNCTIONS], sub(s[LIMITS + 6], s[SEEN])?];
      s[PENDING] = add(sub(s[PENDING], 1)?, f[5])?;
      ensure!(
        add(s[PENDING], s[SEEN])? <= s[LIMITS + 6],
        "pending child budget"
      );
      next_phase = if f[0] == 0 {
        control[3] = Phase::FinishValue as u8;
        Phase::Scalar
      } else {
        Phase::FinishValue
      };
    },
    Phase::Done => {
      used = 0;
    },
    _ => unreachable!(),
  }
  ensure!(
    integer(input[GRAMMAR_STATE_WORDS]) == u128::from(event.tag()),
    "typed event"
  );
  ensure!(
    input[GRAMMAR_STATE_WORDS + 1..GRAMMAR_STATE_WORDS + 4]
      .iter()
      .copied()
      .map(integer)
      .eq(bounds),
    "decoder bounds"
  );
  ensure!(f[used..].iter().all(|v| *v == 0), "unused event fields");
  if next_phase == Phase::FinishBlock {
    next_phase = if s[BLOCKS_LEFT] != 0 {
      Phase::Block
    } else if s[FUNCTIONS_LEFT] != 0 {
      Phase::Function
    } else {
      Phase::Done
    };
  }
  if next_phase == Phase::FinishValue {
    next_phase = if s[PENDING] != 0 { Phase::Value } else { Phase::Done };
  }
  ensure!(next_phase as u8 <= Phase::Done as u8, "unresolved next phase");
  if next_phase == Phase::Done {
    ensure!(next_offset == cursor.hi, "exact EOF");
    for index in
      [FUNCTIONS_LEFT, BLOCKS_LEFT, CTORS_LEFT, ITEMS, PAYLOAD, PENDING]
    {
      ensure!(s[index] == 0, "unfinished work");
    }
  }
  control[0] = next_phase as u8;
  s[1] = u128::from_le_bytes(control);
  s[0] = u128::from(next_offset) | (u128::from(cursor.hi) << 64);
  Ok(s.map(record_tests::word))
}
