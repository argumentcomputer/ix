//! Prepare the interpreter's next action once, including skipped instructions,
//! flattened hot bytecode ops, and fixed host calls. Original PCs remain the
//! keys for errors and trace replay.
use crate::{
  bytecode::{Binary as BinOp, CheckedProgram, Instruction},
  field::FieldBackend,
  hints::HintSite,
  host::{
    self, DirectHintKind, DirectMapKind, MapCalls, RegisterHint, RegisterMap,
  },
};
use std::sync::Arc;

pub(crate) struct DispatchProgram<F> {
  pub(crate) functions: Vec<Vec<Dispatch<F>>>,
  pub(crate) reg_lists: Vec<u32>,
}

pub(crate) struct Dispatch<F> {
  pub(crate) pc: usize,
  pub(crate) next: usize,
  pub(crate) instructions: u64,
  pub(crate) action: Action<F>,
}

#[derive(Clone, Copy)]
pub(crate) enum DirectMapOp {
  FromField { src: u32, dst: u32 },
  RangePair { a: u32, b: u32 },
  RawXor { a: u32, b: u32, dst: u32 },
  RawAnd { a: u32, b: u32, dst: u32 },
  RawOr { a: u32, b: u32, dst: u32 },
  RawLt { a: u32, b: u32, dst: u32 },
  RawAdd { a: u32, b: u32, dst0: u32, dst1: u32 },
  RawSub { a: u32, b: u32, dst0: u32, dst1: u32 },
  RawMul { a: u32, b: u32, dst0: u32, dst1: u32 },
  RawXorSplit4 { a: u32, b: u32, dst0: u32, dst1: u32 },
  RawXorSplit7 { a: u32, b: u32, dst0: u32, dst1: u32 },
  RawSumByte { src: u32, dst: u32 },
  RawBitDecomp { src: u32, dst_off: u32 },
}

impl DirectMapOp {
  #[inline(always)]
  #[allow(clippy::cast_possible_truncation)] // Bounds are checked before casting.
  pub(crate) fn eval<B: FieldBackend>(
    self,
    field: B,
    regs: &mut [B::Element],
    reg_lists: &[u32],
    counts: &mut [u64],
  ) -> Result<(), String> {
    macro_rules! pair {
      ($a:expr, $b:expr) => {{
        let va = field.to_u64(regs[$a as usize]);
        let vb = field.to_u64(regs[$b as usize]);
        if (va | vb) > 255 {
          return Err("no table entry for map input".into());
        }
        (va, vb, ((va << 8) | vb) as usize)
      }};
    }
    match self {
      Self::FromField { src, dst } => {
        let val = regs[src as usize];
        let row = field.to_u64(val);
        if row >= 256 {
          return Err("no table entry for map input".into());
        }
        host::bump(counts, row as usize)?;
        regs[dst as usize] = val;
      },
      Self::RangePair { a, b } => {
        let (_, _, row) = pair!(a, b);
        host::bump(counts, row)?;
      },
      Self::RawXor { a, b, dst } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        regs[dst as usize] = field.from_u64(va ^ vb);
      },
      Self::RawAnd { a, b, dst } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        regs[dst as usize] = field.from_u64(va & vb);
      },
      Self::RawOr { a, b, dst } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        regs[dst as usize] = field.from_u64(va | vb);
      },
      Self::RawLt { a, b, dst } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        regs[dst as usize] = field.from_u64(u64::from(va < vb));
      },
      Self::RawAdd { a, b, dst0, dst1 } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        let sum = va + vb;
        regs[dst0 as usize] = field.from_u64(sum & 255);
        regs[dst1 as usize] = field.from_u64(sum >> 8);
      },
      Self::RawSub { a, b, dst0, dst1 } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        regs[dst0 as usize] = field.from_u64(va.wrapping_sub(vb) & 255);
        regs[dst1 as usize] = field.from_u64(u64::from(va < vb));
      },
      Self::RawMul { a, b, dst0, dst1 } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        let product = va * vb;
        regs[dst0 as usize] = field.from_u64(product & 255);
        regs[dst1 as usize] = field.from_u64(product >> 8);
      },
      Self::RawXorSplit4 { a, b, dst0, dst1 } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        let xor = va ^ vb;
        regs[dst0 as usize] = field.from_u64(xor >> 4);
        regs[dst1 as usize] = field.from_u64((xor & 15) << 4);
      },
      Self::RawXorSplit7 { a, b, dst0, dst1 } => {
        let (va, vb, row) = pair!(a, b);
        host::bump(counts, row)?;
        let xor = va ^ vb;
        regs[dst0 as usize] = field.from_u64(xor >> 7);
        regs[dst1 as usize] = field.from_u64((xor & 127) << 1);
      },
      Self::RawSumByte { src, dst } => {
        let row = field.to_u64(regs[src as usize]);
        if row >= 768 {
          return Err("no table entry for map input".into());
        }
        host::bump(counts, row as usize)?;
        regs[dst as usize] = field.from_u64(row & 255);
      },
      Self::RawBitDecomp { src, dst_off } => {
        let row = field.to_u64(regs[src as usize]);
        if row >= 256 {
          return Err("no table entry for map input".into());
        }
        host::bump(counts, row as usize)?;
        let dsts = &reg_lists[dst_off as usize..dst_off as usize + 8];
        for (i, &dst) in dsts.iter().enumerate() {
          regs[dst as usize] = field.from_u64((row >> i) & 1);
        }
      },
    }
    Ok(())
  }
}

#[inline(always)]
#[allow(clippy::cast_possible_truncation)]
pub(crate) fn eval_direct_hint<B: FieldBackend>(
  kind: DirectHintKind,
  field: B,
  regs: &mut [B::Element],
  reg_slice: &[u32],
) -> Result<(), String> {
  #[inline(always)]
  fn read_u32_word<B: FieldBackend>(
    field: B,
    regs: &[B::Element],
    idxs: &[u32],
  ) -> Result<u32, String> {
    let b0 = field.to_u64(regs[idxs[0] as usize]);
    let b1 = field.to_u64(regs[idxs[1] as usize]);
    let b2 = field.to_u64(regs[idxs[2] as usize]);
    let b3 = field.to_u64(regs[idxs[3] as usize]);
    if (b0 | b1 | b2 | b3) > 255 {
      return Err("non-byte u32 sum operand".into());
    }
    Ok(u32::from_le_bytes([b0 as u8, b1 as u8, b2 as u8, b3 as u8]))
  }

  #[inline(always)]
  fn write_u32_bytes<B: FieldBackend>(
    field: B,
    regs: &mut [B::Element],
    dsts: &[u32],
    word: u32,
  ) {
    let bytes = word.to_le_bytes();
    regs[dsts[0] as usize] = field.from_u64(u64::from(bytes[0]));
    regs[dsts[1] as usize] = field.from_u64(u64::from(bytes[1]));
    regs[dsts[2] as usize] = field.from_u64(u64::from(bytes[2]));
    regs[dsts[3] as usize] = field.from_u64(u64::from(bytes[3]));
  }

  match kind {
    DirectHintKind::U32Bytes => {
      let word = field.to_u64(regs[reg_slice[0] as usize]) as u32;
      write_u32_bytes(field, regs, &reg_slice[1..5], word);
    },
    DirectHintKind::U32Sub => {
      let a = field.to_u64(regs[reg_slice[0] as usize]) as u32;
      let b = field.to_u64(regs[reg_slice[1] as usize]) as u32;
      write_u32_bytes(field, regs, &reg_slice[2..6], a.wrapping_sub(b));
    },
    DirectHintKind::U32Add => {
      let w0 = read_u32_word(field, regs, &reg_slice[0..4])?;
      let w1 = read_u32_word(field, regs, &reg_slice[4..8])?;
      write_u32_bytes(field, regs, &reg_slice[8..12], w0.wrapping_add(w1));
    },
    DirectHintKind::U32Add3 => {
      let w0 = read_u32_word(field, regs, &reg_slice[0..4])?;
      let w1 = read_u32_word(field, regs, &reg_slice[4..8])?;
      let w2 = read_u32_word(field, regs, &reg_slice[8..12])?;
      write_u32_bytes(
        field,
        regs,
        &reg_slice[12..16],
        w0.wrapping_add(w1).wrapping_add(w2),
      );
    },
    DirectHintKind::U32Lt => {
      let a = field.to_u64(regs[reg_slice[0] as usize]) as u32;
      let b = field.to_u64(regs[reg_slice[1] as usize]) as u32;
      write_u32_bytes(field, regs, &reg_slice[2..6], a);
      write_u32_bytes(field, regs, &reg_slice[6..10], a.wrapping_sub(b));
      write_u32_bytes(field, regs, &reg_slice[10..14], b);
    },
    DirectHintKind::BytesLe => {
      let bytes = field.to_u64(regs[reg_slice[0] as usize]).to_le_bytes();
      for (i, &byte) in bytes.iter().enumerate() {
        regs[reg_slice[1 + i] as usize] = field.from_u64(u64::from(byte));
      }
    },
  }
  Ok(())
}

pub(crate) enum Action<F> {
  Literal {
    dest: u32,
    value: F,
  },
  Copy1 {
    dest: u32,
    src: u32,
  },
  CopyDisjoint {
    dest_off: u32,
    src_off: u32,
    len: u32,
  },
  Neg {
    dest: u32,
    src: u32,
  },
  Add {
    dest: u32,
    left: u32,
    right: u32,
  },
  Sub {
    dest: u32,
    left: u32,
    right: u32,
  },
  Mul {
    dest: u32,
    left: u32,
    right: u32,
  },
  DivConst {
    dest: u32,
    left: u32,
    inv: F,
  },
  DivDyn {
    dest: u32,
    left: u32,
    right: u32,
  },
  PtrEq {
    dest: u32,
    left: u32,
    right: u32,
  },
  BranchEq1 {
    reg: u32,
    otherwise_cursor: u32,
    value: F,
  },
  Jump {
    target_cursor: u32,
  },
  Load {
    pointer: u32,
    memory_type: u32,
    dest_off: u32,
    dest_len: u32,
  },
  Store {
    dest: u32,
    memory_type: u32,
    value_off: u32,
    value_len: u32,
  },
  Call {
    callee: u32,
    args_off: u32,
    args_len: u32,
    dest_off: u32,
    dest_len: u32,
  },
  Return {
    vals_off: u32,
    vals_len: u32,
  },
  ReturnPlan {
    plan: usize,
  },
  DirectMap {
    function: u32,
    op: DirectMapOp,
  },
  DirectHint {
    kind: DirectHintKind,
    regs_off: u32,
  },
  Map {
    function: usize,
    call: Arc<RegisterMap<F>>,
  },
  Hint {
    call: Arc<RegisterHint<F>>,
  },
  Bytecode {
    memory_type: usize,
    branch: usize,
  },
}

fn push_regs(arena: &mut Vec<u32>, regs: &[usize]) -> Option<(u32, u32)> {
  let off = u32::try_from(arena.len()).ok()?;
  let len = u32::try_from(regs.len()).ok()?;
  if arena
    .len()
    .checked_add(regs.len())
    .is_none_or(|end| end > u32::MAX as usize)
  {
    return None;
  }
  let start = arena.len();
  arena.reserve(regs.len());
  for &reg in regs {
    let Ok(r) = u32::try_from(reg) else {
      arena.truncate(start);
      return None;
    };
    arena.push(r);
  }
  Some((off, len))
}

fn direct_map_op(
  kind: DirectMapKind,
  args: &[usize],
  dest: &[usize],
  arena: &mut Vec<u32>,
) -> Option<DirectMapOp> {
  let reg = |i: usize, slice: &[usize]| u32::try_from(*slice.get(i)?).ok();
  match kind {
    DirectMapKind::FromField if args.len() == 1 && dest.len() == 1 => {
      Some(DirectMapOp::FromField { src: reg(0, args)?, dst: reg(0, dest)? })
    },
    DirectMapKind::RangePair if args.len() == 2 && dest.is_empty() => {
      Some(DirectMapOp::RangePair { a: reg(0, args)?, b: reg(1, args)? })
    },
    DirectMapKind::RawXor if args.len() == 2 && dest.len() == 1 => {
      Some(DirectMapOp::RawXor {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst: reg(0, dest)?,
      })
    },
    DirectMapKind::RawAnd if args.len() == 2 && dest.len() == 1 => {
      Some(DirectMapOp::RawAnd {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst: reg(0, dest)?,
      })
    },
    DirectMapKind::RawOr if args.len() == 2 && dest.len() == 1 => {
      Some(DirectMapOp::RawOr {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst: reg(0, dest)?,
      })
    },
    DirectMapKind::RawLt if args.len() == 2 && dest.len() == 1 => {
      Some(DirectMapOp::RawLt {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst: reg(0, dest)?,
      })
    },
    DirectMapKind::RawAdd if args.len() == 2 && dest.len() == 2 => {
      Some(DirectMapOp::RawAdd {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst0: reg(0, dest)?,
        dst1: reg(1, dest)?,
      })
    },
    DirectMapKind::RawSub if args.len() == 2 && dest.len() == 2 => {
      Some(DirectMapOp::RawSub {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst0: reg(0, dest)?,
        dst1: reg(1, dest)?,
      })
    },
    DirectMapKind::RawMul if args.len() == 2 && dest.len() == 2 => {
      Some(DirectMapOp::RawMul {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst0: reg(0, dest)?,
        dst1: reg(1, dest)?,
      })
    },
    DirectMapKind::RawXorSplit4 if args.len() == 2 && dest.len() == 2 => {
      Some(DirectMapOp::RawXorSplit4 {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst0: reg(0, dest)?,
        dst1: reg(1, dest)?,
      })
    },
    DirectMapKind::RawXorSplit7 if args.len() == 2 && dest.len() == 2 => {
      Some(DirectMapOp::RawXorSplit7 {
        a: reg(0, args)?,
        b: reg(1, args)?,
        dst0: reg(0, dest)?,
        dst1: reg(1, dest)?,
      })
    },
    DirectMapKind::RawSumByte if args.len() == 1 && dest.len() == 1 => {
      Some(DirectMapOp::RawSumByte { src: reg(0, args)?, dst: reg(0, dest)? })
    },
    DirectMapKind::RawBitDecomp if args.len() == 1 && dest.len() == 8 => {
      let src = reg(0, args)?;
      let (dst_off, _) = push_regs(arena, dest)?;
      Some(DirectMapOp::RawBitDecomp { src, dst_off })
    },
    _ => None,
  }
}

fn direct_hint_action<F>(
  kind: DirectHintKind,
  key: &[usize],
  dest: &[usize],
  arena: &mut Vec<u32>,
) -> Option<Action<F>> {
  let (expected_in, expected_out) = match kind {
    DirectHintKind::U32Bytes => (1, 4),
    DirectHintKind::U32Sub => (2, 4),
    DirectHintKind::U32Add => (8, 4),
    DirectHintKind::U32Add3 => (12, 4),
    DirectHintKind::U32Lt => (2, 12),
    DirectHintKind::BytesLe => (1, 8),
  };
  if key.len() != expected_in || dest.len() != expected_out {
    return None;
  }
  let start = arena.len();
  let off = u32::try_from(start).ok()?;
  if start
    .checked_add(key.len() + dest.len())
    .is_none_or(|end| end > u32::MAX as usize)
  {
    return None;
  }
  arena.reserve(key.len() + dest.len());
  for &reg in key.iter().chain(dest) {
    let Ok(r) = u32::try_from(reg) else {
      arena.truncate(start);
      return None;
    };
    arena.push(r);
  }
  Some(Action::DirectHint { kind, regs_off: off })
}

pub(crate) fn prepare<B: FieldBackend>(
  program: &CheckedProgram<B>,
  hints: &[Vec<Option<HintSite<B::Element>>>],
  maps: Option<&[MapCalls<B::Element>]>,
) -> DispatchProgram<B::Element> {
  let mut reg_lists = Vec::new();
  let num_functions = program.program.functions.len();
  let functions = program
    .steps
    .iter()
    .enumerate()
    .map(|(function, steps)| {
      // Different entries into a skipped prefix can have different
      // instruction counts. Keep each reachable entry, not just each
      // eventual operation, and resolve its successors to dense indices.
      let code = &program.execution_functions[function].code;
      let returns = &program.returns[function];
      let mut reachable = vec![false; steps.len()];
      let mut pending = vec![0];
      while let Some(pc) = pending.pop() {
        if std::mem::replace(&mut reachable[pc], true) {
          continue;
        }
        let step = &steps[pc];
        if returns[step.pc].is_some() {
          continue;
        }
        match &code[step.pc] {
          Instruction::Ret { .. } | Instruction::Fail { .. } => (),
          Instruction::Jump { target } => pending.push(*target),
          Instruction::Branch { tests, otherwise } => {
            if !tests.is_empty() {
              pending.push(*otherwise);
            }
            pending.push(step.pc + 1);
          },
          _ => pending.push(step.pc + 1),
        }
      }
      let pcs: Vec<_> = reachable
        .iter()
        .enumerate()
        .filter_map(|(pc, &reachable)| reachable.then_some(pc))
        .collect();
      let mut entries = vec![usize::MAX; steps.len()];
      for (index, &pc) in pcs.iter().enumerate() {
        entries[pc] = index;
      }
      pcs
        .iter()
        .map(|&pc| {
          let step = &steps[pc];
          if let Some(ret) = &returns[step.pc] {
            let action = match push_regs(&mut reg_lists, &ret.values) {
              Some((vals_off, vals_len)) => {
                Action::Return { vals_off, vals_len }
              },
              None => Action::ReturnPlan { plan: step.pc },
            };
            return Dispatch {
              pc: ret.pc,
              next: usize::MAX,
              instructions: step.skipped + ret.instructions,
              action,
            };
          }
          let op = &code[step.pc];
          let action = match op {
            Instruction::Literal { dest, value } => u32::try_from(*dest)
              .ok()
              .map(|dest| Action::Literal { dest, value: *value }),
            Instruction::Copy { dest, source }
              if dest.len() == source.len() =>
            {
              if let ([d], [s]) = (dest.as_slice(), source.as_slice()) {
                u32::try_from(*d)
                  .ok()
                  .zip(u32::try_from(*s).ok())
                  .map(|(dest, src)| Action::Copy1 { dest, src })
              } else if !dest
                .iter()
                .enumerate()
                .any(|(i, d)| source[i + 1..].contains(d))
              {
                let start = reg_lists.len();
                match (
                  push_regs(&mut reg_lists, dest),
                  push_regs(&mut reg_lists, source),
                ) {
                  (Some((dest_off, len)), Some((src_off, _))) => {
                    Some(Action::CopyDisjoint { dest_off, src_off, len })
                  },
                  _ => {
                    reg_lists.truncate(start);
                    None
                  },
                }
              } else {
                None
              }
            },
            Instruction::Neg { dest, source } => u32::try_from(*dest)
              .ok()
              .zip(u32::try_from(*source).ok())
              .map(|(dest, src)| Action::Neg { dest, src }),
            Instruction::Binary { dest, operator, left, right } => {
              match (
                u32::try_from(*dest).ok(),
                u32::try_from(*left).ok(),
                u32::try_from(*right).ok(),
              ) {
                (Some(dest), Some(left), Some(right)) => match operator {
                  BinOp::Add => Some(Action::Add { dest, left, right }),
                  BinOp::Sub => Some(Action::Sub { dest, left, right }),
                  BinOp::Mul => Some(Action::Mul { dest, left, right }),
                  BinOp::Div => {
                    if let Some(inv) =
                      program.division_inverses[function][step.pc]
                    {
                      Some(Action::DivConst { dest, left, inv })
                    } else {
                      Some(Action::DivDyn { dest, left, right })
                    }
                  },
                },
                _ => None,
              }
            },
            Instruction::PtrEq { dest, left, right } => match (
              u32::try_from(*dest).ok(),
              u32::try_from(*left).ok(),
              u32::try_from(*right).ok(),
            ) {
              (Some(dest), Some(left), Some(right)) => {
                Some(Action::PtrEq { dest, left, right })
              },
              _ => None,
            },
            Instruction::Branch { tests, otherwise } if tests.len() == 1 => {
              let (reg, value) = tests[0];
              u32::try_from(reg)
                .ok()
                .zip(u32::try_from(entries[*otherwise]).ok())
                .map(|(reg, otherwise_cursor)| Action::BranchEq1 {
                  reg,
                  otherwise_cursor,
                  value,
                })
            },
            Instruction::Jump { target } => u32::try_from(entries[*target])
              .ok()
              .map(|target_cursor| Action::Jump { target_cursor }),
            Instruction::Load { pointer, dest, .. } => {
              let start = reg_lists.len();
              match (
                u32::try_from(*pointer).ok(),
                u32::try_from(step.memory_type).ok(),
                push_regs(&mut reg_lists, dest),
              ) {
                (
                  Some(pointer),
                  Some(memory_type),
                  Some((dest_off, dest_len)),
                ) => Some(Action::Load {
                  pointer,
                  memory_type,
                  dest_off,
                  dest_len,
                }),
                _ => {
                  reg_lists.truncate(start);
                  None
                },
              }
            },
            Instruction::Store { value, dest, .. } => {
              let start = reg_lists.len();
              match (
                u32::try_from(*dest).ok(),
                u32::try_from(step.memory_type).ok(),
                push_regs(&mut reg_lists, value),
              ) {
                (
                  Some(dest),
                  Some(memory_type),
                  Some((value_off, value_len)),
                ) => Some(Action::Store {
                  dest,
                  memory_type,
                  value_off,
                  value_len,
                }),
                _ => {
                  reg_lists.truncate(start);
                  None
                },
              }
            },
            Instruction::Call { function: callee, args, dest } => {
              if let Some(bound) =
                maps.and_then(|maps| maps[function][step.pc].as_ref())
              {
                if let Some(kind) = bound.direct
                  && let Some(function_id) = u32::try_from(*callee).ok()
                  && let Some(op) =
                    direct_map_op(kind, args, dest, &mut reg_lists)
                {
                  Some(Action::DirectMap { function: function_id, op })
                } else {
                  Some(Action::Map {
                    function: *callee,
                    call: bound.dynamic.clone(),
                  })
                }
              } else if *callee < num_functions {
                let start = reg_lists.len();
                match (
                  u32::try_from(*callee).ok(),
                  push_regs(&mut reg_lists, args),
                  push_regs(&mut reg_lists, dest),
                ) {
                  (
                    Some(callee),
                    Some((args_off, args_len)),
                    Some((dest_off, dest_len)),
                  ) => Some(Action::Call {
                    callee,
                    args_off,
                    args_len,
                    dest_off,
                    dest_len,
                  }),
                  _ => {
                    reg_lists.truncate(start);
                    None
                  },
                }
              } else {
                None
              }
            },
            Instruction::Hint { key, dest, .. } => {
              hints[function][step.pc].as_ref().and_then(|site| {
                if let Some(kind) = site.direct
                  && let Some(action) =
                    direct_hint_action(kind, key, dest, &mut reg_lists)
                {
                  Some(action)
                } else {
                  site
                    .registers
                    .as_ref()
                    .map(|call| Action::Hint { call: call.clone() })
                }
              })
            },
            _ => None,
          }
          .unwrap_or(Action::Bytecode {
            memory_type: step.memory_type,
            branch: match op {
              Instruction::Branch { otherwise, .. } => entries[*otherwise],
              Instruction::Jump { target } => entries[*target],
              _ => usize::MAX,
            },
          });
          Dispatch {
            pc: step.pc,
            next: entries.get(step.pc + 1).copied().unwrap_or(usize::MAX),
            instructions: step.skipped + 1,
            action,
          }
        })
        .collect()
    })
    .collect();
  DispatchProgram { functions, reg_lists }
}
