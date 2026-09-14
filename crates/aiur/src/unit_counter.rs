// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Check unit-counter relations in the actual constrained bytecode.
//!
//! This independently mirrors the compiler's UnitCounter pass. Constants
//! and affine arithmetic are followed; loads, hints and unrelated calls
//! produce unknown values. Every constrained self-call shifts the same
//! input by one, or each returning path shifts one self-call output by
//! one. Unsupported control flow and excessive depth keep ordinary ranks.
//!
//! A provider cycle would therefore have at least the field characteristic
//! many edges. The verified lookup-consumer bound excludes every such simple
//! cycle. Static component ordering still handles edges between components.

use multi_stark::p3_field::PrimeCharacteristicRing;

use crate::{
  G,
  bytecode::{Block, Ctrl, Function, Op},
};

const MAX_DEPTH: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Affine {
  base: Option<usize>,
  offset: G,
}

impl Affine {
  fn constant(offset: G) -> Self {
    Self { base: None, offset }
  }

  fn variable(base: usize) -> Self {
    Self { base: Some(base), offset: G::ZERO }
  }
}

fn add(a: Option<Affine>, b: Option<Affine>) -> Option<Affine> {
  let (a, b) = (a?, b?);
  let base = match (a.base, b.base) {
    (None, base) | (base, None) => base,
    _ => return None,
  };
  Some(Affine { base, offset: a.offset + b.offset })
}

fn sub(a: Option<Affine>, b: Option<Affine>) -> Option<Affine> {
  let (a, b) = (a?, b?);
  b.base
    .is_none()
    .then_some(Affine { base: a.base, offset: a.offset - b.offset })
}

fn mul(a: Option<Affine>, b: Option<Affine>) -> Option<Affine> {
  let (a, b) = (a?, b?);
  if a.base.is_none() && a.offset == G::ONE {
    Some(b)
  } else if b.base.is_none() && b.offset == G::ONE {
    Some(a)
  } else if a.base.is_none() && b.base.is_none() {
    Some(Affine::constant(a.offset * b.offset))
  } else {
    None
  }
}

#[derive(Clone, Copy)]
enum Mode {
  Input,
  Output,
}

#[derive(Clone, Copy)]
struct Candidate {
  mode: Mode,
  column: usize,
  step: G,
}

#[derive(Clone)]
struct State {
  values: Vec<Option<Affine>>,
  recursive_output: Option<usize>,
}

fn output_count(op: &Op) -> usize {
  match op {
    Op::Const(..)
    | Op::Add(..)
    | Op::Sub(..)
    | Op::Mul(..)
    | Op::EqZero(..)
    | Op::Store(..)
    | Op::U8ShiftLeft(..)
    | Op::U8ShiftRight(..)
    | Op::U8Xor(..)
    | Op::U8And(..)
    | Op::U8Or(..)
    | Op::U8LessThan(..)
    | Op::U32LessThan(..)
    | Op::UnconstrainedGInverse(..)
    | Op::U32ToField(..) => 1,
    Op::Call(_, _, n, _) | Op::Load(n, _) | Op::IORead(_, _, n) => *n,
    Op::IOGetInfo(..)
    | Op::U8Add(..)
    | Op::U8Mul(..)
    | Op::U8Sub(..)
    | Op::U8XorSplit7(..)
    | Op::U8XorSplit4(..)
    | Op::UnconstrainedBigUintDivMod(..) => 2,
    Op::U8BitDecomposition(..) | Op::UnconstrainedGToBytes(..) => 8,
    Op::UnconstrainedU32Add(..) | Op::UnconstrainedU32Add3(..) => 5,
    Op::AssertEq(..)
    | Op::IOSetInfo(..)
    | Op::IOWrite(..)
    | Op::Debug(..)
    | Op::U8RangeCheck(..) => 0,
  }
}

impl State {
  fn get(&self, i: usize) -> Option<Affine> {
    self.values.get(i).copied().flatten()
  }

  fn apply(&mut self, function: usize, candidate: Candidate, op: &Op) -> bool {
    let value = match *op {
      Op::Const(x) => Some(Affine::constant(x)),
      Op::Add(a, b) => add(self.get(a), self.get(b)),
      Op::Sub(a, b) => sub(self.get(a), self.get(b)),
      Op::Mul(a, b) => mul(self.get(a), self.get(b)),
      _ => {
        if let Op::Call(callee, args, outputs, false) = op
          && *callee == function
        {
          match candidate.mode {
            Mode::Input => {
              let Some(&arg) = args.get(candidate.column) else {
                return false;
              };
              if self.get(arg)
                != Some(Affine {
                  base: Some(candidate.column),
                  offset: candidate.step,
                })
              {
                return false;
              }
            },
            Mode::Output => {
              if self.recursive_output.is_some() || candidate.column >= *outputs
              {
                return false;
              }
              let marker = self.values.len() + candidate.column;
              self.recursive_output = Some(marker);
              self.values.extend((0..*outputs).map(|i| {
                (i == candidate.column).then_some(Affine::variable(marker))
              }));
              return true;
            },
          }
        }
        self.values.extend(std::iter::repeat_n(None, output_count(op)));
        return true;
      },
    };
    self.values.push(value);
    true
  }
}

fn check(
  depth: usize,
  function: usize,
  candidate: Candidate,
  mut state: State,
  block: &Block,
) -> bool {
  if depth == 0
    || !block.ops.iter().all(|op| state.apply(function, candidate, op))
  {
    return false;
  }
  match &block.ctrl {
    Ctrl::Return(_, outputs) => {
      match (candidate.mode, state.recursive_output) {
        (Mode::Input, _) | (Mode::Output, None) => true,
        (Mode::Output, Some(marker)) => {
          outputs.get(candidate.column).is_some_and(|&i| {
            state.get(i)
              == Some(Affine { base: Some(marker), offset: candidate.step })
          })
        },
      }
    },
    Ctrl::Match(_, cases, fallback) => {
      cases.values().all(|branch| {
        check(depth - 1, function, candidate, state.clone(), branch)
      }) && fallback.as_deref().is_none_or(|branch| {
        check(depth - 1, function, candidate, state, branch)
      })
    },
    Ctrl::Yield(..) | Ctrl::MatchContinue(..) => false,
  }
}

fn result_size(depth: usize, block: &Block) -> Option<usize> {
  if depth == 0 {
    return None;
  }
  match &block.ctrl {
    Ctrl::Return(_, output) => Some(output.len()),
    Ctrl::Match(_, cases, fallback) => cases
      .values()
      .find_map(|b| result_size(depth - 1, b))
      .or_else(|| fallback.as_deref().and_then(|b| result_size(depth - 1, b))),
    _ => None,
  }
}

pub(crate) fn has_unit_counter(index: usize, function: &Function) -> bool {
  for mode in [Mode::Input, Mode::Output] {
    let columns = match mode {
      Mode::Input => function.layout.input_size,
      Mode::Output => result_size(MAX_DEPTH, &function.body).unwrap_or(0),
    };
    for column in 0..columns {
      for step in [G::ONE, -G::ONE] {
        let state = State {
          values: (0..function.layout.input_size)
            .map(|i| Some(Affine::variable(i)))
            .collect(),
          recursive_output: None,
        };
        if check(
          MAX_DEPTH,
          index,
          Candidate { mode, column, step },
          state,
          &function.body,
        ) {
          return true;
        }
      }
    }
  }
  false
}

#[cfg(test)]
#[path = "unit_counter_tests.rs"]
mod tests;
