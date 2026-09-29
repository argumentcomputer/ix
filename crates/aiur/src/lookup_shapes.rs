// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Structural checks required by zero-padded function lookup messages.
//! Inputs and outputs have no separators in the message.
//! Their boundaries must agree at every constrained call and public claim.

use multi_stark::p3_field::PrimeField64;

use crate::{
  G,
  bytecode::{Block, Ctrl, Op, Toplevel},
  function_channel,
};

fn canonical_size(size: usize) -> bool {
  u64::try_from(size).is_ok_and(|size| size < G::ORDER_U64)
}

#[derive(Clone, Copy)]
enum ReturnArity {
  NoReturns,
  Exact(usize),
  Inconsistent,
}

impl ReturnArity {
  fn merge(self, other: Self) -> Self {
    match (self, other) {
      (Self::NoReturns, arity) | (arity, Self::NoReturns) => arity,
      (Self::Exact(a), Self::Exact(b)) if a == b => Self::Exact(a),
      _ => Self::Inconsistent,
    }
  }

  fn accepts(self, size: usize) -> bool {
    match self {
      Self::NoReturns => true,
      Self::Exact(arity) => arity == size,
      Self::Inconsistent => false,
    }
  }
}

/// Cached for public constrained entries in the system's immutable program.
pub(crate) struct ClaimShape {
  inputs: usize,
  outputs: ReturnArity,
}

impl Block {
  fn return_arity(&self) -> ReturnArity {
    match &self.ctrl {
      Ctrl::Return(_, values) => ReturnArity::Exact(values.len()),
      Ctrl::Yield(..) => ReturnArity::NoReturns,
      Ctrl::Match(_, branches, fallback) => branches
        .values()
        .chain(fallback.iter().map(Box::as_ref))
        .fold(ReturnArity::NoReturns, |arity, block| {
          arity.merge(block.return_arity())
        }),
      Ctrl::MatchContinue(_, branches, fallback, _, _, _, continuation) => {
        branches
          .values()
          .chain(fallback.iter().map(Box::as_ref))
          .fold(continuation.return_arity(), |arity, block| {
            arity.merge(block.return_arity())
          })
      },
    }
  }

  /// Every function return, including an early return from a continuation
  /// arm, has this output arity. Yields return to their own continuation.
  /// Kept as an independent recursive reference for the cached summary.
  #[cfg(test)]
  pub(crate) fn returns_have_size(&self, size: usize) -> bool {
    match &self.ctrl {
      Ctrl::Return(_, values) => values.len() == size,
      Ctrl::Yield(..) => true,
      Ctrl::Match(_, branches, fallback) => {
        branches.values().all(|block| block.returns_have_size(size))
          && fallback.as_ref().is_none_or(|block| block.returns_have_size(size))
      },
      Ctrl::MatchContinue(_, branches, fallback, _, _, _, continuation) => {
        branches.values().all(|block| block.returns_have_size(size))
          && fallback.as_ref().is_none_or(|block| block.returns_have_size(size))
          && continuation.returns_have_size(size)
      },
    }
  }

  fn check_lookup_shapes(
    &self,
    program: &Toplevel,
    return_arities: &[ReturnArity],
    yield_size: Option<usize>,
  ) -> Result<(), &'static str> {
    for op in &self.ops {
      match op {
        Op::Call(index, inputs, outputs, false) => {
          let Some(callee) = program.functions.get(*index) else {
            return Err("constrained call refers to a missing function");
          };
          if !callee.constrained {
            return Err("constrained call refers to an unconstrained function");
          }
          if callee.layout.input_size != inputs.len() {
            return Err("constrained call input arity differs from its callee");
          }
          if !return_arities[*index].accepts(*outputs) {
            return Err(
              "constrained call output arity differs from its callee",
            );
          }
        },
        Op::Store(values) if !canonical_size(values.len()) => {
          return Err("memory width is not a canonical field element");
        },
        Op::Load(size, _) if !canonical_size(*size) => {
          return Err("memory width is not a canonical field element");
        },
        _ => {},
      }
    }
    match &self.ctrl {
      Ctrl::Return(..) => {},
      Ctrl::Yield(_, values) => {
        if yield_size != Some(values.len()) {
          return Err("yield arity differs from its enclosing continuation");
        }
      },
      Ctrl::Match(_, branches, fallback) => {
        for block in branches.values() {
          block.check_lookup_shapes(program, return_arities, yield_size)?;
        }
        if let Some(block) = fallback {
          block.check_lookup_shapes(program, return_arities, yield_size)?;
        }
      },
      Ctrl::MatchContinue(_, branches, fallback, size, _, _, continuation) => {
        for block in branches.values() {
          block.check_lookup_shapes(program, return_arities, Some(*size))?;
        }
        if let Some(block) = fallback {
          block.check_lookup_shapes(program, return_arities, Some(*size))?;
        }
        continuation.check_lookup_shapes(
          program,
          return_arities,
          yield_size,
        )?;
      },
    }
    Ok(())
  }
}

impl Toplevel {
  /// Check the static boundaries of all constrained function messages.
  /// This does not check value indices, layouts or arithmetic constraints.
  pub fn validate_lookup_shapes(&self) -> Result<(), &'static str> {
    self.checked_claim_shapes().map(|_| ())
  }

  pub(crate) fn checked_claim_shapes(
    &self,
  ) -> Result<Vec<Option<ClaimShape>>, &'static str> {
    if !canonical_size(self.functions.len()) {
      return Err("function index domain exceeds the field characteristic");
    }
    if self.memory_sizes.iter().any(|&size| !canonical_size(size)) {
      return Err("memory width is not a canonical field element");
    }
    // Summarize each constrained body once, then reuse the result at every
    // call site and public verification. Yields do not return from functions.
    let return_arities: Vec<_> = self
      .functions
      .iter()
      .map(|function| {
        if function.constrained {
          function.body.return_arity()
        } else {
          ReturnArity::NoReturns
        }
      })
      .collect();
    for function in &self.functions {
      if function.constrained {
        function.body.check_lookup_shapes(self, &return_arities, None)?;
      }
    }
    Ok(
      self
        .functions
        .iter()
        .zip(return_arities)
        .map(|(function, outputs)| {
          (function.entry && function.constrained).then_some(ClaimShape {
            inputs: function.layout.input_size,
            outputs,
          })
        })
        .collect(),
    )
  }
}

pub(crate) fn valid_claim_shape(
  shapes: &[Option<ClaimShape>],
  claim: &[G],
) -> bool {
  let [channel, index, arguments @ ..] = claim else {
    return false;
  };
  if *channel != function_channel() {
    return false;
  }
  let Ok(index) = usize::try_from(index.as_canonical_u64()) else {
    return false;
  };
  let Some(Some(shape)) = shapes.get(index) else {
    return false;
  };
  arguments
    .len()
    .checked_sub(shape.inputs)
    .is_some_and(|outputs| shape.outputs.accepts(outputs))
}
