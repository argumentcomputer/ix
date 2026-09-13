// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Logical scopes and selector reads required by circuit construction.

use crate::bytecode::{Block, Ctrl, Op, Toplevel};

fn indices_in_scope(available: usize, indices: &[usize]) -> bool {
  indices.iter().all(|&index| index < available)
}

fn word_in_scope(available: usize, indices: &[usize]) -> bool {
  indices.len() == 4 && indices_in_scope(available, indices)
}

impl Op {
  /// Includes virtual outputs such as carries, which use no fresh column.
  pub(crate) fn output_size(&self) -> usize {
    match self {
      Self::Const(..)
      | Self::Add(..)
      | Self::Sub(..)
      | Self::Mul(..)
      | Self::EqZero(..)
      | Self::Store(..)
      | Self::U8ShiftLeft(..)
      | Self::U8ShiftRight(..)
      | Self::U8Xor(..)
      | Self::U8And(..)
      | Self::U8Or(..)
      | Self::U8LessThan(..)
      | Self::U32LessThan(..)
      | Self::UnconstrainedGInverse(..)
      | Self::U32ToField(..) => 1,
      Self::Call(_, _, size, _)
      | Self::Load(size, _)
      | Self::IORead(_, _, size) => *size,
      Self::AssertEq(..)
      | Self::IOSetInfo(..)
      | Self::IOWrite(..)
      | Self::Debug(..)
      | Self::U8RangeCheck(..) => 0,
      Self::IOGetInfo(..)
      | Self::U8Add(..)
      | Self::U8Mul(..)
      | Self::U8Sub(..)
      | Self::U8XorSplit7(..)
      | Self::U8XorSplit4(..)
      | Self::UnconstrainedBigUintDivMod(..) => 2,
      Self::U8BitDecomposition(..) | Self::UnconstrainedGToBytes(..) => 8,
      Self::UnconstrainedU32Add(..) | Self::UnconstrainedU32Add3(..) => 5,
    }
  }

  /// Check reads in the incoming scope, before allocating any outputs.
  /// Advice and I/O operands are not consumed while building constraints.
  pub(crate) fn emission_inputs(&self, available: usize) -> bool {
    match self {
      Self::Add(a, b)
      | Self::Sub(a, b)
      | Self::Mul(a, b)
      | Self::U8Xor(a, b)
      | Self::U8Add(a, b)
      | Self::U8Mul(a, b)
      | Self::U8Sub(a, b)
      | Self::U8And(a, b)
      | Self::U8Or(a, b)
      | Self::U8LessThan(a, b)
      | Self::U32LessThan(a, b)
      | Self::U8XorSplit7(a, b)
      | Self::U8XorSplit4(a, b)
      | Self::U8RangeCheck(a, b) => *a < available && *b < available,
      Self::EqZero(index)
      | Self::Load(_, index)
      | Self::U8BitDecomposition(index)
      | Self::U8ShiftLeft(index)
      | Self::U8ShiftRight(index) => *index < available,
      Self::Call(_, indices, _, false) | Self::Store(indices) => {
        indices_in_scope(available, indices)
      },
      Self::AssertEq(left, right, _) => {
        left.len() == right.len()
          && indices_in_scope(available, left)
          && indices_in_scope(available, right)
      },
      Self::UnconstrainedU32Add(left, right) => {
        word_in_scope(available, left) && word_in_scope(available, right)
      },
      Self::UnconstrainedU32Add3(left, middle, right) => {
        word_in_scope(available, left)
          && word_in_scope(available, middle)
          && word_in_scope(available, right)
      },
      Self::U32ToField(indices) => word_in_scope(available, indices),
      _ => true,
    }
  }
}

pub(crate) fn check_emission_ops(
  ops: &[Op],
  mut available: usize,
) -> Result<usize, &'static str> {
  for op in ops {
    if !op.emission_inputs(available) {
      return Err("operation reads outside its incoming scope or width");
    }
    available = available
      .checked_add(op.output_size())
      .ok_or("logical value count overflows")?;
  }
  Ok(available)
}

impl Block {
  pub(crate) fn check_emission(
    &self,
    available: usize,
    selectors: usize,
    yield_size: Option<usize>,
  ) -> Result<(), &'static str> {
    let available = check_emission_ops(&self.ops, available)?;
    match &self.ctrl {
      Ctrl::Return(index, outputs) | Ctrl::Yield(index, outputs) => {
        if *index >= selectors {
          return Err("terminal reads outside its function's selector region");
        }
        if !indices_in_scope(available, outputs) {
          return Err("terminal reads outside its logical scope");
        }
        if matches!(self.ctrl, Ctrl::Yield(..))
          && yield_size != Some(outputs.len())
        {
          return Err("yield width differs from its enclosing continuation");
        }
      },
      Ctrl::Match(index, branches, fallback) => {
        if *index >= available {
          return Err("match reads outside its logical scope");
        }
        for block in branches.values().chain(fallback.as_deref()) {
          block.check_emission(available, selectors, yield_size)?;
        }
      },
      Ctrl::MatchContinue(index, branches, fallback, size, _, _, cont) => {
        if *index >= available {
          return Err("match reads outside its logical scope");
        }
        for block in branches.values().chain(fallback.as_deref()) {
          block.check_emission(available, selectors, Some(*size))?;
        }
        let available = available
          .checked_add(*size)
          .ok_or("continuation merge count overflows")?;
        cont.check_emission(available, selectors, yield_size)?;
      },
    }
    Ok(())
  }
}

impl Toplevel {
  /// Validate every constrained function before native circuit construction.
  /// This does not typecheck source programs or constrain advice operands.
  pub fn validate_emission(&self) -> Result<(), &'static str> {
    for function in &self.functions {
      if function.constrained {
        function.body.check_emission(
          function.layout.input_size,
          function.layout.selectors,
          None,
        )?;
      }
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use multi_stark::p3_field::PrimeCharacteristicRing;
  use multi_stark::types::{CommitmentParameters, FriParameters};

  use super::check_emission_ops;
  use crate::{
    G,
    bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Op, Toplevel},
    synthesis::AiurSystem,
  };

  fn malformed_operand() -> Toplevel {
    let layout = FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 7,
      lookups: 4,
    };
    Toplevel {
      functions: vec![Function {
        body: Block {
          ops: vec![Op::Add(0, 1)],
          ctrl: Ctrl::Return(0, vec![1]),
        },
        layout,
        entry: true,
        constrained: true,
      }],
      memory_sizes: vec![],
      circuits: vec![Circuit { members: vec![0], layout }],
    }
  }

  #[test]
  #[should_panic(expected = "invalid Aiur emission inputs")]
  fn system_construction_rejects_invalid_operand() {
    let top = malformed_operand();
    top.validate_lookup_shapes().unwrap();
    top.validate_row_counts().unwrap();
    AiurSystem::build(
      top,
      CommitmentParameters { log_blowup: 1, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 64,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    );
  }

  #[test]
  fn incoming_scopes_exclude_store_pointers_and_include_virtual_carries() {
    assert!(check_emission_ops(&[Op::Store(vec![1])], 1).is_err());
    assert_eq!(check_emission_ops(&[Op::Store(vec![0])], 1), Ok(2));
    let ops = [
      Op::UnconstrainedU32Add(vec![0, 1, 2, 3], vec![0, 1, 2, 3]),
      Op::U8RangeCheck(4, 7),
      Op::Add(8, 0),
    ];
    assert_eq!(check_emission_ops(&ops, 4), Ok(10));
    assert!(
      check_emission_ops(&[Op::U8RangeCheck(0, 0), Op::Add(1, 0)], 1).is_err()
    );
    assert!(check_emission_ops(&[Op::U32ToField(vec![0; 3])], 1).is_err());
    assert!(check_emission_ops(&[Op::U32ToField(vec![0; 5])], 1).is_err());
    assert!(
      check_emission_ops(&[Op::AssertEq(vec![0], vec![], None)], 1).is_err()
    );
  }

  fn continuation_body(output: usize, yield_width: usize) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        [(
          G::ZERO,
          Block {
            ops: vec![Op::Const(G::ONE), Op::Const(G::TWO)],
            ctrl: Ctrl::Yield(0, vec![2; yield_width]),
          },
        )]
        .into_iter()
        .collect(),
        Some(Box::new(Block { ops: vec![], ctrl: Ctrl::Return(1, vec![0]) })),
        1,
        0,
        0,
        Box::new(Block { ops: vec![], ctrl: Ctrl::Return(2, vec![output]) }),
      ),
    }
  }

  #[test]
  fn continuations_expose_only_merged_values_and_check_every_selector() {
    assert!(continuation_body(1, 1).check_emission(1, 3, None).is_ok());
    assert!(continuation_body(2, 1).check_emission(1, 3, None).is_err());
    assert!(continuation_body(1, 0).check_emission(1, 3, None).is_err());
    assert!(continuation_body(1, 2).check_emission(1, 3, None).is_err());
    assert!(continuation_body(1, 1).check_emission(1, 2, None).is_err());
    assert!(
      Block { ops: vec![], ctrl: Ctrl::Return(1, vec![]) }
        .check_emission(0, 1, None)
        .is_err()
    );
    assert!(
      Block { ops: vec![], ctrl: Ctrl::Yield(0, vec![]) }
        .check_emission(0, 1, None)
        .is_err()
    );
  }

  #[test]
  fn siblings_restore_scope_and_native_scope_addition_is_checked() {
    let block = Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [
          (
            G::ZERO,
            Block {
              ops: vec![Op::Const(G::ONE)],
              ctrl: Ctrl::Return(0, vec![1]),
            },
          ),
          (G::ONE, Block { ops: vec![], ctrl: Ctrl::Return(1, vec![1]) }),
        ]
        .into_iter()
        .collect(),
        None,
      ),
    };
    assert!(block.check_emission(1, 2, None).is_err());
    assert!(block.check_emission(2, 2, None).is_ok());
    assert!(check_emission_ops(&[Op::Const(G::ZERO)], usize::MAX).is_err());
    let block = Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        Default::default(),
        None,
        1,
        0,
        0,
        Box::new(Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) }),
      ),
    };
    assert!(block.check_emission(usize::MAX, 1, None).is_err());
  }

  #[test]
  fn unused_advice_operands_do_not_become_constraint_requirements() {
    let ignored = [
      Op::Call(usize::MAX, vec![usize::MAX], 2, true),
      Op::UnconstrainedGInverse(usize::MAX),
      Op::IOWrite(usize::MAX, vec![usize::MAX]),
    ];
    assert_eq!(check_emission_ops(&ignored, 0), Ok(3));
    let mut top = malformed_operand();
    assert!(top.validate_emission().is_err());
    top.functions[0].constrained = false;
    top.circuits.clear();
    assert!(top.validate_emission().is_ok());
  }
}
