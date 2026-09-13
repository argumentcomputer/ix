// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Witness-independent bounds for branch selection and terminal counts.
//! Every return/yield allocates a selector, including consumed yields.

use multi_stark::p3_field::PrimeField64;

use crate::{
  G,
  bytecode::{Block, Circuit, Ctrl, Toplevel},
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ControlCounts {
  pub(crate) nodes: usize,
  pub(crate) leaves: usize,
  pub(crate) returns: usize,
  pub(crate) yields: usize,
}

impl ControlCounts {
  fn checked_add(self, other: Self) -> Option<Self> {
    Some(Self {
      nodes: self.nodes.checked_add(other.nodes)?,
      leaves: self.leaves.checked_add(other.leaves)?,
      returns: self.returns.checked_add(other.returns)?,
      yields: self.yields.checked_add(other.yields)?,
    })
  }

  fn branches<'a>(blocks: impl Iterator<Item = &'a Block>) -> Option<Self> {
    let mut counts = Self::default();
    for block in blocks {
      counts = counts.checked_add(block.control_counts()?)?;
    }
    counts.nodes = counts.nodes.checked_add(1)?;
    Some(counts)
  }

  fn continued(self, continuation: Self) -> Option<Self> {
    Some(Self {
      nodes: self.nodes.checked_add(continuation.nodes)?,
      leaves: self.leaves.checked_add(continuation.leaves)?,
      returns: self.returns.checked_add(continuation.returns)?,
      yields: continuation.yields,
    })
  }
}

impl Block {
  pub(crate) fn control_counts(&self) -> Option<ControlCounts> {
    match &self.ctrl {
      Ctrl::Return(..) => {
        Some(ControlCounts { nodes: 1, leaves: 1, returns: 1, yields: 0 })
      },
      Ctrl::Yield(..) => {
        Some(ControlCounts { nodes: 1, leaves: 1, returns: 0, yields: 1 })
      },
      Ctrl::Match(_, branches, fallback) => {
        ControlCounts::branches(branches.values().chain(fallback.as_deref()))
      },
      Ctrl::MatchContinue(_, branches, fallback, _, _, _, continuation) => {
        ControlCounts::branches(branches.values().chain(fallback.as_deref()))?
          .continued(continuation.control_counts()?)
      },
    }
  }
}

fn canonical_count(count: usize) -> bool {
  u64::try_from(count).is_ok_and(|count| count < G::ORDER_U64)
}

impl Circuit {
  pub(crate) fn validate_row_counts(
    &self,
    program: &Toplevel,
  ) -> Result<(), &'static str> {
    if !canonical_count(self.members.len()) {
      return Err("circuit member count exceeds the field characteristic");
    }
    let mut leaves = 0usize;
    for &index in &self.members {
      let Some(function) = program.functions.get(index) else {
        return Err("circuit refers to a missing function");
      };
      let Some(counts) = function.body.control_counts() else {
        return Err("function control count overflows");
      };
      if !canonical_count(counts.nodes) {
        return Err("function control count exceeds the field characteristic");
      }
      leaves = leaves
        .checked_add(counts.leaves)
        .ok_or("circuit leaf count overflows")?;
    }
    if leaves > self.layout.selectors {
      return Err("circuit has fewer selectors than return/yield leaves");
    }
    Ok(())
  }
}

impl Toplevel {
  pub fn validate_row_counts(&self) -> Result<(), &'static str> {
    for circuit in &self.circuits {
      circuit.validate_row_counts(self)?;
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use multi_stark::{
    p3_field::PrimeCharacteristicRing,
    types::{CommitmentParameters, FriParameters},
  };

  use super::*;
  use crate::{
    FxIndexMap,
    bytecode::{Function, FunctionLayout},
    synthesis::AiurSystem,
  };

  fn continued_body() -> Block {
    let mut branches = FxIndexMap::default();
    branches
      .insert(G::ZERO, Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) });
    branches
      .insert(G::ONE, Block { ops: vec![], ctrl: Ctrl::Yield(1, vec![]) });
    Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        branches,
        None,
        0,
        0,
        0,
        Box::new(Block { ops: vec![], ctrl: Ctrl::Return(2, vec![]) }),
      ),
    }
  }

  fn continued_program(selectors: usize) -> Toplevel {
    let layout =
      FunctionLayout { input_size: 1, selectors, auxiliaries: 7, lookups: 4 };
    Toplevel {
      functions: vec![Function {
        body: continued_body(),
        layout,
        entry: true,
        constrained: true,
      }],
      memory_sizes: vec![],
      circuits: vec![Circuit { members: vec![0], layout }],
    }
  }

  #[test]
  fn counts_include_consumed_yields_and_empty_matches() {
    assert_eq!(
      continued_body().control_counts(),
      Some(ControlCounts { nodes: 4, leaves: 3, returns: 2, yields: 0 })
    );
    let empty =
      Block { ops: vec![], ctrl: Ctrl::Match(0, FxIndexMap::default(), None) };
    assert_eq!(
      empty.control_counts(),
      Some(ControlCounts { nodes: 1, ..ControlCounts::default() })
    );
    assert!(continued_program(3).validate_row_counts().is_ok());
    assert!(continued_program(2).validate_row_counts().is_err());
    assert!(continued_program(1).validate_row_counts().is_err());
  }

  #[test]
  fn count_bounds_reject_machine_overflow_and_field_wrap() {
    let maximal = ControlCounts { nodes: usize::MAX, ..Default::default() };
    let one = ControlCounts { nodes: 1, ..Default::default() };
    assert!(maximal.checked_add(one).is_none());
    assert!(maximal.continued(one).is_none());
    if let Ok(order) = usize::try_from(G::ORDER_U64) {
      assert!(canonical_count(order - 1));
      assert!(!canonical_count(order));
      assert!(!canonical_count(usize::MAX));
    }
  }

  #[test]
  #[should_panic(expected = "invalid Aiur control counts")]
  fn system_construction_rejects_missing_leaf_selectors() {
    let top = continued_program(1);
    top.validate_lookup_shapes().unwrap();
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
}
