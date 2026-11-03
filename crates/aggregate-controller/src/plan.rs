//! Aggregation plan.

use crate::{
  GIB,
  backend::Identity,
  prepare::PreparedRun,
  protocol::{ChildKind, shape_code, structural_shape_code},
  statement::Statement,
};
use ix_common::address::Address;
use ixon::shard::AggNode;
use rustc_hash::FxHashMap;
use std::sync::Arc;

pub const WRAP_RAM_BYTES: usize = 195 * GIB;

pub const STRUCTURAL_RAM_BYTES: usize = 195 * GIB;

pub const RAW_SHARD_RAM_BYTES: usize = 4 * GIB;

pub const DIRECT_RAM_BYTES: usize = 390 * GIB;

pub const MIXED_RAM_BYTES: usize = 340 * GIB;

pub const FLAT_RAM_PER_SUBJECT: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug)]
pub enum PlanOp {
  Leaf(usize),
  Join(usize, usize),
}

#[derive(Debug)]
pub struct StatementSpec {
  pub op: PlanOp,
  pub statement: Arc<Statement>,
  pub subject_count: usize,
  pub structural: bool,
}

#[derive(Debug)]
pub struct SlotSpec<C> {
  pub op: PlanOp,
  pub statement: Arc<Statement>,
  pub subject_count: usize,
  pub structural: bool,
  pub kind: ChildKind,
  pub shape: Option<u8>,
  pub outer_claim: C,
  pub cache_key: Address,
  pub ram_bytes: usize,
}

pub fn build_plan(
  tree: &AggNode,
  shard_by_id: &FxHashMap<u32, usize>,
  out: &mut Vec<PlanOp>,
) -> Result<usize, String> {
  match tree {
    AggNode::Leaf(id) => {
      let shard = shard_by_id.get(id).copied().ok_or_else(|| {
        format!("aggregate tree references missing shard {id}")
      })?;
      let index = out.len();
      out.push(PlanOp::Leaf(shard));
      Ok(index)
    },
    AggNode::Internal(left, right) => {
      let left_index = build_plan(left, shard_by_id, out)?;
      let right_index = build_plan(right, shard_by_id, out)?;
      let index = out.len();
      out.push(PlanOp::Join(left_index, right_index));
      Ok(index)
    },
  }
}

pub fn shape_ram_bytes(shape: u8, subject_count: usize) -> usize {
  match shape {
    0 | 1 => WRAP_RAM_BYTES,
    3 | 4 | 7 | 8 => MIXED_RAM_BYTES,
    5 => STRUCTURAL_RAM_BYTES
      .saturating_add(subject_count.saturating_mul(FLAT_RAM_PER_SUBJECT)),
    9 => STRUCTURAL_RAM_BYTES,
    // Shapes 2/6 are direct pairs; unknown shapes retain the conservative
    // direct-pair fallback used by the Lean reference scheduler.
    _ => DIRECT_RAM_BYTES,
  }
}

/// Build the claim-bearing statement at every aggregate slot. This is the
/// shared source of truth for proving and manifest-bound verification: the
/// verifier must not reconstruct the same DAG independently in Lean.
pub fn build_statement_specs(
  prepared: &PreparedRun,
  structural_above: usize,
) -> Result<Vec<StatementSpec>, String> {
  let shard_by_id: FxHashMap<u32, usize> = prepared
    .shards
    .iter()
    .enumerate()
    .map(|(index, shard)| (shard.original_id, index))
    .collect();
  let mut ops = Vec::new();
  build_plan(&prepared.tree, &shard_by_id, &mut ops)?;
  let mut specs: Vec<StatementSpec> = Vec::with_capacity(ops.len());
  for op in ops {
    match op {
      PlanOp::Leaf(shard) => {
        let prepared_shard = &prepared.shards[shard];
        specs.push(StatementSpec {
          op,
          statement: prepared_shard.statement.clone(),
          subject_count: prepared_shard.statement.subjects.count,
          structural: false,
        });
      },
      PlanOp::Join(left_index, right_index) => {
        let left = specs
          .get(left_index)
          .ok_or("aggregate plan has a missing left child")?;
        let right = specs
          .get(right_index)
          .ok_or("aggregate plan has a missing right child")?;
        let subject_count =
          left.subject_count.saturating_add(right.subject_count);
        let structural = subject_count > structural_above;
        let statement = Statement::join(
          &left.statement,
          &right.statement,
          structural,
          &prepared.owner_by_address,
        )?;
        if statement.subjects.count != subject_count {
          return Err("aggregate plan has inconsistent subject counts".into());
        }
        specs.push(StatementSpec { op, statement, subject_count, structural });
      },
    }
  }
  Ok(specs)
}

/// Host folding choices; neither changes the statement's public meaning.
#[derive(Clone, Copy)]
pub struct FoldPolicy {
  pub structural_above: usize,
  pub direct_joins: bool,
}

pub fn build_specs<I: Identity>(
  prepared: &PreparedRun,
  identity: &I,
  policy: FoldPolicy,
) -> Result<Vec<SlotSpec<I::Claim>>, String> {
  let FoldPolicy { structural_above, direct_joins } = policy;
  let statement_specs = build_statement_specs(prepared, structural_above)?;
  let raw_leaves = direct_joins && statement_specs.len() > 1;
  let mut specs: Vec<SlotSpec<I::Claim>> =
    Vec::with_capacity(statement_specs.len());
  for statement_spec in statement_specs {
    let StatementSpec { op, statement, subject_count, structural } =
      statement_spec;
    match op {
      PlanOp::Leaf(_) => {
        let kind = if raw_leaves { ChildKind::Ixvm } else { ChildKind::Aggr };
        let shape = (!raw_leaves).then_some(shape_code(ChildKind::Ixvm, None));
        let outer_claim = identity.outer_claim(kind, &statement.claim_bytes);
        let key = identity.cache_key(&outer_claim);
        specs.push(SlotSpec {
          op,
          statement,
          subject_count,
          structural,
          kind,
          shape,
          outer_claim,
          cache_key: key,
          ram_bytes: shape.map_or(RAW_SHARD_RAM_BYTES, |value| {
            shape_ram_bytes(value, subject_count)
          }),
        });
      },
      PlanOp::Join(left_index, right_index) => {
        let left = specs
          .get(left_index)
          .ok_or("aggregate plan has a missing left child")?;
        let right = specs
          .get(right_index)
          .ok_or("aggregate plan has a missing right child")?;
        let shape = if structural {
          structural_shape_code(left.kind, right.kind)
        } else {
          shape_code(left.kind, Some(right.kind))
        };
        let outer_claim =
          identity.outer_claim(ChildKind::Aggr, &statement.claim_bytes);
        let key = identity.cache_key(&outer_claim);
        specs.push(SlotSpec {
          op,
          statement,
          subject_count,
          structural,
          kind: ChildKind::Aggr,
          shape: Some(shape),
          outer_claim,
          cache_key: key,
          ram_bytes: shape_ram_bytes(shape, subject_count),
        });
      },
    }
  }
  Ok(specs)
}

#[derive(Debug, PartialEq, Eq)]
pub struct ReplayPlan {
  pub children: Vec<usize>,
  pub needs_input_proofs: bool,
}

pub fn plan_replay<C>(
  specs: &[SlotSpec<C>],
  target: usize,
) -> Result<ReplayPlan, String> {
  let spec = specs.get(target).ok_or_else(|| {
    format!(
      "--reprove-slot {target} is out of range; the plan has slots 0..{}",
      specs.len().saturating_sub(1)
    )
  })?;
  if spec.kind == ChildKind::Ixvm {
    return Err(format!(
      "--reprove-slot {target} selects a raw IxVM leaf, not a Stage 2 proof"
    ));
  }
  let children = match spec.op {
    PlanOp::Leaf(_) => Vec::new(),
    PlanOp::Join(left, right) => vec![left, right],
  };
  let needs_input_proofs = children.is_empty()
    || children.iter().any(|index| specs[*index].kind == ChildKind::Ixvm);
  Ok(ReplayPlan { children, needs_input_proofs })
}

/// Leaves under every slot of a post-order plan.
pub fn leaves_under(ops: &[PlanOp]) -> Vec<usize> {
  let mut leaves = vec![0usize; ops.len()];
  for (index, op) in ops.iter().enumerate() {
    leaves[index] = match *op {
      PlanOp::Leaf(_) => 1,
      PlanOp::Join(left, right) => leaves[left] + leaves[right],
    };
  }
  leaves
}

/// Splits frontier node `at` into its children when it is a join. A child
/// that is a raw leaf becomes a one-leaf subtree: its claim proof is its
/// published proof, and the join above it verifies that raw leaf beside
/// its cached sibling. Returns whether it split.
fn split_frontier(
  ops: &[PlanOp],
  frontier: &mut Vec<usize>,
  at: usize,
) -> bool {
  let PlanOp::Join(left, right) = ops[frontier[at]] else {
    return false;
  };
  frontier.swap_remove(at);
  frontier.push(left);
  frontier.push(right);
  true
}

/// The plan cut into subtrees for dynamic scheduling: the tree is split from
/// the root while any frontier node holds more leaves than
/// `ceil(leaves / subtrees)`. Returns the frontier (the subtrees, post-order;
/// a subtree may be a single raw leaf) and every join above it (post-order,
/// so each appears after its children). A subtree of several leaves is
/// proven as one `--subtree` task once its leaves' claims exist; a
/// one-leaf subtree is published by its claim proof alone; an upper join
/// once both children are published; whichever device is free takes the
/// next ready task, so no packing is decided ahead of time.
pub fn subtree_plan(
  ops: &[PlanOp],
  max_leaves: usize,
) -> (Vec<usize>, Vec<usize>) {
  let Some(root) = ops.len().checked_sub(1) else {
    return (Vec::new(), Vec::new());
  };
  let leaves = leaves_under(ops);
  let target = max_leaves.max(1);
  let mut frontier = vec![root];
  while let Some(at) = (0..frontier.len())
    .filter(|&at| leaves[frontier[at]] > target)
    .max_by_key(|&at| leaves[frontier[at]])
  {
    if !split_frontier(ops, &mut frontier, at) {
      break;
    }
  }
  frontier.sort_unstable();
  // Everything above the frontier: the ancestors of frontier nodes.
  let mut above = vec![false; ops.len()];
  let mut in_frontier = vec![false; ops.len()];
  for &slot in &frontier {
    in_frontier[slot] = true;
  }
  for index in 0..ops.len() {
    if let PlanOp::Join(left, right) = ops[index]
      && (in_frontier[left]
        || in_frontier[right]
        || above[left]
        || above[right])
    {
      above[index] = true;
    }
  }
  let upper: Vec<usize> = (0..ops.len()).filter(|&i| above[i]).collect();
  (frontier, upper)
}
