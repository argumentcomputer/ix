//! Aggregation plan.

use super::{
  GIB,
  prepare::PreparedRun,
  protocol::{
    ChildKind, aggregate_outer_claim, cache_key, inner_claim, shape_code,
    structural_shape_code,
  },
  statement::Statement,
};
use aiur::G;
use ix_common::address::Address;
use ix_kernel::shard::AggNode;
use rustc_hash::FxHashMap;
use std::sync::Arc;

pub(super) const WRAP_RAM_BYTES: usize = 195 * GIB;

pub(super) const STRUCTURAL_RAM_BYTES: usize = 195 * GIB;

pub(super) const RAW_SHARD_RAM_BYTES: usize = 4 * GIB;

pub(super) const DIRECT_RAM_BYTES: usize = 390 * GIB;

pub(super) const MIXED_RAM_BYTES: usize = 340 * GIB;

pub(super) const FLAT_RAM_PER_SUBJECT: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug)]
pub(super) enum PlanOp {
  Leaf(usize),
  Join(usize, usize),
}

#[derive(Debug)]
pub(super) struct StatementSpec {
  pub(super) op: PlanOp,
  pub(super) statement: Arc<Statement>,
  pub(super) subject_count: usize,
  pub(super) structural: bool,
}

#[derive(Debug)]
pub(super) struct SlotSpec {
  pub(super) op: PlanOp,
  pub(super) statement: Arc<Statement>,
  pub(super) subject_count: usize,
  pub(super) structural: bool,
  pub(super) kind: ChildKind,
  pub(super) shape: Option<u8>,
  pub(super) outer_claim: Vec<G>,
  pub(super) cache_key: Address,
  pub(super) ram_bytes: usize,
}

pub(super) fn build_plan(
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

pub(super) fn shape_ram_bytes(shape: u8, subject_count: usize) -> usize {
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
pub(super) fn build_statement_specs(
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

/// Proof-system identities and cache framing shared by every slot.
#[derive(Clone, Copy)]
pub(super) struct PlanIdentity<'a> {
  pub(super) verify_idx: usize,
  pub(super) aggr_idx: usize,
  pub(super) aggr_vk: &'a [u8],
  pub(super) allowed: &'a [u8],
  pub(super) cache_fri_bytes: &'a [u8],
}

/// Host folding choices; neither changes the statement's public meaning.
#[derive(Clone, Copy)]
pub(super) struct FoldPolicy {
  pub(super) structural_above: usize,
  pub(super) direct_joins: bool,
}

pub(super) fn build_specs(
  prepared: &PreparedRun,
  identity: PlanIdentity<'_>,
  policy: FoldPolicy,
) -> Result<Vec<SlotSpec>, String> {
  let PlanIdentity { verify_idx, aggr_idx, aggr_vk, allowed, cache_fri_bytes } =
    identity;
  let FoldPolicy { structural_above, direct_joins } = policy;
  let statement_specs = build_statement_specs(prepared, structural_above)?;
  let raw_leaves = direct_joins && statement_specs.len() > 1;
  let mut specs: Vec<SlotSpec> = Vec::with_capacity(statement_specs.len());
  for statement_spec in statement_specs {
    let StatementSpec { op, statement, subject_count, structural } =
      statement_spec;
    match op {
      PlanOp::Leaf(_) => {
        let kind = if raw_leaves { ChildKind::Ixvm } else { ChildKind::Aggr };
        let shape = (!raw_leaves).then_some(shape_code(ChildKind::Ixvm, None));
        let outer_claim = if raw_leaves {
          inner_claim(verify_idx, &statement.claim_bytes)
        } else {
          aggregate_outer_claim(aggr_idx, allowed, &statement.claim_bytes)
        };
        let key = cache_key(aggr_vk, cache_fri_bytes, &outer_claim);
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
          aggregate_outer_claim(aggr_idx, allowed, &statement.claim_bytes);
        let key = cache_key(aggr_vk, cache_fri_bytes, &outer_claim);
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
pub(super) struct ReplayPlan {
  pub(super) children: Vec<usize>,
  pub(super) needs_input_proofs: bool,
}

pub(super) fn plan_replay(
  specs: &[SlotSpec],
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
