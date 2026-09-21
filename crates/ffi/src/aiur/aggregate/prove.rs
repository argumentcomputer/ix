//! Aggregation prove.

use super::{
  format_gib, format_mib,
  plan::{PlanOp, ReplayPlan, SlotSpec},
  prepare::PreparedShard,
  protocol::{ChildKind, inner_claim, packed_digest, serialize_claims},
  statement::{CanonicalTree, Statement, merge_optional_sets},
  store::{load_cached, persist_cached, wrapper_address},
};
use aiur::{
  G,
  synthesis::{AiurProof, AiurSystem, GatedProve},
};
use ix_common::address::Address;
use ixon::{Proof as IxonProof, merkle::MerklePath};
use ixvm_codegen::aiur_ix_aggr_runner::{
  AggrAdvice, AggrPath, AggrPreimage, AggrTree, aggr_io_buffer, execute_ix_aggr,
};
use rustc_hash::FxHashMap;
use std::{path::Path, sync::Arc, time::Instant};

pub(super) struct Slot {
  pub(super) kind: ChildKind,
  pub(super) statement: Arc<Statement>,
  pub(super) outer_claim: Vec<G>,
  pub(super) proof: AiurProof,
  pub(super) proof_address: Option<Address>,
  pub(super) claims_bytes: Vec<u8>,
}

#[derive(Clone, Copy)]
pub(super) struct ProveContext<'a> {
  pub(super) specs: &'a [SlotSpec],
  pub(super) prepared: &'a [PreparedShard],
  pub(super) proofs: Option<&'a [Arc<IxonProof>]>,
  pub(super) owner_by_address: &'a FxHashMap<Address, usize>,
  pub(super) ixvm_system: &'a AiurSystem,
  pub(super) aggr_system: &'a AiurSystem,
  pub(super) ixvm_vk: &'a [u8],
  pub(super) aggr_vk: &'a [u8],
  pub(super) allowed: &'a [u8],
  pub(super) verify_idx: usize,
  pub(super) aggr_idx: usize,
  pub(super) store_dir: &'a Path,
  pub(super) cache_dir: Option<&'a Path>,
  pub(super) reprove_slot: Option<usize>,
  pub(super) write_outputs: bool,
}

pub(super) struct OwnedTreeAdvice {
  pub(super) root: [u8; 32],
  pub(super) bytes: Vec<u8>,
}

pub(super) fn push_canonical_tree(
  out: &mut Vec<OwnedTreeAdvice>,
  tree: &CanonicalTree,
) {
  out.push(OwnedTreeAdvice {
    root: *tree.root.as_bytes(),
    bytes: tree.serialized().to_vec(),
  });
}

pub(super) fn path_payload(
  path: Option<&MerklePath>,
) -> Result<Vec<u8>, String> {
  let Some(path) = path else {
    return Ok(vec![0]);
  };
  let length = u8::try_from(path.len()).map_err(|_overflow| {
    format!("aggregate Merkle path has {} steps", path.len())
  })?;
  if length > 64 {
    return Err(format!(
      "aggregate Merkle path has {length} steps (maximum 64)"
    ));
  }
  let mut out = Vec::with_capacity(2 + path.len() * 33);
  out.extend([1, length]);
  for (sibling, is_left) in path {
    out.push(if *is_left { 0 } else { 1 });
    out.extend_from_slice(sibling.as_bytes());
  }
  Ok(out)
}

pub(super) fn tree_advice(
  left: &Statement,
  right: &Statement,
  output: &Statement,
  structural: bool,
) -> Result<Vec<OwnedTreeAdvice>, String> {
  let mut trees = Vec::new();
  if !structural {
    let left_subjects = left
      .subjects
      .canonical_tree()
      .ok_or("flat join has structural left subjects")?;
    push_canonical_tree(&mut trees, left_subjects);
  }
  if let Some(tree) = &left.assumptions {
    push_canonical_tree(&mut trees, tree);
  }
  if !structural {
    let right_subjects = right
      .subjects
      .canonical_tree()
      .ok_or("flat join has structural right subjects")?;
    push_canonical_tree(&mut trees, right_subjects);
  }
  if let Some(tree) = &right.assumptions {
    push_canonical_tree(&mut trees, tree);
  }
  if !structural {
    let output_subjects = output
      .subjects
      .canonical_tree()
      .ok_or("flat join produced structural subjects")?;
    push_canonical_tree(&mut trees, output_subjects);
  }
  if let Some(tree) = &output.assumptions {
    push_canonical_tree(&mut trees, tree);
  }
  Ok(trees)
}

pub(super) fn structural_path_advice(
  left: &Statement,
  right: &Statement,
  output: &Statement,
  owner_by_address: &FxHashMap<Address, usize>,
) -> Result<Vec<(Address, Vec<u8>)>, String> {
  let candidates = merge_optional_sets(
    left.assumptions.as_deref(),
    right.assumptions.as_deref(),
  );
  let mut paths = Vec::with_capacity(candidates.len());
  for candidate in candidates {
    let owner = owner_by_address.get(&candidate).ok_or_else(|| {
      format!("aggregate assumption {} has no owning shard", candidate.hex())
    })?;
    let path = output.subjects.merkle_proof(&candidate, *owner);
    paths.push((candidate, path_payload(path.as_ref())?));
  }
  Ok(paths)
}

pub(super) fn assumption_count(statement: &Statement) -> usize {
  statement.assumptions.as_ref().map_or(0, |tree| tree.leaves.len())
}

pub(super) fn prove_aggregate(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  left: &Slot,
  right: Option<&Slot>,
  slot_index: usize,
) -> Result<(AiurProof, Option<Address>), String> {
  let replaying = ctx.reprove_slot == Some(slot_index);
  if !replaying {
    if let Some((proof, address)) = load_cached(
      ctx.aggr_system,
      ctx.store_dir,
      ctx.cache_dir,
      slot_index,
      spec,
    ) {
      return Ok((proof, Some(address)));
    }
  } else {
    eprintln!(
      "[aggregate] replay slot {slot_index}: bypassing its cache entry"
    );
  }
  let started = Instant::now();

  let left_system = match left.kind {
    ChildKind::Ixvm => ctx.ixvm_system,
    ChildKind::Aggr => ctx.aggr_system,
  };
  let left_advice = left_system
    .proof_to_advice_bytes(&left.outer_claim, &left.proof)
    .map_err(|error| format!("left child proof advice failed: {error:?}"))?;
  let right_advice = if let Some(right) = right {
    let system = match right.kind {
      ChildKind::Ixvm => ctx.ixvm_system,
      ChildKind::Aggr => ctx.aggr_system,
    };
    system
      .proof_to_advice_bytes(&right.outer_claim, &right.proof)
      .map_err(|error| format!("right child proof advice failed: {error:?}"))?
  } else {
    Vec::new()
  };

  let mut preimage_storage = Vec::new();
  if let Some(right) = right {
    preimage_storage.push((
      *blake3::hash(&left.statement.claim_bytes).as_bytes(),
      left.statement.claim_bytes.as_slice(),
    ));
    preimage_storage.push((
      *blake3::hash(&right.statement.claim_bytes).as_bytes(),
      right.statement.claim_bytes.as_slice(),
    ));
  }
  let preimages: Vec<AggrPreimage<'_>> = preimage_storage
    .iter()
    .map(|(digest, bytes)| AggrPreimage { digest: *digest, bytes })
    .collect();

  let (tree_storage, path_storage) = if let Some(right) = right {
    (
      tree_advice(
        &left.statement,
        &right.statement,
        &spec.statement,
        spec.structural,
      )?,
      if spec.structural {
        structural_path_advice(
          &left.statement,
          &right.statement,
          &spec.statement,
          ctx.owner_by_address,
        )?
      } else {
        Vec::new()
      },
    )
  } else {
    (Vec::new(), Vec::new())
  };
  let trees: Vec<AggrTree<'_>> = tree_storage
    .iter()
    .map(|tree| AggrTree { root: tree.root, bytes: &tree.bytes })
    .collect();
  let paths: Vec<AggrPath<'_>> = path_storage
    .iter()
    .map(|(candidate, bytes)| AggrPath {
      candidate: *candidate.as_bytes(),
      bytes,
    })
    .collect();
  let empty = Vec::new();
  let right_claims =
    right.map_or(empty.as_slice(), |slot| slot.claims_bytes.as_slice());
  let shape = spec.shape.ok_or("aggregate proof slot has no shape")?;
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape,
    proof_advice: [&left_advice, &right_advice],
    ixvm_vk: ctx.ixvm_vk,
    self_vk: ctx.aggr_vk,
    child_claims: [&left.claims_bytes, right_claims],
    output_claim: &spec.statement.claim_bytes,
    allowed: ctx.allowed,
    preimages: &preimages,
    trees: &trees,
    paths: &paths,
  });
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&spec.statement.claim_bytes));
  let proving_started = Instant::now();
  let (outer_claim, proof, peak) = match ctx
    .aggr_system
    .prove_ixvm_within_budget(
      ctx.aggr_idx,
      &public_input,
      &mut io,
      execute_ix_aggr,
      None,
      false,
    ) {
    GatedProve::Proved { claim, proof, peak } => (claim, proof, peak),
    GatedProve::Split { .. } | GatedProve::Measured { .. } => {
      return Err("unbudgeted aggregate prove did not produce a proof".into());
    },
  };
  let proved_at = Instant::now();
  if outer_claim != spec.outer_claim {
    return Err("aggregate prover returned an unexpected outer claim".into());
  }
  let address = persist_cached(
    ctx.store_dir,
    ctx.cache_dir,
    ctx.write_outputs,
    slot_index,
    spec,
    &proof,
  );
  if replaying {
    let tree_bytes: usize =
      tree_storage.iter().map(|tree| tree.bytes.len()).sum();
    let path_bytes: usize =
      path_storage.iter().map(|(_, path)| path.len()).sum();
    let preimage_bytes: usize =
      preimage_storage.iter().map(|(_, bytes)| bytes.len()).sum();
    let right_assumptions =
      right.map_or(0, |slot| assumption_count(&slot.statement));
    eprintln!(
      "[aggregate] replay slot {slot_index}: shape {shape}, {} subjects, assumptions {}/{}/{}, proof advice {}+{} MiB, {} trees/{} MiB, {} paths/{} MiB, preimages {} MiB, query-record peak {} GiB ({} bytes)",
      spec.subject_count,
      assumption_count(&left.statement),
      right_assumptions,
      assumption_count(&spec.statement),
      format_mib(left_advice.len()),
      format_mib(right_advice.len()),
      tree_storage.len(),
      format_mib(tree_bytes),
      path_storage.len(),
      format_mib(path_bytes),
      format_mib(preimage_bytes),
      format_gib(peak),
      peak,
    );
    eprintln!(
      "[aggregate] replay slot {slot_index}: advice {:.3}s, execute+prove {:.3}s, persistence {:.3}s, total {:.3}s",
      (proving_started - started).as_secs_f64(),
      (proved_at - proving_started).as_secs_f64(),
      proved_at.elapsed().as_secs_f64(),
      started.elapsed().as_secs_f64(),
    );
  }
  Ok((proof, address))
}

pub(super) fn prove_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  children: &[Arc<Slot>],
) -> Result<Arc<Slot>, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  match spec.op {
    PlanOp::Leaf(shard) => {
      let prepared = &ctx.prepared[shard];
      let wrapper =
        ctx.proofs.and_then(|proofs| proofs.get(shard)).ok_or_else(|| {
          format!(
            "shard {} proof was not loaded for replay",
            prepared.original_id
          )
        })?;
      let proof = AiurProof::from_bytes(&wrapper.proof).map_err(|error| {
        format!("shard {} proof does not decode: {error}", prepared.original_id)
      })?;
      let inner = inner_claim(ctx.verify_idx, &prepared.statement.claim_bytes);
      ctx.ixvm_system.verify(&inner, &proof).map_err(|error| {
        format!(
          "shard {} proof fails native verification: {error:?}",
          prepared.original_id
        )
      })?;
      let inner_claims = serialize_claims(&[&inner]);
      if spec.kind == ChildKind::Ixvm {
        if spec.outer_claim != inner {
          return Err("direct shard slot has an unexpected outer claim".into());
        }
        return Ok(Arc::new(Slot {
          kind: ChildKind::Ixvm,
          statement: spec.statement.clone(),
          outer_claim: inner,
          proof,
          proof_address: None,
          claims_bytes: inner_claims,
        }));
      }
      eprintln!(
        "[aggregate] wrapping shard {} into slot {slot_index}",
        prepared.original_id
      );
      let raw = Slot {
        kind: ChildKind::Ixvm,
        statement: spec.statement.clone(),
        outer_claim: inner,
        proof,
        proof_address: None,
        claims_bytes: inner_claims,
      };
      let (proof, proof_address) =
        prove_aggregate(ctx, spec, &raw, None, slot_index)?;
      Ok(Arc::new(Slot {
        kind: ChildKind::Aggr,
        statement: spec.statement.clone(),
        outer_claim: spec.outer_claim.clone(),
        proof,
        proof_address,
        claims_bytes: serialize_claims(&[&spec.outer_claim]),
      }))
    },
    PlanOp::Join(left_index, right_index) => {
      if children.len() != 2 {
        return Err("aggregate join did not receive two children".into());
      }
      let left = &children[0];
      let right = &children[1];
      let mode = if spec.structural { "structural" } else { "flat" };
      eprintln!(
        "[aggregate] {mode}-joining slots {left_index}, {right_index} into {slot_index}"
      );
      let (proof, proof_address) =
        prove_aggregate(ctx, spec, left, Some(right), slot_index)?;
      Ok(Arc::new(Slot {
        kind: ChildKind::Aggr,
        statement: spec.statement.clone(),
        outer_claim: spec.outer_claim.clone(),
        proof,
        proof_address,
        claims_bytes: serialize_claims(&[&spec.outer_claim]),
      }))
    },
  }
}

pub(super) fn load_replay_child(
  ctx: ProveContext<'_>,
  target: usize,
  child_index: usize,
) -> Result<Arc<Slot>, String> {
  let spec = ctx
    .specs
    .get(child_index)
    .ok_or("replay target has a missing child slot")?;
  if spec.kind == ChildKind::Ixvm {
    return prove_slot(ctx, child_index, &[]);
  }
  let (proof, proof_address) = load_cached(ctx.aggr_system, ctx.store_dir, ctx.cache_dir, child_index, spec).ok_or_else(|| {
    format!(
      "replay slot {target} requires cached child slot {child_index}; run Stage 2 through that child first"
    )
  })?;
  Ok(Arc::new(Slot {
    kind: ChildKind::Aggr,
    statement: spec.statement.clone(),
    outer_claim: spec.outer_claim.clone(),
    proof,
    proof_address: Some(proof_address),
    claims_bytes: serialize_claims(&[&spec.outer_claim]),
  }))
}

pub(super) fn run_replay(
  ctx: ProveContext<'_>,
  target: usize,
  plan: &ReplayPlan,
) -> Result<String, String> {
  let started = Instant::now();
  eprintln!(
    "[aggregate] replay slot {target}: loading {} immediate child proof(s)",
    plan.children.len()
  );
  let children: Vec<Arc<Slot>> = plan
    .children
    .iter()
    .map(|child| load_replay_child(ctx, target, *child))
    .collect::<Result<_, _>>()?;
  let children_loaded_at = Instant::now();
  let slot = prove_slot(ctx, target, &children)?;
  ctx.aggr_system.verify(&slot.outer_claim, &slot.proof).map_err(|error| {
    format!("replayed slot {target} proof failed verification: {error:?}")
  })?;
  let verified_at = Instant::now();
  let persisted = slot.proof_address.is_some();
  let address = match slot.proof_address.as_ref() {
    Some(address) => address.clone(),
    None => wrapper_address(&slot.statement, &slot.proof)?,
  };
  let disposition = if persisted { "persisted" } else { "not persisted" };
  eprintln!(
    "[aggregate] replay slot {target}: proof {} ({disposition})",
    address.hex()
  );
  eprintln!(
    "[aggregate] replay slot {target}: children {:.3}s, target+verify {:.3}s, address {:.3}s, end-to-end {:.3}s",
    (children_loaded_at - started).as_secs_f64(),
    (verified_at - children_loaded_at).as_secs_f64(),
    verified_at.elapsed().as_secs_f64(),
    started.elapsed().as_secs_f64(),
  );
  Ok(address.hex())
}
