//! Aggregation prove.

use super::{
  format_gib, format_mib, panic_text,
  plan::{PlanOp, ReplayPlan, SlotSpec},
  prepare::PreparedShard,
  protocol::{
    ChildKind, RANGE_JOIN_SHAPE, RANGE_LEAF_SHAPE, RANGE_ROOT_SHAPE,
    inner_claim, packed_digest, serialize_claims, shape_code,
  },
  statement::{CanonicalTree, Statement, merge_optional_sets},
  store::{load_cached, persist_cached, wrapper_address},
};
use aiur::{
  G,
  execute::IOBuffer,
  range::{
    preamble_bytes, proofs_slice_bytes, range_residual, range_statement,
  },
  synthesis::{AiurProof, AiurSystem, GatedProve, PreparedProve},
};
use ix_common::address::Address;
use ixon::{Proof as IxonProof, merkle::MerklePath};
use ixvm_codegen::aiur_ix_aggr_runner::{
  AggrAdvice, AggrPath, AggrPreimage, AggrTree, aggr_io_buffer, execute_ix_aggr,
};
use multi_stark::types::ExtVal;
use rustc_hash::FxHashMap;
use std::{
  path::Path,
  sync::{Arc, mpsc},
  thread,
  time::Instant,
};

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
  /// One entry per manifest shard; `None` for shards outside the run's
  /// selection (a subtree run) or when a replay needs no input proofs.
  pub(super) proofs: Option<&'a [Option<Arc<IxonProof>>]>,
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
  /// The prover budget of one slot when its execution is proven as trace
  /// shards; `None` proves every slot unsharded and unbudgeted.
  pub(super) wrap_budget: Option<usize>,
  /// Wrap a shard proof of more than this many trace shards as a range-sum
  /// tree whose leaves verify at most this many shards each; 0 always wraps
  /// the whole batch in one proof.
  pub(super) range_width: usize,
  /// How many range-tree nodes prove at once, each under `wrap_budget`.
  pub(super) range_jobs: usize,
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

/// A slot executed and planned, waiting for the prover.
pub(super) struct PreparedAggregate {
  slot_index: usize,
  prepared: PreparedProve,
  started: Instant,
  proving_started: Instant,
  /// The replayed slot's advice diagnostics, printed once it is proven.
  replay: Option<String>,
}

/// What preparing a slot yields: its proof straight from the cache, or its
/// execution waiting for the prover.
pub(super) enum Staged {
  Cached(Box<AiurProof>, Address),
  Prepared(Box<PreparedAggregate>),
}

/// The execution half of a slot's proof: the cache probe, both children's
/// advice, the trees and paths, then the `ix_aggr` execution planned within
/// the slot budget. CPU work only, so one slot can prepare while another
/// proves.
fn prepare_aggregate(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  left: &Slot,
  right: Option<&Slot>,
  slot_index: usize,
) -> Result<Staged, PrepareFailure> {
  let replaying = ctx.reprove_slot == Some(slot_index);
  if !replaying {
    if let Some((proof, address)) = load_cached(
      ctx.aggr_system,
      ctx.store_dir,
      ctx.cache_dir,
      slot_index,
      spec,
    ) {
      return Ok(Staged::Cached(Box::new(proof), address));
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
  let prepared = prepare_aggr_io(
    ctx,
    &mut io,
    &public_input,
    &format!("slot {slot_index}"),
  )?;
  let replay = replaying.then(|| {
    let tree_bytes: usize =
      tree_storage.iter().map(|tree| tree.bytes.len()).sum();
    let path_bytes: usize =
      path_storage.iter().map(|(_, path)| path.len()).sum();
    let preimage_bytes: usize =
      preimage_storage.iter().map(|(_, bytes)| bytes.len()).sum();
    let right_assumptions =
      right.map_or(0, |slot| assumption_count(&slot.statement));
    format!(
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
      format_gib(prepared.peak),
      prepared.peak,
    )
  });
  Ok(Staged::Prepared(Box::new(PreparedAggregate {
    slot_index,
    prepared,
    started,
    proving_started,
    replay,
  })))
}

/// The proving half of a slot's proof: the STARK, the outer-claim check and
/// persistence.
fn finish_aggregate(
  ctx: ProveContext<'_>,
  staged: Staged,
) -> Result<(AiurProof, Option<Address>), String> {
  let PreparedAggregate {
    slot_index,
    prepared,
    started,
    proving_started,
    replay,
  } = match staged {
    Staged::Cached(proof, address) => return Ok((*proof, Some(address))),
    Staged::Prepared(prepared) => *prepared,
  };
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let (outer_claim, proof, _) = finish_aggr_io(ctx, prepared);
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
  )?;
  if let Some(line) = replay {
    eprintln!("{line}");
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

/// Execute and prove one `ix_aggr` invocation over its advice buffer, as
/// trace shards within the slot budget when the run has one.
fn prove_aggr_io(
  ctx: ProveContext<'_>,
  io: &mut IOBuffer,
  public_input: &[G],
  label: &str,
) -> Result<(Vec<G>, AiurProof, usize), String> {
  let prepared = prepare_aggr_io(ctx, io, public_input, label)?;
  Ok(finish_aggr_io(ctx, prepared))
}

/// The execution half of [`prove_aggr_io`]: executes the invocation, gates
/// and plans it within the slot budget, and returns what
/// [`finish_aggr_io`] proves from, so one node can execute while another
/// proves.
fn prepare_aggr_io(
  ctx: ProveContext<'_>,
  io: &mut IOBuffer,
  public_input: &[G],
  label: &str,
) -> Result<PreparedProve, PrepareFailure> {
  match ctx.aggr_system.prepare_ixvm_within_budget(
    ctx.aggr_idx,
    public_input,
    io,
    execute_ix_aggr,
    ctx.wrap_budget,
    ctx.wrap_budget.is_some(),
    None,
  ) {
    Ok(prepared) => Ok(prepared),
    Err(GatedProve::Split { peak, .. }) => Err(
      format!(
        "{OVER_SLOT_BUDGET}{label}: no trace-shard count fits the {} B budget \
       (whole-execution peak {peak} B) — raise --max-ram",
        ctx.wrap_budget.unwrap_or(0)
      )
      .into(),
    ),
    Err(GatedProve::Failed(
      aiur::execute::ExecError::RecordBudgetExceeded { bytes, cap },
    )) => Err(PrepareFailure::OverRecordCap { bytes, cap }),
    Err(GatedProve::Failed(
      aiur::execute::ExecError::RecordMemoryContention,
    )) => Err(PrepareFailure::MemoryContention),
    Err(GatedProve::Failed(error)) => {
      Err(format!("{label}: execution failed: {error}").into())
    },
    Err(_) => {
      Err(format!("{label}: aggregate prove did not produce a proof").into())
    },
  }
}

/// Why a node's preparation failed: its execution reached the record cap
/// it ran under (the thread-local cap of `aiur::execute`), which a
/// scheduler can answer by rerunning it alone, or anything else.
pub(super) enum PrepareFailure {
  OverRecordCap { bytes: usize, cap: usize },
  MemoryContention,
  Other(String),
}

impl From<String> for PrepareFailure {
  fn from(message: String) -> Self {
    Self::Other(message)
  }
}

impl From<&str> for PrepareFailure {
  fn from(message: &str) -> Self {
    Self::Other(message.to_string())
  }
}

impl From<PrepareFailure> for String {
  fn from(failure: PrepareFailure) -> Self {
    match failure {
      PrepareFailure::OverRecordCap { bytes, cap } => {
        format!("record reached {bytes} B, over the {cap} B record cap")
      },
      PrepareFailure::MemoryContention => {
        "record cancelled to resolve memory contention".into()
      },
      PrepareFailure::Other(message) => message,
    }
  }
}

/// Prefix of the error [`prepare_aggr_io`] returns when a node's execution
/// does not fit the slot budget, so callers can tell that outcome apart.
const OVER_SLOT_BUDGET: &str = "over the slot budget: ";

/// The proving half of [`prove_aggr_io`].
fn finish_aggr_io(
  ctx: ProveContext<'_>,
  prepared: PreparedProve,
) -> (Vec<G>, AiurProof, usize) {
  ctx.aggr_system.prove_prepared(prepared)
}

/// One proven node of a range-sum tree: shards `[lo, hi)` of the batch and
/// their residual sum, stated by `statement` (`aiur::range::range_statement`).
struct RangeNode {
  lo: usize,
  hi: usize,
  residual: ExtVal,
  statement: Vec<u8>,
  outer_claim: Vec<G>,
  proof: AiurProof,
}

/// A range-tree node executed and planned, waiting for the prover.
struct PreparedNode {
  lo: usize,
  hi: usize,
  residual: ExtVal,
  statement: Vec<u8>,
  kind: &'static str,
  started: Instant,
  prepared: PreparedProve,
}

/// Prove every item of one tree level. With one job the level is a
/// pipeline: a producer thread executes and plans item `k + 1` while this
/// thread proves item `k`, at most one node ahead (a rendezvous channel), so
/// the prover never waits for an execution it could have overlapped. With
/// more jobs, that many items execute and prove at once.
fn prove_range_level<T, P, F>(
  items: Vec<T>,
  jobs: usize,
  prepare: &P,
  finish: &F,
) -> Result<Vec<RangeNode>, String>
where
  T: Send,
  P: Fn(T) -> Result<PreparedNode, String> + Sync,
  F: Fn(PreparedNode) -> Result<RangeNode, String> + Sync,
{
  if jobs <= 1 {
    let span = tracing::Span::current();
    return thread::scope(|scope| {
      let (sender, receiver) =
        mpsc::sync_channel::<Result<PreparedNode, String>>(0);
      let producer = scope.spawn(move || {
        let _g = span.entered();
        for item in items {
          let prepared = prepare(item);
          let failed = prepared.is_err();
          if sender.send(prepared).is_err() || failed {
            break;
          }
        }
      });
      let mut nodes = Vec::new();
      let mut outcome = Ok(());
      for prepared in receiver {
        match prepared.and_then(finish) {
          Ok(node) => nodes.push(node),
          Err(error) => {
            outcome = Err(error);
            break;
          },
        }
      }
      // Dropping the receiver stops the producer at its next send.
      producer.join().map_err(|payload| {
        format!("range node preparation panicked: {}", panic_text(&payload))
      })?;
      outcome.map(|()| nodes)
    });
  }
  let mut nodes = Vec::with_capacity(items.len());
  let mut pending = items.into_iter().peekable();
  while pending.peek().is_some() {
    let batch: Vec<T> = pending.by_ref().take(jobs).collect();
    let proven: Vec<Result<RangeNode, String>> = thread::scope(|scope| {
      let handles: Vec<_> = batch
        .into_iter()
        .map(|item| scope.spawn(move || prepare(item).and_then(finish)))
        .collect();
      handles
        .into_iter()
        .map(|handle| {
          handle.join().unwrap_or_else(|payload| {
            Err(format!("range node panicked: {}", panic_text(&payload)))
          })
        })
        .collect()
    });
    for node in proven {
      nodes.push(node?);
    }
  }
  Ok(nodes)
}

/// Wrap a shard proof of many trace shards as a range-sum tree: leaves of at
/// most `range_width` shards, joins of adjacent ranges, and a root whose
/// statement is exactly the wrap's, so the slot's cache entry and every
/// consumer are unchanged.
fn prove_range_tree(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  batch: &AiurProof,
  slot_index: usize,
) -> Result<(AiurProof, Option<Address>), String> {
  if ctx.reprove_slot != Some(slot_index)
    && let Some((proof, address)) = load_cached(
      ctx.aggr_system,
      ctx.store_dir,
      ctx.cache_dir,
      slot_index,
      spec,
    )
  {
    return Ok((proof, Some(address)));
  }
  let started = Instant::now();
  let shards = batch.preamble.headers.len();
  // No requested width: two leaves per node slot, so a slot's pipeline
  // always has a next leaf to execute while it proves one, and each leaf
  // is as large as that allows; a leaf over the slot budget fails its
  // gate, and a derived width is halved until the leaves fit.
  let mut width = if ctx.range_width > 0 {
    ctx.range_width
  } else {
    shards.div_ceil(2 * ctx.range_jobs.max(1)).max(1)
  };
  let preamble = preamble_bytes(batch)?;
  let digest = *blake3::hash(&preamble).as_bytes();
  let leaves_of = |width: usize| -> Vec<(usize, usize)> {
    (0..shards)
      .step_by(width)
      .map(|lo| (lo, (lo + width).min(shards)))
      .collect()
  };
  eprintln!(
    "[aggregate] slot {slot_index}: range tree over {shards} shards: {} leaves of at most {width} shards, {} at a time",
    leaves_of(width).len(),
    ctx.range_jobs
  );
  let self_claims = |node: &RangeNode| serialize_claims(&[&node.outer_claim]);
  let child_advice = |node: &RangeNode| -> Result<Vec<u8>, String> {
    ctx
      .aggr_system
      .proof_to_advice_bytes(&node.outer_claim, &node.proof)
      .map_err(|error| {
        format!(
          "slot {slot_index}: range node {}..{} proof advice failed: {error}",
          node.lo, node.hi
        )
      })
  };
  let prepare_node = |shape: u8,
                      lo: usize,
                      hi: usize,
                      residual: ExtVal,
                      proof_advice: [&[u8]; 2],
                      child_claims: [&[u8]; 2],
                      preimages: &[AggrPreimage<'_>]|
   -> Result<PreparedNode, String> {
    let node_started = Instant::now();
    let statement = range_statement(&digest, lo, hi, residual);
    let mut io = aggr_io_buffer(&AggrAdvice {
      shape,
      proof_advice,
      ixvm_vk: ctx.ixvm_vk,
      self_vk: ctx.aggr_vk,
      child_claims,
      output_claim: &statement,
      allowed: ctx.allowed,
      preimages,
      trees: &[],
      paths: &[],
    });
    let mut public_input = packed_digest(ctx.allowed);
    public_input.extend(packed_digest(&statement));
    let kind = if shape == RANGE_LEAF_SHAPE { "leaf" } else { "join" };
    let prepared = prepare_aggr_io(
      ctx,
      &mut io,
      &public_input,
      &format!("slot {slot_index} range {kind} {lo}..{hi}"),
    )?;
    eprintln!(
      "[aggregate] slot {slot_index}: range {kind} {lo}..{hi} executed in {:.1}s",
      node_started.elapsed().as_secs_f64()
    );
    Ok(PreparedNode {
      lo,
      hi,
      residual,
      statement,
      kind,
      started: node_started,
      prepared,
    })
  };
  let finish_node = |node: PreparedNode| -> Result<RangeNode, String> {
    let PreparedNode { lo, hi, residual, statement, kind, started, prepared } =
      node;
    let (outer_claim, proof, peak) = finish_aggr_io(ctx, prepared);
    eprintln!(
      "[aggregate] slot {slot_index}: range {kind} {lo}..{hi} proven in {:.1}s (query-record peak {} GiB)",
      started.elapsed().as_secs_f64(),
      format_gib(peak)
    );
    Ok(RangeNode { lo, hi, residual, statement, outer_claim, proof })
  };

  let prove_leaves = |width: usize| {
    prove_range_level(
      leaves_of(width),
      ctx.range_jobs,
      &|(lo, hi)| {
        let proofs = proofs_slice_bytes(batch, lo, hi)?;
        prepare_node(
          RANGE_LEAF_SHAPE,
          lo,
          hi,
          range_residual(batch, lo, hi),
          [&preamble, &proofs],
          [&[], &[]],
          &[],
        )
      },
      &finish_node,
    )
  };
  let mut nodes = loop {
    match prove_leaves(width) {
      Ok(nodes) => break nodes,
      Err(error)
        if ctx.range_width == 0
          && width > 1
          && error.starts_with(OVER_SLOT_BUDGET) =>
      {
        width /= 2;
        eprintln!(
          "[aggregate] slot {slot_index}: a leaf did not fit the slot budget; retrying with leaves of at most {width} shards"
        );
      },
      Err(error) => return Err(error),
    }
  };
  while nodes.len() > 1 {
    let mut pairs = Vec::with_capacity(nodes.len().div_ceil(2));
    let mut carried = None;
    let mut pending = nodes.into_iter();
    while let Some(left) = pending.next() {
      match pending.next() {
        Some(right) => pairs.push((left, right)),
        None => carried = Some(left),
      }
    }
    nodes = prove_range_level(
      pairs,
      ctx.range_jobs,
      &|(left, right)| {
        let advice = [child_advice(&left)?, child_advice(&right)?];
        let claims = [self_claims(&left), self_claims(&right)];
        let preimages = [
          AggrPreimage {
            digest: *blake3::hash(&left.statement).as_bytes(),
            bytes: &left.statement,
          },
          AggrPreimage {
            digest: *blake3::hash(&right.statement).as_bytes(),
            bytes: &right.statement,
          },
        ];
        prepare_node(
          RANGE_JOIN_SHAPE,
          left.lo,
          right.hi,
          left.residual + right.residual,
          [&advice[0], &advice[1]],
          [&claims[0], &claims[1]],
          &preimages,
        )
      },
      &finish_node,
    )?;
    // An unpaired last node joins at the next level, keeping ranges in
    // shard order.
    nodes.extend(carried);
  }
  let node = nodes.pop().ok_or("range tree has no root")?;

  let root_started = Instant::now();
  let advice = child_advice(&node)?;
  let claims = self_claims(&node);
  let preimages = [AggrPreimage {
    digest: *blake3::hash(&node.statement).as_bytes(),
    bytes: &node.statement,
  }];
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape: RANGE_ROOT_SHAPE,
    proof_advice: [&advice, &preamble],
    ixvm_vk: ctx.ixvm_vk,
    self_vk: ctx.aggr_vk,
    child_claims: [&claims, &[]],
    output_claim: &spec.statement.claim_bytes,
    allowed: ctx.allowed,
    preimages: &preimages,
    trees: &[],
    paths: &[],
  });
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&spec.statement.claim_bytes));
  let (outer_claim, proof, peak) = prove_aggr_io(
    ctx,
    &mut io,
    &public_input,
    &format!("slot {slot_index} range root"),
  )?;
  if outer_claim != spec.outer_claim {
    return Err("range root returned an unexpected outer claim".into());
  }
  eprintln!(
    "[aggregate] slot {slot_index}: range root proven in {:.1}s (query-record peak {} GiB); range tree total {:.1}s",
    root_started.elapsed().as_secs_f64(),
    format_gib(peak),
    started.elapsed().as_secs_f64()
  );
  let address = persist_cached(
    ctx.store_dir,
    ctx.cache_dir,
    ctx.write_outputs,
    slot_index,
    spec,
    &proof,
  )?;
  Ok((proof, address))
}

/// Wraps `proof`, a proof of `root`'s claim, once more: shape 1 verifies
/// one `ix_aggr` proof and passes its statement through, so a root that is
/// a batch of trace shards (a direct join) ends as a smaller proof of the
/// same claim.
pub(super) fn wrap_root(
  ctx: ProveContext<'_>,
  root: &Slot,
  proof: &AiurProof,
) -> Result<AiurProof, String> {
  let started = Instant::now();
  let advice_shards = proof.preamble.headers.len();
  let advice = ctx
    .aggr_system
    .proof_to_advice_bytes(&root.outer_claim, proof)
    .map_err(|error| format!("root proof advice failed: {error}"))?;
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape: shape_code(ChildKind::Aggr, None),
    proof_advice: [&advice, &[]],
    ixvm_vk: ctx.ixvm_vk,
    self_vk: ctx.aggr_vk,
    child_claims: [&root.claims_bytes, &[]],
    output_claim: &root.statement.claim_bytes,
    allowed: ctx.allowed,
    preimages: &[],
    trees: &[],
    paths: &[],
  });
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&root.statement.claim_bytes));
  let (outer_claim, proof, peak) =
    prove_aggr_io(ctx, &mut io, &public_input, "root wrap")?;
  if outer_claim != root.outer_claim {
    return Err("root wrap returned an unexpected outer claim".into());
  }
  eprintln!(
    "[aggregate] root wrap proven in {:.1}s (query-record peak {} GiB): {} shard(s) verified into {}",
    started.elapsed().as_secs_f64(),
    format_gib(peak),
    advice_shards,
    proof.preamble.headers.len()
  );
  Ok(proof)
}

/// Verifies raw shard `shard` of slot `slot_index` natively and returns it
/// as a raw IxVM slot (the child a direct join takes, or what a wrap-first
/// leaf wraps).
fn verify_leaf(
  ctx: ProveContext<'_>,
  slot_index: usize,
  shard: usize,
) -> Result<Slot, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let prepared = &ctx.prepared[shard];
  let wrapper = ctx
    .proofs
    .and_then(|proofs| proofs.get(shard))
    .and_then(|proof| proof.as_ref())
    .ok_or_else(|| {
      format!("shard {} proof was not loaded for replay", prepared.original_id)
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
  if spec.kind == ChildKind::Ixvm && spec.outer_claim != inner {
    return Err("direct shard slot has an unexpected outer claim".into());
  }
  Ok(Slot {
    kind: ChildKind::Ixvm,
    statement: spec.statement.clone(),
    outer_claim: inner,
    proof,
    proof_address: None,
    claims_bytes: inner_claims,
  })
}

/// A slot prepared for the prover: complete already (a raw leaf verified,
/// a cached proof), a wrap-first leaf whose batch becomes a range tree
/// (executed and proven together), or an execution waiting for its STARK
/// (a wrap or a join).
pub(super) enum StagedSlot {
  Done(Arc<Slot>),
  Range(Box<Slot>),
  Staged(Staged),
}

/// The execution half of [`prove_slot`]: verification and, for a wrap or
/// a join, the `ix_aggr` execution planned within the slot budget. No
/// proving happens here, so it can run beside the prover.
#[tracing::instrument(level = "info", skip_all, name = "aiur/prepare_slot", fields(slot = slot_index))]
pub(super) fn prepare_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  children: &[Arc<Slot>],
) -> Result<StagedSlot, PrepareFailure> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  match spec.op {
    PlanOp::Leaf(shard) => {
      let raw = verify_leaf(ctx, slot_index, shard)?;
      if spec.kind == ChildKind::Ixvm {
        return Ok(StagedSlot::Done(Arc::new(raw)));
      }
      eprintln!(
        "[aggregate] wrapping shard {} into slot {slot_index}",
        ctx.prepared[shard].original_id
      );
      // A batch of several shards becomes a range tree: leaves of the
      // requested width, or of the derived width (as few leaves as there
      // are node slots) when none was requested and slots are budgeted.
      let shards = raw.proof.preamble.headers.len();
      let ranged = shards > 1
        && (ctx.range_width > 0 && shards > ctx.range_width
          || ctx.range_width == 0 && ctx.wrap_budget.is_some());
      if ranged {
        return Ok(StagedSlot::Range(Box::new(raw)));
      }
      let staged = prepare_aggregate(ctx, spec, &raw, None, slot_index)?;
      Ok(StagedSlot::Staged(staged))
    },
    PlanOp::Join(left_index, right_index) => {
      if children.len() != 2 {
        return Err("aggregate join did not receive two children".into());
      }
      let mode = if spec.structural { "structural" } else { "flat" };
      eprintln!(
        "[aggregate] {mode}-joining slots {left_index}, {right_index} into {slot_index}"
      );
      let staged = prepare_aggregate(
        ctx,
        spec,
        &children[0],
        Some(&children[1]),
        slot_index,
      )?;
      Ok(StagedSlot::Staged(staged))
    },
  }
}

/// The proving half of [`prove_slot`].
#[tracing::instrument(level = "info", skip_all, name = "aiur/finish_slot", fields(slot = slot_index))]
pub(super) fn finish_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  staged: StagedSlot,
) -> Result<Arc<Slot>, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let (proof, proof_address) = match staged {
    StagedSlot::Done(slot) => return Ok(slot),
    StagedSlot::Range(raw) => {
      prove_range_tree(ctx, spec, &raw.proof, slot_index)?
    },
    StagedSlot::Staged(staged) => finish_aggregate(ctx, staged)?,
  };
  Ok(Arc::new(Slot {
    kind: ChildKind::Aggr,
    statement: spec.statement.clone(),
    outer_claim: spec.outer_claim.clone(),
    proof,
    proof_address,
    claims_bytes: serialize_claims(&[&spec.outer_claim]),
  }))
}

/// Prepares and proves one slot in place.
pub(super) fn prove_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  children: &[Arc<Slot>],
) -> Result<Arc<Slot>, String> {
  let staged = prepare_slot(ctx, slot_index, children)?;
  finish_slot(ctx, slot_index, staged)
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
  let (proof, proof_address) = load_cached(
    ctx.aggr_system,
    ctx.store_dir,
    ctx.cache_dir,
    child_index,
    spec,
  )
  .ok_or_else(|| {
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

#[tracing::instrument(level = "info", skip_all, name = "aiur/replay", fields(slot = target))]
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
