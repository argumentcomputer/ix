//! `ix aggregate` for any backend: fold supplied claim proofs into the
//! manifest's root, or into one subtree of it, on the slot scheduler, with
//! the fold the lane controller proves with (claims join directly).

use std::{
  fs,
  path::{Path, PathBuf},
  sync::{Arc, Condvar, Mutex},
};

use ix_common::address::Address;
use ixon::Proof as IxonProof;
use ixon::shard::ShardManifest;
use record_pool::{RecordPool, RecordReservation};

use crate::{
  backend::{Backend, BackendSlot, Run},
  discharge::{BindingSource, discharge, load_binding},
  plan::{FoldPolicy, PlanOp, SlotSpec, build_specs, plan_replay},
  prepare::{PreparedRun, prepare_run, validate_root_statement},
  protocol::ChildKind,
  scheduler::{Prepared, SlotWorker, run_scheduler_with},
  statement::Statement,
  store::{
    InputProofs, load_cached, load_input_proofs, persist_wrapper, wrapper_bytes,
  },
};

pub struct Config {
  /// Lanes, and slots proving at once.
  pub lanes: usize,
  /// Slots executing ahead of the provers; 0 fuses execution and proving.
  pub exec_ahead: usize,
  pub structural_above: usize,
  pub reprove_slot: Option<usize>,
  pub subtree: Option<usize>,
  pub plan_only: bool,
  pub use_cache: bool,
  pub write_outputs: bool,
  /// Wrap the root until it is one trace shard.
  pub wrap_root: bool,
  /// Claims assume their role binding meets the specifications instead of
  /// validating it.
  pub assume_binding: bool,
  /// A proof of the environment's `Binding` claim. The claims then assume
  /// their binding (as with `assume_binding`), and the root discharges
  /// that assumption before any wrap.
  pub binding_proof: Option<BindingSource>,
  /// The content-addressed store; `None` is `~/.ix/store`.
  pub store_dir: Option<PathBuf>,
  /// The aggregate cache; `None` is `AIUR_LANES_CACHE_DIR/aggregate`, or
  /// `~/.ix/cache/aggregate`.
  pub cache_dir: Option<PathBuf>,
}

fn home() -> Result<PathBuf, String> {
  std::env::var_os("HOME")
    .map(PathBuf::from)
    .ok_or_else(|| "no HOME environment variable".into())
}

/// A reservation outside any shared budget: slots here are gated by the
/// scheduler, not by a record pool.
pub(crate) fn reservation() -> Result<(RecordPool, RecordReservation), String> {
  let pool = RecordPool::new(usize::MAX / 2, 16 << 20);
  let reservation = pool
    .try_admit()
    .map_err(|e| format!("record admission: {e:?}"))?
    .ok_or("record pool refused admission")?;
  Ok((pool, reservation))
}

/// Lanes handed out to one proving thread at a time.
struct Lanes<L> {
  lanes: Vec<L>,
  free: Mutex<Vec<usize>>,
  released: Condvar,
}

impl<L> Lanes<L> {
  fn new(lanes: Vec<L>) -> Self {
    let free = Mutex::new((0..lanes.len()).collect());
    Self { lanes, free, released: Condvar::new() }
  }

  fn with<R>(&self, work: impl FnOnce(&L) -> R) -> R {
    let index = {
      let mut free = self.free.lock().unwrap_or_else(|e| e.into_inner());
      loop {
        if let Some(index) = free.pop() {
          break index;
        }
        free = self.released.wait(free).unwrap_or_else(|e| e.into_inner());
      }
    };
    let result = work(&self.lanes[index]);
    self.free.lock().unwrap_or_else(|e| e.into_inner()).push(index);
    self.released.notify_one();
    result
  }
}

struct Worker<'a, B: Backend> {
  backend: &'a B,
  run: Run<'a, B::Claim>,
  lanes: &'a Lanes<B::Lane>,
  proofs: &'a [Option<Arc<IxonProof>>],
  /// The slots a supplied or cached proof already covers, resolved before
  /// scheduling.
  resolved: &'a [Option<Arc<BackendSlot<B>>>],
}

impl<B: Backend> Worker<'_, B> {
  /// A supplied claim proof, verified against the claim the plan expects.
  fn leaf(&self, index: usize) -> Result<Arc<BackendSlot<B>>, String> {
    let spec = &self.run.specs[index];
    let PlanOp::Leaf(shard) = spec.op else {
      return Err(format!("slot {index} is not a claim"));
    };
    let id = self.run.prepared[shard].original_id;
    let wrapper = self
      .proofs
      .get(shard)
      .and_then(Option::as_ref)
      .ok_or_else(|| format!("claim {id} has no supplied proof"))?;
    let backend = self.backend;
    let proof = backend
      .decode_proof(&wrapper.proof)
      .map_err(|error| format!("claim {id} proof does not decode: {error}"))?;
    let claim_bytes = &self.run.prepared[shard].statement.claim_bytes;
    let inner = backend.outer_claim(ChildKind::Ixvm, claim_bytes);
    backend.verify(ChildKind::Ixvm, &inner, &proof).map_err(|error| {
      format!("claim {id} proof fails native verification: {error}")
    })?;
    Ok(Arc::new(BackendSlot::<B> {
      kind: ChildKind::Ixvm,
      statement: spec.statement.clone(),
      claims_bytes: backend.claims_bytes(&inner),
      outer_claim: inner,
      proof,
      proof_address: None,
    }))
  }

  fn execute(
    &self,
    index: usize,
    children: &[Arc<BackendSlot<B>>],
  ) -> Result<B::Staged, String> {
    let (_pool, reservation) = reservation()?;
    let _binding = self.backend.bind(&reservation);
    let staged = self.backend.execute_aggregate(
      &self.lanes.lanes[0],
      self.run,
      index,
      children,
      &reservation,
    )?;
    reservation.finish_execution();
    Ok(staged)
  }

  fn prove(
    &self,
    index: usize,
    staged: B::Staged,
  ) -> Result<Arc<BackendSlot<B>>, String> {
    self
      .lanes
      .with(|lane| self.backend.prove_aggregate(lane, self.run, index, staged))
  }
}

impl<B: Backend> SlotWorker for Worker<'_, B>
where
  B::Claim: Sync,
{
  type Claim = B::Claim;
  type Staged = B::Staged;
  type Done = BackendSlot<B>;

  fn specs(&self) -> &[SlotSpec<B::Claim>] {
    self.run.specs
  }

  /// Every slot is proven as trace shards within its lane's workspace, so
  /// no slot weighs on the scheduler's budget.
  fn weight(&self, _index: usize) -> usize {
    0
  }

  fn verify_only(&self, index: usize) -> bool {
    matches!(self.run.specs[index].op, PlanOp::Leaf(_))
  }

  fn cached(&self, index: usize) -> Option<Arc<BackendSlot<B>>> {
    self.resolved.get(index).cloned().flatten()
  }

  fn prepare(
    &self,
    index: usize,
    children: &[Arc<BackendSlot<B>>],
  ) -> Result<Prepared<B::Staged, BackendSlot<B>>, String> {
    match self.run.specs[index].op {
      PlanOp::Leaf(_) => Ok(Prepared::Done(self.leaf(index)?)),
      PlanOp::Join(..) => Ok(Prepared::Staged(self.execute(index, children)?)),
    }
  }

  fn finish(
    &self,
    index: usize,
    staged: B::Staged,
  ) -> Result<Arc<BackendSlot<B>>, String> {
    self.prove(index, staged)
  }
}

fn print_plan<C>(specs: &[SlotSpec<C>], prepared: &PreparedRun, above: usize) {
  let leaves =
    specs.iter().filter(|spec| matches!(spec.op, PlanOp::Leaf(_))).count();
  let structural = specs.iter().filter(|spec| spec.structural).count();
  eprintln!(
    "[aggregate] plan: {leaves} claims + {} binary joins ({structural} structural; threshold > {above} subject leaves)",
    specs.len() - leaves
  );
  for (index, spec) in specs.iter().enumerate() {
    match spec.op {
      PlanOp::Leaf(shard) => eprintln!(
        "  slot {index}: claim {} ({} subjects)",
        prepared.shards[shard].original_id, spec.subject_count
      ),
      PlanOp::Join(left, right) => eprintln!(
        "  slot {index}: {} shape {} slots {left}, {right} ({} subjects)",
        if spec.structural { "structural" } else { "flat" },
        spec.shape.unwrap_or(u8::MAX),
        spec.subject_count
      ),
    }
  }
}

/// An aggregate slot's proof from the aggregate cache, verified natively.
fn cached_slot<B: Backend>(
  backend: &B,
  run: Run<'_, B::Claim>,
  index: usize,
) -> Option<Arc<BackendSlot<B>>> {
  let spec = &run.specs[index];
  if spec.kind != ChildKind::Aggr {
    return None;
  }
  let (proof, address) = load_cached(
    run.store_dir,
    run.cache_dir,
    index,
    spec,
    |bytes| backend.decode_proof(bytes),
    |outer, proof| backend.verify(ChildKind::Aggr, outer, proof),
  )?;
  Some(Arc::new(BackendSlot::<B> {
    kind: ChildKind::Aggr,
    statement: spec.statement.clone(),
    outer_claim: spec.outer_claim.clone(),
    proof,
    proof_address: Some(address),
    claims_bytes: backend.claims_bytes(&spec.outer_claim),
  }))
}

/// A supplied proof of an aggregate slot's statement, verified natively.
fn supplied_slot<B: Backend>(
  backend: &B,
  run: Run<'_, B::Claim>,
  index: usize,
  (wrapper, address): &(Arc<IxonProof>, Address),
) -> Result<Arc<BackendSlot<B>>, String> {
  let spec = &run.specs[index];
  let proof = backend.decode_proof(&wrapper.proof).map_err(|error| {
    format!("slot {index} proof {} does not decode: {error}", address.hex())
  })?;
  backend.verify(ChildKind::Aggr, &spec.outer_claim, &proof).map_err(
    |error| {
      format!(
        "slot {index} proof {} fails native verification: {error}",
        address.hex()
      )
    },
  )?;
  Ok(Arc::new(BackendSlot::<B> {
    kind: ChildKind::Aggr,
    statement: spec.statement.clone(),
    outer_claim: spec.outer_claim.clone(),
    proof,
    proof_address: Some(address.clone()),
    claims_bytes: backend.claims_bytes(&spec.outer_claim),
  }))
}

/// From `top` down, the highest aggregate slots a supplied proof or the
/// cache already proves, and the shards whose claims no such slot covers:
/// only those need supplied claim proofs.
fn resolve_covered<B: Backend>(
  backend: &B,
  run: Run<'_, B::Claim>,
  top: usize,
  aggregates: &[Option<(Arc<IxonProof>, Address)>],
  shards: usize,
) -> Result<(Vec<Option<Arc<BackendSlot<B>>>>, Vec<bool>), String> {
  let specs = run.specs;
  let mut resolved = vec![None; specs.len()];
  let mut required = vec![false; shards];
  let mut stack = vec![top];
  while let Some(index) = stack.pop() {
    let slot = match &aggregates[index] {
      Some(supplied) => Some(supplied_slot(backend, run, index, supplied)?),
      None => cached_slot(backend, run, index),
    };
    if let Some(slot) = slot {
      resolved[index] = Some(slot);
      continue;
    }
    match specs[index].op {
      PlanOp::Leaf(shard) => required[shard] = true,
      PlanOp::Join(left, right) => stack.extend([left, right]),
    }
  }
  Ok((resolved, required))
}

/// The slots under `target`, `target` included.
fn subtree_slots<C>(specs: &[SlotSpec<C>], target: usize) -> Vec<bool> {
  let mut active = vec![false; specs.len()];
  let mut stack = vec![target];
  while let Some(index) = stack.pop() {
    if active[index] {
      continue;
    }
    active[index] = true;
    if let PlanOp::Join(left, right) = specs[index].op {
      stack.push(left);
      stack.push(right);
    }
  }
  active
}

/// The proof a run produced.
pub struct Output {
  /// The store address of its `ixon::Proof` wrapper.
  pub address: Address,
  /// The encoded wrapper, when the run did not persist it (`--no-write`):
  /// the address then names nothing in the store, and these bytes are the
  /// only copy a caller can check.
  pub wrapper: Option<Vec<u8>>,
}

impl Output {
  fn stored(address: Address) -> Self {
    Self { address, wrapper: None }
  }

  fn unpersisted(
    statement: &Statement,
    proof: Result<Vec<u8>, String>,
  ) -> Result<Self, String> {
    let wrapper = wrapper_bytes(statement, proof)?;
    Ok(Self { address: Address::hash(&wrapper), wrapper: Some(wrapper) })
  }
}

/// The run: the proof of the root, of the subtree root with `subtree`, or
/// of the replayed slot with `reprove_slot`; nothing with `plan_only`.
pub fn run<B: Backend>(
  cfg: &Config,
  backend: &B,
  env: &ixon::Env,
  manifest_path: &Path,
  proof_hexes: &str,
) -> Result<Option<Output>, String>
where
  B::Claim: Sync,
{
  if cfg.lanes == 0 {
    return Err("at least one lane is required".into());
  }
  if cfg.subtree.is_some() && (cfg.reprove_slot.is_some() || cfg.wrap_root) {
    return Err(
      "--subtree cannot be combined with --reprove-slot or --wrap-root".into(),
    );
  }
  if cfg.reprove_slot.is_some() && (cfg.plan_only || !cfg.use_cache) {
    return Err(
      "--reprove-slot requires aggregate cache reads and cannot be combined with --plan-only"
        .into(),
    );
  }
  let manifest_bytes = fs::read(manifest_path).map_err(|error| {
    format!("read manifest {}: {error}", manifest_path.display())
  })?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))?;
  let ctx = crate::claim_context(
    env,
    cfg.assume_binding || cfg.binding_proof.is_some(),
  )?;
  let prepared = prepare_run(&ctx, env, &manifest)?;
  let specs = build_specs(
    &prepared,
    backend,
    FoldPolicy { structural_above: cfg.structural_above, direct_joins: true },
  )?;
  let replay =
    cfg.reprove_slot.map(|target| plan_replay(&specs, target)).transpose()?;
  let active = match cfg.subtree {
    None => vec![true; specs.len()],
    Some(target) => {
      let spec = specs.get(target).ok_or_else(|| {
        format!(
          "--subtree {target} is out of range; the plan has slots 0..{}",
          specs.len().saturating_sub(1)
        )
      })?;
      if spec.kind == ChildKind::Ixvm {
        return Err(format!("--subtree {target} selects a claim, not a join"));
      }
      if !cfg.plan_only && !cfg.use_cache {
        return Err(
          "--subtree publishes its root through the aggregate cache; it cannot run with --no-cache"
            .into(),
        );
      }
      subtree_slots(&specs, target)
    },
  };
  print_plan(&specs, &prepared, cfg.structural_above);
  if cfg.plan_only {
    if let Some(target) = cfg.subtree {
      let mut ids: Vec<u32> = specs
        .iter()
        .zip(&active)
        .filter_map(|(spec, &active)| match spec.op {
          PlanOp::Leaf(shard) if active => {
            Some(prepared.shards[shard].original_id)
          },
          _ => None,
        })
        .collect();
      ids.sort_unstable();
      let ids: Vec<String> = ids.iter().map(u32::to_string).collect();
      println!("subtree {target} shards: {}", ids.join(","));
    }
    return Ok(None);
  }

  let store_dir = match &cfg.store_dir {
    Some(dir) => dir.clone(),
    None => home()?.join(".ix").join("store"),
  };
  let cache_path = match &cfg.cache_dir {
    Some(dir) => dir.clone(),
    None => match std::env::var_os("AIUR_LANES_CACHE_DIR") {
      Some(dir) => PathBuf::from(dir).join("aggregate"),
      None => home()?.join(".ix").join("cache").join("aggregate"),
    },
  };
  let cache_dir = cfg.use_cache.then_some(cache_path.as_path());
  if let Some(dir) = cache_dir
    && cfg.write_outputs
  {
    fs::create_dir_all(dir)
      .map_err(|error| format!("create {}: {error}", dir.display()))?;
  }
  let needs_input_proofs =
    replay.as_ref().is_none_or(|plan| plan.needs_input_proofs);
  let inputs = if needs_input_proofs {
    load_input_proofs(proof_hexes, &store_dir, &prepared.shards, &specs)?
  } else {
    InputProofs::none(prepared.shards.len(), specs.len())
  };
  let binding = match &cfg.binding_proof {
    Some(source) if cfg.subtree.is_none() && cfg.reprove_slot.is_none() => {
      Some(load_binding(backend, &store_dir, source, env)?)
    },
    _ => None,
  };
  let lanes = Lanes::new(backend.lanes(cfg.lanes)?);
  let run = Run {
    specs: &specs,
    prepared: &prepared.shards,
    owner_by_address: &prepared.owner_by_address,
    store_dir: &store_dir,
    cache_dir,
    write_outputs: cfg.write_outputs,
    wrap_budget: None,
    reprove_slot: cfg.reprove_slot,
  };
  let (resolved, required) = match &replay {
    Some(plan) => {
      let mut required = vec![false; prepared.shards.len()];
      for &child in &plan.children {
        if let PlanOp::Leaf(shard) = specs[child].op {
          required[shard] = true;
        }
      }
      (vec![None; specs.len()], required)
    },
    None => resolve_covered(
      backend,
      run,
      cfg.subtree.unwrap_or(specs.len() - 1),
      &inputs.aggregates,
      prepared.shards.len(),
    )?,
  };
  let expected = required.iter().filter(|flag| **flag).count();
  let supplied = (0..prepared.shards.len())
    .filter(|&shard| required[shard] && inputs.claims[shard].is_some())
    .count();
  if supplied < expected {
    let missing: Vec<String> = (0..prepared.shards.len())
      .filter(|&shard| required[shard] && inputs.claims[shard].is_none())
      .map(|shard| prepared.shards[shard].original_id.to_string())
      .collect();
    return Err(format!(
      "aggregate requires {expected} shard proofs not covered by a supplied or cached aggregate; got {supplied} (missing shards {})",
      missing.join(",")
    ));
  }
  let worker = Worker {
    backend,
    run,
    lanes: &lanes,
    proofs: &inputs.claims,
    resolved: &resolved,
  };

  if let (Some(target), Some(plan)) = (cfg.reprove_slot, replay) {
    let children = plan
      .children
      .iter()
      .map(|&child| {
        if specs[child].kind == ChildKind::Ixvm {
          worker.leaf(child)
        } else {
          cached_slot(backend, run, child).ok_or_else(|| {
            format!(
              "replay slot {target} requires cached child slot {child}; prove through that child first"
            )
          })
        }
      })
      .collect::<Result<Vec<_>, String>>()?;
    let staged = worker.execute(target, &children)?;
    let slot = worker.prove(target, staged)?;
    backend
      .verify(ChildKind::Aggr, &slot.outer_claim, &slot.proof)
      .map_err(|error| format!("replayed slot {target} fails: {error}"))?;
    let output = match &slot.proof_address {
      Some(address) => Output::stored(address.clone()),
      None => {
        Output::unpersisted(&slot.statement, backend.encode_proof(&slot.proof))?
      },
    };
    eprintln!(
      "[aggregate] replay slot {target}: proof {}",
      output.address.hex()
    );
    return Ok(Some(output));
  }

  let mut slots =
    run_scheduler_with(cfg.lanes, cfg.exec_ahead, 1, &active, &worker)?;
  if let Some(target) = cfg.subtree {
    let slot = slots
      .get_mut(target)
      .and_then(Option::take)
      .ok_or_else(|| format!("scheduler produced no slot {target}"))?;
    backend
      .verify(ChildKind::Aggr, &slot.outer_claim, &slot.proof)
      .map_err(|error| format!("subtree {target} root fails: {error}"))?;
    let output = match &slot.proof_address {
      Some(address) => Output::stored(address.clone()),
      None if cfg.write_outputs => {
        return Err(format!(
          "subtree {target} root was proven but not published to the aggregate cache"
        ));
      },
      None => {
        Output::unpersisted(&slot.statement, backend.encode_proof(&slot.proof))?
      },
    };
    eprintln!("[aggregate] subtree {target} root: {}", output.address.hex());
    return Ok(Some(output));
  }
  let root = slots
    .last()
    .and_then(Option::as_ref)
    .ok_or("aggregate plan produced no root slot")?;
  if root.kind != ChildKind::Aggr {
    return Err(
      "the manifest has one claim; there is nothing to aggregate".into(),
    );
  }
  validate_root_statement(&prepared, &root.statement)?;
  let discharged;
  let root = match &binding {
    Some(binding) => {
      let (_pool, reservation) = reservation()?;
      let bound = backend.bind(&reservation);
      discharged = lanes.with(|lane| {
        discharge(backend, lane, run, root, binding, &reservation)
      })?;
      drop(bound);
      &discharged
    },
    None => root,
  };
  let mut wrapped: Option<B::Proof> = None;
  if cfg.wrap_root {
    loop {
      let current = wrapped.as_ref().unwrap_or(&root.proof);
      let shards = backend.trace_shards(current);
      if shards <= 1 {
        break;
      }
      let (_pool, reservation) = reservation()?;
      let binding = backend.bind(&reservation);
      let next = lanes.with(|lane| {
        backend.wrap_root(lane, run, root, current, &reservation)
      })?;
      drop(binding);
      if backend.trace_shards(&next) >= shards {
        eprintln!(
          "[aggregate] root wrap did not shrink the proof ({shards} shards); keeping the previous one"
        );
        break;
      }
      wrapped = Some(next);
    }
  }
  let (proof, proof_address) = match &wrapped {
    Some(proof) => (proof, None),
    None => (&root.proof, root.proof_address.as_ref()),
  };
  backend
    .verify(ChildKind::Aggr, &root.outer_claim, proof)
    .map_err(|error| format!("aggregate root proof fails: {error}"))?;
  let output = match proof_address {
    Some(address) => Output::stored(address.clone()),
    None if cfg.write_outputs => Output::stored(persist_wrapper(
      &store_dir,
      &root.statement,
      backend.encode_proof(proof),
    )?),
    None => Output::unpersisted(&root.statement, backend.encode_proof(proof))?,
  };
  eprintln!("[aggregate] root proof: {}", output.address.hex());
  Ok(Some(output))
}
