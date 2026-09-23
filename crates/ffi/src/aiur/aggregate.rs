//! Native Stage 2 orchestration for `ix aggregate`.
//!
//! Lean still constructs the two Aiur bytecode systems, because their source
//! programs are Lean-authored. Everything data-dependent after that point is
//! kept here: manifest/environment binding, shard-claim reconstruction,
//! statement folding, cache validation, dependency scheduling, recursive
//! advice construction, proving, and persistence.
//!
//! The host statements deliberately cache roots and sorted leaves. Structural
//! subject trees carry only their two children and a small shard-membership
//! bitset, so deciding whether an assumption is discharged is O(1), and a
//! Merkle path is O(log n). This avoids the eager recursive `root`/`leaves`/
//! `contains` traversals that made the former Lean startup super-linear.

use aiur::synthesis::{AiurProof, AiurSystem};
use ix_kernel::shard::ShardManifest;
use ixvm_codegen::env_handle::EnvHandle;
use plan::{
  FoldPolicy, PlanIdentity, PlanOp, SlotSpec, build_specs,
  build_statement_specs, plan_replay,
};
use prepare::{PreparedShard, prepare_run, validate_root_statement};
use protocol::{ChildKind, allowed_blob, inner_claim};
use prove::{ProveContext, run_replay, wrap_root};
use rayon::prelude::*;
use scheduler::run_scheduler;
use statement::Statement;
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
  time::Instant,
};
pub(crate) use store::write_store;
use store::{load_input_proofs, persist_wrapper, wrapper_address};

mod ffi;
mod plan;
mod prepare;
mod protocol;
mod prove;
mod scheduler;
mod statement;
mod store;

const MIB: usize = 1024 * 1024;
const GIB: usize = 1024 * 1024 * 1024;

pub(crate) fn format_gib(bytes: usize) -> String {
  let tenths = bytes.saturating_mul(10) / GIB;
  format!("{}.{:01}", tenths / 10, tenths % 10)
}

fn format_mib(bytes: usize) -> String {
  let tenths = bytes.saturating_mul(10) / MIB;
  format!("{}.{:01}", tenths / 10, tenths % 10)
}

#[derive(Clone, Copy)]
struct RunConfig<'a> {
  ixvm_system: &'a AiurSystem,
  aggr_system: &'a AiurSystem,
  env_handle: &'a EnvHandle,
  manifest_path: &'a Path,
  proof_hexes: &'a str,
  verify_idx: usize,
  aggr_idx: usize,
  jobs: usize,
  ram_budget_bytes: usize,
  structural_above: usize,
  reprove_slot: Option<usize>,
  direct_joins: bool,
  plan_only: bool,
  cache_fri_bytes: &'a [u8],
  use_cache: bool,
  write_outputs: bool,
  trace_shards: bool,
  range_width: usize,
  /// Wrap the root proof (shape 1) until the final proof is a single
  /// trace shard.
  wrap_root: bool,
  /// Slots preparing (executing) ahead of the provers; `0` fuses
  /// preparation and proving on one worker per slot.
  exec_ahead: usize,
  /// `ix verify --ixes <proofs>`: stop after the proof import — every
  /// shard claim reconstructed natively, every supplied proof bound to its
  /// shard by claim digest and verified in parallel, exactly one per shard
  /// — and report that composed verdict instead of proving.
  verify_only: bool,
  /// Prove only the plan subtree rooted at this slot, from the proofs of
  /// the leaves under it, and report that slot's proof; the root-only steps
  /// (root validation, wrapping) are skipped. `None` proves the whole plan.
  subtree: Option<usize>,
}

fn expected_from_manifest(
  env: &ixon::Env,
  manifest: &ShardManifest,
  structural_above: usize,
) -> Result<(Arc<Statement>, usize), String> {
  let prepared = prepare_run(env, manifest)?;
  let specs = build_statement_specs(&prepared, structural_above)?;
  let root = specs
    .last()
    .ok_or("aggregate manifest produced no root statement")?
    .statement
    .clone();
  validate_root_statement(&prepared, &root)?;
  Ok((root, prepared.env_count))
}

fn print_plan(
  specs: &[SlotSpec],
  prepared: &[PreparedShard],
  threshold: usize,
) {
  let leaves =
    specs.iter().filter(|spec| matches!(spec.op, PlanOp::Leaf(_))).count();
  let wraps = specs
    .iter()
    .filter(|spec| {
      matches!(spec.op, PlanOp::Leaf(_)) && spec.kind == ChildKind::Aggr
    })
    .count();
  let structural = specs.iter().filter(|spec| spec.structural).count();
  let policy = if wraps == leaves {
    format!("{wraps} wraps")
  } else {
    format!("{} direct IxVM leaves", leaves - wraps)
  };
  eprintln!(
    "[aggregate] plan: {policy} + {} binary joins ({structural} structural; threshold > {threshold} subject leaves)",
    specs.len() - leaves
  );
  for (index, spec) in specs.iter().enumerate() {
    match spec.op {
      PlanOp::Leaf(shard) => {
        let mode =
          if spec.kind == ChildKind::Ixvm { "raw shard" } else { "wrap shard" };
        eprintln!(
          "  slot {index}: {mode} {} ({} subjects)",
          prepared[shard].original_id, spec.subject_count
        );
      },
      PlanOp::Join(left, right) => {
        let mode = if spec.structural { "structural" } else { "flat" };
        eprintln!(
          "  slot {index}: {mode} shape {} slots {left}, {right} ({} subjects)",
          spec.shape.unwrap_or(u8::MAX),
          spec.subject_count
        );
      },
    }
  }
}

fn run(config: RunConfig<'_>) -> Result<String, String> {
  if config.cache_fri_bytes.len() != 40 {
    return Err(format!(
      "aggregate cache FRI serialization is {} bytes, expected 40",
      config.cache_fri_bytes.len()
    ));
  }
  if config.plan_only && config.reprove_slot.is_some() {
    return Err("--plan-only cannot be combined with --reprove-slot".into());
  }
  if config.reprove_slot.is_some() && !config.use_cache {
    return Err("--reprove-slot requires aggregate cache reads".into());
  }
  let started = Instant::now();
  let manifest_bytes = fs::read(config.manifest_path).map_err(|error| {
    format!("read manifest {}: {error}", config.manifest_path.display())
  })?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))?;
  let parsed_at = Instant::now();
  let prepared = prepare_run(&config.env_handle.env, &manifest)?;
  let prepared_at = Instant::now();

  let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(config.ixvm_system)
    .map_err(|error| format!("IxVM VK serialization failed: {error}"))?;
  let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(config.aggr_system)
    .map_err(|error| format!("ixAggr VK serialization failed: {error}"))?;
  let allowed =
    allowed_blob(&ixvm_vk, config.verify_idx, &aggr_vk, config.aggr_idx);
  let specs = build_specs(
    &prepared,
    PlanIdentity {
      verify_idx: config.verify_idx,
      aggr_idx: config.aggr_idx,
      aggr_vk: &aggr_vk,
      allowed: &allowed,
      cache_fri_bytes: config.cache_fri_bytes,
    },
    FoldPolicy {
      structural_above: config.structural_above,
      direct_joins: config.direct_joins,
    },
  )?;
  let replay_plan = config
    .reprove_slot
    .map(|target| plan_replay(&specs, target))
    .transpose()?;
  // The slots this run proves: the whole plan, or one subtree of it.
  let active: Vec<bool> = match config.subtree {
    None => vec![true; specs.len()],
    Some(target) => {
      if config.reprove_slot.is_some() {
        return Err("--subtree cannot be combined with --reprove-slot".into());
      }
      if config.verify_only {
        return Err("--subtree has no meaning for a composed verdict".into());
      }
      if config.wrap_root {
        return Err(
          "--wrap-root applies to the root; --subtree proves a subtree".into(),
        );
      }
      if !config.plan_only && !config.use_cache {
        return Err(
          "--subtree publishes its root through the aggregate cache; it cannot run with --no-cache"
            .into(),
        );
      }
      let spec = specs.get(target).ok_or_else(|| {
        format!(
          "--subtree {target} is out of range; the plan has slots 0..{}",
          specs.len().saturating_sub(1)
        )
      })?;
      if spec.kind == ChildKind::Ixvm {
        return Err(format!(
          "--subtree {target} selects a raw IxVM leaf, not a Stage 2 proof"
        ));
      }
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
    },
  };
  // The manifest shards whose proofs this run takes as input.
  let mut required = vec![false; prepared.shards.len()];
  for (index, spec) in specs.iter().enumerate() {
    if let PlanOp::Leaf(shard) = spec.op {
      required[shard] = active[index];
    }
  }
  let specs_at = Instant::now();
  if !config.verify_only {
    print_plan(&specs, &prepared.shards, config.structural_above);
  }
  if let (true, Some(target)) = (config.plan_only, config.subtree) {
    // The lane's `ix prove --shards` argument, on stdout as one line.
    let mut ids: Vec<u32> = required
      .iter()
      .enumerate()
      .filter(|(_, flag)| **flag)
      .map(|(shard, _)| prepared.shards[shard].original_id)
      .collect();
    ids.sort_unstable();
    let ids: Vec<String> = ids.iter().map(u32::to_string).collect();
    println!("subtree {target} shards: {}", ids.join(","));
  }
  if config.plan_only {
    eprintln!(
      "[aggregate] Rust plan startup: manifest {:.3}s, env/claims {:.3}s, plan/statements {:.3}s; total {:.3}s",
      (parsed_at - started).as_secs_f64(),
      (prepared_at - parsed_at).as_secs_f64(),
      (specs_at - prepared_at).as_secs_f64(),
      (specs_at - started).as_secs_f64(),
    );
    return Ok(String::new());
  }

  let home = std::env::var_os("HOME").ok_or("no HOME environment variable")?;
  let ix_root = PathBuf::from(home).join(".ix");
  let store_dir = ix_root.join("store");
  let cache_path = std::env::var_os("AIUR_AGGREGATE_CACHE_DIR")
    .map_or_else(|| ix_root.join("cache").join("aggregate"), PathBuf::from);
  let cache_dir = config.use_cache.then_some(cache_path.as_path());
  if let Some(dir) = cache_dir {
    if config.write_outputs {
      fs::create_dir_all(dir).map_err(|error| {
        format!("create aggregate cache {}: {error}", dir.display())
      })?;
    } else if config.reprove_slot.is_some() && !dir.is_dir() {
      return Err(format!(
        "aggregate replay cache {} does not exist",
        dir.display()
      ));
    }
  } else if !config.verify_only {
    eprintln!("[aggregate] cache disabled (--no-cache)");
  }
  if !config.write_outputs && !config.verify_only {
    eprintln!("[aggregate] output writes disabled (--no-write)");
  }
  let needs_input_proofs =
    replay_plan.as_ref().is_none_or(|plan| plan.needs_input_proofs);
  let proofs = if needs_input_proofs {
    Some(load_input_proofs(
      config.proof_hexes,
      &store_dir,
      &prepared.shards,
      &required,
    )?)
  } else {
    let supplied =
      config.proof_hexes.lines().filter(|line| !line.is_empty()).count();
    eprintln!(
      "[aggregate] replay uses cached aggregate children; skipping {supplied} supplied shard proof wrapper(s)"
    );
    None
  };
  let proofs_at = Instant::now();
  if config.verify_only {
    let shards = prepared.shards.len();
    let proofs = proofs.as_deref().unwrap_or(&[]);
    let bound = proofs.iter().flatten().count();
    if bound != shards {
      return Err(format!(
        "bound {bound} shard proofs but the manifest has {shards} shards"
      ));
    }
    let failures: Vec<String> = proofs
      .par_iter()
      .enumerate()
      .filter_map(|(shard, wrapper)| {
        let wrapper = wrapper.as_ref()?;
        let statement = &prepared.shards[shard].statement;
        let inner = inner_claim(config.verify_idx, &statement.claim_bytes);
        let proof = match AiurProof::from_bytes(&wrapper.proof) {
          Ok(proof) => proof,
          Err(error) => {
            return Some(format!(
              "shard {shard}: proof does not decode: {error}"
            ));
          },
        };
        config.ixvm_system.verify(&inner, &proof).err().map(|error| {
          format!("shard {shard}: proof fails verification: {error:?}")
        })
      })
      .collect();
    if !failures.is_empty() {
      return Err(failures.join("; "));
    }
    eprintln!(
      "[verify] OK: composed verdict — all {shards} shards proven + disjoint cover ({shards} proofs verified natively in {:.1}s; claims {:.1}s)",
      proofs_at.elapsed().as_secs_f64(),
      (prepared_at - parsed_at).as_secs_f64(),
    );
    return Ok(String::new());
  }
  eprintln!(
    "[aggregate] Rust startup: manifest {:.3}s, env/claims {:.3}s, plan/statements {:.3}s, proofs {:.3}s; total {:.3}s",
    (parsed_at - started).as_secs_f64(),
    (prepared_at - parsed_at).as_secs_f64(),
    (specs_at - prepared_at).as_secs_f64(),
    (proofs_at - specs_at).as_secs_f64(),
    (proofs_at - started).as_secs_f64(),
  );
  let context = ProveContext {
    specs: &specs,
    prepared: &prepared.shards,
    proofs: proofs.as_deref(),
    owner_by_address: &prepared.owner_by_address,
    ixvm_system: config.ixvm_system,
    aggr_system: config.aggr_system,
    ixvm_vk: &ixvm_vk,
    aggr_vk: &aggr_vk,
    allowed: &allowed,
    verify_idx: config.verify_idx,
    aggr_idx: config.aggr_idx,
    store_dir: &store_dir,
    cache_dir,
    reprove_slot: config.reprove_slot,
    write_outputs: config.write_outputs,
    // Slots share the run's budget evenly across the concurrent jobs; with
    // every ready slot allowed at once, each gets the whole budget and the
    // scheduler's per-slot weights alone bound concurrency.
    wrap_budget: config
      .trace_shards
      .then(|| config.ram_budget_bytes / config.jobs.max(1)),
    range_width: config.range_width,
    range_jobs: config.jobs.max(1),
  };
  if let (Some(target), Some(plan)) =
    (config.reprove_slot, replay_plan.as_ref())
  {
    return run_replay(context, target, plan);
  }

  let jobs_label = if config.jobs == 0 {
    "all ready slots".to_string()
  } else {
    config.jobs.to_string()
  };
  eprintln!(
    "[aggregate] scheduler: jobs={jobs_label}, RAM budget {} GiB; wrap/self 195.0 GiB, direct 390.0 GiB, mixed 340.0 GiB, flat +1 MiB/subject",
    format_gib(config.ram_budget_bytes)
  );
  let mut slots = run_scheduler(
    context,
    config.jobs,
    config.exec_ahead,
    config.ram_budget_bytes,
    &active,
  )?;
  if let Some(target) = config.subtree {
    // A lane's success means its subtree root is proven, verified and
    // published where the final run will look for it.
    let slot = slots
      .get_mut(target)
      .and_then(Option::take)
      .ok_or_else(|| format!("scheduler produced no slot {target}"))?;
    config.aggr_system.verify(&slot.outer_claim, &slot.proof).map_err(
      |error| {
        format!("subtree {target} root proof failed verification: {error:?}")
      },
    )?;
    let (address, disposition) = match slot.proof_address.as_ref() {
      Some(address) => (address.clone(), ""),
      None if config.write_outputs => {
        return Err(format!(
          "subtree {target} root was proven but not published to the aggregate cache"
        ));
      },
      None => {
        (wrapper_address(&slot.statement, &slot.proof)?, " (not persisted)")
      },
    };
    eprintln!(
      "[aggregate] subtree {target} root: {}{disposition}",
      address.hex()
    );
    return Ok(address.hex());
  }
  let root = slots
    .last()
    .and_then(Option::as_ref)
    .ok_or("aggregate plan produced no root slot")?;
  if root.kind != ChildKind::Aggr {
    return Err("aggregate plan produced a raw IxVM root".into());
  }
  validate_root_statement(&prepared, &root.statement)?;
  // Wrap until the final proof is a single trace shard: each wrap verifies
  // the previous proof, so its own execution shrinks with that proof's
  // shard count until one shard verifies it.
  let mut wrapped: Option<AiurProof> = None;
  if config.wrap_root {
    loop {
      let current = wrapped.as_ref().unwrap_or(&root.proof);
      let shards = current.preamble.headers.len();
      if shards <= 1 {
        break;
      }
      let next = wrap_root(context, root, current)?;
      if next.preamble.headers.len() >= shards {
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
  config.aggr_system.verify(&root.outer_claim, proof).map_err(|error| {
    format!("aggregate root proof failed verification: {error:?}")
  })?;
  let (address, persisted) = match proof_address {
    Some(address) => (address.clone(), true),
    None if config.write_outputs => {
      (persist_wrapper(&store_dir, &root.statement, proof)?, true)
    },
    None => (wrapper_address(&root.statement, proof)?, false),
  };
  let disposition = if persisted { "" } else { " (not persisted)" };
  eprintln!("[aggregate] root proof: {}{disposition}", address.hex());
  Ok(address.hex())
}

fn panic_text(payload: &Box<dyn std::any::Any + Send>) -> &str {
  payload
    .downcast_ref::<&str>()
    .copied()
    .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
    .unwrap_or("unknown Rust panic")
}

#[cfg(test)]
mod tests;
