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

use crate::{aiur::lean_unbox_nat_as_usize, lean::LeanAiurAggregateExpected};
use aiur::synthesis::AiurSystem;
use ix_kernel::shard::ShardManifest;
use ixvm_codegen::env_handle::EnvHandle;
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanExcept, LeanExternal, LeanNat, LeanOwned,
  LeanString,
};
use plan::{PlanOp, SlotSpec, build_specs, build_statement_specs, plan_replay};
use prepare::{PreparedShard, prepare_run, validate_root_statement};
use protocol::{ChildKind, allowed_blob};
use prove::{ProveContext, run_replay};
use scheduler::run_scheduler;
use statement::Statement;
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
  time::Instant,
};
use store::{load_input_proofs, persist_wrapper, wrapper_address};

mod plan;
mod prepare;
mod protocol;
mod prove;
mod scheduler;
mod statement;
mod store;

const MIB: usize = 1024 * 1024;
const GIB: usize = 1024 * 1024 * 1024;

fn format_gib(bytes: usize) -> String {
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
    config.verify_idx,
    config.aggr_idx,
    config.structural_above,
    config.direct_joins,
    &aggr_vk,
    &allowed,
    config.cache_fri_bytes,
  )?;
  let replay_plan = config
    .reprove_slot
    .map(|target| plan_replay(&specs, target))
    .transpose()?;
  let specs_at = Instant::now();
  print_plan(&specs, &prepared.shards, config.structural_above);
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
  let cache_path = ix_root.join("cache").join("aggregate");
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
  } else {
    eprintln!("[aggregate] cache disabled (--no-cache)");
  }
  if !config.write_outputs {
    eprintln!("[aggregate] output writes disabled (--no-write)");
  }
  let needs_input_proofs =
    replay_plan.as_ref().is_none_or(|plan| plan.needs_input_proofs);
  let proofs = if needs_input_proofs {
    Some(load_input_proofs(config.proof_hexes, &store_dir, &prepared.shards)?)
  } else {
    let supplied =
      config.proof_hexes.lines().filter(|line| !line.is_empty()).count();
    eprintln!(
      "[aggregate] replay uses cached aggregate children; skipping {supplied} supplied shard proof wrapper(s)"
    );
    None
  };
  let proofs_at = Instant::now();
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
  let slots = run_scheduler(context, config.jobs, config.ram_budget_bytes)?;
  let root = slots.last().ok_or("aggregate plan produced no root slot")?;
  if root.kind != ChildKind::Aggr {
    return Err("aggregate plan produced a raw IxVM root".into());
  }
  validate_root_statement(&prepared, &root.statement)?;
  config.aggr_system.verify(&root.outer_claim, &root.proof).map_err(
    |error| format!("aggregate root proof failed verification: {error:?}"),
  )?;
  let (address, persisted) = match &root.proof_address {
    Some(address) => (address.clone(), true),
    None if config.write_outputs => {
      (persist_wrapper(&store_dir, &root.statement, &root.proof)?, true)
    },
    None => (wrapper_address(&root.statement, &root.proof)?, false),
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

/// Native manifest/environment binding for `ix verify --aggregate --ixes`.
/// The returned claim comes from the exact statement builder used by Stage 2,
/// after a full constant/shard/assumption audit.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_aggregate_expected(
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let manifest_bytes =
      fs::read(Path::new(manifest_path.as_str())).map_err(|error| {
        format!("read manifest {}: {error}", manifest_path.as_str())
      })?;
    let manifest = ShardManifest::from_bytes(&manifest_bytes)
      .map_err(|error| format!("manifest parse failed: {error}"))?;
    expected_from_manifest(
      &env_handle.get().env,
      &manifest,
      lean_unbox_nat_as_usize(structural_above.inner()),
    )
  }));
  match result {
    Ok(Ok((statement, constant_count))) => {
      let expected = LeanAiurAggregateExpected::alloc(0);
      expected.set_obj(0, LeanByteArray::from_bytes(&statement.claim_bytes));
      expected.set_obj(1, LeanOwned::box_usize(constant_count));
      LeanExcept::ok(expected)
    },
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "native aggregate verification setup panicked: {}",
      panic_text(&payload)
    )),
  }
}

/// Production FFI called once after Lean has compiled the IxVM and ixAggr
/// systems. Proof addresses are newline-separated to keep the ABI flat.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_stage2_aggregate(
  ixvm_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  proof_hexes: LeanString<LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  jobs: LeanNat<LeanBorrowed<'_>>,
  ram_budget_bytes: LeanNat<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
  reprove_slot_code: LeanNat<LeanBorrowed<'_>>,
  direct_joins: bool,
  plan_only: bool,
  cache_fri_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_cache: bool,
  write_outputs: bool,
) -> LeanExcept<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let reprove_slot =
      lean_unbox_nat_as_usize(reprove_slot_code.inner()).checked_sub(1);
    run(RunConfig {
      ixvm_system: ixvm_system.get(),
      aggr_system: aggr_system.get(),
      env_handle: env_handle.get(),
      manifest_path: Path::new(manifest_path.as_str()),
      proof_hexes: proof_hexes.as_str(),
      verify_idx: lean_unbox_nat_as_usize(verify_idx.inner()),
      aggr_idx: lean_unbox_nat_as_usize(aggr_idx.inner()),
      jobs: lean_unbox_nat_as_usize(jobs.inner()),
      ram_budget_bytes: lean_unbox_nat_as_usize(ram_budget_bytes.inner()),
      structural_above: lean_unbox_nat_as_usize(structural_above.inner()),
      reprove_slot,
      direct_joins,
      plan_only,
      cache_fri_bytes: cache_fri_bytes.as_bytes(),
      use_cache,
      write_outputs,
    })
  }));
  match result {
    Ok(Ok(address)) => LeanExcept::ok(LeanString::new(&address)),
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "native Stage 2 orchestration panicked: {}",
      panic_text(&payload)
    )),
  }
}

#[cfg(test)]
mod tests;
