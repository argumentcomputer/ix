//! Native startup for whole-partition or selected-shard `ix check`. Small counts
//! cross the FFI: the mmap, manifest, ownership lists and audit stay in Rust.
//! The kernel/witness executor is shared with the existing Lean wave driver.

mod refine;

use std::{fs, path::Path, sync::Arc, time::Instant};

use aiur::{bytecode::Toplevel, synthesis::AiurSystem};
use ix_common::address::Address;
use ix_kernel::shard::ShardManifest;
use ixon::{ConstantInfo, Env};
use lean_ffi::object::{
  LeanBorrowed, LeanExcept, LeanIOResult, LeanNat, LeanOption, LeanOwned,
  LeanRef, LeanString,
};
use rayon::prelude::*;
use rustc_hash::FxHashMap;
use serde_json::{Value, json};

use super::{
  admission::Admission,
  lean_unbox_nat_as_usize,
  protocol::{
    ShardCheckResult, ShardExecutor, decode_commitment_parameters,
    decode_fri_parameters,
  },
  toplevel::decode_toplevel,
};
use crate::lean::{
  LeanAiurCommitmentParameters, LeanAiurFriParameters,
  LeanAiurPartitionCheckResult, LeanAiurToplevel,
};

/// Validate every serialized body and assign it to exactly one shard, in a
/// single parallel pass. Do not replace parsing with a header-only peek: an
/// unparseable constant must fail coverage even if no other constant uses it.
/// Projection wrappers belong to their block, not to their own address.
fn prepare_owned(
  env: &Env,
  manifest: &ShardManifest,
) -> Result<Vec<Vec<Address>>, String> {
  if manifest.shards.is_empty() {
    return Err("manifest contains no shards".into());
  }
  let mut block_to_shard = FxHashMap::default();
  for (index, shard) in manifest.shards.iter().enumerate() {
    // The CLI's Lean parser requires dense, ascending ids. Keep that gate
    // even though the general Rust manifest representation permits other ids.
    if usize::try_from(shard.id).ok() != Some(index) {
      return Err(format!("manifest shard entry {index} has id {}", shard.id));
    }
    for block in &shard.blocks {
      if let Some(previous) = block_to_shard.insert(block.clone(), index) {
        return Err(format!(
          "block {} is owned more than once (shards {previous} and {index})",
          block.hex(),
        ));
      }
    }
  }
  let mut addresses: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  addresses.par_sort_unstable();
  // Indexed collection makes both ownership ordering and the first error
  // independent of Rayon scheduling; no partially validated plan escapes.
  let classified: Vec<Result<usize, String>> = addresses
    .par_iter()
    .map(|addr| {
      let lc = env
        .consts
        .get(addr)
        .ok_or_else(|| format!("constant {} disappeared", addr.hex()))?;
      if !lc.verify_address(addr) {
        return Err(format!(
          "constant {}: content-address mismatch",
          addr.hex()
        ));
      }
      let constant = lc.get().map_err(|error| {
        format!("cannot parse constant {}: {error}", addr.hex())
      })?;
      let block = match &constant.info {
        ConstantInfo::IPrj(p) => &p.block,
        ConstantInfo::CPrj(p) => &p.block,
        ConstantInfo::RPrj(p) => &p.block,
        ConstantInfo::DPrj(p) => &p.block,
        _ => addr,
      };
      block_to_shard.get(block).copied().ok_or_else(|| {
        format!(
          "constant {} (block {}) has no owning shard",
          addr.hex(),
          block.hex(),
        )
      })
    })
    .collect();
  let owners = classified.into_iter().collect::<Result<Vec<_>, _>>()?;
  let mut owned = vec![Vec::new(); manifest.shards.len()];
  for (addr, owner) in addresses.into_iter().zip(owners) {
    owned[owner].push(addr);
  }
  Ok(owned)
}

struct LoadedEnv {
  env: Env,
  /// Diagnostic alias only; never used for ownership or checking decisions.
  names: FxHashMap<Address, String>,
  bytes: usize,
}

fn load_env(path: &Path, keep_names: bool) -> Result<LoadedEnv, String> {
  let file = fs::File::open(path)
    .map_err(|e| format!("open {}: {e}", path.display()))?;
  // As for the existing Env mmap reader, the input must not be modified or
  // truncated while this run holds the mapping. No path here writes the input.
  let mmap = Arc::new(
    unsafe { memmap2::Mmap::map(&file) }
      .map_err(|e| format!("mmap {}: {e}", path.display()))?,
  );
  // Same metadata-light decoder as Lean deEnvAnon, including validation of
  // every section. Avoid materializing the 28 GiB input as a Lean ByteArray.
  let index = Env::parse_lazy_index(&mmap)?;
  let env = Env::from_lazy_index_mmap(&index, &mmap)?;
  let names = if keep_names {
    // Match registerName's last diagnostic alias for an address. Aliases
    // cannot be collapsed for semantic name resolution, which is not used here.
    index.named.iter().map(|n| (n.addr.clone(), n.name.pretty())).collect()
  } else {
    FxHashMap::default()
  };
  Ok(LoadedEnv { env, names, bytes: mmap.len() })
}

struct RunConfig<'a> {
  ixe: &'a Path,
  manifest: &'a Path,
  jobs: usize,
  use_bytecode: bool,
  report: &'a str,
  revision: &'a str,
  command: &'a str,
  budget_source: &'a str,
  selection: Option<&'a [usize]>,
}

/// Startup hashes/parses immutable input, not execution records. Keep its
/// modest default independent of --jobs and RAYON_NUM_THREADS, which users
/// often set to one to bound the much heavier witness-execution phase.
fn setup_pool_size(
  setting: Option<&str>,
  available: usize,
) -> Result<usize, String> {
  match setting {
    None => Ok(available.clamp(1, 8)),
    Some(value) => {
      value.parse::<usize>().ok().filter(|&n| n > 0).ok_or_else(|| {
        "IX_AIUR_SETUP_THREADS must be a positive thread count".to_string()
      })
    },
  }
}

fn prepare_with_pool(
  env: &Env,
  manifest: &ShardManifest,
  threads: usize,
) -> Result<Vec<Vec<Address>>, String> {
  let pool = rayon::ThreadPoolBuilder::new()
    .num_threads(threads)
    .thread_name(|i| format!("ixvm-setup-{i}"))
    .build()
    .map_err(|e| format!("setup rayon pool: {e}"))?;
  // This pool is dropped before execution starts. Ownership order and the
  // first validation error still come from prepare_owned's indexed collect.
  pool.install(|| prepare_owned(env, manifest))
}

/// Selection affects execution only, never global validation. Normalize at
/// this boundary as well as in the CLI: direct FFI callers must not duplicate
/// work, truncate an invalid id, or turn an empty selection into full coverage.
fn select_shards(
  count: usize,
  selection: Option<&[usize]>,
) -> Result<Vec<usize>, String> {
  let Some(selection) = selection else {
    return Ok((0..count).collect());
  };
  if selection.is_empty() {
    return Err("--shards: empty selection".into());
  }
  if let Some(id) = selection.iter().find(|&&id| id >= count) {
    return Err(format!("--shards: shard {id} out of range ({count} shards)"));
  }
  let mut selected = selection.to_vec();
  selected.sort_unstable();
  selected.dedup();
  Ok(selected)
}

struct CheckSummary {
  constants: usize,
  shards: usize,
  failures: usize,
  elapsed_ms: usize,
}

fn audit_report(
  config: &RunConfig<'_>,
  loaded: &LoadedEnv,
  manifest: &ShardManifest,
  manifest_bytes: &[u8],
  owned: &[Vec<Address>],
  results: &[Option<ShardCheckResult>],
) -> Value {
  let mut leaves = Vec::new();
  let mut failures = Vec::new();
  for (id, ((shard, owned), result)) in
    manifest.shards.iter().zip(owned).zip(results).enumerate()
  {
    let Some(result) = result else {
      // Do not construct claims for thousands of untouched leaves, or imply
      // that global coverage validation typechecked their declarations.
      leaves.push(json!({
        "id": id, "blocks": shard.blocks.len(), "consts": owned.len(),
        "claim": null, "predicted_peak_bytes": null, "status": "unchanged",
      }));
      continue;
    };
    // Usually already computed by the witness builder. Empty/failed witness
    // builds retain the same nullable claim field as the old audit path.
    let claim = result.claim.clone().or_else(|| {
      let (claim, _) =
        ixon::shard_claim::shard_check_env_claim(&loaded.env, owned)?;
      let mut bytes = Vec::new();
      claim.put(&mut bytes);
      Some(Address::hash(&bytes))
    });
    leaves.push(json!({
      "id": id, "blocks": shard.blocks.len(), "consts": owned.len(),
      "claim": claim.map(|a| a.hex()), "predicted_peak_bytes": result.peak_bytes,
      "status": if result.error.is_empty() { "measured" } else { "failed" },
    }));
    if !result.error.is_empty() {
      let names: Vec<&String> =
        owned.iter().filter_map(|a| loaded.names.get(a)).take(8).collect();
      let mut failure = json!({
        "id": id, "label": id.to_string(), "reason": result.error,
        "blocks": shard.blocks.len(), "consts": owned.len(),
        "predicted_peak_bytes": result.peak_bytes, "names": names,
      });
      if shard.blocks.len() == 1 {
        failure["block"] = json!(shard.blocks[0].hex());
      }
      failures.push(failure);
    }
  }
  json!({
    "schema": "ix-refine/0", "revision": config.revision, "command": config.command,
    "env": { "path": config.ixe, "bytes": loaded.bytes },
    "source": { "path": config.manifest, "bytes": manifest_bytes.len(),
      "blake3": blake3::hash(manifest_bytes).to_hex().to_string(), "shards": manifest.shards.len() },
    "out": null, "budget_bytes": 0, "budget_source": config.budget_source,
    "jobs": config.jobs, "selected": results.iter().flatten().count(),
    "executed": results.iter().flatten().count(),
    "waves": 0, "consolidation_shards": null, "leaves": leaves, "failures": failures,
  })
}

fn run_partition(
  toplevel: &Toplevel,
  fun_idx: usize,
  build_system: impl FnOnce() -> AiurSystem,
  config: &RunConfig<'_>,
) -> Result<CheckSummary, String> {
  let started = Instant::now();
  let setup_setting = match std::env::var("IX_AIUR_SETUP_THREADS") {
    Ok(value) => Some(value),
    Err(std::env::VarError::NotPresent) => None,
    Err(error) => return Err(format!("IX_AIUR_SETUP_THREADS: {error}")),
  };
  let available = std::thread::available_parallelism().map_or(1, usize::from);
  let setup_threads = setup_pool_size(setup_setting.as_deref(), available)?;
  eprintln!("[ixvm_setup] loading manifest and metadata-light mmap");
  let manifest_bytes = fs::read(config.manifest)
    .map_err(|e| format!("read {}: {e}", config.manifest.display()))?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|e| format!("manifest parse failed: {e}"))?;
  let selected = select_shards(manifest.shards.len(), config.selection)?;
  let loaded = load_env(config.ixe, !config.report.is_empty())?;
  let loaded_at = Instant::now();
  eprintln!(
    "[ixvm_setup] loaded in {:.3}s; validating coverage and assigning ownership in Rust ({setup_threads} setup threads)",
    (loaded_at - started).as_secs_f64()
  );
  let owned = prepare_with_pool(&loaded.env, &manifest, setup_threads)?;
  eprintln!(
    "[shards] OK: partition covers all {} consts, disjoint ({} shards)",
    loaded.env.consts.len(),
    owned.len()
  );
  eprintln!(
    "[ixvm_setup] coverage/ownership {:.3}s; total startup {:.3}s",
    loaded_at.elapsed().as_secs_f64(),
    started.elapsed().as_secs_f64()
  );
  eprintln!(
    "Typechecking {} selected source shard(s) of {} with completion-driven refinement, {} thread(s) (0 = all)",
    selected.len(),
    manifest.shards.len(),
    config.jobs
  );
  let execution_start = Instant::now();
  let pool = rayon::ThreadPoolBuilder::new()
    .num_threads(config.jobs)
    .build()
    .map_err(|e| format!("execution rayon pool: {e}"))?;
  // Keep circuit/peak-model construction in the execution measurement,
  // matching the legacy shardCheckBatchWithEnv timing boundary.
  let system = build_system();
  let gate = Admission::new(pool.current_num_threads())?;
  let executor = ShardExecutor::new(
    toplevel,
    fun_idx,
    &loaded.env,
    config.use_bytecode,
    &system,
    0,
    gate.execution_budget(),
  )?;
  // Keep the admission dispatcher outside the execution pool. Its width is
  // still exactly --jobs (0 = Rayon's default), regardless of setup width.
  let runs = refine::run(
    &loaded.env,
    &manifest,
    &owned,
    Some(&selected),
    &gate,
    &pool,
    |owned| executor.reservation(owned),
    |owned, label| Ok(executor.check(owned, label)),
  )?;
  let results = &runs.results;
  let elapsed_ms = usize::try_from(execution_start.elapsed().as_millis())
    .unwrap_or(usize::MAX);
  let failures =
    results.iter().flatten().filter(|r| !r.error.is_empty()).count();
  if !config.report.is_empty() {
    let mut report = audit_report(
      config,
      &loaded,
      &manifest,
      &manifest_bytes,
      &owned,
      results,
    );
    refine::extend_report(&mut report, &runs);
    let mut bytes = serde_json::to_vec_pretty(&report)
      .map_err(|e| format!("audit JSON: {e}"))?;
    bytes.push(b'\n');
    fs::write(config.report, bytes)
      .map_err(|e| format!("write audit {}: {e}", config.report))?;
    eprintln!("[split-audit] report → {}", config.report);
  }
  if failures == 0 {
    eprintln!(
      "All {} selected source shard(s) passed via {} executed final part(s) ({} in manifest)",
      selected.len(),
      runs.parts.iter().map(Vec::len).sum::<usize>(),
      manifest.shards.len()
    );
  } else {
    eprintln!(
      "{failures} of {} selected source shard(s) FAILED",
      selected.len()
    );
  }
  Ok(CheckSummary {
    constants: selected.iter().map(|&id| owned[id].len()).sum(),
    shards: selected.len(),
    failures,
    elapsed_ms,
  })
}

/// Full or selected-partition execution with early resource-limit refinement.
/// Destination prover budgets and proof-cache paths retain the existing driver.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_check_partition(
  toplevel_obj: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  ixe: LeanString<LeanBorrowed<'_>>,
  manifest: LeanString<LeanBorrowed<'_>>,
  jobs: LeanNat<LeanBorrowed<'_>>,
  use_bytecode: bool,
  commitment: LeanAiurCommitmentParameters<LeanBorrowed<'_>>,
  fri: LeanAiurFriParameters<LeanBorrowed<'_>>,
  report: LeanString<LeanBorrowed<'_>>,
  revision: LeanString<LeanBorrowed<'_>>,
  command: LeanString<LeanBorrowed<'_>>,
  budget_source: LeanString<LeanBorrowed<'_>>,
  selection: LeanOption<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let selection = selection
      .to_option()
      .map(|ids| {
        ids
          .as_array()
          .iter()
          .map(|id| {
            if !id.is_scalar() {
              return Err("--shards: shard id too large".to_owned());
            }
            Ok(id.unbox_usize())
          })
          .collect::<Result<Vec<_>, String>>()
      })
      .transpose()?;
    let toplevel = decode_toplevel(&toplevel_obj);
    let system_toplevel = decode_toplevel(&toplevel_obj);
    let commitment = decode_commitment_parameters(&commitment);
    let fri = decode_fri_parameters(&fri);
    let config = RunConfig {
      ixe: Path::new(ixe.as_str()),
      manifest: Path::new(manifest.as_str()),
      jobs: lean_unbox_nat_as_usize(jobs.inner()),
      use_bytecode,
      report: report.as_str(),
      revision: revision.as_str(),
      command: command.as_str(),
      budget_source: budget_source.as_str(),
      selection: selection.as_deref(),
    };
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    run_partition(
      &toplevel,
      fun_idx,
      || AiurSystem::build(system_toplevel, commitment, fri),
      &config,
    )
  }));
  let result = match result {
    Ok(Ok(summary)) => {
      let out = LeanAiurPartitionCheckResult::alloc(0);
      out.set_obj(0, LeanOwned::box_usize(summary.constants));
      out.set_obj(1, LeanOwned::box_usize(summary.shards));
      out.set_obj(2, LeanOwned::box_usize(summary.failures));
      out.set_obj(3, LeanOwned::box_usize(summary.elapsed_ms));
      LeanExcept::ok(out)
    },
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => {
      let msg = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or("unknown panic");
      LeanExcept::error_string(&format!(
        "native partition check panicked: {msg}"
      ))
    },
  };
  LeanIOResult::ok(result)
}

#[cfg(test)]
mod tests;
