//! Native startup for a whole-partition `ix check`. Only small result counts
//! cross the FFI: the mmap, manifest, ownership lists and audit stay in Rust.
//! The kernel/witness executor is shared with the existing Lean wave driver.

use std::{fs, path::Path, sync::Arc, time::Instant};

use aiur::{bytecode::Toplevel, synthesis::AiurSystem};
use ix_common::address::Address;
use ix_kernel::shard::ShardManifest;
use ixon::{ConstantInfo, Env};
use lean_ffi::object::{
  LeanBorrowed, LeanExcept, LeanIOResult, LeanNat, LeanOwned, LeanString,
};
use rayon::prelude::*;
use rustc_hash::FxHashMap;
use serde_json::{Value, json};

use super::{
  lean_unbox_nat_as_usize,
  protocol::{
    ShardCheckResult, check_shard_batch, decode_commitment_parameters,
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
  results: &[ShardCheckResult],
) -> Value {
  let mut leaves = Vec::new();
  let mut failures = Vec::new();
  for (id, ((shard, owned), result)) in
    manifest.shards.iter().zip(owned).zip(results).enumerate()
  {
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
    "jobs": config.jobs, "selected": manifest.shards.len(), "executed": manifest.shards.len(),
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
  eprintln!("[ixvm_setup] loading manifest and metadata-light mmap");
  let manifest_bytes = fs::read(config.manifest)
    .map_err(|e| format!("read {}: {e}", config.manifest.display()))?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|e| format!("manifest parse failed: {e}"))?;
  let loaded = load_env(config.ixe, !config.report.is_empty())?;
  let loaded_at = Instant::now();
  eprintln!(
    "[ixvm_setup] loaded in {:.3}s; validating coverage and assigning ownership in Rust",
    (loaded_at - started).as_secs_f64()
  );
  let owned = prepare_owned(&loaded.env, &manifest)?;
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
    "Typechecking {} shard(s) in one rayon batch, {} thread(s) (0 = all)",
    owned.len(),
    config.jobs
  );
  let execution_start = Instant::now();
  // Keep circuit/peak-model construction in the execution measurement,
  // matching the legacy shardCheckBatchWithEnv timing boundary.
  let system = build_system();
  // The caller installed the requested pool for both preparation and checking.
  let results = check_shard_batch(
    toplevel,
    fun_idx,
    &loaded.env,
    &owned,
    config.use_bytecode,
    0,
    &system,
    0,
    true,
  )?;
  let elapsed_ms = usize::try_from(execution_start.elapsed().as_millis())
    .unwrap_or(usize::MAX);
  let failures = results.iter().filter(|r| !r.error.is_empty()).count();
  if !config.report.is_empty() {
    let report = audit_report(
      config,
      &loaded,
      &manifest,
      &manifest_bytes,
      &owned,
      &results,
    );
    let mut bytes = serde_json::to_vec_pretty(&report)
      .map_err(|e| format!("audit JSON: {e}"))?;
    bytes.push(b'\n');
    fs::write(config.report, bytes)
      .map_err(|e| format!("write audit {}: {e}", config.report))?;
    eprintln!("[split-audit] report → {}", config.report);
  }
  if failures == 0 {
    eprintln!("All {} shard(s) passed", owned.len());
  } else {
    eprintln!("{failures} of {} shard(s) FAILED", owned.len());
  }
  Ok(CheckSummary {
    constants: loaded.env.consts.len(),
    shards: owned.len(),
    failures,
    elapsed_ms,
  })
}

/// Full-partition, no-refinement execution. Advanced split/selection/proof-cache
/// paths keep the existing driver until their orchestration is ported too.
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
) -> LeanIOResult<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
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
    };
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let run = || {
      run_partition(
        &toplevel,
        fun_idx,
        || AiurSystem::build(system_toplevel, commitment, fri),
        &config,
      )
    };
    if config.jobs == 0 {
      run()
    } else {
      let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(config.jobs)
        .build()
        .map_err(|e| format!("rayon pool: {e}"))?;
      pool.install(run)
    }
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
