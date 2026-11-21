//! FFI for Ixon types (canonical serialization format).
//!
//! This module provides build/decode/roundtrip functions for Ixon types used in
//! cross-implementation compatibility testing and serialization.

pub mod constant;
pub mod diff;
pub mod enums;
pub mod env;
pub mod expr;
pub mod meta;
pub mod modes;
pub mod pack;
#[cfg(feature = "test-ffi")]
pub mod serialize;
pub mod univ;

use std::sync::LazyLock;
use std::time::Instant;

use ix_common::address::Address;
use ix_common::env::normalize_displayed_name;
use ixon::env::Env as IxonEnv;
use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBool, LeanBorrowed, LeanByteArray, LeanExcept,
  LeanExternal, LeanIOResult, LeanOwned, LeanString,
};
use rustc_hash::FxHashMap;

/// A Rust-owned [`IxonEnv`] exposed to Lean as an opaque external handle.
pub struct EnvHandle {
  pub env: IxonEnv,
}

impl EnvHandle {
  /// Load via [`IxonEnv::get_anon_mmap`] (zero-copy mmap of the `.ixe` file).
  pub fn from_ixe_path(path: &std::path::Path) -> Result<Self, String> {
    let env = IxonEnv::get_anon_mmap(path)?;
    Ok(Self { env })
  }

  /// Decode a serialized env blob (`Ixon.serEnv` output) via [`IxonEnv::get`].
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut cursor: &[u8] = bytes;
    let env = IxonEnv::get(&mut cursor)?;
    Ok(Self { env })
  }
}

static IX_ENV_HANDLE_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<EnvHandle>);

/// `Aiur.EnvHandle.fromIxe`: open and parse a `.ixe` file once, returning an
/// opaque Rust-owned handle.
#[unsafe(no_mangle)]
pub extern "C" fn rs_aiur_env_handle_from_ixe(
  path_bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let path_str = String::from_utf8_lossy(path_bytes.as_bytes()).into_owned();
  match EnvHandle::from_ixe_path(std::path::Path::new(&path_str)) {
    Ok(h) => {
      let lean_handle: LeanOwned =
        LeanExternal::alloc(&IX_ENV_HANDLE_CLASS, h).into();
      LeanExcept::ok(lean_handle)
    },
    Err(e) => LeanExcept::error_string(&format!("env handle from_ixe: {e}")),
  }
}

/// `Aiur.EnvHandle.fromBytes`: decode a serialized env blob (`Ixon.serEnv`
/// output) into an opaque Rust-owned handle.
#[unsafe(no_mangle)]
pub extern "C" fn rs_aiur_env_handle_from_bytes(
  bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  match EnvHandle::from_bytes(bytes.as_bytes()) {
    Ok(h) => {
      let lean_handle: LeanOwned =
        LeanExternal::alloc(&IX_ENV_HANDLE_CLASS, h).into();
      LeanExcept::ok(lean_handle)
    },
    Err(e) => LeanExcept::error_string(&format!("env handle from_bytes: {e}")),
  }
}

/// FFI: the detected prover/execution RAM budget in bytes
/// ([`ixon::shard::RAM_USABLE_FRAC`] of `MemAvailable`), or `0` when
/// `/proc/meminfo` is unreadable.
#[unsafe(no_mangle)]
pub extern "C" fn rs_aiur_detected_ram_budget() -> LeanIOResult<LeanOwned> {
  let bytes = detected_ram_budget().unwrap_or(0);
  LeanIOResult::ok(LeanOwned::box_u64(bytes as u64))
}

fn trace_shard_max_cells() -> usize {
  std::env::var("AIUR_TRACE_SHARD_MAX_CELLS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .unwrap_or(0)
}

fn record_budget(max_ram_bytes: usize, cells: usize) -> usize {
  max_ram_bytes.saturating_sub(2 * 8 * cells + (256 << 20))
}

fn record_share(max_ram_bytes: usize, cells: usize, in_flight: usize) -> usize {
  record_budget(max_ram_bytes, cells) / in_flight.max(1)
}

#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
#[allow(clippy::cast_sign_loss)]
fn detected_ram_budget() -> Option<usize> {
  available_ram_bytes()
    .map(|b| (b as f64 * ixon::shard::RAM_USABLE_FRAC) as usize)
}

fn available_ram_bytes() -> Option<usize> {
  let s = std::fs::read_to_string("/proc/meminfo").ok()?;
  let rest = s.lines().find_map(|l| l.strip_prefix("MemAvailable:"))?;
  let kib: usize = rest.trim().trim_end_matches("kB").trim().parse().ok()?;
  Some(kib * 1024)
}

/// FFI: extract the named constants' dependency closure from a serialized
/// env into a standalone `.ixe` — genuine constant bytes, blobs, and
/// reducibility hints (via the anon view), plus every closure constant's
/// Named entry (via the full view) so names still resolve downstream — all
/// without recompiling from source. Each name extracts its covering work
/// item (a mutual-block member pulls the whole block).
#[unsafe(no_mangle)]
pub extern "C" fn rs_env_extract(
  env_path: LeanString<LeanBorrowed<'_>>,
  names: LeanArray<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
  quiet: LeanBool<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  use ixon::shard::{
    block_of_addr, build_anon_work, build_sub_env_named, work_block_addr,
  };

  let quiet = quiet.to_bool();
  let path = env_path.to_string();
  let out = out_path.to_string();
  let names_vec: Vec<String> = names.map(|obj| obj.as_string().to_string());
  if names_vec.is_empty() {
    return LeanIOResult::error_string(
      "rs_env_extract: no constant names given",
    );
  }

  let bytes = match std::fs::read(&path) {
    Ok(bytes) => bytes,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_env_extract: failed to read {path}: {e}"
      ));
    },
  };
  let mut slice: &[u8] = &bytes;
  let full = match IxonEnv::get(&mut slice) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_env_extract: failed to deserialize {path}: {e}"
      ));
    },
  };
  // Resolve displayed names → addresses through the full env's `named`
  // metadata (the anon view discards it). Keys and requests both go
  // through `normalize_displayed_name` (Lean `«»`-escaped ↔ Rust bare).
  let by_name: FxHashMap<String, Address> = full
    .named
    .iter()
    .map(|e| {
      (normalize_displayed_name(&e.key().to_string()), e.value().addr.clone())
    })
    .collect();
  let mut resolved: Vec<Address> = Vec::with_capacity(names_vec.len());
  let mut missing: Vec<&str> = Vec::new();
  for n in &names_vec {
    match by_name.get(&normalize_displayed_name(n)) {
      Some(a) => resolved.push(a.clone()),
      None => missing.push(n),
    }
  }
  if !missing.is_empty() {
    return LeanIOResult::error_string(&format!(
      "rs_env_extract: no constant(s) named [{}] in {path}",
      missing.join(", ")
    ));
  }

  let mut slice: &[u8] = &bytes;
  let anon = match IxonEnv::get_anon(&mut slice) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_env_extract: failed to deserialize (anon) {path}: {e}"
      ));
    },
  };

  // Roots: each name's covering work item's proven targets (standalone →
  // itself; a mutual-block member → every sibling, checked atomically).
  let work = match build_anon_work(&anon) {
    Ok(work) => work,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_env_extract: build_anon_work: {e}"
      ));
    },
  };
  let by_block: FxHashMap<Address, usize> = work
    .iter()
    .enumerate()
    .map(|(i, w)| (work_block_addr(&anon, w), i))
    .collect();
  let mut roots: Vec<Address> = Vec::new();
  for addr in &resolved {
    let block = block_of_addr(&anon, addr);
    match by_block.get(&block) {
      Some(&i) => roots.extend(work[i].proven_targets()),
      None => {
        return LeanIOResult::error_string(&format!(
          "rs_env_extract: no work item covers block {}…",
          &block.hex()[..16]
        ));
      },
    }
  }

  let sub_bytes = match build_sub_env_named(&anon, &full, &roots) {
    Ok(b) => b,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_env_extract: {e}"));
    },
  };
  if let Err(e) = std::fs::write(&out, &sub_bytes) {
    return LeanIOResult::error_string(&format!(
      "rs_env_extract: failed to write {out}: {e}"
    ));
  }
  if !quiet {
    eprintln!(
      "[rs_env_extract] {} name(s) → {} ({} bytes) from {path}",
      names_vec.len(),
      out,
      sub_bytes.len(),
    );
  }
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// FFI: partition a `.ixe` with the STATIC strategy — no out-of-circuit
/// profiling run. An explicit nonzero `num_shards` fixes the count. Otherwise,
/// `ram_gib` seeds it from the static block-shape score after the profile is
/// loaded ([`ixon::shard::static_seed_shards`]). Builds the static block
/// profile ([`static_block_profile`]), then either the byte-balanced min-cut
/// over the walk-edge nets with the predicted-cost rebalance post-pass
/// (`ixon::shard::shard_static`, `layout` = `mincut`) or contiguous
/// ranges of a dependency order (`ixon::shard::shard_static_ordered`,
/// `layout` = `ordered`). Writes a `.ixes` manifest.
#[allow(clippy::cast_precision_loss)] // balance_pct is a small percentage
#[unsafe(no_mangle)]
pub extern "C" fn rs_shard_env_static(
  env_path: LeanString<LeanBorrowed<'_>>,
  requested_shards: usize,
  ram_gib: u64,
  balance_pct: u64,
  layout: LeanString<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
  exec_ahead: usize,
) -> LeanIOResult<LeanOwned> {
  let path = env_path.to_string();
  let layout = layout.to_string();
  if layout != "mincut" && layout != "ordered" {
    return LeanIOResult::error_string(&format!(
      "rs_shard_env_static: unknown layout `{layout}` (mincut or ordered)"
    ));
  }
  if requested_shards == 0 && ram_gib == 0 {
    return LeanIOResult::error_string(
      "rs_shard_env_static: pass a positive shard count or RAM budget",
    );
  }
  let balance = (balance_pct as f64) / 100.0;
  let out = out_path.to_string();
  let out_opt = if out.is_empty() { None } else { Some(out.as_str()) };
  let t0 = Instant::now();
  let env = match IxonEnv::get_anon_mmap(std::path::Path::new(&path)) {
    Ok(e) => e,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_shard_env_static: failed to load {path}: {e}"
      ));
    },
  };
  let t_load = t0.elapsed();
  let t1 = Instant::now();
  let profile = ixon::shard::static_block_profile(&env);
  eprintln!(
    "[rs_shard_static] env load {:.1?}, static graph {:.1?} ({} blocks, {} edges)",
    t_load,
    t1.elapsed(),
    profile.num_blocks(),
    profile.num_edges()
  );
  let num_shards = if requested_shards > 0 {
    requested_shards
  } else if cfg!(feature = "cuda") {
    // The trace-shard prover: seed against one execution's record share,
    // computed as `ix prove --lanes` computes it.
    let cells = trace_shard_max_cells();
    let budget = usize::try_from(ram_gib << 30).unwrap_or(usize::MAX);
    let share = record_share(budget, cells, exec_ahead + 2);
    let tenths =
      u32::try_from(share.saturating_mul(10) >> 30).unwrap_or(u32::MAX);
    let share_gib = f64::from(tenths) / 10.0;
    let bytes = ixon::shard::static_env_bytes(&profile);
    let n = ixon::shard::gpu_seed_shards(&profile, share_gib);
    eprintln!(
      "[shard] trace-shard seed (cuda build): bytes={bytes:.4e}; round({} x (bytes/{:.4e}) x ({} GiB / {share_gib:.1} GiB record share: {ram_gib} GiB per worker, {cells} cells, {exec_ahead} executions ahead)) -> {n} shard(s) (heuristic; the record cap names any shard over its share)",
      ixon::shard::GPU_SEED_REFERENCE_SHARDS,
      ixon::shard::GPU_SEED_REFERENCE_BYTES,
      ixon::shard::GPU_SEED_REFERENCE_SHARE_GIB,
    );
    n
  } else {
    let score = ixon::shard::static_env_score(&profile);
    let n = ixon::shard::static_seed_shards(&profile, ram_gib);
    eprintln!(
      "[shard] static seed (cpu prover model): score={score:.3e}; round({} x (score/{:.3e})^{:.2} x ({}/{ram_gib})^{:.2}) -> {n} shard(s) (heuristic; gated execution corrects every boundary)",
      ixon::shard::STATIC_SEED_REFERENCE_SHARDS,
      ixon::shard::STATIC_SEED_REFERENCE_SCORE,
      ixon::shard::STATIC_SEED_SCORE_EXPONENT,
      ixon::shard::STATIC_SEED_REFERENCE_RAM_GIB,
      ixon::shard::STATIC_SEED_BUDGET_EXPONENT,
    );
    n
  };
  let report = if layout == "ordered" {
    let (depends, primitives) =
      ixon::shard::static_block_dependencies(&env, &profile);
    ixon::shard::shard_static_ordered(
      &profile,
      &depends,
      &primitives,
      num_shards,
      out_opt,
    )
  } else {
    ixon::shard::shard_static(&profile, num_shards, balance, out_opt)
  };
  match report {
    Ok(report) => {
      eprintln!("[rs_shard_static]\n{report}");
      LeanIOResult::ok(LeanOwned::box_usize(0))
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_shard_env_static: {e}")),
  }
}

/// Decode `rs_shard_manifest_refine`'s refinements blob: `count(u32)`, then
/// per refined leaf `id(u32) ‖ nparts(u32)` and per part
/// `nblocks(u32) ‖ 32·nblocks ‖ peak(u64)`.
fn decode_refinements(
  bytes: &[u8],
) -> Result<Vec<ixon::shard::LeafRefinement>, String> {
  struct Cur<'a> {
    b: &'a [u8],
    p: usize,
  }
  impl<'a> Cur<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
      let end = self
        .p
        .checked_add(n)
        .filter(|&end| end <= self.b.len())
        .ok_or("refinements blob: truncated")?;
      let s = &self.b[self.p..end];
      self.p = end;
      Ok(s)
    }
    fn u32(&mut self) -> Result<usize, String> {
      Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize)
    }
    fn u64(&mut self) -> Result<u64, String> {
      Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
  }
  let mut c = Cur { b: bytes, p: 0 };
  let count = c.u32()?;
  let mut out = Vec::with_capacity(count);
  for _ in 0..count {
    let id = u32::try_from(c.u32()?)
      .map_err(|e| format!("refinements blob: bad id: {e}"))?;
    let nparts = c.u32()?;
    let mut parts = Vec::with_capacity(nparts);
    let mut part_peaks = Vec::with_capacity(nparts);
    for _ in 0..nparts {
      let nblocks = c.u32()?;
      let raw = c.take(nblocks * 32)?;
      parts.push(
        raw
          .as_chunks::<32>()
          .0
          .iter()
          .map(|chunk| Address::from_slice(chunk).unwrap())
          .collect(),
      );
      part_peaks.push(c.u64()?);
    }
    out.push(ixon::shard::LeafRefinement { id, parts, part_peaks });
  }
  if c.p != bytes.len() {
    return Err("refinements blob: trailing bytes".into());
  }
  Ok(out)
}

/// FFI: refine an existing `.ixes` manifest by cutting some of its leaves
/// into parts (`ShardManifest::refine`): every other leaf keeps its block
/// list, record, id and place in the aggregation tree; a refined leaf's
/// place becomes a balanced subtree over its parts, part 0 keeping the
/// leaf's id and later parts taking fresh ids after the last existing one.
/// `measured_blob` is empty or one `u64` analytic prover peak per SOURCE
/// shard in id order (nonzero overrides the peak carried forward for an
/// unsplit leaf). The new partition is validated as an exact, disjoint
/// cover of the env's block profile; the manifest summary goes to stderr.
/// Returns the parts' new ids: `count(u32)`, then per refinement
/// `n(u32) ‖ n × id(u32)`.
#[allow(clippy::cast_possible_truncation)] // ids and counts are u32 by construction
#[unsafe(no_mangle)]
pub extern "C" fn rs_shard_manifest_refine(
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  source_path: LeanString<LeanBorrowed<'_>>,
  refinements_blob: LeanByteArray<LeanBorrowed<'_>>,
  measured_blob: LeanByteArray<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let source_path = source_path.to_string();
  let out = out_path.to_string();
  let fail = |e: String| {
    LeanIOResult::error_string(&format!("rs_shard_manifest_refine: {e}"))
  };
  let source = match std::fs::read(&source_path)
    .map_err(|e| format!("read {source_path}: {e}"))
    .and_then(|bytes| ixon::shard::ShardManifest::from_bytes(&bytes))
  {
    Ok(m) => m,
    Err(e) => return fail(e),
  };
  let refinements = match decode_refinements(refinements_blob.as_bytes()) {
    Ok(r) => r,
    Err(e) => return fail(e),
  };
  let measured: Vec<u64> = measured_blob
    .as_bytes()
    .as_chunks::<8>()
    .0
    .iter()
    .map(|c| u64::from_le_bytes(*c))
    .collect();
  let profile = ixon::shard::static_block_profile(&env_handle.get().env);
  match ixon::shard::shard_manifest_refine(
    &profile,
    &source,
    &refinements,
    &measured,
    &out,
  ) {
    Ok((summary, part_ids)) => {
      eprintln!("[shard-refine] {out}: {summary}");
      let mut bytes = Vec::new();
      bytes.extend_from_slice(&(part_ids.len() as u32).to_le_bytes());
      for ids in &part_ids {
        bytes.extend_from_slice(&(ids.len() as u32).to_le_bytes());
        for id in ids {
          bytes.extend_from_slice(&id.to_le_bytes());
        }
      }
      let ids: LeanOwned = LeanByteArray::from_bytes(&bytes).into();
      LeanIOResult::ok(ids)
    },
    Err(e) => fail(e),
  }
}

/// FFI: dump the static block-level reference graph of a `.ixe` as text —
/// `block <hex> <bytes> <consts>` per ingress unit (a Muts block or a
/// standalone constant) and `edge <consumer> <producer>` per deduped
/// claim-walk edge (`ixon::shard_claim::walk_edges`, mapped to block
/// granularity, self-edges dropped). The graph is the input for offline
/// partitioner prototypes in the sharding campaign: the walk-edge
/// relation is exactly what generates a shard's thin frontier, so a
/// partition's ingress cost is computable from this file alone. Same
/// data as [`static_block_profile`], serialized for offline use.
#[allow(clippy::cast_possible_truncation)] // block ids are u32 by construction
#[unsafe(no_mangle)]
pub extern "C" fn rs_shard_static_graph(
  env_path: LeanString<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let path = env_path.to_string();
  let out = out_path.to_string();
  let env = match IxonEnv::get_anon_mmap(std::path::Path::new(&path)) {
    Ok(e) => e,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_shard_static_graph: failed to load {path}: {e}"
      ));
    },
  };
  let profile = ixon::shard::static_block_profile(&env);
  let mut buf = String::new();
  for b in profile.blocks() {
    buf.push_str(&format!(
      "block {} {} {}\n",
      b.addr.hex(),
      b.serialized_size,
      b.const_count
    ));
  }
  for c in 0..profile.num_blocks() as u32 {
    let ca = profile.block(c).addr.hex();
    for &p in profile.producers(c) {
      buf.push_str(&format!("edge {} {}\n", ca, profile.block(p).addr.hex()));
    }
  }
  if let Err(e) = std::fs::write(&out, buf) {
    return LeanIOResult::error_string(&format!(
      "rs_shard_static_graph: failed to write {out}: {e}"
    ));
  }
  eprintln!(
    "[rs_shard_static_graph] {} blocks, {} edges → {}",
    profile.num_blocks(),
    profile.num_edges(),
    out
  );
  LeanIOResult::ok(LeanOwned::box_usize(0))
}
