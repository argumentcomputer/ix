//! FFI bridge between Lean and Rust for the Ixon compilation/decompilation pipeline.
//!
//! Provides `extern "C"` functions callable from Lean via `@[extern]`:
//! - `rs_compile_env` / `rs_compile_env_full`: compile a Lean environment to Ixon
//! - `rs_compile_phases`: run individual pipeline phases (canon, condense, graph, compile)
//! - `rs_decompile_env`: decompile a serialized `.ixe` env back to Lean constants
//! - `rs_roundtrip_*`: roundtrip FFI tests for Lean↔Rust type conversions
//! - `build_*` / `decode_*`: convert between Lean constructor layouts and Rust types

use std::sync::Arc;

use crate::lean::{
  LeanIxBlock, LeanIxCompileError, LeanIxCompilePhases, LeanIxCondensedBlocks,
  LeanIxDecompileError, LeanIxName, LeanIxRawEnvironment, LeanIxSerializeError,
  LeanIxonRawBlob, LeanIxonRawComm, LeanIxonRawConst, LeanIxonRawEnv,
  LeanIxonRawNameEntry, LeanIxonRawNamed,
};
use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};
use ix_compile::compile::{
  CompileOptions, CompileState, compile_env_with_options,
};
use ix_compile::condense::compute_sccs;
use ix_compile::decompile::decompile_env;
use ix_compile::graph::build_ref_graph;
use ixon::constant::Constant as IxonConstant;
#[cfg(feature = "test-ffi")]
use ixon::constant::ConstantInfo;
#[cfg(feature = "test-ffi")]
use ixon::expr::Expr as IxonExpr;
use ixon::{Comm, ConstantMeta};
use lean_ffi::object::LeanIOResult;
use lean_ffi::object::LeanNat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanList, LeanOwned, LeanProd,
  LeanRef, LeanString,
};

use crate::builder::LeanBuildCache;
use crate::lean::LeanIxAddress;

#[cfg(feature = "test-ffi")]
use crate::lean::{LeanIxBlockCompareDetail, LeanIxBlockCompareResult};
#[cfg(feature = "test-ffi")]
use crate::lean_env::{GlobalCache, decode_name};
#[cfg(feature = "test-ffi")]
use ixon::serialize::put_expr;
#[cfg(feature = "test-ffi")]
use std::collections::HashMap;

// =============================================================================
// Helper builders
// =============================================================================

/// Build a Lean String from a Rust &str.
fn build_lean_string(s: &str) -> LeanString<LeanOwned> {
  LeanString::new(s)
}

/// Build a Lean Nat from a usize.
fn build_lean_nat_usize(n: usize) -> LeanOwned {
  LeanOwned::from_nat_u64(n as u64)
}

// =============================================================================
// Raw* Builder Functions for Compile FFI
// =============================================================================

/// Build RawConst using type method.
fn build_raw_const(
  addr: &Address,
  constant: &IxonConstant,
) -> LeanIxonRawConst<LeanOwned> {
  LeanIxonRawConst::build_from_parts(addr, constant)
}

/// Build RawNamed using type method.
fn build_raw_named(
  cache: &mut LeanBuildCache,
  name: &Name,
  addr: &Address,
  meta: &ConstantMeta,
  original: &Option<(Address, ConstantMeta)>,
  hints: Option<ReducibilityHints>,
) -> LeanIxonRawNamed<LeanOwned> {
  LeanIxonRawNamed::build_from_parts(cache, name, addr, meta, original, hints)
}

/// Build RawBlob using type method.
fn build_raw_blob(addr: &Address, bytes: &[u8]) -> LeanIxonRawBlob<LeanOwned> {
  LeanIxonRawBlob::build_from_parts(addr, bytes)
}

/// Build RawComm using type method.
fn build_raw_comm(addr: &Address, comm: &Comm) -> LeanIxonRawComm<LeanOwned> {
  LeanIxonRawComm::build_from_parts(addr, comm)
}

// =============================================================================
// RustCondensedBlocks roundtrip FFI
// =============================================================================

/// Round-trip a RustCondensedBlocks structure.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_rust_condensed_blocks(
  obj: LeanIxCondensedBlocks<LeanBorrowed<'_>>,
) -> LeanIxCondensedBlocks<LeanOwned> {
  let low_links = obj.get_obj(0).to_owned_ref();
  let blocks = obj.get_obj(1).to_owned_ref();
  let block_refs = obj.get_obj(2).to_owned_ref();

  let result = LeanIxCondensedBlocks::alloc(0);
  result.set_obj(0, low_links);
  result.set_obj(1, blocks);
  result.set_obj(2, block_refs);
  result
}

/// Round-trip a RustCompilePhases structure.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_rust_compile_phases(
  obj: LeanIxCompilePhases<LeanBorrowed<'_>>,
) -> LeanIxCompilePhases<LeanOwned> {
  let raw_env = obj.get_obj(0).to_owned_ref();
  let condensed = obj.get_obj(1).to_owned_ref();
  let compile_env = obj.get_obj(2).to_owned_ref();

  let result = LeanIxCompilePhases::alloc(0);
  result.set_obj(0, raw_env);
  result.set_obj(1, condensed);
  result.set_obj(2, compile_env);
  result
}

// =============================================================================
// BlockCompareResult and BlockCompareDetail roundtrip FFI
// =============================================================================

/// Round-trip a BlockCompareResult.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_result(
  obj: LeanIxBlockCompareResult<LeanBorrowed<'_>>,
) -> LeanIxBlockCompareResult<LeanOwned> {
  // Tags 0 (match) and 2 (notFound) have 0 fields → Lean represents as scalars
  if obj.inner().is_scalar() {
    return LeanIxBlockCompareResult::new(obj.inner().to_owned_ref());
  }
  match obj.as_ctor().tag() {
    1 => {
      // mismatch: 0 obj, 24 scalar bytes (3 × u64)
      let lean_size = obj.get_num_64(0);
      let rust_size = obj.get_num_64(1);
      let first_diff = obj.get_num_64(2);

      let out = LeanIxBlockCompareResult::alloc(1);
      out.set_num_64(0, lean_size);
      out.set_num_64(1, rust_size);
      out.set_num_64(2, first_diff);
      out
    },
    tag => unreachable!("Invalid BlockCompareResult tag: {tag}"),
  }
}

/// Round-trip a BlockCompareDetail.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_detail(
  obj: LeanIxBlockCompareDetail<LeanBorrowed<'_>>,
) -> LeanIxBlockCompareDetail<LeanOwned> {
  let lean_sharing_len = obj.get_num_64(0);
  let rust_sharing_len = obj.get_num_64(1);

  let result_obj =
    rs_roundtrip_block_compare_result(LeanIxBlockCompareResult(obj.get_obj(0)));

  let out = LeanIxBlockCompareDetail::alloc(0);
  out.set_obj(0, result_obj);
  out.set_num_64(0, lean_sharing_len);
  out.set_num_64(1, rust_sharing_len);
  out
}

// =============================================================================
// Full Compilation FFI
// =============================================================================

/// FFI function to run the complete compilation pipeline and return all data.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_full(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  {
    // Phase 1: Decode Lean environment
    let rust_env = crate::lean_env::decode_env(env_consts_ptr);
    let env_len = rust_env.len();
    let rust_env = Arc::new(rust_env);

    // Phase 2: Build ref graph and compute SCCs
    let ref_graph = build_ref_graph(&rust_env);
    let condensed = compute_sccs(&ref_graph.out_refs);

    // Phase 3: Compile
    let compile_stt =
      match compile_env_with_options(&rust_env, CompileOptions::default()) {
        Ok(stt) => stt,
        Err(e) => {
          let msg =
            format!("rs_compile_env_full: Rust compilation failed: {:?}", e);
          return LeanIOResult::error_string(&msg);
        },
      };

    // Phase 4: Build Lean structures
    let mut cache = LeanBuildCache::with_capacity(env_len);

    let raw_env = LeanIxRawEnvironment::build(&mut cache, &rust_env);
    let condensed_obj = LeanIxCondensedBlocks::build(&mut cache, &condensed);

    // Collect blocks
    let mut blocks_data: Vec<(Name, Vec<u8>, usize)> = Vec::new();
    let mut seen_addrs: std::collections::HashSet<Address> =
      std::collections::HashSet::new();

    for entry in compile_stt.name_to_addr.iter() {
      let name = entry.key().clone();
      let addr = entry.value().clone();

      if seen_addrs.contains(&addr) {
        continue;
      }
      seen_addrs.insert(addr.clone());

      if let Some(constant) = compile_stt.env.get_const(&addr) {
        let mut bytes = Vec::new();
        constant.put(&mut bytes);
        let sharing_len = constant.sharing.len();
        blocks_data.push((name, bytes, sharing_len));
      }
    }

    // Build blocks array
    let blocks_arr = LeanArray::alloc(blocks_data.len());
    for (i, (name, bytes, sharing_len)) in blocks_data.iter().enumerate() {
      let name_obj = LeanIxName::build(&mut cache, name);
      let ba = LeanByteArray::from_bytes(bytes);

      // Block: { name: Ix.Name, bytes: ByteArray, sharingLen: UInt64 }
      let block = LeanIxBlock::alloc(0);
      block.set_obj(0, name_obj);
      block.set_obj(1, ba);
      block.set_num_64(0, *sharing_len as u64);

      blocks_arr.set(i, block);
    }

    // Build nameToAddr array
    let name_to_addr_len = compile_stt.name_to_addr.len();
    let name_to_addr_arr = LeanArray::alloc(name_to_addr_len);
    for (i, entry) in compile_stt.name_to_addr.iter().enumerate() {
      let name = entry.key();
      let addr = entry.value();

      let name_obj = LeanIxName::build(&mut cache, name);
      let addr_ba = LeanByteArray::from_bytes(addr.as_bytes());

      let entry_obj = LeanProd::new(name_obj, addr_ba);
      name_to_addr_arr.set(i, entry_obj);
    }

    // Build RawCompiledEnv
    let compiled_obj = LeanProd::new(blocks_arr, name_to_addr_arr);

    // Build RustCompilationResult
    let result = LeanIxCompilePhases::alloc(0);
    result.set_obj(0, raw_env);
    result.set_obj(1, condensed_obj);
    result.set_obj(2, compiled_obj);

    LeanIOResult::ok(result)
  }
}

/// FFI: compile a Lean environment and stream the serialized Ixon.Env
/// straight to `out_path` (see `Env::put_file`) — no env-sized `Vec` or
/// Lean `ByteArray` is built. Writes `<out_path>.tmp`, then renames, so
/// a crash cannot leave a truncated file. Returns bytes written (Nat).
/// The file is the canonical `Env::put` encoding (see `put_file`'s
/// equivalence test).
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let rust_env = crate::lean_env::decode_env_for_compile(env_consts_ptr);
  let rust_env = Arc::new(rust_env);

  let compile_stt =
    match compile_env_with_options(&rust_env, CompileOptions::default()) {
      Ok(stt) => stt,
      Err(e) => {
        let msg = format!("rs_compile_env: Rust compilation failed: {:?}", e);
        return LeanIOResult::error_string(&msg);
      },
    };

  let path = std::path::PathBuf::from(out_path.as_str());
  let tmp = {
    let mut s = path.clone().into_os_string();
    s.push(".tmp");
    std::path::PathBuf::from(s)
  };
  let written = match compile_stt.env.put_file(&tmp) {
    Ok(n) => n,
    Err(e) => {
      std::fs::remove_file(&tmp).ok();
      let msg = format!("rs_compile_env: serialization failed: {e}");
      return LeanIOResult::error_string(&msg);
    },
  };
  if let Err(e) = std::fs::rename(&tmp, &path) {
    std::fs::remove_file(&tmp).ok();
    let msg = format!(
      "rs_compile_env: rename {} -> {}: {e}",
      tmp.display(),
      path.display()
    );
    return LeanIOResult::error_string(&msg);
  }

  // Skip destructors: the compile CLI is a one-shot process, the OS
  // reclaims at exit, and dropping the maps costs tens of seconds at
  // Mathlib scale.
  std::mem::forget(compile_stt);
  std::mem::forget(rust_env);
  LeanIOResult::ok(LeanOwned::from_nat_u64(written))
}

/// Round-trip a RawEnv: decode from Lean, re-encode via builder.
/// This performs a full decode/build cycle to verify FFI correctness.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_raw_env(
  raw_env_obj: LeanIxonRawEnv<LeanBorrowed<'_>>,
) -> LeanIxonRawEnv<LeanOwned> {
  let env = raw_env_obj.decode();
  LeanIxonRawEnv::build(&env)
}

/// FFI function to run all compilation phases and return combined results.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_phases(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  {
    let rust_env = crate::lean_env::decode_env(env_consts_ptr);
    let env_len = rust_env.len();
    let rust_env = Arc::new(rust_env);

    let mut cache = LeanBuildCache::with_capacity(env_len);
    let raw_env = LeanIxRawEnvironment::build(&mut cache, &rust_env);

    let ref_graph = build_ref_graph(&rust_env);

    let condensed = compute_sccs(&ref_graph.out_refs);

    let condensed_obj = LeanIxCondensedBlocks::build(&mut cache, &condensed);

    let compile_stt =
      match compile_env_with_options(&rust_env, CompileOptions::default()) {
        Ok(stt) => stt,
        Err(e) => {
          let msg = format!("rs_compile_phases: compilation failed: {:?}", e);
          return LeanIOResult::error_string(&msg);
        },
      };

    // Build Lean objects from compile results
    let consts: Vec<_> = compile_stt
      .env
      .consts
      .iter()
      .filter_map(|e| {
        let c = e.value().get().ok()?;
        Some((e.key().clone(), c))
      })
      .collect();
    let consts_arr = LeanArray::alloc(consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      consts_arr.set(i, build_raw_const(addr, constant.as_ref()));
    }

    let named: Vec<_> = compile_stt
      .env
      .named
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let named_arr = LeanArray::alloc(named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      named_arr.set(
        i,
        build_raw_named(
          &mut cache,
          name,
          &n.addr,
          &n.meta(),
          &n.original().map(|(a, m)| (a, (*m).clone())),
          n.hints(),
        ),
      );
    }

    let blobs: Vec<_> = compile_stt
      .env
      .blobs
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let blobs_arr = LeanArray::alloc(blobs.len());
    for (i, (addr, bytes)) in blobs.iter().enumerate() {
      blobs_arr.set(i, build_raw_blob(addr, bytes));
    }

    let comms: Vec<_> = compile_stt
      .env
      .comms
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let comms_arr = LeanArray::alloc(comms.len());
    for (i, (addr, comm)) in comms.iter().enumerate() {
      comms_arr.set(i, build_raw_comm(addr, comm));
    }

    // Build names array (Address → Ix.Name)
    let names: Vec<_> = compile_stt
      .env
      .names
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let names_arr = LeanArray::alloc(names.len());
    for (i, (addr, name)) in names.iter().enumerate() {
      names_arr.set(i, LeanIxonRawNameEntry::build(&mut cache, addr, name));
    }

    let raw_ixon_env = LeanIxonRawEnv::alloc(0);
    raw_ixon_env.set_obj(0, consts_arr);
    raw_ixon_env.set_obj(1, named_arr);
    raw_ixon_env.set_obj(2, blobs_arr);
    raw_ixon_env.set_obj(3, comms_arr);
    raw_ixon_env.set_obj(4, names_arr);
    crate::lean_ixon::env::set_raw_env_bundle_fields(
      &raw_ixon_env,
      &compile_stt.env,
    );

    let result = LeanIxCompilePhases::alloc(0);
    result.set_obj(0, raw_env);
    result.set_obj(1, condensed_obj);
    result.set_obj(2, raw_ixon_env);

    LeanIOResult::ok(result)
  }
}

/// FFI function to compile a Lean environment to a RawEnv.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_to_ixon(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  {
    let rust_env = crate::lean_env::decode_env(env_consts_ptr);
    let rust_env = Arc::new(rust_env);

    let compile_stt =
      match compile_env_with_options(&rust_env, CompileOptions::default()) {
        Ok(stt) => stt,
        Err(e) => {
          let msg =
            format!("rs_compile_env_to_ixon: compilation failed: {:?}", e);
          return LeanIOResult::error_string(&msg);
        },
      };

    let mut cache = LeanBuildCache::with_capacity(rust_env.len());

    let consts: Vec<_> = compile_stt
      .env
      .consts
      .iter()
      .filter_map(|e| {
        let c = e.value().get().ok()?;
        Some((e.key().clone(), c))
      })
      .collect();
    let consts_arr = LeanArray::alloc(consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      consts_arr.set(i, build_raw_const(addr, constant.as_ref()));
    }

    let named: Vec<_> = compile_stt
      .env
      .named
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let named_arr = LeanArray::alloc(named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      named_arr.set(
        i,
        build_raw_named(
          &mut cache,
          name,
          &n.addr,
          &n.meta(),
          &n.original().map(|(a, m)| (a, (*m).clone())),
          n.hints(),
        ),
      );
    }

    let blobs: Vec<_> = compile_stt
      .env
      .blobs
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let blobs_arr = LeanArray::alloc(blobs.len());
    for (i, (addr, bytes)) in blobs.iter().enumerate() {
      blobs_arr.set(i, build_raw_blob(addr, bytes));
    }

    let comms: Vec<_> = compile_stt
      .env
      .comms
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let comms_arr = LeanArray::alloc(comms.len());
    for (i, (addr, comm)) in comms.iter().enumerate() {
      comms_arr.set(i, build_raw_comm(addr, comm));
    }

    // Build names array (Address → Ix.Name)
    let names: Vec<_> = compile_stt
      .env
      .names
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let names_arr = LeanArray::alloc(names.len());
    for (i, (addr, name)) in names.iter().enumerate() {
      names_arr.set(i, LeanIxonRawNameEntry::build(&mut cache, addr, name));
    }

    let result = LeanIxonRawEnv::alloc(0);
    result.set_obj(0, consts_arr);
    result.set_obj(1, named_arr);
    result.set_obj(2, blobs_arr);
    result.set_obj(3, comms_arr);
    result.set_obj(4, names_arr);
    crate::lean_ixon::env::set_raw_env_bundle_fields(&result, &compile_stt.env);
    LeanIOResult::ok(result)
  }
}

/// FFI function to canonicalize environment to Ix.RawEnvironment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_canonicalize_env_to_ix(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  {
    let rust_env = crate::lean_env::decode_env(env_consts_ptr);
    let mut cache = LeanBuildCache::with_capacity(rust_env.len());
    let raw_env = LeanIxRawEnvironment::build(&mut cache, &rust_env);
    LeanIOResult::ok(raw_env)
  }
}

/// FFI function to compute the LEON content hash of every constant in a
/// Lean environment. Returns an `Array (Ix.Name × Ix.Address)` where each
/// `Address` is the 32-byte Blake3 digest produced by
/// `ConstantInfo::get_hash()` in `src/ix/env.rs`.
///
/// The LEON hash is the Rust kernel's "original" addressing scheme: it's
/// derived from the serialized `ConstantInfo` (name + level params + type
/// expression + variant-specific fields: ctors, rules, `all`, value, hints,
/// etc.) so two constants with the same name but different content get
/// distinct addresses. This is the address scheme `lean_ingress` uses (or
/// will use) when populating `orig_kenv`, and the table Lean callers need
/// to dump when regenerating `PrimOrigAddrs` in the Rust kernel.
///
/// No compilation happens here — we only decode the Lean env and hash each
/// `ConstantInfo` in place. That makes this cheap relative to
/// `rs_compile_env_to_ixon` and safe to run on the full environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_leon_hashes(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let rust_env = crate::lean_env::decode_env(env_consts_ptr);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());

  let arr = LeanArray::alloc(rust_env.len());
  for (i, (name, ci)) in rust_env.iter().enumerate() {
    let name_obj = LeanIxName::build(&mut cache, name);
    let addr_obj = LeanIxAddress::build_from_hash(&ci.get_hash());
    arr.set(i, LeanProd::new(name_obj, addr_obj));
  }
  LeanIOResult::ok(arr)
}

// =============================================================================
// RustCompiledEnv - Holds Rust compilation results for comparison
// =============================================================================

#[cfg(feature = "test-ffi")]
/// Rust-compiled environment holding blocks indexed by low-link name.
/// Each block is stored as serialized bytes for comparison with Lean output.
pub struct RustCompiledEnv {
  /// Map from low-link name to (serialized constant bytes, sharing vector length)
  blocks: HashMap<Name, (Vec<u8>, usize)>,
  /// The full compile state for accessing pre-sharing expressions
  compile_state: CompileState,
}

// =============================================================================
// Block-by-block comparison FFI
// =============================================================================

/// FFI: Simple test to verify FFI round-trip works.
/// Takes a Lean.Name and returns a magic number to verify the call succeeded.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_test_ffi_roundtrip(name_ptr: LeanBorrowed<'_>) -> u64 {
  let global_cache = GlobalCache::default();
  let name = decode_name(name_ptr, &global_cache);

  // Return a magic number plus the hash of the name to verify it worked
  let hash = name.get_hash();
  let hash_bytes = hash.as_bytes();
  let hash_prefix =
    u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap_or([0u8; 8]));

  // Magic number 0xDEADBEEF plus hash prefix
  0xDEAD_BEEF_0000_0000 | (hash_prefix & 0x0000_0000_FFFF_FFFF)
}

/// FFI: Compile entire environment with Rust, returning a handle to RustCompiledEnv.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_compile_env_rust_first(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> *mut RustCompiledEnv {
  // Decode Lean environment
  let lean_env = crate::lean_env::decode_env(env_consts_ptr);
  let lean_env = Arc::new(lean_env);

  // Compile with Rust
  let rust_stt =
    match compile_env_with_options(&lean_env, CompileOptions::default()) {
      Ok(stt) => stt,
      Err(_e) => {
        return std::ptr::null_mut();
      },
    };

  // Build block map: lowlink name -> (serialized bytes, sharing len)
  let mut blocks: HashMap<Name, (Vec<u8>, usize)> = HashMap::new();

  // Iterate over all names and their addresses
  for entry in rust_stt.name_to_addr.iter() {
    let name = entry.key().clone();
    let addr = entry.value().clone();

    // Skip if we already have this block (multiple names map to same block)
    if blocks.contains_key(&name) {
      continue;
    }

    // Get the compiled constant
    if let Some(constant) = rust_stt.env.get_const(&addr) {
      let mut bytes = Vec::new();
      constant.put(&mut bytes);
      let sharing_len = constant.sharing.len();
      blocks.insert(name, (bytes, sharing_len));
    }
  }

  // Return boxed RustCompiledEnv with full compile state for pre-sharing access
  Box::into_raw(Box::new(RustCompiledEnv { blocks, compile_state: rust_stt }))
}

/// FFI: Compare a single block and return packed result.
/// Returns a packed u64: high 32 bits = matches (1) or error code (0 = mismatch, 2 = not found)
///                       low 32 bits = first diff offset (if mismatch)
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_compare_block(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanOwned,
  lean_bytes: LeanByteArray<LeanOwned>,
) -> u64 {
  if rust_env.is_null() {
    return 2u64 << 32; // not found
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };
  let lean_data = lean_bytes.as_bytes();

  // Look up Rust's compiled block
  let rust_bytes = match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes,
    None => {
      // Block not found in Rust compilation: code 2
      return 2u64 << 32;
    },
  };

  // Compare bytes
  if rust_bytes == lean_data {
    // Match: code 1
    return 1u64 << 32;
  }

  // Mismatch: find first differing byte
  rust_bytes.iter().zip(lean_data.iter()).position(|(a, b)| a != b).map_or_else(
    || {
      // One is a prefix of the other
      rust_bytes.len().min(lean_data.len()) as u64
    },
    |i| i as u64,
  )
}

/// FFI: Free a RustCompiledEnv.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_free_rust_env(rust_env: *mut RustCompiledEnv) {
  if !rust_env.is_null() {
    unsafe {
      drop(Box::from_raw(rust_env));
    }
  }
}

/// FFI: Get the number of blocks in a RustCompiledEnv.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_get_rust_env_block_count(
  rust_env: *const RustCompiledEnv,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let rust_env = unsafe { &*rust_env };
  rust_env.blocks.len() as u64
}

/// FFI: Get Rust's compiled bytes length for a block.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_bytes_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanOwned,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };

  match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes.len() as u64,
    None => 0,
  }
}

/// FFI: Copy Rust's compiled bytes into a pre-allocated Lean ByteArray.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_copy_block_bytes(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanOwned,
  dest: LeanByteArray<LeanOwned>,
) {
  if rust_env.is_null() {
    return;
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };

  let bytes = match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes,
    None => return,
  };

  // Copy into the Lean ByteArray
  unsafe { dest.set_data(bytes) };
}

/// FFI: Get Rust's sharing vector length for a block.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_sharing_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanOwned,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };

  match rust_env.blocks.get(&name) {
    Some((_, sharing_len)) => *sharing_len as u64,
    None => 0,
  }
}

// =============================================================================
// Pre-sharing expression extraction FFI
// =============================================================================

#[cfg(feature = "test-ffi")]
/// Frame for iterative unshare traversal.
enum UnshareFrame<'a> {
  Visit(&'a Arc<IxonExpr>),
  BuildApp,
  BuildLam,
  BuildAll,
  BuildLet(bool),
  BuildPrj(u64, u64),
}

#[cfg(feature = "test-ffi")]
/// Expand Share(idx) references in an expression using the sharing vector.
/// This reconstructs the "pre-sharing" expression from the post-sharing
/// representation. Uses iterative traversal to avoid stack overflow on deep
/// expressions.
#[allow(clippy::cast_possible_truncation)]
fn unshare_expr(
  expr: &Arc<IxonExpr>,
  sharing: &[Arc<IxonExpr>],
) -> Arc<IxonExpr> {
  let mut stack: Vec<UnshareFrame<'_>> = vec![UnshareFrame::Visit(expr)];
  let mut results: Vec<Arc<IxonExpr>> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      UnshareFrame::Visit(e) => match e.as_ref() {
        IxonExpr::Share(idx) => {
          if (*idx as usize) < sharing.len() {
            stack.push(UnshareFrame::Visit(&sharing[*idx as usize]));
          } else {
            results.push(e.clone());
          }
        },
        IxonExpr::App(f, a) => {
          stack.push(UnshareFrame::BuildApp);
          stack.push(UnshareFrame::Visit(a));
          stack.push(UnshareFrame::Visit(f));
        },
        IxonExpr::Lam(t, b) => {
          stack.push(UnshareFrame::BuildLam);
          stack.push(UnshareFrame::Visit(b));
          stack.push(UnshareFrame::Visit(t));
        },
        IxonExpr::All(t, b) => {
          stack.push(UnshareFrame::BuildAll);
          stack.push(UnshareFrame::Visit(b));
          stack.push(UnshareFrame::Visit(t));
        },
        IxonExpr::Let(nd, t, v, b) => {
          stack.push(UnshareFrame::BuildLet(*nd));
          stack.push(UnshareFrame::Visit(b));
          stack.push(UnshareFrame::Visit(v));
          stack.push(UnshareFrame::Visit(t));
        },
        IxonExpr::Prj(ti, fi, v) => {
          stack.push(UnshareFrame::BuildPrj(*ti, *fi));
          stack.push(UnshareFrame::Visit(v));
        },
        // Leaf nodes - no children to unshare
        _ => results.push(e.clone()),
      },
      UnshareFrame::BuildApp => {
        let a = results.pop().unwrap();
        let f = results.pop().unwrap();
        results.push(Arc::new(IxonExpr::App(f, a)));
      },
      UnshareFrame::BuildLam => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Arc::new(IxonExpr::Lam(t, b)));
      },
      UnshareFrame::BuildAll => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Arc::new(IxonExpr::All(t, b)));
      },
      UnshareFrame::BuildLet(nd) => {
        let b = results.pop().unwrap();
        let v = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Arc::new(IxonExpr::Let(nd, t, v, b)));
      },
      UnshareFrame::BuildPrj(ti, fi) => {
        let v = results.pop().unwrap();
        results.push(Arc::new(IxonExpr::Prj(ti, fi, v)));
      },
    }
  }

  results.pop().unwrap()
}

/// FFI: Get the pre-sharing root expressions for a constant.
/// Returns the number of root expressions, and writes serialized expressions to the output buffer.
/// Each expression is serialized without sharing (Share nodes are expanded).
///
/// Output format: [n_exprs:u64, len1:u64, expr1_bytes..., len2:u64, expr2_bytes..., ...]
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanOwned,
  out_buf: LeanByteArray<LeanOwned>,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  let addr = match rust_env.compile_state.name_to_addr.get(&name) {
    Some(a) => a.clone(),
    None => {
      return 0;
    },
  };

  // Get the constant (note: contains post-sharing expressions)
  let constant = match rust_env.compile_state.env.get_const(&addr) {
    Some(c) => c,
    None => {
      return 0;
    },
  };

  // Extract root expressions from the constant info
  let root_exprs: Vec<Arc<IxonExpr>> = match &constant.info {
    ConstantInfo::Defn(def) => vec![def.typ.clone(), def.value.clone()],
    ConstantInfo::Axio(ax) => vec![ax.typ.clone()],
    ConstantInfo::Quot(q) => vec![q.typ.clone()],
    ConstantInfo::Recr(rec) => {
      let mut exprs = vec![rec.typ.clone()];
      for rule in &rec.rules {
        exprs.push(rule.rhs.clone());
      }
      exprs
    },
    // Projections don't contain expressions directly
    ConstantInfo::CPrj(_)
    | ConstantInfo::RPrj(_)
    | ConstantInfo::IPrj(_)
    | ConstantInfo::DPrj(_) => {
      vec![]
    },
    ConstantInfo::Muts(muts) => {
      let mut exprs = Vec::new();
      for mc in muts {
        match mc {
          ixon::constant::MutConst::Defn(def) => {
            exprs.push(def.typ.clone());
            exprs.push(def.value.clone());
          },
          ixon::constant::MutConst::Indc(ind) => {
            exprs.push(ind.typ.clone());
            for ctor in &ind.ctors {
              exprs.push(ctor.typ.clone());
            }
          },
          ixon::constant::MutConst::Recr(rec) => {
            exprs.push(rec.typ.clone());
            for rule in &rec.rules {
              exprs.push(rule.rhs.clone());
            }
          },
        }
      }
      exprs
    },
  };

  // Unshare and serialize each root expression
  let mut output_bytes: Vec<u8> = Vec::new();
  let n_exprs = root_exprs.len() as u64;

  // Write number of expressions
  output_bytes.extend_from_slice(&n_exprs.to_le_bytes());

  for expr in &root_exprs {
    // Unshare the expression
    let unshared = unshare_expr(expr, &constant.sharing);

    // Serialize to bytes
    let mut expr_bytes: Vec<u8> = Vec::new();
    put_expr(&unshared, &mut expr_bytes);

    // Write length and bytes
    output_bytes.extend_from_slice(&(expr_bytes.len() as u64).to_le_bytes());
    output_bytes.extend(expr_bytes);
  }

  // Write to output buffer
  unsafe { out_buf.set_data(&output_bytes) };

  n_exprs
}

/// FFI: Get the buffer length needed for pre-sharing expressions.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanOwned,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  let addr = match rust_env.compile_state.name_to_addr.get(&name) {
    Some(a) => a.clone(),
    None => return 0,
  };

  // Get the constant
  let constant = match rust_env.compile_state.env.get_const(&addr) {
    Some(c) => c,
    None => return 0,
  };

  // Count root expressions
  let n_exprs = match &constant.info {
    ConstantInfo::Defn(_) => 2,
    ConstantInfo::Axio(_) | ConstantInfo::Quot(_) => 1,
    ConstantInfo::Recr(rec) => 1 + rec.rules.len(),
    // Projections don't contain expressions directly
    ConstantInfo::CPrj(_)
    | ConstantInfo::RPrj(_)
    | ConstantInfo::IPrj(_)
    | ConstantInfo::DPrj(_) => 0,
    ConstantInfo::Muts(muts) => {
      let mut count = 0;
      for mc in muts {
        match mc {
          ixon::constant::MutConst::Defn(_) => count += 2,
          ixon::constant::MutConst::Indc(ind) => count += 1 + ind.ctors.len(),
          ixon::constant::MutConst::Recr(rec) => count += 1 + rec.rules.len(),
        }
      }
      count
    },
  };

  // Estimate: 8 bytes per header + some for expression data
  // This is an upper bound estimate
  (8 + n_exprs * 1024) as u64
}

/// FFI: Look up a constant's compiled address from RustCompiledEnv.
/// Copies the 32-byte blake3 hash into the provided ByteArray.
/// Returns 1 on success, 0 if name not found.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_lookup_const_addr(
  rust_env: *const RustCompiledEnv,
  name_ptr: LeanOwned,
  out_addr: LeanByteArray<LeanOwned>,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = decode_name(name_ptr.borrow(), &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  match rust_env.compile_state.name_to_addr.get(&name) {
    Some(addr_ref) => {
      // Copy the 32-byte address into the output ByteArray
      unsafe { out_addr.set_data(addr_ref.as_bytes()) };
      1
    },
    None => 0,
  }
}

/// FFI: Get the total number of compiled constants in RustCompiledEnv.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_get_compiled_const_count(
  rust_env: *const RustCompiledEnv,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let rust_env = unsafe { &*rust_env };
  rust_env.compile_state.name_to_addr.len() as u64
}

// =============================================================================
// Error type FFI builders
// =============================================================================

use ixon::error::{CompileError, DecompileError, SerializeError};

impl LeanIxSerializeError<LeanOwned> {
  /// Build a Lean Ixon.SerializeError from a Rust SerializeError.
  ///
  /// Tags 0–6:
  ///   0: unexpectedEof (expected : String) → 1 obj
  ///   1: invalidTag (tag : UInt8) (context : String) → 1 obj + 1 scalar (UInt8)
  ///   2: invalidFlag (flag : UInt8) (context : String) → 1 obj + 1 scalar (UInt8)
  ///   3: invalidVariant (variant : UInt64) (context : String) → 1 obj + 8 scalar (UInt64)
  ///   4: invalidBool (value : UInt8) → 0 obj + 1 scalar (UInt8)
  ///   5: addressError → 0 obj + 0 scalar
  ///   6: invalidShareIndex (idx : UInt64) (max : Nat) → 1 obj (Nat) + 8 scalar (UInt64)
  pub fn build(se: &SerializeError) -> Self {
    match se {
      SerializeError::UnexpectedEof { expected } => {
        let ctor = LeanIxSerializeError::alloc(0);
        ctor.set_obj(0, build_lean_string(expected));
        ctor
      },
      SerializeError::InvalidTag { tag, context } => {
        let ctor = LeanIxSerializeError::alloc(1);
        ctor.set_obj(0, build_lean_string(context));
        ctor.set_num_8(0, *tag);
        ctor
      },
      SerializeError::InvalidFlag { flag, context } => {
        let ctor = LeanIxSerializeError::alloc(2);
        ctor.set_obj(0, build_lean_string(context));
        ctor.set_num_8(0, *flag);
        ctor
      },
      SerializeError::InvalidVariant { variant, context } => {
        let ctor = LeanIxSerializeError::alloc(3);
        ctor.set_obj(0, build_lean_string(context));
        ctor.set_num_64(0, *variant);
        ctor
      },
      SerializeError::InvalidBool { value } => {
        let ctor = LeanIxSerializeError::alloc(4);
        ctor.set_num_8(0, *value);
        ctor
      },
      SerializeError::AddressError => Self::new(LeanOwned::box_usize(5)),
      SerializeError::InvalidShareIndex { idx, max } => {
        let ctor = LeanIxSerializeError::alloc(6);
        ctor.set_obj(0, build_lean_nat_usize(*max));
        ctor.set_num_64(0, *idx);
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxSerializeError<R> {
  /// Decode a Lean Ixon.SerializeError to a Rust SerializeError.
  pub fn decode(&self) -> SerializeError {
    // Tag 5 (addressError) has 0 fields → Lean represents as scalar
    if self.inner().is_scalar() {
      let tag = self.inner().unbox_usize();
      assert_eq!(tag, 5, "Invalid scalar SerializeError tag: {}", tag);
      return SerializeError::AddressError;
    }
    match self.as_ctor().tag() {
      0 => {
        let expected = self.get_obj(0).as_string().to_string();
        SerializeError::UnexpectedEof { expected }
      },
      1 => {
        let context = self.get_obj(0).as_string().to_string();
        let tag_val = self.get_num_8(0);
        SerializeError::InvalidTag { tag: tag_val, context }
      },
      2 => {
        let context = self.get_obj(0).as_string().to_string();
        let flag = self.get_num_8(0);
        SerializeError::InvalidFlag { flag, context }
      },
      3 => {
        let context = self.get_obj(0).as_string().to_string();
        let variant = self.get_num_64(0);
        SerializeError::InvalidVariant { variant, context }
      },
      4 => {
        let value = self.get_num_8(0);
        SerializeError::InvalidBool { value }
      },
      5 => SerializeError::AddressError,
      6 => {
        let max = LeanNat::to_nat(&self.get_obj(0))
          .to_u64()
          .and_then(|x| usize::try_from(x).ok())
          .unwrap_or(0);
        let idx = self.get_num_64(0);
        SerializeError::InvalidShareIndex { idx, max }
      },
      tag => unreachable!("Invalid SerializeError tag: {tag}"),
    }
  }
}

impl LeanIxDecompileError<LeanOwned> {
  /// Build a Lean DecompileError from a Rust DecompileError.
  pub fn build(err: &DecompileError) -> Self {
    match err {
      DecompileError::InvalidRefIndex { idx, refs_len, constant } => {
        let ctor = LeanIxDecompileError::alloc(0);
        ctor.set_obj(0, build_lean_nat_usize(*refs_len));
        ctor.set_obj(1, build_lean_string(constant));
        ctor.set_num_64(0, *idx);
        ctor
      },
      DecompileError::InvalidUnivIndex { idx, univs_len, constant } => {
        let ctor = LeanIxDecompileError::alloc(1);
        ctor.set_obj(0, build_lean_nat_usize(*univs_len));
        ctor.set_obj(1, build_lean_string(constant));
        ctor.set_num_64(0, *idx);
        ctor
      },
      DecompileError::InvalidShareIndex { idx, max, constant } => {
        let ctor = LeanIxDecompileError::alloc(2);
        ctor.set_obj(0, build_lean_nat_usize(*max));
        ctor.set_obj(1, build_lean_string(constant));
        ctor.set_num_64(0, *idx);
        ctor
      },
      DecompileError::InvalidRecIndex { idx, ctx_size, constant } => {
        let ctor = LeanIxDecompileError::alloc(3);
        ctor.set_obj(0, build_lean_nat_usize(*ctx_size));
        ctor.set_obj(1, build_lean_string(constant));
        ctor.set_num_64(0, *idx);
        ctor
      },
      DecompileError::InvalidUnivVarIndex { idx, max, constant } => {
        let ctor = LeanIxDecompileError::alloc(4);
        ctor.set_obj(0, build_lean_nat_usize(*max));
        ctor.set_obj(1, build_lean_string(constant));
        ctor.set_num_64(0, *idx);
        ctor
      },
      DecompileError::MissingAddress(addr) => {
        let ctor = LeanIxDecompileError::alloc(5);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      DecompileError::MissingMetadata(addr) => {
        let ctor = LeanIxDecompileError::alloc(6);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      DecompileError::BlobNotFound(addr) => {
        let ctor = LeanIxDecompileError::alloc(7);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      DecompileError::BadBlobFormat { addr, expected } => {
        let ctor = LeanIxDecompileError::alloc(8);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor.set_obj(1, build_lean_string(expected));
        ctor
      },
      DecompileError::BadConstantFormat { msg } => {
        let ctor = LeanIxDecompileError::alloc(9);
        ctor.set_obj(0, build_lean_string(msg));
        ctor
      },
      DecompileError::Serialize(se) => {
        let ctor = LeanIxDecompileError::alloc(10);
        ctor.set_obj(0, LeanIxSerializeError::build(se));
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxDecompileError<R> {
  /// Decode a Lean DecompileError to a Rust DecompileError.
  pub fn decode(&self) -> DecompileError {
    match self.as_ctor().tag() {
      0 => {
        let refs_len = LeanNat::to_nat(&self.get_obj(0))
          .to_u64()
          .and_then(|x| usize::try_from(x).ok())
          .unwrap_or(0);
        let constant = self.get_obj(1).as_string().to_string();
        let idx = self.get_num_64(0);
        DecompileError::InvalidRefIndex { idx, refs_len, constant }
      },
      1 => {
        let univs_len = LeanNat::to_nat(&self.get_obj(0))
          .to_u64()
          .and_then(|x| usize::try_from(x).ok())
          .unwrap_or(0);
        let constant = self.get_obj(1).as_string().to_string();
        let idx = self.get_num_64(0);
        DecompileError::InvalidUnivIndex { idx, univs_len, constant }
      },
      2 => {
        let max = LeanNat::to_nat(&self.get_obj(0))
          .to_u64()
          .and_then(|x| usize::try_from(x).ok())
          .unwrap_or(0);
        let constant = self.get_obj(1).as_string().to_string();
        let idx = self.get_num_64(0);
        DecompileError::InvalidShareIndex { idx, max, constant }
      },
      3 => {
        let ctx_size = LeanNat::to_nat(&self.get_obj(0))
          .to_u64()
          .and_then(|x| usize::try_from(x).ok())
          .unwrap_or(0);
        let constant = self.get_obj(1).as_string().to_string();
        let idx = self.get_num_64(0);
        DecompileError::InvalidRecIndex { idx, ctx_size, constant }
      },
      4 => {
        let max = LeanNat::to_nat(&self.get_obj(0))
          .to_u64()
          .and_then(|x| usize::try_from(x).ok())
          .unwrap_or(0);
        let constant = self.get_obj(1).as_string().to_string();
        let idx = self.get_num_64(0);
        DecompileError::InvalidUnivVarIndex { idx, max, constant }
      },
      5 => DecompileError::MissingAddress(
        LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array()).decode(),
      ),
      6 => DecompileError::MissingMetadata(
        LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array()).decode(),
      ),
      7 => DecompileError::BlobNotFound(
        LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array()).decode(),
      ),
      8 => {
        let addr =
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let expected = self.get_obj(1).as_string().to_string();
        DecompileError::BadBlobFormat { addr, expected }
      },
      9 => {
        let msg = self.get_obj(0).as_string().to_string();
        DecompileError::BadConstantFormat { msg }
      },
      10 => DecompileError::Serialize(
        LeanIxSerializeError(self.get_obj(0)).decode(),
      ),
      tag => unreachable!("Invalid DecompileError tag: {tag}"),
    }
  }
}

impl LeanIxCompileError<LeanOwned> {
  /// Build a Lean CompileError from a Rust CompileError.
  ///
  /// Tags 0–5:
  ///   0: missingConstant (name : String) → 1 obj
  ///   1: missingAddress (addr : Address) → 1 obj
  ///   2: invalidMutualBlock (reason : String) → 1 obj
  ///   3: unsupportedExpr (desc : String) → 1 obj
  ///   4: unknownUnivParam (curr param : String) → 2 obj
  ///   5: serializeError (msg : String) → 1 obj
  pub fn build(err: &CompileError) -> Self {
    match err {
      CompileError::MissingConstant { name, .. } => {
        let ctor = LeanIxCompileError::alloc(0);
        ctor.set_obj(0, build_lean_string(name));
        ctor
      },
      CompileError::MissingAddress(addr) => {
        let ctor = LeanIxCompileError::alloc(1);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      CompileError::InvalidMutualBlock { reason } => {
        let ctor = LeanIxCompileError::alloc(2);
        ctor.set_obj(0, build_lean_string(reason));
        ctor
      },
      CompileError::UnsupportedExpr { desc } => {
        let ctor = LeanIxCompileError::alloc(3);
        ctor.set_obj(0, build_lean_string(desc));
        ctor
      },
      CompileError::UnknownUnivParam { curr, param } => {
        let ctor = LeanIxCompileError::alloc(4);
        ctor.set_obj(0, build_lean_string(curr));
        ctor.set_obj(1, build_lean_string(param));
        ctor
      },
      CompileError::Serialize(se) => {
        let ctor = LeanIxCompileError::alloc(5);
        ctor.set_obj(0, LeanIxSerializeError::build(se));
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxCompileError<R> {
  /// Decode a Lean CompileError to a Rust CompileError.
  pub fn decode(&self) -> CompileError {
    match self.as_ctor().tag() {
      0 => {
        let name = self.get_obj(0).as_string().to_string();
        CompileError::MissingConstant {
          name,
          caller: "ffi:decode_compile_error".into(),
        }
      },
      1 => CompileError::MissingAddress(
        LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array()).decode(),
      ),
      2 => {
        let reason = self.get_obj(0).as_string().to_string();
        CompileError::InvalidMutualBlock { reason }
      },
      3 => {
        let desc = self.get_obj(0).as_string().to_string();
        CompileError::UnsupportedExpr { desc }
      },
      4 => {
        let curr = self.get_obj(0).as_string().to_string();
        let param = self.get_obj(1).as_string().to_string();
        CompileError::UnknownUnivParam { curr, param }
      },
      5 => {
        CompileError::Serialize(LeanIxSerializeError(self.get_obj(0)).decode())
      },
      tag => unreachable!("Invalid CompileError tag: {tag}"),
    }
  }
}

/// FFI: Round-trip a DecompileError: Lean → Rust → Lean.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_decompile_error(
  obj: LeanIxDecompileError<LeanBorrowed<'_>>,
) -> LeanIxDecompileError<LeanOwned> {
  let err = obj.decode();
  LeanIxDecompileError::build(&err)
}

/// FFI: Round-trip a CompileError: Lean → Rust → Lean.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_compile_error(
  obj: LeanIxCompileError<LeanBorrowed<'_>>,
) -> LeanIxCompileError<LeanOwned> {
  let err = obj.decode();
  LeanIxCompileError::build(&err)
}

/// FFI: Round-trip a SerializeError: Lean → Rust → Lean.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_serialize_error(
  obj: LeanIxSerializeError<LeanBorrowed<'_>>,
) -> LeanIxSerializeError<LeanOwned> {
  let err = obj.decode();
  LeanIxSerializeError::build(&err)
}

// =============================================================================
// Decompilation FFI
// =============================================================================

/// FFI: decompile a serialized `.ixe` env from disk — the inverse of
/// `rs_compile_env` — returning the decompiled constant count.
///
/// A `decompile_env` failure (malformed output) is a hard error,
/// returned as an IO error so the caller reddens the cell. Timing and
/// peak-RSS are measured by the Lean caller around this call, with the
/// same texray infrastructure `ix compile --json` uses. Deeper
/// compile→decompile roundtrip fidelity is gated by the canonical
/// roundtrip tests (`ix validate` / `rs_decompile_roundtrip`), which
/// need the original Lean env a `.ixe` can't supply — the bench does
/// not reproduce them here.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_decompile_env"]
/// opaque rsDecompileEnvFFI : @& String → IO Nat
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rs_decompile_env(
  path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let path = path.as_str().to_string();

  let bytes = match std::fs::read(&path) {
    Ok(b) => b,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_decompile_env: failed to read {path}: {e}"
      ));
    },
  };
  // Demoted-at-parse load: decompile reads each entry's metadata a
  // bounded number of times, and the whole named section's structured
  // form costs a large multiple of its encoding — enough to dominate
  // the decompile's peak RSS on the biggest envs. One load path at
  // every scale also keeps the bench rows comparable across envs.
  let mut slice: &[u8] = &bytes;
  let env = match ixon::env::Env::get_demoted_named(&mut slice) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_decompile_env: failed to deserialize {path}: {e}"
      ));
    },
  };

  // The env owns its bytes after parsing; release the file buffer
  // before the decompile allocates next to it.
  drop(bytes);

  // Decompile needs every reachable constant carried: a thin bundle
  // deliberately omits its assumed subtrees, and a bundle with a broken
  // closure would otherwise surface deep inside the decompile as a
  // confusing per-constant error. Whole envs (`main = None`) carry
  // everything by construction and skip the closure walk.
  if !env.assumptions.is_empty() {
    return LeanIOResult::error_string(&format!(
      "rs_decompile_env: {path} is a thin bundle ({} assumptions); \
       decompile needs a self-contained env",
      env.assumptions.len()
    ));
  }
  if env.main.is_some()
    && let Err(e) = env.validate_closed()
  {
    return LeanIOResult::error_string(&format!(
      "rs_decompile_env: {path}: {e}"
    ));
  }

  // decompile_env reads only `stt.env`; Pass 2 (aux_gen regeneration)
  // reconstructs the block structure from the env itself —
  // `name_to_addr` so aux_gen resolves addresses for the names it
  // regenerates (mirroring `rs_compile_validate_aux`'s Phase 7 setup).
  let stt = CompileState { env, ..CompileState::default() };
  for entry in stt.env.named.iter() {
    stt.name_to_addr.insert(entry.key().clone(), entry.value().addr.clone());
  }

  let dstt = match decompile_env(&stt) {
    Ok(d) => d,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_decompile_env: decompile of {path} failed: {e:?}"
      ));
    },
  };
  LeanIOResult::ok(LeanOwned::from_nat_u64(dstt.env.len() as u64))
}

// =============================================================================
// aux_gen differential dumps (test-ffi)
// =============================================================================

/// Render an expression's canonical content hash as an address hex string.
#[cfg(feature = "test-ffi")]
fn aux_dump_expr_addr(e: &ix_common::env::Expr) -> String {
  Address::from_blake3_hash(*e.get_hash()).hex()
}

/// Dump the nested-expansion/canonicity intermediates for one SCC block,
/// rebuilding exactly the production aux_gen Phase-1 inputs
/// (`compile_mutual` → `generate_aux_patches`): member `MutConst`s →
/// `sort_consts` → `ordered_originals`/`alias_to_rep` →
/// `expand_nested_block` → (nested path) `sort_aux_by_partition_refinement`
/// → `compute_aux_perm` → `source_aux_order_with_owner`. Every step is
/// deterministic, so a post-compile re-run reproduces what production did
/// (same argument as the `validate-aux` Phase 2 re-run).
#[cfg(feature = "test-ffi")]
fn aux_dump_block(
  lo: &Name,
  all: &[Name],
  lean_env: &Arc<ix_common::env::Env>,
  stt: &CompileState,
  out: &mut String,
) {
  use ix_compile::compile::{BlockCache, mk_indc, sort_consts};
  use ix_compile::compile::aux_gen::nested;
  use ix_compile::mutual::{Def, MutConst};
  use ix_common::env::ConstantInfo as LeanCI;
  use std::fmt::Write as _;

  let _ = writeln!(out, "block {}", lo.pretty());

  // Mirror compile_mutual's cs construction (compile.rs:3732-3753).
  let mut cs: Vec<MutConst> = Vec::new();
  for n in all {
    let Some(ci) = lean_env.get(n).map(|e| e.cloned()) else {
      let _ = writeln!(out, "error collect missing {}", n.pretty());
      return;
    };
    let mc = match &ci {
      LeanCI::InductInfo(val) => match mk_indc(val, lean_env) {
        Ok(ind) => MutConst::Indc(ind),
        Err(e) => {
          let _ = writeln!(out, "error mk_indc {e:?}");
          return;
        },
      },
      LeanCI::DefnInfo(val) => MutConst::Defn(Def::mk_defn(val)),
      LeanCI::OpaqueInfo(val) => MutConst::Defn(Def::mk_opaq(val)),
      LeanCI::ThmInfo(val) => MutConst::Defn(Def::mk_theo(val)),
      LeanCI::RecInfo(val) => MutConst::Recr(val.clone()),
      _ => continue,
    };
    cs.push(mc);
  }

  let mut cache = BlockCache::default();
  let sorted_classes = match sort_consts(&cs.iter().collect::<Vec<_>>(), &mut cache, stt)
  {
    Ok(sc) => sc,
    Err(e) => {
      let _ = writeln!(out, "error sort_consts {e:?}");
      return;
    },
  };

  // generate_aux_patches Phase-1 inputs (aux_gen.rs:241-263).
  let ordered_originals: Vec<Name> =
    sorted_classes.iter().map(|c| c[0].name()).collect();
  let alias_to_rep: rustc_hash::FxHashMap<Name, Name> = sorted_classes
    .iter()
    .flat_map(|class| {
      class[1..].iter().map(move |alias| (alias.name(), class[0].name()))
    })
    .collect();
  let original_all: Vec<Name> = cs
    .iter()
    .find_map(|c| match c {
      MutConst::Indc(ind) => Some(ind.ind.all.clone()),
      _ => None,
    })
    .unwrap_or_default();

  let metadata_has_nested = original_all.iter().any(|name| {
    matches!(
      lean_env.get(name).as_deref(),
      Some(LeanCI::InductInfo(v))
        if ix_compile::compile::nat_conv::nat_to_usize(&v.num_nested) > 0
    )
  });

  let mut expanded =
    match nested::expand_nested_block(&ordered_originals, lean_env, &alias_to_rep) {
      Ok(x) => x,
      Err(e) => {
        let _ = writeln!(out, "error expand {e:?}");
        return;
      },
    };
  let structural_has_nested = expanded.types.len() > expanded.n_originals;

  let _ = writeln!(
    out,
    "flags meta_nested={metadata_has_nested} structural_nested={structural_has_nested} n_classes={}",
    sorted_classes.len()
  );
  let levels: Vec<String> =
    expanded.level_params.iter().map(|n| n.pretty()).collect();
  let _ = writeln!(out, "levels {}", levels.join(" "));
  for (i, n) in ordered_originals.iter().enumerate() {
    let _ = writeln!(out, "original {i} {}", n.pretty());
  }

  // Pre-sort expansion state.
  for (i, mem) in expanded.types.iter().enumerate() {
    let _ = writeln!(
      out,
      "pre {i} name={} owner={} params={} indices={} typ={}",
      mem.name.pretty(),
      mem.source_owner.pretty(),
      mem.n_params,
      mem.n_indices,
      aux_dump_expr_addr(&mem.typ)
    );
    for (j, ctor) in mem.ctors.iter().enumerate() {
      let _ = writeln!(
        out,
        "prector {i} {j} name={} fields={} typ={}",
        ctor.name.pretty(),
        ctor.n_fields,
        aux_dump_expr_addr(&ctor.typ)
      );
    }
  }
  let mut nested_entries: Vec<(String, String)> = expanded
    .aux_to_nested
    .iter()
    .map(|(n, e)| (n.pretty(), aux_dump_expr_addr(e)))
    .collect();
  nested_entries.sort();
  for (n, h) in &nested_entries {
    let _ = writeln!(out, "nested {n} {h}");
  }
  let mut auxctor_entries: Vec<(String, String, String)> = expanded
    .aux_ctor_map
    .iter()
    .map(|(c, (orig, ind))| (c.pretty(), orig.pretty(), ind.pretty()))
    .collect();
  auxctor_entries.sort();
  for (c, o, i) in &auxctor_entries {
    let _ = writeln!(out, "auxctor {c} {o} {i}");
  }

  if !(metadata_has_nested && structural_has_nested) {
    return;
  }

  // Canonical sort of the aux tail (aux_gen.rs:280).
  let sortperm = match nested::sort_aux_by_partition_refinement(&mut expanded, stt) {
    Ok(p) => p,
    Err(e) => {
      let _ = writeln!(out, "error sortaux {e:?}");
      return;
    },
  };
  let sortperm_strs: Vec<String> =
    sortperm.iter().map(|p| p.to_string()).collect();
  let _ = writeln!(out, "sortperm {}", sortperm_strs.join(" "));
  for (i, mem) in expanded.types.iter().enumerate().skip(expanded.n_originals) {
    let _ = writeln!(
      out,
      "post {i} name={} owner={} typ={}",
      mem.name.pretty(),
      mem.source_owner.pretty(),
      aux_dump_expr_addr(&mem.typ)
    );
    for (j, ctor) in mem.ctors.iter().enumerate() {
      let _ = writeln!(
        out,
        "postctor {i} {j} name={} typ={}",
        ctor.name.pretty(),
        aux_dump_expr_addr(&ctor.typ)
      );
    }
  }

  // Source→canonical permutation (aux_gen.rs:292-307).
  let orig_to_canon_map: HashMap<Name, Name> = sorted_classes
    .iter()
    .flat_map(|class| {
      let rep = class[0].name();
      class.iter().map(move |n| (n.name(), rep.clone()))
    })
    .collect();
  match nested::compute_aux_perm(
    &expanded,
    &original_all,
    lean_env,
    stt,
    &orig_to_canon_map,
  ) {
    Ok(perm) => {
      let perm_strs: Vec<String> = perm
        .iter()
        .map(|&p| {
          if p == nested::PERM_OUT_OF_SCC { "out".to_string() } else { p.to_string() }
        })
        .collect();
      let _ = writeln!(out, "perm {}", perm_strs.join(" "));
    },
    Err(e) => {
      let _ = writeln!(out, "error perm {e:?}");
      return;
    },
  }

  // Lean source-walk discovery order (nested.rs:997).
  match nested::source_aux_order_with_owner(&original_all, lean_env) {
    Ok(entries) => {
      for (j, (owner, head, specs)) in entries.iter().enumerate() {
        let spec_strs: Vec<String> =
          specs.iter().map(aux_dump_expr_addr).collect();
        let _ = writeln!(
          out,
          "source {j} owner={} head={} specs={}",
          owner.pretty(),
          head.pretty(),
          spec_strs.join(",")
        );
      }
    },
    Err(e) => {
      let _ = writeln!(out, "error source {e:?}");
    },
  }
}

/// FFI: deterministic text dump of nested-expansion/canonicity
/// intermediates for every inductive SCC block. The pure-Lean port
/// (`Tests.Compile.AuxGenDiff`) reproduces the same text from its own
/// structures; the A2 gate is a line diff. See `aux_dump_block` for the
/// format contract.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_aux_gen_dump_expand(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let rust_env = crate::lean_env::decode_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);

  let stt = match compile_env_with_options(&rust_env, CompileOptions::default())
  {
    Ok(stt) => stt,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_aux_gen_dump_expand: compile failed: {e:?}"
      ));
    },
  };

  let ref_graph = build_ref_graph(&rust_env);
  let condensed = compute_sccs(&ref_graph.out_refs);

  // Deterministic block order: sort inductive-containing blocks by
  // lowlink pretty name.
  let mut blocks: Vec<(String, Name, Vec<Name>)> = condensed
    .blocks
    .iter()
    .filter_map(|(lo, members)| {
      let mut all: Vec<Name> = members.iter().cloned().collect();
      all.sort_by_key(|a| a.pretty());
      let has_ind = all.iter().any(|n| {
        matches!(
          rust_env.get(n).as_deref(),
          Some(ix_common::env::ConstantInfo::InductInfo(_))
        )
      });
      has_ind.then(|| (lo.pretty(), lo.clone(), all))
    })
    .collect();
  blocks.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

  let mut out = String::new();
  for (_, lo, all) in &blocks {
    aux_dump_block(lo, all, &rust_env, &stt, &mut out);
  }

  LeanIOResult::ok(LeanString::new(&out))
}

/// Render one generated patch as stable text lines. Expression bodies are
/// content HASHES (both sides build via mirrored hash-maintaining
/// constructors, so tree equality ⇔ hash equality — the A2 gate
/// established this for expansion outputs). Lines are kind-tagged so the
/// Lean harness can widen its comparison scope per milestone
/// (rec → casesOn/recOn → below → brecOn).
#[cfg(feature = "test-ffi")]
fn aux_dump_patch(
  name: &Name,
  patch: &ix_compile::compile::aux_gen::PatchedConstant,
  out: &mut String,
) {
  use ix_compile::compile::aux_gen::PatchedConstant as PC;
  use std::fmt::Write as _;
  match patch {
    PC::Rec(rv) => {
      let lps: Vec<String> =
        rv.cnst.level_params.iter().map(|n| n.pretty()).collect();
      let _ = writeln!(
        out,
        "patch {} kind=rec lvls={} k={} params={} indices={} motives={} minors={} all={} typ={}",
        name.pretty(),
        lps.join(","),
        rv.k,
        ix_compile::compile::nat_conv::nat_to_u64(&rv.num_params),
        ix_compile::compile::nat_conv::nat_to_u64(&rv.num_indices),
        ix_compile::compile::nat_conv::nat_to_u64(&rv.num_motives),
        ix_compile::compile::nat_conv::nat_to_u64(&rv.num_minors),
        rv.all.iter().map(|n| n.pretty()).collect::<Vec<_>>().join(","),
        aux_dump_expr_addr(&rv.cnst.typ)
      );
      for (i, rule) in rv.rules.iter().enumerate() {
        let _ = writeln!(
          out,
          "rule {} {} ctor={} fields={} rhs={}",
          name.pretty(),
          i,
          rule.ctor.pretty(),
          ix_compile::compile::nat_conv::nat_to_u64(&rule.n_fields),
          aux_dump_expr_addr(&rule.rhs)
        );
      }
    },
    PC::RecOn(d) | PC::CasesOn(d) => {
      let kind = if matches!(patch, PC::RecOn(_)) { "recOn" } else { "casesOn" };
      let lps: Vec<String> =
        d.level_params.iter().map(|n| n.pretty()).collect();
      let _ = writeln!(
        out,
        "patch {} kind={} lvls={} unsafe={} typ={} value={}",
        name.pretty(),
        kind,
        lps.join(","),
        d.is_unsafe,
        aux_dump_expr_addr(&d.typ),
        aux_dump_expr_addr(&d.value)
      );
    },
    PC::BelowDef(d) => {
      let lps: Vec<String> =
        d.level_params.iter().map(|n| n.pretty()).collect();
      let _ = writeln!(
        out,
        "patch {} kind=belowDef lvls={} unsafe={} typ={} value={}",
        name.pretty(),
        lps.join(","),
        d.is_unsafe,
        aux_dump_expr_addr(&d.typ),
        aux_dump_expr_addr(&d.value)
      );
    },
    PC::BelowIndc(ind) => {
      let lps: Vec<String> =
        ind.level_params.iter().map(|n| n.pretty()).collect();
      let _ = writeln!(
        out,
        "patch {} kind=belowIndc lvls={} params={} indices={} reflexive={} unsafe={} typ={}",
        name.pretty(),
        lps.join(","),
        ind.n_params,
        ind.n_indices,
        ind.is_reflexive,
        ind.is_unsafe,
        aux_dump_expr_addr(&ind.typ)
      );
      for (i, ctor) in ind.ctors.iter().enumerate() {
        let _ = writeln!(
          out,
          "belowctor {} {} name={} params={} fields={} typ={}",
          name.pretty(),
          i,
          ctor.name.pretty(),
          ctor.n_params,
          ctor.n_fields,
          aux_dump_expr_addr(&ctor.typ)
        );
      }
    },
    PC::BRecOn(d) => {
      let lps: Vec<String> =
        d.level_params.iter().map(|n| n.pretty()).collect();
      let _ = writeln!(
        out,
        "patch {} kind=brecOn lvls={} unsafe={} prop={} typ={} value={}",
        name.pretty(),
        lps.join(","),
        d.is_unsafe,
        d.is_prop,
        aux_dump_expr_addr(&d.typ),
        aux_dump_expr_addr(&d.value)
      );
    },
  }
}

/// FFI: deterministic text dump of `generate_aux_patches` output for
/// every inductive SCC block — the gate medium for the recursor/casesOn/
/// recOn/below/brecOn port milestones. Re-runs the production Phase-1
/// pipeline per block post-compile (the `validate-aux` Phase 2 precedent)
/// with the REAL sorted classes.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_aux_gen_dump_patches(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  use ix_compile::compile::aux_gen;
  use ix_compile::compile::{BlockCache, mk_indc, sort_consts};
  use ix_compile::mutual::{Def, MutConst};
  use ix_common::env::ConstantInfo as LeanCI;
  use std::fmt::Write as _;

  let rust_env = crate::lean_env::decode_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);

  let stt = match compile_env_with_options(&rust_env, CompileOptions::default())
  {
    Ok(stt) => stt,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_aux_gen_dump_patches: compile failed: {e:?}"
      ));
    },
  };

  let ref_graph = build_ref_graph(&rust_env);
  let condensed = compute_sccs(&ref_graph.out_refs);

  let mut blocks: Vec<(String, Name, Vec<Name>)> = condensed
    .blocks
    .iter()
    .filter_map(|(lo, members)| {
      let mut all: Vec<Name> = members.iter().cloned().collect();
      all.sort_by_key(|a| a.pretty());
      let has_ind = all.iter().any(|n| {
        matches!(rust_env.get(n).as_deref(), Some(LeanCI::InductInfo(_)))
      });
      has_ind.then(|| (lo.pretty(), lo.clone(), all))
    })
    .collect();
  blocks.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

  let mut out = String::new();
  for (_, lo, all) in &blocks {
    let _ = writeln!(out, "block {}", lo.pretty());

    // Production inputs (mirrors compile_mutual + generate_aux_patches).
    let mut cs: Vec<MutConst> = Vec::new();
    for n in all {
      let Some(ci) = rust_env.get(n).map(|e| e.cloned()) else { continue };
      let mc = match &ci {
        LeanCI::InductInfo(val) => match mk_indc(val, &rust_env) {
          Ok(ind) => MutConst::Indc(ind),
          Err(e) => {
            let _ = writeln!(out, "error mk_indc {e:?}");
            continue;
          },
        },
        LeanCI::DefnInfo(val) => MutConst::Defn(Def::mk_defn(val)),
        LeanCI::OpaqueInfo(val) => MutConst::Defn(Def::mk_opaq(val)),
        LeanCI::ThmInfo(val) => MutConst::Defn(Def::mk_theo(val)),
        LeanCI::RecInfo(val) => MutConst::Recr(val.clone()),
        _ => continue,
      };
      cs.push(mc);
    }
    let mut cache = BlockCache::default();
    let sorted_classes =
      match sort_consts(&cs.iter().collect::<Vec<_>>(), &mut cache, &stt) {
        Ok(sc) => sc,
        Err(e) => {
          let _ = writeln!(out, "error sort_consts {e:?}");
          continue;
        },
      };
    let class_names: Vec<Vec<Name>> = sorted_classes
      .iter()
      .map(|class| class.iter().map(|c| c.name()).collect())
      .collect();
    let original_all: Vec<Name> = cs
      .iter()
      .find_map(|c| match c {
        MutConst::Indc(ind) => Some(ind.ind.all.clone()),
        _ => None,
      })
      .unwrap_or_default();

    let mut kctx = ix_compile::compile::KernelCtx::new();
    let aux_out = match aux_gen::generate_aux_patches(
      &class_names,
      &original_all,
      &rust_env,
      &stt,
      &mut kctx,
    ) {
      Ok(p) => p,
      Err(e) => {
        let _ = writeln!(out, "error generate {e:?}");
        continue;
      },
    };

    let mut patch_names: Vec<&Name> = aux_out.patches.keys().collect();
    patch_names.sort_by_key(|n| n.pretty());
    for name in patch_names {
      aux_dump_patch(name, &aux_out.patches[name], &mut out);
    }
    let mut aliases: Vec<(String, String)> = aux_out
      .aliases
      .iter()
      .map(|(k, v)| (k.pretty(), v.pretty()))
      .collect();
    aliases.sort();
    for (k, v) in &aliases {
      let _ = writeln!(out, "alias {k} {v}");
    }
  }

  LeanIOResult::ok(LeanString::new(&out))
}

/// Render bool-vec keep masks / usize perms compactly for the plans dump.
#[cfg(feature = "test-ffi")]
fn aux_dump_bits(bits: &[bool]) -> String {
  bits.iter().map(|&b| if b { '1' } else { '0' }).collect()
}

#[cfg(feature = "test-ffi")]
fn aux_dump_usizes(xs: &[usize]) -> String {
  xs.iter()
    .map(|&x| {
      if x == usize::MAX { "out".to_string() } else { x.to_string() }
    })
    .collect::<Vec<_>>()
    .join(",")
}

/// FFI: deterministic text dump of the post-compile surgery plans,
/// AuxLayouts, and synthetic `Muts` named entries — the A7 gate medium
/// (orchestration parity). Lines:
///   plan <name> params=<n> smotives=<n> sminors=<n> indices=<n>
///        mkeep=<bits> nkeep=<bits> m2c=<csv> n2c=<csv> inblock=<bits>
///        head=<target>@<pos>|none
///   bplan <name> params=<n> smotives=<n> indices=<n> mkeep=<bits> m2c=<csv>
///   wplan <name> ...                    (below plans, same shape as bplan)
///   layout <all0> perm=<csv> counts=<csv>
///   muts <name> addr=<hex> all=<h,h;h|...> layout=<perm csv>/<counts csv>|none
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_aux_gen_dump_plans(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  use std::fmt::Write as _;

  let rust_env = crate::lean_env::decode_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);

  let stt = match compile_env_with_options(&rust_env, CompileOptions::default())
  {
    Ok(stt) => stt,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_aux_gen_dump_plans: compile failed: {e:?}"
      ));
    },
  };

  let mut out = String::new();

  let mut plans: Vec<(String, ix_compile::compile::surgery::CallSitePlan)> =
    stt
      .call_site_plans
      .iter()
      .map(|e| (e.key().pretty(), e.value().clone()))
      .collect();
  plans.sort_by(|(a, _), (b, _)| a.cmp(b));
  for (name, p) in &plans {
    let head = match &p.head_rewrite {
      Some(h) => format!("{}@{}", h.target_rec.pretty(), h.target_motive_pos),
      None => "none".to_string(),
    };
    let _ = writeln!(
      out,
      "plan {name} params={} smotives={} sminors={} indices={} mkeep={} nkeep={} m2c={} n2c={} inblock={} head={head}",
      p.n_params,
      p.n_source_motives,
      p.n_source_minors,
      p.n_indices,
      aux_dump_bits(&p.motive_keep),
      aux_dump_bits(&p.minor_keep),
      aux_dump_usizes(&p.source_to_canon_motive),
      aux_dump_usizes(&p.source_to_canon_minor),
      aux_dump_bits(&p.source_in_block),
    );
  }

  for (tag, map) in [
    ("bplan", &stt.brec_on_call_site_plans),
    ("wplan", &stt.below_call_site_plans),
  ] {
    let mut bplans: Vec<(
      String,
      ix_compile::compile::surgery::BRecOnCallSitePlan,
    )> = map.iter().map(|e| (e.key().pretty(), e.value().clone())).collect();
    bplans.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (name, p) in &bplans {
      let _ = writeln!(
        out,
        "{tag} {name} params={} smotives={} indices={} mkeep={} m2c={}",
        p.n_params,
        p.n_source_motives,
        p.n_indices,
        aux_dump_bits(&p.motive_keep),
        aux_dump_usizes(&p.source_to_canon_motive),
      );
    }
  }

  let mut layouts: Vec<(String, ix_compile::compile::surgery::AuxLayout)> =
    stt
      .aux_perms
      .iter()
      .map(|e| (e.key().pretty(), e.value().clone()))
      .collect();
  layouts.sort_by(|(a, _), (b, _)| a.cmp(b));
  for (name, l) in &layouts {
    let _ = writeln!(
      out,
      "layout {name} perm={} counts={}",
      aux_dump_usizes(&l.perm),
      l.source_ctor_counts
        .iter()
        .map(|c| c.to_string())
        .collect::<Vec<_>>()
        .join(",")
    );
  }

  // Synthetic Muts named entries (kernel ingress discovery points).
  let mut muts: Vec<(String, String, String, String)> = stt
    .env
    .named
    .iter()
    .filter_map(|e| {
      let named = e.value();
      match &named.meta().info {
        ixon::metadata::ConstantMetaInfo::Muts { all, aux_layout } => {
          let all_str = all
            .iter()
            .map(|class| {
              class.iter().map(|a| a.hex()).collect::<Vec<_>>().join(",")
            })
            .collect::<Vec<_>>()
            .join(";");
          let layout_str = match aux_layout {
            Some(l) => format!(
              "{}/{}",
              aux_dump_usizes(&l.perm),
              l.source_ctor_counts
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(",")
            ),
            None => "none".to_string(),
          };
          Some((e.key().pretty(), named.addr.hex(), all_str, layout_str))
        },
        _ => None,
      }
    })
    .collect();
  muts.sort();
  for (name, addr, all_str, layout_str) in &muts {
    let _ = writeln!(out, "muts {name} addr={addr} all={all_str} layout={layout_str}");
  }

  LeanIOResult::ok(LeanString::new(&out))
}
