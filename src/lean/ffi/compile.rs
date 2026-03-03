//! FFI bridge between Lean and Rust for the Ixon compilation/decompilation pipeline.
//!
//! Provides `extern "C"` functions callable from Lean via `@[extern]`:
//! - `rs_compile_env_full` / `rs_compile_env`: compile a Lean environment to Ixon
//! - `rs_compile_phases`: run individual pipeline phases (canon, condense, graph, compile)
//! - `rs_decompile_env`: decompile Ixon back to Lean environment
//! - `rs_roundtrip_*`: roundtrip FFI tests for Lean↔Rust type conversions
//! - `build_*` / `decode_*`: convert between Lean constructor layouts and Rust types

use std::collections::HashMap;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::compile::{CompileState, compile_env};
use crate::ix::condense::compute_sccs;
use crate::ix::decompile::decompile_env;
use crate::ix::env::Name;
use crate::ix::graph::build_ref_graph;
use crate::ix::ixon::constant::{Constant as IxonConstant, ConstantInfo};
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::{Comm, ConstantMeta};
use crate::lean::ffi::{ffi_io_guard, io_error, io_ok};
use crate::lean::lean_sys::lean_uint64_to_nat;
use crate::lean::nat::Nat;
use crate::lean::object::{
  LeanArray, LeanByteArray, LeanCtor, LeanExcept, LeanIxBlockCompareDetail,
  LeanIxBlockCompareResult, LeanIxCompileError, LeanIxCompilePhases,
  LeanIxCondensedBlocks, LeanIxDecompileError, LeanIxSerializeError,
  LeanIxonRawEnv, LeanObject, LeanString,
};

use dashmap::DashMap;
use dashmap::DashSet;

use crate::lean::ffi::builder::LeanBuildCache;
use crate::lean::ffi::graph::build_condensed_blocks;
use crate::lean::ffi::ix::constant::build_constant_info;
use crate::lean::ffi::ix::env::build_raw_environment;
use crate::lean::ffi::ix::name::build_name;
use crate::lean::ffi::ixon::constant::{
  build_address_from_ixon, build_ixon_constant, decode_ixon_address,
};
use crate::lean::ffi::ixon::env::{
  build_raw_env, build_raw_name_entry, decode_raw_env, decoded_to_ixon_env,
};
use crate::lean::ffi::ixon::meta::{build_constant_meta, build_ixon_comm};
use crate::lean::ffi::lean_env::{
  GlobalCache, lean_ptr_to_env, lean_ptr_to_name,
};

// =============================================================================
// Helper builders
// =============================================================================

/// Build a Lean String from a Rust &str.
fn build_lean_string(s: &str) -> LeanObject {
  LeanString::from_str(s).into()
}

/// Build a Lean Nat from a usize.
fn build_lean_nat_usize(n: usize) -> LeanObject {
  unsafe { LeanObject::from_raw(lean_uint64_to_nat(n as u64).cast()) }
}

// =============================================================================
// Raw* Builder Functions for Compile FFI
// =============================================================================

/// Build RawConst: { addr : Address, const : Ixon.Constant }
pub fn build_raw_const(addr: &Address, constant: &IxonConstant) -> LeanObject {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(addr));
  ctor.set(1, build_ixon_constant(constant));
  *ctor
}

/// Build RawNamed: { name : Ix.Name, addr : Address, constMeta : Ixon.ConstantMeta }
pub fn build_raw_named(
  cache: &mut LeanBuildCache,
  name: &Name,
  addr: &Address,
  meta: &ConstantMeta,
) -> LeanObject {
  let ctor = LeanCtor::alloc(0, 3, 0);
  ctor.set(0, build_name(cache, name));
  ctor.set(1, build_address_from_ixon(addr));
  ctor.set(2, build_constant_meta(meta));
  *ctor
}

/// Build RawBlob: { addr : Address, bytes : ByteArray }
pub fn build_raw_blob(addr: &Address, bytes: &[u8]) -> LeanObject {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(addr));
  ctor.set(1, LeanByteArray::from_bytes(bytes));
  *ctor
}

/// Build RawComm: { addr : Address, comm : Ixon.Comm }
pub fn build_raw_comm(addr: &Address, comm: &Comm) -> LeanObject {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(addr));
  ctor.set(1, build_ixon_comm(comm));
  *ctor
}

// =============================================================================
// RustCondensedBlocks roundtrip FFI
// =============================================================================

/// Round-trip a RustCondensedBlocks structure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_rust_condensed_blocks(
  obj: LeanIxCondensedBlocks,
) -> LeanIxCondensedBlocks {
  let ctor = obj.as_ctor();
  let low_links = ctor.get(0);
  let blocks = ctor.get(1);
  let block_refs = ctor.get(2);

  low_links.inc_ref();
  blocks.inc_ref();
  block_refs.inc_ref();

  let result = LeanCtor::alloc(0, 3, 0);
  result.set(0, low_links);
  result.set(1, blocks);
  result.set(2, block_refs);
  (*result).into()
}

/// Round-trip a RustCompilePhases structure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_rust_compile_phases(
  obj: LeanIxCompilePhases,
) -> LeanIxCompilePhases {
  let ctor = obj.as_ctor();
  let raw_env = ctor.get(0);
  let condensed = ctor.get(1);
  let compile_env = ctor.get(2);

  raw_env.inc_ref();
  condensed.inc_ref();
  compile_env.inc_ref();

  let result = LeanCtor::alloc(0, 3, 0);
  result.set(0, raw_env);
  result.set(1, condensed);
  result.set(2, compile_env);
  (*result).into()
}

// =============================================================================
// BlockCompareResult and BlockCompareDetail roundtrip FFI
// =============================================================================

/// Round-trip a BlockCompareResult.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_result(
  obj: LeanIxBlockCompareResult,
) -> LeanIxBlockCompareResult {
  // Tags 0 (match) and 2 (notFound) have 0 fields → Lean represents as scalars
  if obj.is_scalar() {
    return obj;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    1 => {
      // mismatch: 0 obj, 24 scalar bytes (3 × u64)
      let lean_size = ctor.scalar_u64(0, 0);
      let rust_size = ctor.scalar_u64(0, 8);
      let first_diff = ctor.scalar_u64(0, 16);

      let out = LeanCtor::alloc(1, 0, 24);
      out.set_u64(0, lean_size);
      out.set_u64(8, rust_size);
      out.set_u64(16, first_diff);
      (*out).into()
    },
    _ => unreachable!("Invalid BlockCompareResult tag: {}", ctor.tag()),
  }
}

/// Round-trip a BlockCompareDetail.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_detail(
  obj: LeanIxBlockCompareDetail,
) -> LeanIxBlockCompareDetail {
  let ctor = obj.as_ctor();
  let result_ptr = ctor.get(0);
  let lean_sharing_len = ctor.scalar_u64(1, 0);
  let rust_sharing_len = ctor.scalar_u64(1, 8);

  let result_obj = rs_roundtrip_block_compare_result(result_ptr.into());

  let out = LeanCtor::alloc(0, 1, 16);
  out.set(0, result_obj);
  out.set_u64(8, lean_sharing_len);
  out.set_u64(16, rust_sharing_len);
  (*out).into()
}

// =============================================================================
// Full Compilation FFI
// =============================================================================

/// FFI function to run the complete compilation pipeline and return all data.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_full(
  env_consts_ptr: LeanObject,
) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    // Phase 1: Decode Lean environment
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let env_len = rust_env.len();
    let rust_env = Arc::new(rust_env);

    // Phase 2: Build ref graph and compute SCCs
    let ref_graph = build_ref_graph(&rust_env);
    let condensed = compute_sccs(&ref_graph.out_refs);

    // Phase 3: Compile
    let compile_stt = match compile_env(&rust_env) {
      Ok(stt) => stt,
      Err(e) => {
        let msg =
          format!("rs_compile_env_full: Rust compilation failed: {:?}", e);
        return io_error(&msg);
      },
    };

    // Phase 4: Build Lean structures
    let mut cache = LeanBuildCache::with_capacity(env_len);

    let raw_env = build_raw_environment(&mut cache, &rust_env);
    let condensed_obj = build_condensed_blocks(&mut cache, &condensed);

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
      let name_obj = build_name(&mut cache, name);
      let ba = LeanByteArray::from_bytes(bytes);

      // Block: { name: Ix.Name, bytes: ByteArray, sharingLen: UInt64 }
      let block = LeanCtor::alloc(0, 2, 8);
      block.set(0, name_obj);
      block.set(1, ba);
      block.set_u64(2 * 8, *sharing_len as u64);

      blocks_arr.set(i, *block);
    }

    // Build nameToAddr array
    let name_to_addr_len = compile_stt.name_to_addr.len();
    let name_to_addr_arr = LeanArray::alloc(name_to_addr_len);
    for (i, entry) in compile_stt.name_to_addr.iter().enumerate() {
      let name = entry.key();
      let addr = entry.value();

      let name_obj = build_name(&mut cache, name);
      let addr_ba = LeanByteArray::from_bytes(addr.as_bytes());

      let entry_obj = LeanCtor::alloc(0, 2, 0);
      entry_obj.set(0, name_obj);
      entry_obj.set(1, addr_ba);

      name_to_addr_arr.set(i, *entry_obj);
    }

    // Build RawCompiledEnv
    let compiled_obj = LeanCtor::alloc(0, 2, 0);
    compiled_obj.set(0, *blocks_arr);
    compiled_obj.set(1, *name_to_addr_arr);

    // Build RustCompilationResult
    let result = LeanCtor::alloc(0, 3, 0);
    result.set(0, raw_env);
    result.set(1, condensed_obj);
    result.set(2, *compiled_obj);

    io_ok(*result)
  }))
}

/// FFI function to compile a Lean environment to serialized Ixon.Env bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env(env_consts_ptr: LeanObject) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let rust_env = Arc::new(rust_env);

    let compile_stt = match compile_env(&rust_env) {
      Ok(stt) => stt,
      Err(e) => {
        let msg = format!("rs_compile_env: Rust compilation failed: {:?}", e);
        return io_error(&msg);
      },
    };

    // Serialize the compiled Env to bytes
    let mut buf = Vec::new();
    if let Err(e) = compile_stt.env.put(&mut buf) {
      let msg = format!("rs_compile_env: Env serialization failed: {}", e);
      return io_error(&msg);
    }

    // Build Lean ByteArray
    let ba = LeanByteArray::from_bytes(&buf);
    io_ok(ba)
  }))
}

/// Round-trip a RawEnv: decode from Lean, re-encode via builder.
/// This performs a full decode/build cycle to verify FFI correctness.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_raw_env(
  raw_env_obj: LeanIxonRawEnv,
) -> LeanIxonRawEnv {
  let env = decode_raw_env(*raw_env_obj);
  build_raw_env(&env).into()
}

/// FFI function to run all compilation phases and return combined results.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_phases(env_consts_ptr: LeanObject) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let env_len = rust_env.len();
    let rust_env = Arc::new(rust_env);

    let mut cache = LeanBuildCache::with_capacity(env_len);
    let raw_env = build_raw_environment(&mut cache, &rust_env);

    let ref_graph = build_ref_graph(&rust_env);

    let condensed = compute_sccs(&ref_graph.out_refs);

    let condensed_obj = build_condensed_blocks(&mut cache, &condensed);

    let compile_stt = match compile_env(&rust_env) {
      Ok(stt) => stt,
      Err(e) => {
        let msg = format!("rs_compile_phases: compilation failed: {:?}", e);
        return io_error(&msg);
      },
    };

    // Build Lean objects from compile results
    let consts: Vec<_> = compile_stt
      .env
      .consts
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let consts_arr = LeanArray::alloc(consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      consts_arr.set(i, build_raw_const(addr, constant));
    }

    let named: Vec<_> = compile_stt
      .env
      .named
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let named_arr = LeanArray::alloc(named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      named_arr.set(i, build_raw_named(&mut cache, name, &n.addr, &n.meta));
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
      names_arr.set(i, build_raw_name_entry(&mut cache, addr, name));
    }

    let raw_ixon_env = LeanCtor::alloc(0, 5, 0);
    raw_ixon_env.set(0, *consts_arr);
    raw_ixon_env.set(1, *named_arr);
    raw_ixon_env.set(2, *blobs_arr);
    raw_ixon_env.set(3, *comms_arr);
    raw_ixon_env.set(4, *names_arr);

    let result = LeanCtor::alloc(0, 3, 0);
    result.set(0, raw_env);
    result.set(1, condensed_obj);
    result.set(2, *raw_ixon_env);

    io_ok(*result)
  }))
}

/// FFI function to compile a Lean environment to a RawEnv.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_to_ixon(
  env_consts_ptr: LeanObject,
) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let rust_env = Arc::new(rust_env);

    let compile_stt = match compile_env(&rust_env) {
      Ok(stt) => stt,
      Err(e) => {
        let msg =
          format!("rs_compile_env_to_ixon: compilation failed: {:?}", e);
        return io_error(&msg);
      },
    };

    let mut cache = LeanBuildCache::with_capacity(rust_env.len());

    let consts: Vec<_> = compile_stt
      .env
      .consts
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let consts_arr = LeanArray::alloc(consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      consts_arr.set(i, build_raw_const(addr, constant));
    }

    let named: Vec<_> = compile_stt
      .env
      .named
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let named_arr = LeanArray::alloc(named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      named_arr.set(i, build_raw_named(&mut cache, name, &n.addr, &n.meta));
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
      names_arr.set(i, build_raw_name_entry(&mut cache, addr, name));
    }

    let result = LeanCtor::alloc(0, 5, 0);
    result.set(0, *consts_arr);
    result.set(1, *named_arr);
    result.set(2, *blobs_arr);
    result.set(3, *comms_arr);
    result.set(4, *names_arr);
    io_ok(*result)
  }))
}

/// FFI function to canonicalize environment to Ix.RawEnvironment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_canonicalize_env_to_ix(
  env_consts_ptr: LeanObject,
) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let mut cache = LeanBuildCache::with_capacity(rust_env.len());
    let raw_env = build_raw_environment(&mut cache, &rust_env);
    io_ok(raw_env)
  }))
}

// =============================================================================
// RustCompiledEnv - Holds Rust compilation results for comparison
// =============================================================================

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
#[unsafe(no_mangle)]
extern "C" fn rs_test_ffi_roundtrip(name_ptr: LeanObject) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(name_ptr, &global_cache);

  // Return a magic number plus the hash of the name to verify it worked
  let hash = name.get_hash();
  let hash_bytes = hash.as_bytes();
  let hash_prefix =
    u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap_or([0u8; 8]));

  // Magic number 0xDEADBEEF plus hash prefix
  0xDEAD_BEEF_0000_0000 | (hash_prefix & 0x0000_0000_FFFF_FFFF)
}

/// FFI: Compile entire environment with Rust, returning a handle to RustCompiledEnv.
#[unsafe(no_mangle)]
extern "C" fn rs_compile_env_rust_first(
  env_consts_ptr: LeanObject,
) -> *mut RustCompiledEnv {
  // Decode Lean environment
  let lean_env = lean_ptr_to_env(env_consts_ptr);
  let lean_env = Arc::new(lean_env);

  // Compile with Rust
  let rust_stt = match compile_env(&lean_env) {
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
#[unsafe(no_mangle)]
extern "C" fn rs_compare_block(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanObject,
  lean_bytes: LeanByteArray,
) -> u64 {
  if rust_env.is_null() {
    return 2u64 << 32; // not found
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

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
#[unsafe(no_mangle)]
extern "C" fn rs_free_rust_env(rust_env: *mut RustCompiledEnv) {
  if !rust_env.is_null() {
    unsafe {
      drop(Box::from_raw(rust_env));
    }
  }
}

/// FFI: Get the number of blocks in a RustCompiledEnv.
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
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_bytes_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanObject,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes.len() as u64,
    None => 0,
  }
}

/// FFI: Copy Rust's compiled bytes into a pre-allocated Lean ByteArray.
#[unsafe(no_mangle)]
extern "C" fn rs_copy_block_bytes(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanObject,
  dest: LeanByteArray,
) {
  if rust_env.is_null() {
    return;
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  let bytes = match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes,
    None => return,
  };

  // Copy into the Lean ByteArray
  unsafe { dest.set_data(bytes) };
}

/// FFI: Get Rust's sharing vector length for a block.
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_sharing_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanObject,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  match rust_env.blocks.get(&name) {
    Some((_, sharing_len)) => *sharing_len as u64,
    None => 0,
  }
}

// =============================================================================
// Pre-sharing expression extraction FFI
// =============================================================================

/// Frame for iterative unshare traversal.
enum UnshareFrame<'a> {
  Visit(&'a Arc<IxonExpr>),
  BuildApp,
  BuildLam,
  BuildAll,
  BuildLet(bool),
  BuildPrj(u64, u64),
}

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
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanObject,
  out_buf: LeanByteArray,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

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
          crate::ix::ixon::constant::MutConst::Defn(def) => {
            exprs.push(def.typ.clone());
            exprs.push(def.value.clone());
          },
          crate::ix::ixon::constant::MutConst::Indc(ind) => {
            exprs.push(ind.typ.clone());
            for ctor in &ind.ctors {
              exprs.push(ctor.typ.clone());
            }
          },
          crate::ix::ixon::constant::MutConst::Recr(rec) => {
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
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: LeanObject,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

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
          crate::ix::ixon::constant::MutConst::Defn(_) => count += 2,
          crate::ix::ixon::constant::MutConst::Indc(ind) => {
            count += 1 + ind.ctors.len()
          },
          crate::ix::ixon::constant::MutConst::Recr(rec) => {
            count += 1 + rec.rules.len()
          },
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
#[unsafe(no_mangle)]
extern "C" fn rs_lookup_const_addr(
  rust_env: *const RustCompiledEnv,
  name_ptr: LeanObject,
  out_addr: LeanByteArray,
) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(name_ptr, &global_cache);

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

use crate::ix::ixon::error::{CompileError, DecompileError, SerializeError};

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
pub fn build_serialize_error(se: &SerializeError) -> LeanObject {
  match se {
    SerializeError::UnexpectedEof { expected } => {
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, build_lean_string(expected));
      *ctor
    },
    SerializeError::InvalidTag { tag, context } => {
      let ctor = LeanCtor::alloc(1, 1, 1);
      ctor.set(0, build_lean_string(context));
      ctor.set_u8(8, *tag);
      *ctor
    },
    SerializeError::InvalidFlag { flag, context } => {
      let ctor = LeanCtor::alloc(2, 1, 1);
      ctor.set(0, build_lean_string(context));
      ctor.set_u8(8, *flag);
      *ctor
    },
    SerializeError::InvalidVariant { variant, context } => {
      let ctor = LeanCtor::alloc(3, 1, 8);
      ctor.set(0, build_lean_string(context));
      ctor.set_u64(8, *variant);
      *ctor
    },
    SerializeError::InvalidBool { value } => {
      let ctor = LeanCtor::alloc(4, 0, 1);
      ctor.set_u8(0, *value);
      *ctor
    },
    SerializeError::AddressError => LeanObject::box_usize(5),
    SerializeError::InvalidShareIndex { idx, max } => {
      let ctor = LeanCtor::alloc(6, 1, 8);
      ctor.set(0, build_lean_nat_usize(*max));
      ctor.set_u64(8, *idx);
      *ctor
    },
  }
}

/// Decode a Lean Ixon.SerializeError to a Rust SerializeError.
pub fn decode_serialize_error(obj: LeanObject) -> SerializeError {
  // Tag 5 (addressError) has 0 fields → Lean represents as scalar
  if obj.is_scalar() {
    let tag = obj.unbox_usize();
    assert_eq!(tag, 5, "Invalid scalar SerializeError tag: {}", tag);
    return SerializeError::AddressError;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let expected = ctor.get(0).as_string().to_string();
      SerializeError::UnexpectedEof { expected }
    },
    1 => {
      let context = ctor.get(0).as_string().to_string();
      let tag_val = ctor.scalar_u8(1, 0);
      SerializeError::InvalidTag { tag: tag_val, context }
    },
    2 => {
      let context = ctor.get(0).as_string().to_string();
      let flag = ctor.scalar_u8(1, 0);
      SerializeError::InvalidFlag { flag, context }
    },
    3 => {
      let context = ctor.get(0).as_string().to_string();
      let variant = ctor.scalar_u64(1, 0);
      SerializeError::InvalidVariant { variant, context }
    },
    4 => {
      let value = ctor.scalar_u8(0, 0);
      SerializeError::InvalidBool { value }
    },
    5 => SerializeError::AddressError,
    6 => {
      let max = Nat::from_ptr(ctor.get(0).as_ptr())
        .to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(0);
      let idx = ctor.scalar_u64(1, 0);
      SerializeError::InvalidShareIndex { idx, max }
    },
    _ => unreachable!("Invalid SerializeError tag: {}", ctor.tag()),
  }
}

/// Build a Lean DecompileError from a Rust DecompileError.
///
/// Layout for index variants (tags 0–4):
///   `(idx : UInt64) (len/max : Nat) (constant : String)`
///   → 2 object fields (Nat, String) + 8 scalar bytes (UInt64)
///   → `lean_alloc_ctor(tag, 2, 8)`
///   → obj[0] = Nat, obj[1] = String, scalar[0] = UInt64
pub fn build_decompile_error(err: &DecompileError) -> LeanObject {
  match err {
    DecompileError::InvalidRefIndex { idx, refs_len, constant } => {
      let ctor = LeanCtor::alloc(0, 2, 8);
      ctor.set(0, build_lean_nat_usize(*refs_len));
      ctor.set(1, build_lean_string(constant));
      ctor.set_u64(2 * 8, *idx);
      *ctor
    },
    DecompileError::InvalidUnivIndex { idx, univs_len, constant } => {
      let ctor = LeanCtor::alloc(1, 2, 8);
      ctor.set(0, build_lean_nat_usize(*univs_len));
      ctor.set(1, build_lean_string(constant));
      ctor.set_u64(2 * 8, *idx);
      *ctor
    },
    DecompileError::InvalidShareIndex { idx, max, constant } => {
      let ctor = LeanCtor::alloc(2, 2, 8);
      ctor.set(0, build_lean_nat_usize(*max));
      ctor.set(1, build_lean_string(constant));
      ctor.set_u64(2 * 8, *idx);
      *ctor
    },
    DecompileError::InvalidRecIndex { idx, ctx_size, constant } => {
      let ctor = LeanCtor::alloc(3, 2, 8);
      ctor.set(0, build_lean_nat_usize(*ctx_size));
      ctor.set(1, build_lean_string(constant));
      ctor.set_u64(2 * 8, *idx);
      *ctor
    },
    DecompileError::InvalidUnivVarIndex { idx, max, constant } => {
      let ctor = LeanCtor::alloc(4, 2, 8);
      ctor.set(0, build_lean_nat_usize(*max));
      ctor.set(1, build_lean_string(constant));
      ctor.set_u64(2 * 8, *idx);
      *ctor
    },
    DecompileError::MissingAddress(addr) => {
      let ctor = LeanCtor::alloc(5, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    DecompileError::MissingMetadata(addr) => {
      let ctor = LeanCtor::alloc(6, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    DecompileError::BlobNotFound(addr) => {
      let ctor = LeanCtor::alloc(7, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    DecompileError::BadBlobFormat { addr, expected } => {
      let ctor = LeanCtor::alloc(8, 2, 0);
      ctor.set(0, build_address_from_ixon(addr));
      ctor.set(1, build_lean_string(expected));
      *ctor
    },
    DecompileError::BadConstantFormat { msg } => {
      let ctor = LeanCtor::alloc(9, 1, 0);
      ctor.set(0, build_lean_string(msg));
      *ctor
    },
    DecompileError::Serialize(se) => {
      let ctor = LeanCtor::alloc(10, 1, 0);
      ctor.set(0, build_serialize_error(se));
      *ctor
    },
  }
}

/// Decode a Lean DecompileError to a Rust DecompileError.
pub fn decode_decompile_error(obj: LeanObject) -> DecompileError {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let refs_len = Nat::from_ptr(ctor.get(0).as_ptr())
        .to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(0);
      let constant = ctor.get(1).as_string().to_string();
      let idx = ctor.scalar_u64(2, 0);
      DecompileError::InvalidRefIndex { idx, refs_len, constant }
    },
    1 => {
      let univs_len = Nat::from_ptr(ctor.get(0).as_ptr())
        .to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(0);
      let constant = ctor.get(1).as_string().to_string();
      let idx = ctor.scalar_u64(2, 0);
      DecompileError::InvalidUnivIndex { idx, univs_len, constant }
    },
    2 => {
      let max = Nat::from_ptr(ctor.get(0).as_ptr())
        .to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(0);
      let constant = ctor.get(1).as_string().to_string();
      let idx = ctor.scalar_u64(2, 0);
      DecompileError::InvalidShareIndex { idx, max, constant }
    },
    3 => {
      let ctx_size = Nat::from_ptr(ctor.get(0).as_ptr())
        .to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(0);
      let constant = ctor.get(1).as_string().to_string();
      let idx = ctor.scalar_u64(2, 0);
      DecompileError::InvalidRecIndex { idx, ctx_size, constant }
    },
    4 => {
      let max = Nat::from_ptr(ctor.get(0).as_ptr())
        .to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(0);
      let constant = ctor.get(1).as_string().to_string();
      let idx = ctor.scalar_u64(2, 0);
      DecompileError::InvalidUnivVarIndex { idx, max, constant }
    },
    5 => DecompileError::MissingAddress(decode_ixon_address(ctor.get(0))),
    6 => DecompileError::MissingMetadata(decode_ixon_address(ctor.get(0))),
    7 => DecompileError::BlobNotFound(decode_ixon_address(ctor.get(0))),
    8 => {
      let addr = decode_ixon_address(ctor.get(0));
      let expected = ctor.get(1).as_string().to_string();
      DecompileError::BadBlobFormat { addr, expected }
    },
    9 => {
      let msg = ctor.get(0).as_string().to_string();
      DecompileError::BadConstantFormat { msg }
    },
    10 => DecompileError::Serialize(decode_serialize_error(ctor.get(0))),
    _ => unreachable!("Invalid DecompileError tag: {}", ctor.tag()),
  }
}

/// Build a Lean CompileError from a Rust CompileError.
///
/// Tags 0–5:
///   0: missingConstant (name : String) → 1 obj
///   1: missingAddress (addr : Address) → 1 obj
///   2: invalidMutualBlock (reason : String) → 1 obj
///   3: unsupportedExpr (desc : String) → 1 obj
///   4: unknownUnivParam (curr param : String) → 2 obj
///   5: serializeError (msg : String) → 1 obj
pub fn build_compile_error(err: &CompileError) -> LeanObject {
  match err {
    CompileError::MissingConstant { name } => {
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, build_lean_string(name));
      *ctor
    },
    CompileError::MissingAddress(addr) => {
      let ctor = LeanCtor::alloc(1, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    CompileError::InvalidMutualBlock { reason } => {
      let ctor = LeanCtor::alloc(2, 1, 0);
      ctor.set(0, build_lean_string(reason));
      *ctor
    },
    CompileError::UnsupportedExpr { desc } => {
      let ctor = LeanCtor::alloc(3, 1, 0);
      ctor.set(0, build_lean_string(desc));
      *ctor
    },
    CompileError::UnknownUnivParam { curr, param } => {
      let ctor = LeanCtor::alloc(4, 2, 0);
      ctor.set(0, build_lean_string(curr));
      ctor.set(1, build_lean_string(param));
      *ctor
    },
    CompileError::Serialize(se) => {
      let ctor = LeanCtor::alloc(5, 1, 0);
      ctor.set(0, build_serialize_error(se));
      *ctor
    },
  }
}

/// Decode a Lean CompileError to a Rust CompileError.
pub fn decode_compile_error(obj: LeanObject) -> CompileError {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let name = ctor.get(0).as_string().to_string();
      CompileError::MissingConstant { name }
    },
    1 => CompileError::MissingAddress(decode_ixon_address(ctor.get(0))),
    2 => {
      let reason = ctor.get(0).as_string().to_string();
      CompileError::InvalidMutualBlock { reason }
    },
    3 => {
      let desc = ctor.get(0).as_string().to_string();
      CompileError::UnsupportedExpr { desc }
    },
    4 => {
      let curr = ctor.get(0).as_string().to_string();
      let param = ctor.get(1).as_string().to_string();
      CompileError::UnknownUnivParam { curr, param }
    },
    5 => CompileError::Serialize(decode_serialize_error(ctor.get(0))),
    _ => unreachable!("Invalid CompileError tag: {}", ctor.tag()),
  }
}

/// FFI: Round-trip a DecompileError: Lean → Rust → Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_decompile_error(
  obj: LeanIxDecompileError,
) -> LeanIxDecompileError {
  let err = decode_decompile_error(*obj);
  build_decompile_error(&err).into()
}

/// FFI: Round-trip a CompileError: Lean → Rust → Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_compile_error(
  obj: LeanIxCompileError,
) -> LeanIxCompileError {
  let err = decode_compile_error(*obj);
  build_compile_error(&err).into()
}

/// FFI: Round-trip a SerializeError: Lean → Rust → Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_serialize_error(
  obj: LeanIxSerializeError,
) -> LeanIxSerializeError {
  let err = decode_serialize_error(*obj);
  build_serialize_error(&err).into()
}

// =============================================================================
// Decompilation FFI
// =============================================================================

/// FFI: Decompile an Ixon.RawEnv → Except DecompileError (Array (Ix.Name × Ix.ConstantInfo)). Pure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_decompile_env(raw_env_obj: LeanIxonRawEnv) -> LeanObject {
  let decoded = decode_raw_env(*raw_env_obj);
  let env = decoded_to_ixon_env(&decoded);

  // Wrap in CompileState (decompile_env only uses .env)
  let stt = CompileState {
    env,
    name_to_addr: DashMap::new(),
    blocks: DashSet::new(),
    block_stats: DashMap::new(),
  };

  match decompile_env(&stt) {
    Ok(dstt) => {
      let entries: Vec<_> = dstt.env.into_iter().collect();
      let mut cache = LeanBuildCache::with_capacity(entries.len());

      let arr = LeanArray::alloc(entries.len());
      for (i, (name, info)) in entries.iter().enumerate() {
        let name_obj = build_name(&mut cache, name);
        let info_obj = build_constant_info(&mut cache, info);
        let pair = LeanCtor::alloc(0, 2, 0);
        pair.set(0, name_obj);
        pair.set(1, info_obj);
        arr.set(i, *pair);
      }

      LeanExcept::ok(arr).into()
    },
    Err(e) => LeanExcept::error(build_decompile_error(&e)).into(),
  }
}
