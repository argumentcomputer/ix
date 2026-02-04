//! Compilation FFI functions.
//!
//! Contains FFI for rs_compile_env_full, rs_compile_env, rs_compile_phases, etc.

use std::collections::HashMap;
use std::ffi::{CString, c_void};
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
use crate::lean::nat::Nat;
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_alloc_sarray,
  lean_array_set_core, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8,
  lean_ctor_set_uint64, lean_inc, lean_io_result_mk_ok, lean_mk_string,
  lean_obj_tag, lean_sarray_cptr, lean_uint64_to_nat,
};

use dashmap::DashMap;
use dashmap::DashSet;

use super::builder::LeanBuildCache;
use super::graph::build_condensed_blocks;
use super::ix::constant::build_constant_info;
use super::ix::env::build_raw_environment;
use super::ix::name::build_name;
use super::ixon::constant::{
  build_address_from_ixon, build_ixon_constant, decode_ixon_address,
};
use super::ixon::env::{
  build_raw_env, build_raw_name_entry, decode_raw_env, decoded_to_ixon_env,
};
use super::ixon::meta::{build_constant_meta, build_ixon_comm};
use super::lean_env::{GlobalCache, lean_ptr_to_env, lean_ptr_to_name};

// =============================================================================
// Raw* Builder Functions for Compile FFI
// =============================================================================

/// Build RawConst: { addr : Address, const : Ixon.Constant }
pub fn build_raw_const(addr: &Address, constant: &IxonConstant) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(addr);
    let const_obj = build_ixon_constant(constant);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, const_obj);
    obj
  }
}

/// Build RawNamed: { name : Ix.Name, addr : Address, constMeta : Ixon.ConstantMeta }
pub fn build_raw_named(
  cache: &mut LeanBuildCache,
  name: &Name,
  addr: &Address,
  meta: &ConstantMeta,
) -> *mut c_void {
  unsafe {
    let name_obj = build_name(cache, name);
    let addr_obj = build_address_from_ixon(addr);
    let meta_obj = build_constant_meta(meta);
    let obj = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(obj, 0, name_obj);
    lean_ctor_set(obj, 1, addr_obj);
    lean_ctor_set(obj, 2, meta_obj);
    obj
  }
}

/// Build RawBlob: { addr : Address, bytes : ByteArray }
pub fn build_raw_blob(addr: &Address, bytes: &[u8]) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(addr);
    let ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let ba_data = lean_sarray_cptr(ba);
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), ba_data, bytes.len());
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, ba);
    obj
  }
}

/// Build RawComm: { addr : Address, comm : Ixon.Comm }
pub fn build_raw_comm(addr: &Address, comm: &Comm) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(addr);
    let comm_obj = build_ixon_comm(comm);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, comm_obj);
    obj
  }
}

// =============================================================================
// RustCondensedBlocks roundtrip FFI
// =============================================================================

/// Round-trip a RustCondensedBlocks structure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_rust_condensed_blocks(
  ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    let low_links = lean_ctor_get(ptr as *mut _, 0) as *mut c_void;
    let blocks = lean_ctor_get(ptr as *mut _, 1) as *mut c_void;
    let block_refs = lean_ctor_get(ptr as *mut _, 2) as *mut c_void;

    lean_inc(low_links);
    lean_inc(blocks);
    lean_inc(block_refs);

    let result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, low_links);
    lean_ctor_set(result, 1, blocks);
    lean_ctor_set(result, 2, block_refs);
    result
  }
}

/// Round-trip a RustCompilePhases structure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_rust_compile_phases(
  ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    let raw_env = lean_ctor_get(ptr as *mut _, 0) as *mut c_void;
    let condensed = lean_ctor_get(ptr as *mut _, 1) as *mut c_void;
    let compile_env = lean_ctor_get(ptr as *mut _, 2) as *mut c_void;

    lean_inc(raw_env);
    lean_inc(condensed);
    lean_inc(compile_env);

    let result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, raw_env);
    lean_ctor_set(result, 1, condensed);
    lean_ctor_set(result, 2, compile_env);
    result
  }
}

// =============================================================================
// BlockCompareResult and BlockCompareDetail roundtrip FFI
// =============================================================================

/// Round-trip a BlockCompareResult.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_result(
  ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => lean_alloc_ctor(0, 0, 0),
      1 => {
        let base = ptr.cast::<u8>();
        let lean_size = *base.add(8).cast::<u64>();
        let rust_size = *base.add(16).cast::<u64>();
        let first_diff = *base.add(24).cast::<u64>();

        let obj = lean_alloc_ctor(1, 0, 24);
        let out_base = obj.cast::<u8>();
        *out_base.add(8).cast::<u64>() = lean_size;
        *out_base.add(16).cast::<u64>() = rust_size;
        *out_base.add(24).cast::<u64>() = first_diff;
        obj
      },
      2 => lean_alloc_ctor(2, 0, 0),
      _ => panic!("Invalid BlockCompareResult tag: {}", tag),
    }
  }
}

/// Round-trip a BlockCompareDetail.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_detail(
  ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    let result_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr.cast::<u8>();
    let lean_sharing_len = *base.add(16).cast::<u64>();
    let rust_sharing_len = *base.add(24).cast::<u64>();

    let result_obj = rs_roundtrip_block_compare_result(result_ptr);

    let obj = lean_alloc_ctor(0, 1, 16);
    lean_ctor_set(obj, 0, result_obj);
    let out_base = obj.cast::<u8>();
    *out_base.add(16).cast::<u64>() = lean_sharing_len;
    *out_base.add(24).cast::<u64>() = rust_sharing_len;
    obj
  }
}

// =============================================================================
// Full Compilation FFI
// =============================================================================

/// FFI function to run the complete compilation pipeline and return all data.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_full(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  use std::time::Instant;
  let total_start = Instant::now();

  // Phase 1: Decode Lean environment
  let decode_start = Instant::now();
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let env_len = rust_env.len();
  let rust_env = Arc::new(rust_env);
  eprintln!(
    "  [Rust Full] Decode env: {:.2}s ({} constants)",
    decode_start.elapsed().as_secs_f32(),
    env_len
  );

  // Phase 2: Build ref graph and compute SCCs
  let graph_start = Instant::now();
  let ref_graph = build_ref_graph(&rust_env);
  eprintln!(
    "  [Rust Full] Ref graph: {:.2}s",
    graph_start.elapsed().as_secs_f32()
  );

  let scc_start = Instant::now();
  let condensed = compute_sccs(&ref_graph.out_refs);
  eprintln!(
    "  [Rust Full] SCCs: {:.2}s ({} blocks)",
    scc_start.elapsed().as_secs_f32(),
    condensed.blocks.len()
  );

  // Phase 3: Compile
  let compile_start = Instant::now();
  let compile_stt = match compile_env(&rust_env) {
    Ok(stt) => stt,
    Err(e) => {
      eprintln!("Rust compilation failed: {:?}", e);
      unsafe {
        let empty_raw_env = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(empty_raw_env, 0, lean_alloc_array(0, 0));

        let empty_condensed = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(empty_condensed, 0, lean_alloc_array(0, 0));
        lean_ctor_set(empty_condensed, 1, lean_alloc_array(0, 0));
        lean_ctor_set(empty_condensed, 2, lean_alloc_array(0, 0));

        let empty_compiled = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(empty_compiled, 0, lean_alloc_array(0, 0));
        lean_ctor_set(empty_compiled, 1, lean_alloc_array(0, 0));

        let result = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(result, 0, empty_raw_env);
        lean_ctor_set(result, 1, empty_condensed);
        lean_ctor_set(result, 2, empty_compiled);
        return lean_io_result_mk_ok(result);
      }
    },
  };
  eprintln!(
    "  [Rust Full] Compile: {:.2}s",
    compile_start.elapsed().as_secs_f32()
  );

  // Phase 4: Build Lean structures
  let build_start = Instant::now();
  let mut cache = LeanBuildCache::with_capacity(env_len);

  unsafe {
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
    let blocks_arr = lean_alloc_array(blocks_data.len(), blocks_data.len());
    for (i, (name, bytes, sharing_len)) in blocks_data.iter().enumerate() {
      let name_obj = build_name(&mut cache, name);

      let ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
      let ba_data = lean_sarray_cptr(ba);
      std::ptr::copy_nonoverlapping(bytes.as_ptr(), ba_data, bytes.len());

      let block = lean_alloc_ctor(0, 2, 8);
      lean_ctor_set(block, 0, name_obj);
      lean_ctor_set(block, 1, ba);
      let base = block.cast::<u8>();
      *base.add(8 + 16).cast::<u64>() = *sharing_len as u64;

      lean_array_set_core(blocks_arr, i, block);
    }

    // Build nameToAddr array
    let name_to_addr_len = compile_stt.name_to_addr.len();
    let name_to_addr_arr = lean_alloc_array(name_to_addr_len, name_to_addr_len);
    for (i, entry) in compile_stt.name_to_addr.iter().enumerate() {
      let name = entry.key();
      let addr = entry.value();

      let name_obj = build_name(&mut cache, name);

      let addr_bytes = addr.as_bytes();
      let addr_ba = lean_alloc_sarray(1, 32, 32);
      let addr_data = lean_sarray_cptr(addr_ba);
      std::ptr::copy_nonoverlapping(addr_bytes.as_ptr(), addr_data, 32);

      let entry_obj = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(entry_obj, 0, name_obj);
      lean_ctor_set(entry_obj, 1, addr_ba);

      lean_array_set_core(name_to_addr_arr, i, entry_obj);
    }

    // Build RawCompiledEnv
    let compiled_obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(compiled_obj, 0, blocks_arr);
    lean_ctor_set(compiled_obj, 1, name_to_addr_arr);

    // Build RustCompilationResult
    let result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, raw_env);
    lean_ctor_set(result, 1, condensed_obj);
    lean_ctor_set(result, 2, compiled_obj);

    eprintln!(
      "  [Rust Full] Build Lean: {:.2}s",
      build_start.elapsed().as_secs_f32()
    );
    eprintln!(
      "  [Rust Full] Total: {:.2}s",
      total_start.elapsed().as_secs_f32()
    );

    lean_io_result_mk_ok(result)
  }
}

/// FFI function to compile a Lean environment to serialized Ixon.Env bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env(env_consts_ptr: *const c_void) -> *mut c_void {
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);

  let compile_stt = match compile_env(&rust_env) {
    Ok(stt) => stt,
    Err(_) => unsafe {
      let empty_ba = lean_alloc_sarray(1, 0, 0);
      return lean_io_result_mk_ok(empty_ba);
    },
  };

  // Serialize the compiled Env to bytes
  let mut buf = Vec::new();
  compile_stt.env.put(&mut buf);

  // Build Lean ByteArray
  unsafe {
    let ba = lean_alloc_sarray(1, buf.len(), buf.len());
    let ba_data = lean_sarray_cptr(ba);
    std::ptr::copy_nonoverlapping(buf.as_ptr(), ba_data, buf.len());
    lean_io_result_mk_ok(ba)
  }
}

/// Round-trip a RawEnv: decode from Lean, re-encode via builder.
/// This performs a full decode/build cycle to verify FFI correctness.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_raw_env(
  raw_env_ptr: *const c_void,
) -> *mut c_void {
  let env = decode_raw_env(raw_env_ptr);
  build_raw_env(&env)
}

/// FFI function to run all compilation phases and return combined results.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_phases(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
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
      eprintln!("rs_compile_phases: compilation failed: {:?}", e);
      unsafe {
        let empty_consts = lean_alloc_array(0, 0);
        let empty_named = lean_alloc_array(0, 0);
        let empty_blobs = lean_alloc_array(0, 0);
        let empty_comms = lean_alloc_array(0, 0);
        let empty_names = lean_alloc_array(0, 0);
        let raw_ixon_env = lean_alloc_ctor(0, 5, 0);
        lean_ctor_set(raw_ixon_env, 0, empty_consts);
        lean_ctor_set(raw_ixon_env, 1, empty_named);
        lean_ctor_set(raw_ixon_env, 2, empty_blobs);
        lean_ctor_set(raw_ixon_env, 3, empty_comms);
        lean_ctor_set(raw_ixon_env, 4, empty_names);

        let result = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(result, 0, raw_env);
        lean_ctor_set(result, 1, condensed_obj);
        lean_ctor_set(result, 2, raw_ixon_env);
        return lean_io_result_mk_ok(result);
      }
    },
  };
  // Build Lean objects from compile results
  unsafe {
    let consts: Vec<_> = compile_stt
      .env
      .consts
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let consts_arr = lean_alloc_array(consts.len(), consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      let raw_const = build_raw_const(addr, constant);
      lean_array_set_core(consts_arr, i, raw_const);
    }

    let named: Vec<_> = compile_stt
      .env
      .named
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let named_arr = lean_alloc_array(named.len(), named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      let raw_named = build_raw_named(&mut cache, name, &n.addr, &n.meta);
      lean_array_set_core(named_arr, i, raw_named);
    }

    let blobs: Vec<_> = compile_stt
      .env
      .blobs
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let blobs_arr = lean_alloc_array(blobs.len(), blobs.len());
    for (i, (addr, bytes)) in blobs.iter().enumerate() {
      let raw_blob = build_raw_blob(addr, bytes);
      lean_array_set_core(blobs_arr, i, raw_blob);
    }

    let comms: Vec<_> = compile_stt
      .env
      .comms
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let comms_arr = lean_alloc_array(comms.len(), comms.len());
    for (i, (addr, comm)) in comms.iter().enumerate() {
      let raw_comm = build_raw_comm(addr, comm);
      lean_array_set_core(comms_arr, i, raw_comm);
    }

    // Build names array (Address → Ix.Name)
    let names: Vec<_> = compile_stt
      .env
      .names
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let names_arr = lean_alloc_array(names.len(), names.len());
    for (i, (addr, name)) in names.iter().enumerate() {
      let obj = build_raw_name_entry(&mut cache, addr, name);
      lean_array_set_core(names_arr, i, obj);
    }

    let raw_ixon_env = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(raw_ixon_env, 0, consts_arr);
    lean_ctor_set(raw_ixon_env, 1, named_arr);
    lean_ctor_set(raw_ixon_env, 2, blobs_arr);
    lean_ctor_set(raw_ixon_env, 3, comms_arr);
    lean_ctor_set(raw_ixon_env, 4, names_arr);

    let result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, raw_env);
    lean_ctor_set(result, 1, condensed_obj);
    lean_ctor_set(result, 2, raw_ixon_env);

    lean_io_result_mk_ok(result)
  }
}

/// FFI function to compile a Lean environment to a RawEnv.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_to_ixon(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);

  let compile_stt = match compile_env(&rust_env) {
    Ok(stt) => stt,
    Err(e) => {
      eprintln!("rs_compile_env_to_ixon: compilation failed: {:?}", e);
      unsafe {
        let empty_consts = lean_alloc_array(0, 0);
        let empty_named = lean_alloc_array(0, 0);
        let empty_blobs = lean_alloc_array(0, 0);
        let empty_comms = lean_alloc_array(0, 0);
        let empty_names = lean_alloc_array(0, 0);
        let result = lean_alloc_ctor(0, 5, 0);
        lean_ctor_set(result, 0, empty_consts);
        lean_ctor_set(result, 1, empty_named);
        lean_ctor_set(result, 2, empty_blobs);
        lean_ctor_set(result, 3, empty_comms);
        lean_ctor_set(result, 4, empty_names);
        return lean_io_result_mk_ok(result);
      }
    },
  };

  let mut cache = LeanBuildCache::with_capacity(rust_env.len());

  unsafe {
    let consts: Vec<_> = compile_stt
      .env
      .consts
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let consts_arr = lean_alloc_array(consts.len(), consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      let raw_const = build_raw_const(addr, constant);
      lean_array_set_core(consts_arr, i, raw_const);
    }

    let named: Vec<_> = compile_stt
      .env
      .named
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let named_arr = lean_alloc_array(named.len(), named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      let raw_named = build_raw_named(&mut cache, name, &n.addr, &n.meta);
      lean_array_set_core(named_arr, i, raw_named);
    }

    let blobs: Vec<_> = compile_stt
      .env
      .blobs
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let blobs_arr = lean_alloc_array(blobs.len(), blobs.len());
    for (i, (addr, bytes)) in blobs.iter().enumerate() {
      let raw_blob = build_raw_blob(addr, bytes);
      lean_array_set_core(blobs_arr, i, raw_blob);
    }

    let comms: Vec<_> = compile_stt
      .env
      .comms
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let comms_arr = lean_alloc_array(comms.len(), comms.len());
    for (i, (addr, comm)) in comms.iter().enumerate() {
      let raw_comm = build_raw_comm(addr, comm);
      lean_array_set_core(comms_arr, i, raw_comm);
    }

    // Build names array (Address → Ix.Name)
    let names: Vec<_> = compile_stt
      .env
      .names
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    let names_arr = lean_alloc_array(names.len(), names.len());
    for (i, (addr, name)) in names.iter().enumerate() {
      let obj = build_raw_name_entry(&mut cache, addr, name);
      lean_array_set_core(names_arr, i, obj);
    }

    let result = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(result, 0, consts_arr);
    lean_ctor_set(result, 1, named_arr);
    lean_ctor_set(result, 2, blobs_arr);
    lean_ctor_set(result, 3, comms_arr);
    lean_ctor_set(result, 4, names_arr);
    lean_io_result_mk_ok(result)
  }
}

/// FFI function to canonicalize environment to Ix.RawEnvironment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_canonicalize_env_to_ix(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());
  let raw_env = build_raw_environment(&mut cache, &rust_env);
  unsafe { lean_io_result_mk_ok(raw_env) }
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
  compile_state: crate::ix::compile::CompileState,
}

// =============================================================================
// Block-by-block comparison FFI
// =============================================================================

/// FFI: Simple test to verify FFI round-trip works.
/// Takes a Lean.Name and returns a magic number to verify the call succeeded.
#[unsafe(no_mangle)]
extern "C" fn rs_test_ffi_roundtrip(name_ptr: *const c_void) -> u64 {
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
/// Takes:
///   - env_consts_ptr: pointer to List (Name x ConstantInfo) from Lean environment
///
/// Returns: pointer to RustCompiledEnv (or null on failure)
#[unsafe(no_mangle)]
extern "C" fn rs_compile_env_rust_first(
  env_consts_ptr: *const c_void,
) -> *mut RustCompiledEnv {
  // Decode Lean environment
  let start_decode = std::time::Instant::now();
  let lean_env = lean_ptr_to_env(env_consts_ptr);
  let env_len = lean_env.len();
  let lean_env = Arc::new(lean_env);
  println!(
    "  [Rust] Decode env: {:.2}s ({} constants)",
    start_decode.elapsed().as_secs_f32(),
    env_len
  );

  // Compile with Rust
  let start_compile = std::time::Instant::now();
  let rust_stt = match compile_env(&lean_env) {
    Ok(stt) => stt,
    Err(e) => {
      eprintln!("Rust compilation failed: {:?}", e);
      return std::ptr::null_mut();
    },
  };
  println!(
    "  [Rust] Compile env: {:.2}s",
    start_compile.elapsed().as_secs_f32()
  );

  // Build block map: lowlink name -> (serialized bytes, sharing len)
  let start_extract = std::time::Instant::now();
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

  println!(
    "  [Rust] Extract {} blocks: {:.2}s",
    blocks.len(),
    start_extract.elapsed().as_secs_f32()
  );

  // Return boxed RustCompiledEnv with full compile state for pre-sharing access
  Box::into_raw(Box::new(RustCompiledEnv { blocks, compile_state: rust_stt }))
}

/// FFI: Compare a single block and return packed result.
/// Returns a packed u64: high 32 bits = matches (1) or error code (0 = mismatch, 2 = not found)
///                       low 32 bits = first diff offset (if mismatch)
#[unsafe(no_mangle)]
extern "C" fn rs_compare_block(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  lean_bytes: &LeanSArrayObject,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };
  let lean_data = lean_bytes.data();

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
  lowlink_name: *const c_void,
) -> u64 {
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
  lowlink_name: *const c_void,
  dest: *mut c_void,
) {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  let bytes = match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes,
    None => return,
  };

  // Copy into the Lean ByteArray
  let dest_arr: &mut LeanSArrayObject = unsafe { &mut *dest.cast() };
  dest_arr.set_data(bytes);
}

/// FFI: Get Rust's sharing vector length for a block.
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_sharing_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
) -> u64 {
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

/// Expand Share(idx) references in an expression using the sharing vector.
/// This reconstructs the "pre-sharing" expression from the post-sharing representation.
#[allow(clippy::cast_possible_truncation)]
fn unshare_expr(
  expr: &Arc<IxonExpr>,
  sharing: &[Arc<IxonExpr>],
) -> Arc<IxonExpr> {
  match expr.as_ref() {
    IxonExpr::Share(idx) => {
      // Recursively unshare the sharing vector entry
      if (*idx as usize) < sharing.len() {
        unshare_expr(&sharing[*idx as usize], sharing)
      } else {
        expr.clone() // Invalid index, keep as-is
      }
    },
    IxonExpr::App(f, a) => Arc::new(IxonExpr::App(
      unshare_expr(f, sharing),
      unshare_expr(a, sharing),
    )),
    IxonExpr::Lam(t, b) => Arc::new(IxonExpr::Lam(
      unshare_expr(t, sharing),
      unshare_expr(b, sharing),
    )),
    IxonExpr::All(t, b) => Arc::new(IxonExpr::All(
      unshare_expr(t, sharing),
      unshare_expr(b, sharing),
    )),
    IxonExpr::Let(nd, t, v, b) => Arc::new(IxonExpr::Let(
      *nd,
      unshare_expr(t, sharing),
      unshare_expr(v, sharing),
      unshare_expr(b, sharing),
    )),
    IxonExpr::Prj(ti, fi, v) => {
      Arc::new(IxonExpr::Prj(*ti, *fi, unshare_expr(v, sharing)))
    },
    // Leaf nodes - no children to unshare
    _ => expr.clone(),
  }
}

/// FFI: Get the pre-sharing root expressions for a constant.
/// Returns the number of root expressions, and writes serialized expressions to the output buffer.
/// Each expression is serialized without sharing (Share nodes are expanded).
///
/// Output format: [n_exprs:u64, len1:u64, expr1_bytes..., len2:u64, expr2_bytes..., ...]
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  out_buf: *mut c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  let addr = match rust_env.compile_state.name_to_addr.get(&name) {
    Some(a) => a.clone(),
    None => {
      eprintln!("rs_get_pre_sharing_exprs: name not found: {:?}", name);
      return 0;
    },
  };

  // Get the constant (note: contains post-sharing expressions)
  let constant = match rust_env.compile_state.env.get_const(&addr) {
    Some(c) => c,
    None => {
      eprintln!("rs_get_pre_sharing_exprs: constant not found at addr");
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
  let out_arr: &mut LeanSArrayObject = unsafe { &mut *out_buf.cast() };
  out_arr.set_data(&output_bytes);

  n_exprs
}

/// FFI: Get the buffer length needed for pre-sharing expressions.
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
) -> u64 {
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
  name_ptr: *const c_void,
  out_addr: *mut c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(name_ptr, &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  match rust_env.compile_state.name_to_addr.get(&name) {
    Some(addr_ref) => {
      // Copy the 32-byte address into the output ByteArray
      let out_arr: &mut LeanSArrayObject = unsafe { &mut *out_addr.cast() };
      out_arr.set_data(addr_ref.as_bytes());
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
  let rust_env = unsafe { &*rust_env };
  rust_env.compile_state.name_to_addr.len() as u64
}

// =============================================================================
// Error type FFI builders
// =============================================================================

use crate::ix::ixon::error::{CompileError, DecompileError, SerializeError};

/// Build a Lean String from a Rust &str.
fn build_lean_string(s: &str) -> *mut c_void {
  let cstr = CString::new(s)
    .unwrap_or_else(|_| CString::new("(invalid string)").unwrap());
  unsafe { lean_mk_string(cstr.as_ptr()) }
}

/// Build a Lean Nat from a usize.
fn build_lean_nat_usize(n: usize) -> *mut c_void {
  unsafe { lean_uint64_to_nat(n as u64) }
}

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
pub fn build_serialize_error(se: &SerializeError) -> *mut c_void {
  unsafe {
    match se {
      SerializeError::UnexpectedEof { expected } => {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_lean_string(expected));
        obj
      },
      SerializeError::InvalidTag { tag, context } => {
        // 1 obj (String) + 1 scalar byte (UInt8)
        let obj = lean_alloc_ctor(1, 1, 1);
        lean_ctor_set(obj, 0, build_lean_string(context));
        lean_ctor_set_uint8(obj, 1 * 8, *tag);
        obj
      },
      SerializeError::InvalidFlag { flag, context } => {
        let obj = lean_alloc_ctor(2, 1, 1);
        lean_ctor_set(obj, 0, build_lean_string(context));
        lean_ctor_set_uint8(obj, 1 * 8, *flag);
        obj
      },
      SerializeError::InvalidVariant { variant, context } => {
        let obj = lean_alloc_ctor(3, 1, 8);
        lean_ctor_set(obj, 0, build_lean_string(context));
        lean_ctor_set_uint64(obj, 1 * 8, *variant);
        obj
      },
      SerializeError::InvalidBool { value } => {
        let obj = lean_alloc_ctor(4, 0, 1);
        lean_ctor_set_uint8(obj, 0, *value);
        obj
      },
      SerializeError::AddressError => lean_alloc_ctor(5, 0, 0),
      SerializeError::InvalidShareIndex { idx, max } => {
        let obj = lean_alloc_ctor(6, 1, 8);
        lean_ctor_set(obj, 0, build_lean_nat_usize(*max));
        lean_ctor_set_uint64(obj, 1 * 8, *idx);
        obj
      },
    }
  }
}

/// Decode a Lean Ixon.SerializeError to a Rust SerializeError.
pub fn decode_serialize_error(ptr: *const c_void) -> SerializeError {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let expected =
          as_ref_unsafe::<LeanStringObject>(str_ptr.cast()).as_string();
        SerializeError::UnexpectedEof {
          expected: Box::leak(expected.into_boxed_str()),
        }
      },
      1 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let base = ptr.cast::<u8>();
        let tag_val = *base.add(8 + 1 * 8);
        let context =
          as_ref_unsafe::<LeanStringObject>(str_ptr.cast()).as_string();
        SerializeError::InvalidTag {
          tag: tag_val,
          context: Box::leak(context.into_boxed_str()),
        }
      },
      2 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let base = ptr.cast::<u8>();
        let flag = *base.add(8 + 1 * 8);
        let context =
          as_ref_unsafe::<LeanStringObject>(str_ptr.cast()).as_string();
        SerializeError::InvalidFlag {
          flag,
          context: Box::leak(context.into_boxed_str()),
        }
      },
      3 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let base = ptr.cast::<u8>();
        let variant = *base.add(8 + 1 * 8).cast::<u64>();
        let context =
          as_ref_unsafe::<LeanStringObject>(str_ptr.cast()).as_string();
        SerializeError::InvalidVariant {
          variant,
          context: Box::leak(context.into_boxed_str()),
        }
      },
      4 => {
        let base = ptr.cast::<u8>();
        let value = *base.add(8);
        SerializeError::InvalidBool { value }
      },
      5 => SerializeError::AddressError,
      6 => {
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let base = ptr.cast::<u8>();
        let idx = *base.add(8 + 1 * 8).cast::<u64>();
        let max = Nat::from_ptr(nat_ptr).to_u64().unwrap_or(0) as usize;
        SerializeError::InvalidShareIndex { idx, max }
      },
      _ => panic!("Invalid SerializeError tag: {}", tag),
    }
  }
}

/// Build a Lean DecompileError from a Rust DecompileError.
///
/// Layout for index variants (tags 0–4):
///   `(idx : UInt64) (len/max : Nat) (constant : String)`
///   → 2 object fields (Nat, String) + 8 scalar bytes (UInt64)
///   → `lean_alloc_ctor(tag, 2, 8)`
///   → obj[0] = Nat, obj[1] = String, scalar[0] = UInt64
pub fn build_decompile_error(err: &DecompileError) -> *mut c_void {
  unsafe {
    match err {
      DecompileError::InvalidRefIndex { idx, refs_len, constant } => {
        let obj = lean_alloc_ctor(0, 2, 8);
        lean_ctor_set(obj, 0, build_lean_nat_usize(*refs_len));
        lean_ctor_set(obj, 1, build_lean_string(constant));
        lean_ctor_set_uint64(obj, 2 * 8, *idx);
        obj
      },
      DecompileError::InvalidUnivIndex { idx, univs_len, constant } => {
        let obj = lean_alloc_ctor(1, 2, 8);
        lean_ctor_set(obj, 0, build_lean_nat_usize(*univs_len));
        lean_ctor_set(obj, 1, build_lean_string(constant));
        lean_ctor_set_uint64(obj, 2 * 8, *idx);
        obj
      },
      DecompileError::InvalidShareIndex { idx, max, constant } => {
        let obj = lean_alloc_ctor(2, 2, 8);
        lean_ctor_set(obj, 0, build_lean_nat_usize(*max));
        lean_ctor_set(obj, 1, build_lean_string(constant));
        lean_ctor_set_uint64(obj, 2 * 8, *idx);
        obj
      },
      DecompileError::InvalidRecIndex { idx, ctx_size, constant } => {
        let obj = lean_alloc_ctor(3, 2, 8);
        lean_ctor_set(obj, 0, build_lean_nat_usize(*ctx_size));
        lean_ctor_set(obj, 1, build_lean_string(constant));
        lean_ctor_set_uint64(obj, 2 * 8, *idx);
        obj
      },
      DecompileError::InvalidUnivVarIndex { idx, max, constant } => {
        let obj = lean_alloc_ctor(4, 2, 8);
        lean_ctor_set(obj, 0, build_lean_nat_usize(*max));
        lean_ctor_set(obj, 1, build_lean_string(constant));
        lean_ctor_set_uint64(obj, 2 * 8, *idx);
        obj
      },
      DecompileError::MissingAddress(addr) => {
        // tag 5, 1 object (Address = ByteArray)
        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, build_address_from_ixon(addr));
        obj
      },
      DecompileError::MissingMetadata(addr) => {
        // tag 6, 1 object (Address = ByteArray)
        let obj = lean_alloc_ctor(6, 1, 0);
        lean_ctor_set(obj, 0, build_address_from_ixon(addr));
        obj
      },
      DecompileError::BlobNotFound(addr) => {
        // tag 7, 1 object (Address = ByteArray)
        let obj = lean_alloc_ctor(7, 1, 0);
        lean_ctor_set(obj, 0, build_address_from_ixon(addr));
        obj
      },
      DecompileError::BadBlobFormat { addr, expected } => {
        // tag 8, 2 objects (Address, String)
        let obj = lean_alloc_ctor(8, 2, 0);
        lean_ctor_set(obj, 0, build_address_from_ixon(addr));
        lean_ctor_set(obj, 1, build_lean_string(expected));
        obj
      },
      DecompileError::BadConstantFormat { msg } => {
        // tag 9, 1 object (String)
        let obj = lean_alloc_ctor(9, 1, 0);
        lean_ctor_set(obj, 0, build_lean_string(msg));
        obj
      },
      DecompileError::Serialize(se) => {
        // tag 10, 1 object (SerializeError)
        let obj = lean_alloc_ctor(10, 1, 0);
        lean_ctor_set(obj, 0, build_serialize_error(se));
        obj
      },
    }
  }
}

/// Decode a Lean DecompileError to a Rust DecompileError.
pub fn decode_decompile_error(ptr: *const c_void) -> DecompileError {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_ptr = lean_ctor_get(ptr as *mut _, 1);
        let base = ptr.cast::<u8>();
        let idx = *base.add(8 + 2 * 8).cast::<u64>();
        let refs_len = Nat::from_ptr(nat_ptr).to_u64().unwrap_or(0) as usize;
        let constant = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::InvalidRefIndex { idx, refs_len, constant }
      },
      1 => {
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_ptr = lean_ctor_get(ptr as *mut _, 1);
        let base = ptr.cast::<u8>();
        let idx = *base.add(8 + 2 * 8).cast::<u64>();
        let univs_len = Nat::from_ptr(nat_ptr).to_u64().unwrap_or(0) as usize;
        let constant = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::InvalidUnivIndex { idx, univs_len, constant }
      },
      2 => {
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_ptr = lean_ctor_get(ptr as *mut _, 1);
        let base = ptr.cast::<u8>();
        let idx = *base.add(8 + 2 * 8).cast::<u64>();
        let max = Nat::from_ptr(nat_ptr).to_u64().unwrap_or(0) as usize;
        let constant = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::InvalidShareIndex { idx, max, constant }
      },
      3 => {
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_ptr = lean_ctor_get(ptr as *mut _, 1);
        let base = ptr.cast::<u8>();
        let idx = *base.add(8 + 2 * 8).cast::<u64>();
        let ctx_size = Nat::from_ptr(nat_ptr).to_u64().unwrap_or(0) as usize;
        let constant = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::InvalidRecIndex { idx, ctx_size, constant }
      },
      4 => {
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_ptr = lean_ctor_get(ptr as *mut _, 1);
        let base = ptr.cast::<u8>();
        let idx = *base.add(8 + 2 * 8).cast::<u64>();
        let max = Nat::from_ptr(nat_ptr).to_u64().unwrap_or(0) as usize;
        let constant = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::InvalidUnivVarIndex { idx, max, constant }
      },
      5 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        DecompileError::MissingAddress(decode_ixon_address(addr_ptr))
      },
      6 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        DecompileError::MissingMetadata(decode_ixon_address(addr_ptr))
      },
      7 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        DecompileError::BlobNotFound(decode_ixon_address(addr_ptr))
      },
      8 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_ptr = lean_ctor_get(ptr as *mut _, 1);
        let addr = decode_ixon_address(addr_ptr);
        let expected = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::BadBlobFormat { addr, expected }
      },
      9 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let msg = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        DecompileError::BadConstantFormat { msg }
      },
      10 => {
        let se_ptr = lean_ctor_get(ptr as *mut _, 0);
        DecompileError::Serialize(decode_serialize_error(se_ptr))
      },
      _ => panic!("Invalid DecompileError tag: {}", tag),
    }
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
pub fn build_compile_error(err: &CompileError) -> *mut c_void {
  unsafe {
    match err {
      CompileError::MissingConstant { name } => {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_lean_string(name));
        obj
      },
      CompileError::MissingAddress(addr) => {
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, build_address_from_ixon(addr));
        obj
      },
      CompileError::InvalidMutualBlock { reason } => {
        let obj = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(obj, 0, build_lean_string(reason));
        obj
      },
      CompileError::UnsupportedExpr { desc } => {
        let obj = lean_alloc_ctor(3, 1, 0);
        lean_ctor_set(obj, 0, build_lean_string(desc));
        obj
      },
      CompileError::UnknownUnivParam { curr, param } => {
        let obj = lean_alloc_ctor(4, 2, 0);
        lean_ctor_set(obj, 0, build_lean_string(curr));
        lean_ctor_set(obj, 1, build_lean_string(param));
        obj
      },
      CompileError::Serialize(se) => {
        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, build_serialize_error(se));
        obj
      },
    }
  }
}

/// Decode a Lean CompileError to a Rust CompileError.
pub fn decode_compile_error(ptr: *const c_void) -> CompileError {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let name = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        CompileError::MissingConstant { name }
      },
      1 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        CompileError::MissingAddress(decode_ixon_address(addr_ptr))
      },
      2 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let reason = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        CompileError::InvalidMutualBlock { reason }
      },
      3 => {
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let desc = as_ref_unsafe::<LeanStringObject>(str_ptr.cast())
          .as_string()
          .to_string();
        CompileError::UnsupportedExpr { desc }
      },
      4 => {
        let str0 = lean_ctor_get(ptr as *mut _, 0);
        let str1 = lean_ctor_get(ptr as *mut _, 1);
        let curr = as_ref_unsafe::<LeanStringObject>(str0.cast())
          .as_string()
          .to_string();
        let param = as_ref_unsafe::<LeanStringObject>(str1.cast())
          .as_string()
          .to_string();
        CompileError::UnknownUnivParam { curr, param }
      },
      5 => {
        let se_ptr = lean_ctor_get(ptr as *mut _, 0);
        CompileError::Serialize(decode_serialize_error(se_ptr))
      },
      _ => panic!("Invalid CompileError tag: {}", tag),
    }
  }
}

/// FFI: Round-trip a DecompileError: Lean → Rust → Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_decompile_error(
  ptr: *const c_void,
) -> *mut c_void {
  let err = decode_decompile_error(ptr);
  build_decompile_error(&err)
}

/// FFI: Round-trip a CompileError: Lean → Rust → Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_compile_error(
  ptr: *const c_void,
) -> *mut c_void {
  let err = decode_compile_error(ptr);
  build_compile_error(&err)
}

/// FFI: Round-trip a SerializeError: Lean → Rust → Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_serialize_error(
  ptr: *const c_void,
) -> *mut c_void {
  let err = decode_serialize_error(ptr);
  build_serialize_error(&err)
}

// =============================================================================
// Decompilation FFI
// =============================================================================

/// FFI: Decompile an Ixon.RawEnv → Except DecompileError (Array (Ix.Name × Ix.ConstantInfo)). Pure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_decompile_env(raw_env_ptr: *const c_void) -> *mut c_void {
  let decoded = decode_raw_env(raw_env_ptr);
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
      unsafe {
        let arr = lean_alloc_array(entries.len(), entries.len());
        for (i, (name, info)) in entries.iter().enumerate() {
          let name_obj = build_name(&mut cache, name);
          let info_obj = build_constant_info(&mut cache, info);
          let pair = lean_alloc_ctor(0, 2, 0);
          lean_ctor_set(pair, 0, name_obj);
          lean_ctor_set(pair, 1, info_obj);
          lean_array_set_core(arr, i, pair);
        }
        // Except.ok (tag 1)
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, arr);
        obj
      }
    },
    Err(e) => {
      // Except.error (tag 0) — build DecompileError directly
      unsafe {
        let err_obj = build_decompile_error(&e);
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, err_obj);
        obj
      }
    },
  }
}
