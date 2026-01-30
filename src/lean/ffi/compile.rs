//! Compilation FFI functions.
//!
//! Contains FFI for rs_compile_env_full, rs_compile_env, rs_compile_phases, etc.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::compile::compile_env;
use crate::ix::condense::compute_sccs;
use crate::ix::env::Name;
use crate::ix::graph::build_ref_graph;
use crate::ix::ixon::constant::Constant as IxonConstant;
use crate::ix::ixon::{Comm, ConstantMeta};
use crate::lean::{
  lean_alloc_array, lean_alloc_ctor, lean_alloc_sarray, lean_array_set_core, lean_ctor_get,
  lean_ctor_set, lean_inc, lean_io_result_mk_ok, lean_obj_tag, lean_sarray_cptr,
};

use super::builder::LeanBuildCache;
use super::graph::build_condensed_blocks;
use super::ix::env::build_raw_environment;
use super::ix::name::build_name;
use super::ixon::constant::{build_address_from_ixon, build_ixon_constant};
use super::ixon::env::{build_raw_env, decode_raw_env};
use super::ixon::meta::{build_constant_meta, build_ixon_comm};
use super::lean_env::lean_ptr_to_env;

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
pub fn build_raw_named(cache: &mut LeanBuildCache, name: &Name, addr: &Address, meta: &ConstantMeta) -> *mut c_void {
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
pub extern "C" fn rs_roundtrip_rust_condensed_blocks(ptr: *const c_void) -> *mut c_void {
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
pub extern "C" fn rs_roundtrip_rust_compile_phases(ptr: *const c_void) -> *mut c_void {
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
pub extern "C" fn rs_roundtrip_block_compare_result(ptr: *const c_void) -> *mut c_void {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => lean_alloc_ctor(0, 0, 0),
      1 => {
        let base = ptr as *const u8;
        let lean_size = *(base.add(8) as *const u64);
        let rust_size = *(base.add(16) as *const u64);
        let first_diff = *(base.add(24) as *const u64);

        let obj = lean_alloc_ctor(1, 0, 24);
        let out_base = obj as *mut u8;
        *(out_base.add(8) as *mut u64) = lean_size;
        *(out_base.add(16) as *mut u64) = rust_size;
        *(out_base.add(24) as *mut u64) = first_diff;
        obj
      }
      2 => lean_alloc_ctor(2, 0, 0),
      _ => panic!("Invalid BlockCompareResult tag: {}", tag),
    }
  }
}

/// Round-trip a BlockCompareDetail.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_block_compare_detail(ptr: *const c_void) -> *mut c_void {
  unsafe {
    let result_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let lean_sharing_len = *(base.add(16) as *const u64);
    let rust_sharing_len = *(base.add(24) as *const u64);

    let result_obj = rs_roundtrip_block_compare_result(result_ptr);

    let obj = lean_alloc_ctor(0, 1, 16);
    lean_ctor_set(obj, 0, result_obj);
    let out_base = obj as *mut u8;
    *(out_base.add(16) as *mut u64) = lean_sharing_len;
    *(out_base.add(24) as *mut u64) = rust_sharing_len;
    obj
  }
}

// =============================================================================
// Full Compilation FFI
// =============================================================================

/// FFI function to run the complete compilation pipeline and return all data.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_full(env_consts_ptr: *const c_void) -> *mut c_void {
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
  eprintln!("  [Rust Full] Ref graph: {:.2}s", graph_start.elapsed().as_secs_f32());

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
    }
  };
  eprintln!("  [Rust Full] Compile: {:.2}s", compile_start.elapsed().as_secs_f32());

  // Phase 4: Build Lean structures
  let build_start = Instant::now();
  let mut cache = LeanBuildCache::with_capacity(env_len);

  unsafe {
    let raw_env = build_raw_environment(&mut cache, &rust_env);
    let condensed_obj = build_condensed_blocks(&mut cache, &condensed);

    // Collect blocks
    let mut blocks_data: Vec<(crate::ix::env::Name, Vec<u8>, usize)> = Vec::new();
    let mut seen_addrs: std::collections::HashSet<crate::ix::address::Address> =
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
      let base = block as *mut u8;
      *(base.add(8 + 16) as *mut u64) = *sharing_len as u64;

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

    eprintln!("  [Rust Full] Build Lean: {:.2}s", build_start.elapsed().as_secs_f32());
    eprintln!("  [Rust Full] Total: {:.2}s", total_start.elapsed().as_secs_f32());

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
pub extern "C" fn rs_roundtrip_raw_env(raw_env_ptr: *const c_void) -> *mut c_void {
  let env = decode_raw_env(raw_env_ptr);
  build_raw_env(&env)
}

/// FFI function to run all compilation phases and return combined results.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_phases(env_consts_ptr: *const c_void) -> *mut c_void {
  use std::time::Instant;
  let total_start = Instant::now();

  let decode_start = Instant::now();
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let env_len = rust_env.len();
  let rust_env = Arc::new(rust_env);
  eprintln!(
    "  [rs_compile_phases] Decode: {:.2}s ({} constants)",
    decode_start.elapsed().as_secs_f32(),
    env_len
  );

  let raw_env_start = Instant::now();
  let mut cache = LeanBuildCache::with_capacity(env_len);
  let raw_env = build_raw_environment(&mut cache, &rust_env);
  eprintln!("  [rs_compile_phases] RawEnvironment: {:.2}s", raw_env_start.elapsed().as_secs_f32());

  let graph_start = Instant::now();
  let ref_graph = build_ref_graph(&rust_env);
  eprintln!("  [rs_compile_phases] Ref graph: {:.2}s", graph_start.elapsed().as_secs_f32());

  let scc_start = Instant::now();
  let condensed = compute_sccs(&ref_graph.out_refs);
  eprintln!(
    "  [rs_compile_phases] SCCs: {:.2}s ({} blocks)",
    scc_start.elapsed().as_secs_f32(),
    condensed.blocks.len()
  );

  let condensed_obj = build_condensed_blocks(&mut cache, &condensed);

  let compile_start = Instant::now();
  let compile_stt = match compile_env(&rust_env) {
    Ok(stt) => stt,
    Err(e) => {
      eprintln!("rs_compile_phases: compilation failed: {:?}", e);
      unsafe {
        let empty_consts = lean_alloc_array(0, 0);
        let empty_named = lean_alloc_array(0, 0);
        let empty_blobs = lean_alloc_array(0, 0);
        let empty_comms = lean_alloc_array(0, 0);
        let raw_ixon_env = lean_alloc_ctor(0, 4, 0);
        lean_ctor_set(raw_ixon_env, 0, empty_consts);
        lean_ctor_set(raw_ixon_env, 1, empty_named);
        lean_ctor_set(raw_ixon_env, 2, empty_blobs);
        lean_ctor_set(raw_ixon_env, 3, empty_comms);

        let result = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(result, 0, raw_env);
        lean_ctor_set(result, 1, condensed_obj);
        lean_ctor_set(result, 2, raw_ixon_env);
        return lean_io_result_mk_ok(result);
      }
    }
  };
  eprintln!("  [rs_compile_phases] Compile: {:.2}s", compile_start.elapsed().as_secs_f32());

  let build_raw_start = Instant::now();
  unsafe {
    let consts: Vec<_> =
      compile_stt.env.consts.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let consts_arr = lean_alloc_array(consts.len(), consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      let raw_const = build_raw_const(addr, constant);
      lean_array_set_core(consts_arr, i, raw_const);
    }

    let named: Vec<_> =
      compile_stt.env.named.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let named_arr = lean_alloc_array(named.len(), named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      let raw_named = build_raw_named(&mut cache, name, &n.addr, &n.meta);
      lean_array_set_core(named_arr, i, raw_named);
    }

    let blobs: Vec<_> =
      compile_stt.env.blobs.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let blobs_arr = lean_alloc_array(blobs.len(), blobs.len());
    for (i, (addr, bytes)) in blobs.iter().enumerate() {
      let raw_blob = build_raw_blob(addr, bytes);
      lean_array_set_core(blobs_arr, i, raw_blob);
    }

    let comms: Vec<_> =
      compile_stt.env.comms.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let comms_arr = lean_alloc_array(comms.len(), comms.len());
    for (i, (addr, comm)) in comms.iter().enumerate() {
      let raw_comm = build_raw_comm(addr, comm);
      lean_array_set_core(comms_arr, i, raw_comm);
    }

    let raw_ixon_env = lean_alloc_ctor(0, 4, 0);
    lean_ctor_set(raw_ixon_env, 0, consts_arr);
    lean_ctor_set(raw_ixon_env, 1, named_arr);
    lean_ctor_set(raw_ixon_env, 2, blobs_arr);
    lean_ctor_set(raw_ixon_env, 3, comms_arr);

    eprintln!(
      "  [rs_compile_phases] Build RawEnv: {:.2}s",
      build_raw_start.elapsed().as_secs_f32()
    );

    let result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, raw_env);
    lean_ctor_set(result, 1, condensed_obj);
    lean_ctor_set(result, 2, raw_ixon_env);

    eprintln!("  [rs_compile_phases] Total: {:.2}s", total_start.elapsed().as_secs_f32());

    lean_io_result_mk_ok(result)
  }
}

/// FFI function to compile a Lean environment to a RawEnv.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compile_env_to_ixon(env_consts_ptr: *const c_void) -> *mut c_void {
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
        let result = lean_alloc_ctor(0, 4, 0);
        lean_ctor_set(result, 0, empty_consts);
        lean_ctor_set(result, 1, empty_named);
        lean_ctor_set(result, 2, empty_blobs);
        lean_ctor_set(result, 3, empty_comms);
        return lean_io_result_mk_ok(result);
      }
    }
  };

  let mut cache = LeanBuildCache::with_capacity(rust_env.len());

  unsafe {
    let consts: Vec<_> =
      compile_stt.env.consts.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let consts_arr = lean_alloc_array(consts.len(), consts.len());
    for (i, (addr, constant)) in consts.iter().enumerate() {
      let raw_const = build_raw_const(addr, constant);
      lean_array_set_core(consts_arr, i, raw_const);
    }

    let named: Vec<_> =
      compile_stt.env.named.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let named_arr = lean_alloc_array(named.len(), named.len());
    for (i, (name, n)) in named.iter().enumerate() {
      let raw_named = build_raw_named(&mut cache, name, &n.addr, &n.meta);
      lean_array_set_core(named_arr, i, raw_named);
    }

    let blobs: Vec<_> =
      compile_stt.env.blobs.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let blobs_arr = lean_alloc_array(blobs.len(), blobs.len());
    for (i, (addr, bytes)) in blobs.iter().enumerate() {
      let raw_blob = build_raw_blob(addr, bytes);
      lean_array_set_core(blobs_arr, i, raw_blob);
    }

    let comms: Vec<_> =
      compile_stt.env.comms.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let comms_arr = lean_alloc_array(comms.len(), comms.len());
    for (i, (addr, comm)) in comms.iter().enumerate() {
      let raw_comm = build_raw_comm(addr, comm);
      lean_array_set_core(comms_arr, i, raw_comm);
    }

    let result = lean_alloc_ctor(0, 4, 0);
    lean_ctor_set(result, 0, consts_arr);
    lean_ctor_set(result, 1, named_arr);
    lean_ctor_set(result, 2, blobs_arr);
    lean_ctor_set(result, 3, comms_arr);
    lean_io_result_mk_ok(result)
  }
}

/// FFI function to canonicalize environment to Ix.RawEnvironment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_canonicalize_env_to_ix(env_consts_ptr: *const c_void) -> *mut c_void {
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());
  let raw_env = build_raw_environment(&mut cache, &rust_env);
  unsafe { lean_io_result_mk_ok(raw_env) }
}
