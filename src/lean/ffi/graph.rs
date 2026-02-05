//! Graph and SCC FFI functions.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::condense::compute_sccs;
use crate::ix::graph::build_ref_graph;
use crate::lean::{
  lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_ctor_set,
  lean_io_result_mk_ok,
};

use super::builder::LeanBuildCache;
use super::ix::name::build_name;
use super::lean_env::lean_ptr_to_env;

/// Build an Array (Ix.Name × Array Ix.Name) from a RefMap.
pub fn build_ref_graph_array(
  cache: &mut LeanBuildCache,
  refs: &crate::ix::graph::RefMap,
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(refs.len(), refs.len());
    for (i, (name, ref_set)) in refs.iter().enumerate() {
      let name_obj = build_name(cache, name);

      let refs_arr = lean_alloc_array(ref_set.len(), ref_set.len());
      for (j, ref_name) in ref_set.iter().enumerate() {
        let ref_name_obj = build_name(cache, ref_name);
        lean_array_set_core(refs_arr, j, ref_name_obj);
      }

      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, name_obj);
      lean_ctor_set(pair, 1, refs_arr);

      lean_array_set_core(arr, i, pair);
    }
    arr
  }
}

/// Build a RustCondensedBlocks structure.
pub fn build_condensed_blocks(
  cache: &mut LeanBuildCache,
  condensed: &crate::ix::condense::CondensedBlocks,
) -> *mut c_void {
  unsafe {
    // Build lowLinks: Array (Ix.Name × Ix.Name)
    let low_links_arr =
      lean_alloc_array(condensed.low_links.len(), condensed.low_links.len());
    for (i, (name, low_link)) in condensed.low_links.iter().enumerate() {
      let name_obj = build_name(cache, name);
      let low_link_obj = build_name(cache, low_link);
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, name_obj);
      lean_ctor_set(pair, 1, low_link_obj);
      lean_array_set_core(low_links_arr, i, pair);
    }

    // Build blocks: Array (Ix.Name × Array Ix.Name)
    let blocks_arr =
      lean_alloc_array(condensed.blocks.len(), condensed.blocks.len());
    for (i, (name, block_set)) in condensed.blocks.iter().enumerate() {
      let name_obj = build_name(cache, name);
      let block_names_arr = lean_alloc_array(block_set.len(), block_set.len());
      for (j, block_name) in block_set.iter().enumerate() {
        let block_name_obj = build_name(cache, block_name);
        lean_array_set_core(block_names_arr, j, block_name_obj);
      }
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, name_obj);
      lean_ctor_set(pair, 1, block_names_arr);
      lean_array_set_core(blocks_arr, i, pair);
    }

    // Build blockRefs: Array (Ix.Name × Array Ix.Name)
    let block_refs_arr =
      lean_alloc_array(condensed.block_refs.len(), condensed.block_refs.len());
    for (i, (name, ref_set)) in condensed.block_refs.iter().enumerate() {
      let name_obj = build_name(cache, name);
      let refs_arr = lean_alloc_array(ref_set.len(), ref_set.len());
      for (j, ref_name) in ref_set.iter().enumerate() {
        let ref_name_obj = build_name(cache, ref_name);
        lean_array_set_core(refs_arr, j, ref_name_obj);
      }
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, name_obj);
      lean_ctor_set(pair, 1, refs_arr);
      lean_array_set_core(block_refs_arr, i, pair);
    }

    // Build RustCondensedBlocks structure (3 fields)
    let result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, low_links_arr);
    lean_ctor_set(result, 1, blocks_arr);
    lean_ctor_set(result, 2, block_refs_arr);
    result
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// FFI function to build a reference graph from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_build_ref_graph(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);
  let ref_graph = build_ref_graph(&rust_env);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());
  let result = build_ref_graph_array(&mut cache, &ref_graph.out_refs);
  unsafe { lean_io_result_mk_ok(result) }
}

/// FFI function to compute SCCs from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compute_sccs(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);
  let ref_graph = build_ref_graph(&rust_env);
  let condensed = compute_sccs(&ref_graph.out_refs);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());
  let result = build_condensed_blocks(&mut cache, &condensed);
  unsafe { lean_io_result_mk_ok(result) }
}
