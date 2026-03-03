//! Graph and SCC FFI functions.

use std::sync::Arc;

use crate::ix::condense::compute_sccs;
use crate::ix::graph::build_ref_graph;
use crate::ffi::{ffi_io_guard, io_ok};
use crate::lean::object::{LeanArray, LeanCtor, LeanObject};

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::ix::name::build_name;
use crate::ffi::lean_env::lean_ptr_to_env;

/// Build an Array (Ix.Name × Array Ix.Name) from a RefMap.
pub fn build_ref_graph_array(
  cache: &mut LeanBuildCache,
  refs: &crate::ix::graph::RefMap,
) -> LeanObject {
  let arr = LeanArray::alloc(refs.len());
  for (i, (name, ref_set)) in refs.iter().enumerate() {
    let name_obj = build_name(cache, name);

    let refs_arr = LeanArray::alloc(ref_set.len());
    for (j, ref_name) in ref_set.iter().enumerate() {
      let ref_name_obj = build_name(cache, ref_name);
      refs_arr.set(j, ref_name_obj);
    }

    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, name_obj);
    pair.set(1, *refs_arr);
    arr.set(i, *pair);
  }
  *arr
}

/// Build a RustCondensedBlocks structure.
pub fn build_condensed_blocks(
  cache: &mut LeanBuildCache,
  condensed: &crate::ix::condense::CondensedBlocks,
) -> LeanObject {
  // Build lowLinks: Array (Ix.Name × Ix.Name)
  let low_links_arr = LeanArray::alloc(condensed.low_links.len());
  for (i, (name, low_link)) in condensed.low_links.iter().enumerate() {
    let name_obj = build_name(cache, name);
    let low_link_obj = build_name(cache, low_link);
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, name_obj);
    pair.set(1, low_link_obj);
    low_links_arr.set(i, *pair);
  }

  // Build blocks: Array (Ix.Name × Array Ix.Name)
  let blocks_arr = LeanArray::alloc(condensed.blocks.len());
  for (i, (name, block_set)) in condensed.blocks.iter().enumerate() {
    let name_obj = build_name(cache, name);
    let block_names_arr = LeanArray::alloc(block_set.len());
    for (j, block_name) in block_set.iter().enumerate() {
      let block_name_obj = build_name(cache, block_name);
      block_names_arr.set(j, block_name_obj);
    }
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, name_obj);
    pair.set(1, *block_names_arr);
    blocks_arr.set(i, *pair);
  }

  // Build blockRefs: Array (Ix.Name × Array Ix.Name)
  let block_refs_arr = LeanArray::alloc(condensed.block_refs.len());
  for (i, (name, ref_set)) in condensed.block_refs.iter().enumerate() {
    let name_obj = build_name(cache, name);
    let refs_arr = LeanArray::alloc(ref_set.len());
    for (j, ref_name) in ref_set.iter().enumerate() {
      let ref_name_obj = build_name(cache, ref_name);
      refs_arr.set(j, ref_name_obj);
    }
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, name_obj);
    pair.set(1, *refs_arr);
    block_refs_arr.set(i, *pair);
  }

  // Build RustCondensedBlocks structure (3 fields)
  let result = LeanCtor::alloc(0, 3, 0);
  result.set(0, *low_links_arr);
  result.set(1, *blocks_arr);
  result.set(2, *block_refs_arr);
  *result
}

// =============================================================================
// FFI Exports
// =============================================================================

/// FFI function to build a reference graph from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_build_ref_graph(env_consts_ptr: LeanObject) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let rust_env = Arc::new(rust_env);
    let ref_graph = build_ref_graph(&rust_env);
    let mut cache = LeanBuildCache::with_capacity(rust_env.len());
    let result = build_ref_graph_array(&mut cache, &ref_graph.out_refs);
    io_ok(result)
  }))
}

/// FFI function to compute SCCs from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compute_sccs(env_consts_ptr: LeanObject) -> LeanObject {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let rust_env = Arc::new(rust_env);
    let ref_graph = build_ref_graph(&rust_env);
    let condensed = compute_sccs(&ref_graph.out_refs);
    let mut cache = LeanBuildCache::with_capacity(rust_env.len());
    let result = build_condensed_blocks(&mut cache, &condensed);
    io_ok(result)
  }))
}
