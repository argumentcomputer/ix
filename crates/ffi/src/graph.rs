//! Graph and SCC FFI functions.

use std::sync::Arc;

use crate::lean::LeanIxCondensedBlocks;
use ix_compile::condense::compute_sccs;
use ix_compile::graph::build_ref_graph;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanIOResult, LeanList, LeanOwned, LeanProd,
};

use crate::builder::LeanBuildCache;
use crate::lean::LeanIxName;
use crate::lean_env::decode_env;

/// Build an Array (Ix.Name × Array Ix.Name) from a RefMap.
pub fn build_ref_graph_array(
  cache: &mut LeanBuildCache,
  refs: &ix_compile::graph::RefMap,
) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(refs.len());
  for (i, (name, ref_set)) in refs.iter().enumerate() {
    let name_obj = LeanIxName::build(cache, name);

    let refs_arr = LeanArray::alloc(ref_set.len());
    for (j, ref_name) in ref_set.iter().enumerate() {
      let ref_name_obj = LeanIxName::build(cache, ref_name);
      refs_arr.set(j, ref_name_obj);
    }

    let pair = LeanProd::new(name_obj, refs_arr);
    arr.set(i, pair);
  }
  arr
}

impl LeanIxCondensedBlocks<LeanOwned> {
  /// Build a RustCondensedBlocks structure.
  pub fn build(
    cache: &mut LeanBuildCache,
    condensed: &ix_compile::condense::CondensedBlocks,
  ) -> Self {
    // Build lowLinks: Array (Ix.Name × Ix.Name)
    let low_links_arr = LeanArray::alloc(condensed.low_links.len());
    for (i, (name, low_link)) in condensed.low_links.iter().enumerate() {
      let name_obj = LeanIxName::build(cache, name);
      let low_link_obj = LeanIxName::build(cache, low_link);
      let pair = LeanProd::new(name_obj, low_link_obj);
      low_links_arr.set(i, pair);
    }

    // Build blocks: Array (Ix.Name × Array Ix.Name)
    let blocks_arr = LeanArray::alloc(condensed.blocks.len());
    for (i, (name, block_set)) in condensed.blocks.iter().enumerate() {
      let name_obj = LeanIxName::build(cache, name);
      let block_names_arr = LeanArray::alloc(block_set.len());
      for (j, block_name) in block_set.iter().enumerate() {
        let block_name_obj = LeanIxName::build(cache, block_name);
        block_names_arr.set(j, block_name_obj);
      }
      let pair = LeanProd::new(name_obj, block_names_arr);
      blocks_arr.set(i, pair);
    }

    // Build blockRefs: Array (Ix.Name × Array Ix.Name)
    let block_refs_arr = LeanArray::alloc(condensed.block_refs.len());
    for (i, (name, ref_set)) in condensed.block_refs.iter().enumerate() {
      let name_obj = LeanIxName::build(cache, name);
      let refs_arr = LeanArray::alloc(ref_set.len());
      for (j, ref_name) in ref_set.iter().enumerate() {
        let ref_name_obj = LeanIxName::build(cache, ref_name);
        refs_arr.set(j, ref_name_obj);
      }
      let pair = LeanProd::new(name_obj, refs_arr);
      block_refs_arr.set(i, pair);
    }

    // Build RustCondensedBlocks structure (3 fields)
    let result = LeanIxCondensedBlocks::alloc(0);
    result.set_obj(0, low_links_arr);
    result.set_obj(1, blocks_arr);
    result.set_obj(2, block_refs_arr);
    result
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// FFI function to build a reference graph from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_build_ref_graph(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let rust_env = decode_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);
  let ref_graph = build_ref_graph(&rust_env);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());
  let result = build_ref_graph_array(&mut cache, &ref_graph.out_refs);
  LeanIOResult::ok(result)
}

/// FFI function to compute SCCs from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compute_sccs(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let rust_env = decode_env(env_consts_ptr);
  let rust_env = Arc::new(rust_env);
  let ref_graph = build_ref_graph(&rust_env);
  let condensed = compute_sccs(&ref_graph.out_refs);
  let mut cache = LeanBuildCache::with_capacity(rust_env.len());
  let result = LeanIxCondensedBlocks::build(&mut cache, &condensed);
  LeanIOResult::ok(result)
}

/// Compare `compute_sccs` with the original name-keyed implementation
/// (`compute_sccs_reference`) on the reference graphs of an environment:
/// the compiler's own (`setup_scan`, references to missing names dropped
/// as the compile's grounding filter would), its reverse graph, and
/// `build_ref_graph`'s. Every map and set of the result is compared in
/// iteration order. Returns the empty string when all agree, otherwise a
/// description of the first difference.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_compute_sccs_reference_diff(
  env_consts_ptr: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  use ix_compile::condense::{compute_sccs_reference, condensed_difference};
  use ix_compile::graph::{RefMap, setup_scan};
  use lean_ffi::object::LeanString;

  let rust_env = decode_env(env_consts_ptr);
  let scan = setup_scan(&rust_env);
  let present = |refs: &RefMap| -> RefMap {
    let mut out = RefMap::default();
    for (name, set) in refs {
      let kept =
        set.iter().filter(|r| refs.contains_key(*r)).cloned().collect();
      out.insert(name.clone(), kept);
    }
    out
  };
  let graphs: [(&str, RefMap); 3] = [
    ("setup_scan out_refs", present(&scan.graph.out_refs)),
    ("setup_scan in_refs", scan.graph.in_refs),
    ("build_ref_graph out_refs", present(&build_ref_graph(&rust_env).out_refs)),
  ];
  let mut report = String::new();
  for (what, refs) in &graphs {
    let new = compute_sccs(refs);
    let old = compute_sccs_reference(refs);
    if let Some(diff) = condensed_difference(&old, &new) {
      report = format!("{what} ({} nodes): {diff}", refs.len());
      break;
    }
    if new.blocks.len() < 2 || new.blocks.len() == refs.len() {
      report = format!(
        "{what}: degenerate graph ({} nodes, {} components)",
        refs.len(),
        new.blocks.len()
      );
      break;
    }
  }
  LeanIOResult::ok(LeanString::new(&report))
}
