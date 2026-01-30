//! Ixon sharing analysis FFI.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::sharing::analyze_block;
use crate::lean::array::LeanArrayObject;
use crate::lean::as_ref_unsafe;

use super::serialize::lean_ptr_to_ixon_expr;

/// FFI: Debug sharing analysis - print usage counts for subterms with usage >= 2.
/// This helps diagnose why Lean and Rust make different sharing decisions.
#[unsafe(no_mangle)]
pub extern "C" fn rs_debug_sharing_analysis(exprs_ptr: *const c_void) {
  let exprs_arr: &LeanArrayObject = as_ref_unsafe(exprs_ptr.cast());
  let exprs: Vec<Arc<IxonExpr>> = exprs_arr.to_vec(lean_ptr_to_ixon_expr);

  println!("[Rust] Analyzing {} input expressions", exprs.len());

  let (info_map, _ptr_to_hash) = analyze_block(&exprs, false);
  let topo_order = crate::ix::ixon::sharing::topological_sort(&info_map);
  let effective_sizes =
    crate::ix::ixon::sharing::compute_effective_sizes(&info_map, &topo_order);

  println!("[Rust] Found {} unique subterms", info_map.len());

  // Collect subterms with usage >= 2
  let mut candidates: Vec<_> = info_map
    .iter()
    .filter(|(_, info)| info.usage_count >= 2)
    .filter_map(|(hash, info)| {
      let eff_size = *effective_sizes.get(hash)?;
      Some((hash, info, eff_size))
    })
    .collect();

  // Sort by usage count descending
  candidates.sort_by(|a, b| b.1.usage_count.cmp(&a.1.usage_count));

  println!("[Rust] Subterms with usage >= 2:");
  for (hash, info, eff_size) in candidates {
    let n = info.usage_count;
    let potential = (n as isize - 1) * (eff_size as isize) - (n as isize + eff_size as isize);
    println!(
      "  usage={} eff_size={} potential={} hash={:.8}",
      n, eff_size, potential, hash
    );
    println!("    expr={:?}", info.expr);
  }
}
