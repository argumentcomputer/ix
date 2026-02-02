//! Ixon sharing analysis FFI.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::sharing::{analyze_block, build_sharing_vec, decide_sharing};
use crate::lean::array::LeanArrayObject;
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::as_ref_unsafe;

use super::expr::decode_ixon_expr_array;
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
    let potential = (n.cast_signed() - 1) * eff_size.cast_signed() - (n.cast_signed() + eff_size.cast_signed());
    println!(
      "  usage={} eff_size={} potential={} hash={:.8}",
      n, eff_size, potential, hash
    );
    println!("    expr={:?}", info.expr);
  }
}

/// FFI: Run Rust's sharing analysis on Lean-provided Ixon.Expr array.
/// Returns the number of shared items Rust would produce.
#[unsafe(no_mangle)]
extern "C" fn rs_analyze_sharing_count(exprs_ptr: *const c_void) -> u64 {
  let exprs = decode_ixon_expr_array(exprs_ptr);

  let (info_map, _ptr_to_hash) = analyze_block(&exprs, false);
  let shared_hashes = decide_sharing(&info_map);

  shared_hashes.len() as u64
}

/// FFI: Run Rust's full sharing pipeline on Lean-provided Ixon.Expr array.
/// Writes the sharing vector and rewritten exprs to output arrays.
/// Returns number of shared items.
#[unsafe(no_mangle)]
extern "C" fn rs_run_sharing_analysis(
  exprs_ptr: *const c_void,
  out_sharing_vec: *mut c_void,
  out_rewritten: *mut c_void,
) -> u64 {
  let exprs = decode_ixon_expr_array(exprs_ptr);

  let (info_map, ptr_to_hash) = analyze_block(&exprs, false);
  let shared_hashes = decide_sharing(&info_map);
  let (rewritten_exprs, sharing_vec) =
    build_sharing_vec(&exprs, &shared_hashes, &ptr_to_hash, &info_map);

  // Serialize sharing vector to bytes
  let mut sharing_bytes: Vec<u8> = Vec::new();
  for expr in &sharing_vec {
    put_expr(expr, &mut sharing_bytes);
  }

  // Serialize rewritten exprs to bytes
  let mut rewritten_bytes: Vec<u8> = Vec::new();
  for expr in &rewritten_exprs {
    put_expr(expr, &mut rewritten_bytes);
  }

  // Write to output arrays
  let sharing_out: &mut LeanSArrayObject = unsafe { &mut *out_sharing_vec.cast() };
  sharing_out.set_data(&sharing_bytes);

  let rewritten_out: &mut LeanSArrayObject = unsafe { &mut *out_rewritten.cast() };
  rewritten_out.set_data(&rewritten_bytes);

  shared_hashes.len() as u64
}

/// FFI: Compare Lean's sharing analysis with Rust's on the same input.
/// Takes: exprs (Array Expr), lean_sharing (Array Expr), lean_rewritten (Array Expr)
/// Returns packed u64:
///   - bits 0-31: 1 if sharing vectors match, 0 otherwise
///   - bits 32-47: Lean sharing count
///   - bits 48-63: Rust sharing count
#[unsafe(no_mangle)]
extern "C" fn rs_compare_sharing_analysis(
  exprs_ptr: *const c_void,
  lean_sharing_ptr: *const c_void,
  _lean_rewritten_ptr: *const c_void,
) -> u64 {
  // Decode input expressions
  let exprs = decode_ixon_expr_array(exprs_ptr);

  // Decode Lean's sharing vector
  let lean_sharing = decode_ixon_expr_array(lean_sharing_ptr);

  // Run Rust's sharing analysis
  let (info_map, ptr_to_hash) = analyze_block(&exprs, false);
  let shared_hashes = decide_sharing(&info_map);
  let (_rewritten_exprs, rust_sharing) =
    build_sharing_vec(&exprs, &shared_hashes, &ptr_to_hash, &info_map);

  // Compare sharing vectors
  let lean_count = lean_sharing.len() as u64;
  let rust_count = rust_sharing.len() as u64;

  // Serialize both to bytes for comparison
  let mut lean_bytes: Vec<u8> = Vec::new();
  for expr in &lean_sharing {
    put_expr(expr, &mut lean_bytes);
  }

  let mut rust_bytes: Vec<u8> = Vec::new();
  for expr in &rust_sharing {
    put_expr(expr, &mut rust_bytes);
  }

  let matches = if lean_bytes == rust_bytes { 1u64 } else { 0u64 };

  // Pack result: matches | (lean_count << 32) | (rust_count << 48)
  matches | (lean_count << 32) | (rust_count << 48)
}
