//! Legacy FFI for incremental block-by-block compilation comparison.
//!
//! This module provides FFI functions for comparing Lean and Rust compilation
//! outputs incrementally, block by block. Used for debugging cross-implementation
//! compatibility.

use std::collections::HashMap;
use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::compile::compile_env;
use crate::ix::env::Name;
use crate::ix::ixon::constant::ConstantInfo;
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::sharing::{analyze_block, build_sharing_vec, decide_sharing};
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::as_ref_unsafe;

use super::ixon::expr::decode_ixon_expr_array;
use super::lean_env::{lean_ptr_to_name, GlobalCache};

// ============================================================================
// Env Serialization FFI
// ============================================================================

/// FFI: Test Env serialization roundtrip.
/// Takes:
/// - lean_bytes_ptr: pointer to ByteArray containing serialized Env from Lean
/// Returns: true if Rust can deserialize and re-serialize to the same bytes
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_roundtrip(lean_bytes_ptr: *const c_void) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let bytes_arr: &LeanSArrayObject = unsafe { as_ref_unsafe(lean_bytes_ptr.cast()) };
  let lean_bytes = bytes_arr.data().to_vec();

  // Try to deserialize with Rust
  let mut slice = lean_bytes.as_slice();
  let env = match Env::get(&mut slice) {
    Ok(e) => e,
    Err(e) => {
      eprintln!("Rust Env::get failed: {}", e);
      return false;
    }
  };

  // Re-serialize
  let mut rust_bytes = Vec::new();
  env.put(&mut rust_bytes);

  // Compare
  if lean_bytes != rust_bytes {
    eprintln!("Env roundtrip mismatch:");
    eprintln!("  Input:  {} bytes", lean_bytes.len());
    eprintln!("  Output: {} bytes", rust_bytes.len());
    if lean_bytes.len() <= 200 {
      eprintln!("  Input bytes:  {:?}", lean_bytes);
    }
    if rust_bytes.len() <= 200 {
      eprintln!("  Output bytes: {:?}", rust_bytes);
    }
    return false;
  }

  true
}

/// FFI: Compare Env serialization between Lean and Rust.
/// Takes:
/// - lean_bytes_ptr: pointer to ByteArray containing serialized Env from Lean
/// Returns: true if Rust can deserialize and the counts match
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_check(lean_bytes_ptr: *const c_void) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let bytes_arr: &LeanSArrayObject = unsafe { as_ref_unsafe(lean_bytes_ptr.cast()) };
  let lean_bytes = bytes_arr.data().to_vec();

  // Try to deserialize with Rust
  let mut slice = lean_bytes.as_slice();
  match Env::get(&mut slice) {
    Ok(_) => true,
    Err(e) => {
      eprintln!("Rust Env::get failed: {}", e);
      false
    }
  }
}

// ============================================================================
// Cross-implementation sharing analysis FFI
// ============================================================================

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

// ============================================================================
// RustCompiledEnv - Holds Rust compilation results for comparison
// ============================================================================

/// Rust-compiled environment holding blocks indexed by low-link name.
/// Each block is stored as serialized bytes for comparison with Lean output.
pub struct RustCompiledEnv {
  /// Map from low-link name to (serialized constant bytes, sharing vector length)
  blocks: HashMap<Name, (Vec<u8>, usize)>,
  /// The full compile state for accessing pre-sharing expressions
  compile_state: crate::ix::compile::CompileState,
}

// ============================================================================
// FFI Functions
// ============================================================================

/// FFI: Simple test to verify FFI round-trip works.
/// Takes a Lean.Name and returns a magic number to verify the call succeeded.
#[unsafe(no_mangle)]
extern "C" fn rs_test_ffi_roundtrip(name_ptr: *const c_void) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(name_ptr, &global_cache);

  // Return a magic number plus the hash of the name to verify it worked
  let hash = name.get_hash();
  let hash_bytes = hash.as_bytes();
  let hash_prefix = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap_or([0u8; 8]));

  // Magic number 0xDEADBEEF plus hash prefix
  0xDEAD_BEEF_0000_0000 | (hash_prefix & 0x0000_0000_FFFF_FFFF)
}

/// FFI: Compile entire environment with Rust, returning a handle to RustCompiledEnv.
/// Takes:
/// - env_consts_ptr: pointer to List (Name × ConstantInfo) from Lean environment
/// Returns: pointer to RustCompiledEnv (or null on failure)
#[unsafe(no_mangle)]
extern "C" fn rs_compile_env_rust_first(env_consts_ptr: *const c_void) -> *mut RustCompiledEnv {
  // Decode Lean environment
  let start_decode = std::time::Instant::now();
  let lean_env = super::lean_env::lean_ptr_to_env(env_consts_ptr);
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
    }
  };
  println!("  [Rust] Compile env: {:.2}s", start_compile.elapsed().as_secs_f32());

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
    }
  };

  // Compare bytes
  if rust_bytes == lean_data {
    // Match: code 1
    return 1u64 << 32;
  }

  // Mismatch: find first differing byte
  let first_diff = rust_bytes
    .iter()
    .zip(lean_data.iter())
    .position(|(a, b)| a != b)
    .map(|i| i as u64)
    .unwrap_or_else(|| {
      // One is a prefix of the other
      rust_bytes.len().min(lean_data.len()) as u64
    });

  // Mismatch: code 0 with first diff offset
  first_diff
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
extern "C" fn rs_get_rust_env_block_count(rust_env: *const RustCompiledEnv) -> u64 {
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

// ============================================================================
// Pre-sharing expression extraction FFI
// ============================================================================

/// Expand Share(idx) references in an expression using the sharing vector.
/// This reconstructs the "pre-sharing" expression from the post-sharing representation.
fn unshare_expr(expr: &Arc<IxonExpr>, sharing: &[Arc<IxonExpr>]) -> Arc<IxonExpr> {
  match expr.as_ref() {
    IxonExpr::Share(idx) => {
      // Recursively unshare the sharing vector entry
      if (*idx as usize) < sharing.len() {
        unshare_expr(&sharing[*idx as usize], sharing)
      } else {
        expr.clone() // Invalid index, keep as-is
      }
    }
    IxonExpr::App(f, a) => {
      Arc::new(IxonExpr::App(unshare_expr(f, sharing), unshare_expr(a, sharing)))
    }
    IxonExpr::Lam(t, b) => {
      Arc::new(IxonExpr::Lam(unshare_expr(t, sharing), unshare_expr(b, sharing)))
    }
    IxonExpr::All(t, b) => {
      Arc::new(IxonExpr::All(unshare_expr(t, sharing), unshare_expr(b, sharing)))
    }
    IxonExpr::Let(nd, t, v, b) => Arc::new(IxonExpr::Let(
      *nd,
      unshare_expr(t, sharing),
      unshare_expr(v, sharing),
      unshare_expr(b, sharing),
    )),
    IxonExpr::Prj(ti, fi, v) => Arc::new(IxonExpr::Prj(*ti, *fi, unshare_expr(v, sharing))),
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
    }
  };

  // Get the constant (note: contains post-sharing expressions)
  let constant = match rust_env.compile_state.env.get_const(&addr) {
    Some(c) => c,
    None => {
      eprintln!("rs_get_pre_sharing_exprs: constant not found at addr");
      return 0;
    }
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
    }
    // Projections don't contain expressions directly
    ConstantInfo::CPrj(_) | ConstantInfo::RPrj(_) | ConstantInfo::IPrj(_) | ConstantInfo::DPrj(_) => {
      vec![]
    }
    ConstantInfo::Muts(muts) => {
      let mut exprs = Vec::new();
      for mc in muts {
        match mc {
          crate::ix::ixon::constant::MutConst::Defn(def) => {
            exprs.push(def.typ.clone());
            exprs.push(def.value.clone());
          }
          crate::ix::ixon::constant::MutConst::Indc(ind) => {
            exprs.push(ind.typ.clone());
            for ctor in &ind.ctors {
              exprs.push(ctor.typ.clone());
            }
          }
          crate::ix::ixon::constant::MutConst::Recr(rec) => {
            exprs.push(rec.typ.clone());
            for rule in &rec.rules {
              exprs.push(rule.rhs.clone());
            }
          }
        }
      }
      exprs
    }
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
    ConstantInfo::CPrj(_) | ConstantInfo::RPrj(_) | ConstantInfo::IPrj(_) | ConstantInfo::DPrj(_) => 0,
    ConstantInfo::Muts(muts) => {
      let mut count = 0;
      for mc in muts {
        match mc {
          crate::ix::ixon::constant::MutConst::Defn(_) => count += 2,
          crate::ix::ixon::constant::MutConst::Indc(ind) => count += 1 + ind.ctors.len(),
          crate::ix::ixon::constant::MutConst::Recr(rec) => count += 1 + rec.rules.len(),
        }
      }
      count
    }
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
    }
    None => 0,
  }
}

/// FFI: Get the total number of compiled constants in RustCompiledEnv.
#[unsafe(no_mangle)]
extern "C" fn rs_get_compiled_const_count(rust_env: *const RustCompiledEnv) -> u64 {
  let rust_env = unsafe { &*rust_env };
  rust_env.compile_state.name_to_addr.len() as u64
}
