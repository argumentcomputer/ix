//! Cross-implementation compilation comparison FFI.

use std::collections::HashMap;
use std::ffi::c_void;

use crate::ix::compile::{BlockCache, CompileState, compile_env, compile_expr};
use crate::ix::env::Name;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::mutual::MutCtx;
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::{lean_alloc_ctor, lean_ctor_set};

use super::super::lean_env::{
  Cache as LeanCache, GlobalCache, lean_ptr_to_expr, lean_ptr_to_name,
};

/// Rust-side compiled environment for block comparison.
pub struct RustCompiledEnv {
  pub blocks: HashMap<Name, (Vec<u8>, usize)>, // (serialized bytes, sharing count)
}

/// Compare Lean's compiled expression output with Rust's compilation of the same input.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compare_expr_compilation(
  lean_expr_ptr: *const c_void,
  lean_output: &LeanSArrayObject,
  univ_ctx_size: u64,
) -> bool {
  // Decode Lean.Expr to Rust's representation
  let global_cache = GlobalCache::default();
  let mut cache = LeanCache::new(&global_cache);
  let lean_expr = lean_ptr_to_expr(lean_expr_ptr, &mut cache);

  // Create universe params for de Bruijn indexing (u0, u1, u2, ...)
  let univ_params: Vec<Name> = (0..univ_ctx_size)
    .map(|i| Name::str(Name::anon(), format!("u{}", i)))
    .collect();
  let mut_ctx = MutCtx::default();

  // Create minimal compile state (no environment needed for simple exprs)
  let compile_stt = CompileState::new_empty();
  let mut block_cache = BlockCache::default();

  // Compile with Rust
  let rust_expr = match compile_expr(
    &lean_expr,
    &univ_params,
    &mut_ctx,
    &mut block_cache,
    &compile_stt,
  ) {
    Ok(expr) => expr,
    Err(_) => return false,
  };

  // Serialize Rust's output
  let mut rust_bytes = Vec::new();
  put_expr(&rust_expr, &mut rust_bytes);

  // Compare byte-for-byte
  let lean_bytes = lean_output.data();
  rust_bytes == lean_bytes
}

/// Build a BlockCompareResult Lean object.
fn build_block_compare_result(
  matched: bool,
  not_found: bool,
  lean_size: u64,
  rust_size: u64,
  first_diff_offset: u64,
) -> *mut c_void {
  unsafe {
    if matched {
      lean_alloc_ctor(0, 0, 0) // match
    } else if not_found {
      lean_alloc_ctor(2, 0, 0) // notFound
    } else {
      // mismatch
      let obj = lean_alloc_ctor(1, 0, 24);
      let base = obj.cast::<u8>();
      *base.add(8).cast::<u64>() = lean_size;
      *base.add(16).cast::<u64>() = rust_size;
      *base.add(24).cast::<u64>() = first_diff_offset;
      obj
    }
  }
}

/// Build a BlockCompareDetail Lean object.
fn build_block_compare_detail(
  result: *mut c_void,
  lean_sharing_len: u64,
  rust_sharing_len: u64,
) -> *mut c_void {
  unsafe {
    let obj = lean_alloc_ctor(0, 1, 16);
    lean_ctor_set(obj, 0, result);
    let base = obj.cast::<u8>();
    *base.add(16).cast::<u64>() = lean_sharing_len;
    *base.add(24).cast::<u64>() = rust_sharing_len;
    obj
  }
}

/// Compare a single block by lowlink name.
///
/// # Safety
///
/// `rust_env` must be a valid pointer to a `RustCompiledEnv`.
/// `lowlink_name` must be a valid Lean object pointer.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_compare_block_v2(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  lean_bytes: &LeanSArrayObject,
  lean_sharing_len: u64,
) -> *mut c_void {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };
  let lean_data = lean_bytes.data();

  // Look up Rust's compiled block
  let (rust_bytes, rust_sharing_len) = match rust_env.blocks.get(&name) {
    Some((bytes, sharing_len)) => (bytes, *sharing_len as u64),
    None => {
      // Block not found in Rust compilation
      let result =
        build_block_compare_result(false, true, lean_data.len() as u64, 0, 0);
      return build_block_compare_detail(result, lean_sharing_len, 0);
    },
  };

  // Compare bytes
  if rust_bytes == lean_data {
    // Match
    let result = build_block_compare_result(
      true,
      false,
      lean_data.len() as u64,
      rust_bytes.len() as u64,
      0,
    );
    return build_block_compare_detail(
      result,
      lean_sharing_len,
      rust_sharing_len,
    );
  }

  // Mismatch: find first differing byte
  let first_diff_offset = rust_bytes
    .iter()
    .zip(lean_data.iter())
    .position(|(a, b)| a != b)
    .map_or_else(
      || {
        // One is a prefix of the other
        rust_bytes.len().min(lean_data.len()) as u64
      },
      |i| i as u64,
    );

  let result = build_block_compare_result(
    false,
    false,
    lean_data.len() as u64,
    rust_bytes.len() as u64,
    first_diff_offset,
  );
  build_block_compare_detail(result, lean_sharing_len, rust_sharing_len)
}

/// Free a RustCompiledEnv pointer.
///
/// # Safety
///
/// `ptr` must be a valid pointer returned by `rs_build_compiled_env`, or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_free_compiled_env(ptr: *mut RustCompiledEnv) {
  if !ptr.is_null() {
    unsafe {
      drop(Box::from_raw(ptr));
    }
  }
}

/// Build a RustCompiledEnv from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_build_compiled_env(
  env_consts_ptr: *const c_void,
) -> *mut RustCompiledEnv {
  use super::super::lean_env::lean_ptr_to_env;

  // Decode Lean environment
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  let rust_env = std::sync::Arc::new(rust_env);

  // Compile
  let compile_stt = match compile_env(&rust_env) {
    Ok(stt) => stt,
    Err(_) => {
      // Return empty env on error
      return Box::into_raw(Box::new(RustCompiledEnv {
        blocks: HashMap::new(),
      }));
    },
  };

  // Collect blocks
  let mut blocks = HashMap::new();
  let mut seen_addrs = std::collections::HashSet::new();

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
      blocks.insert(name, (bytes, sharing_len));
    }
  }

  Box::into_raw(Box::new(RustCompiledEnv { blocks }))
}
