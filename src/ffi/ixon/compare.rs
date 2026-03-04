//! Cross-implementation compilation comparison FFI.

use std::collections::HashMap;

use crate::ix::compile::{BlockCache, CompileState, compile_env, compile_expr};
use crate::ix::env::Name;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::mutual::MutCtx;
use crate::lean::{LeanIxBlockCompareDetail, LeanIxBlockCompareResult};
use lean_ffi::object::{LeanByteArray, LeanCtor, LeanList, LeanObject};

use crate::ffi::lean_env::{
  Cache as LeanCache, GlobalCache, decode_expr, decode_name,
};

/// Rust-side compiled environment for block comparison.
pub struct RustBlockEnv {
  pub blocks: HashMap<Name, (Vec<u8>, usize)>, // (serialized bytes, sharing count)
}

/// Compare Lean's compiled expression output with Rust's compilation of the same input.
#[unsafe(no_mangle)]
pub extern "C" fn rs_compare_expr_compilation(
  lean_expr_ptr: LeanObject,
  lean_output: LeanByteArray,
  univ_ctx_size: u64,
) -> bool {
  // Decode Lean.Expr to Rust's representation
  let global_cache = GlobalCache::default();
  let mut cache = LeanCache::new(&global_cache);
  let lean_expr = decode_expr(lean_expr_ptr, &mut cache);

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
  let lean_bytes = lean_output.as_bytes();
  rust_bytes == lean_bytes
}

impl LeanIxBlockCompareResult {
  /// Build a BlockCompareResult Lean object.
  fn build(
    matched: bool,
    not_found: bool,
    lean_size: u64,
    rust_size: u64,
    first_diff_offset: u64,
  ) -> Self {
    let obj = if matched {
      *LeanCtor::alloc(0, 0, 0) // match
    } else if not_found {
      *LeanCtor::alloc(2, 0, 0) // notFound
    } else {
      // mismatch
      let ctor = LeanCtor::alloc(1, 0, 24);
      ctor.set_u64(0, lean_size);
      ctor.set_u64(8, rust_size);
      ctor.set_u64(16, first_diff_offset);
      *ctor
    };
    Self::new(obj)
  }
}

impl LeanIxBlockCompareDetail {
  /// Build a BlockCompareDetail Lean object.
  fn build(
    result: LeanIxBlockCompareResult,
    lean_sharing_len: u64,
    rust_sharing_len: u64,
  ) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, result);
    ctor.set_u64(8, lean_sharing_len);
    ctor.set_u64(8 + 8, rust_sharing_len);
    Self::new(*ctor)
  }
}

/// Compare a single block by lowlink name.
///
/// # Safety
///
/// `rust_env` must be a valid pointer to a `RustBlockEnv`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_compare_block_v2(
  rust_env: *const RustBlockEnv,
  lowlink_name: LeanObject,
  lean_bytes: LeanByteArray,
  lean_sharing_len: u64,
) -> LeanIxBlockCompareDetail {
  let global_cache = GlobalCache::default();
  let name = decode_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };
  let lean_data = lean_bytes.as_bytes();

  // Look up Rust's compiled block
  let (rust_bytes, rust_sharing_len) = match rust_env.blocks.get(&name) {
    Some((bytes, sharing_len)) => (bytes, *sharing_len as u64),
    None => {
      // Block not found in Rust compilation
      let result =
        LeanIxBlockCompareResult::build(false, true, lean_data.len() as u64, 0, 0);
      return LeanIxBlockCompareDetail::build(result, lean_sharing_len, 0);
    },
  };

  // Compare bytes
  if rust_bytes == lean_data {
    // Match
    let result = LeanIxBlockCompareResult::build(
      true,
      false,
      lean_data.len() as u64,
      rust_bytes.len() as u64,
      0,
    );
    return LeanIxBlockCompareDetail::build(
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

  let result = LeanIxBlockCompareResult::build(
    false,
    false,
    lean_data.len() as u64,
    rust_bytes.len() as u64,
    first_diff_offset,
  );
  LeanIxBlockCompareDetail::build(result, lean_sharing_len, rust_sharing_len)
}

/// Free a RustBlockEnv pointer.
///
/// # Safety
///
/// `ptr` must be a valid pointer returned by `rs_build_compiled_env`, or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_free_compiled_env(ptr: *mut RustBlockEnv) {
  if !ptr.is_null() {
    unsafe {
      drop(Box::from_raw(ptr));
    }
  }
}

/// Build a RustBlockEnv from a Lean environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_build_compiled_env(
  env_consts_ptr: LeanList,
) -> *mut RustBlockEnv {
  use crate::ffi::lean_env::decode_env;

  // Decode Lean environment
  let rust_env = decode_env(env_consts_ptr);
  let rust_env = std::sync::Arc::new(rust_env);

  // Compile
  let compile_stt = match compile_env(&rust_env) {
    Ok(stt) => stt,
    Err(_) => {
      // Return empty env on error
      return Box::into_raw(Box::new(RustBlockEnv { blocks: HashMap::new() }));
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

  Box::into_raw(Box::new(RustBlockEnv { blocks }))
}
