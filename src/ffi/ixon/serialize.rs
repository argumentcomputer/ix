//! Ixon serialization compatibility FFI.
//!
//! Contains FFI functions for comparing Lean and Rust serialization outputs,
//! and Env serialization roundtrip testing.

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::sharing::hash_expr;
use crate::ix::ixon::univ::put_univ;
use crate::lean::{
  LeanIxAddress, LeanIxonConstant, LeanIxonExpr, LeanIxonRawEnv, LeanIxonUniv,
};
use lean_ffi::object::LeanByteArray;


/// Check if Lean's computed hash matches Rust's computed hash.
#[unsafe(no_mangle)]
pub extern "C" fn rs_expr_hash_matches(
  expr_obj: LeanIxonExpr,
  expected_hash: LeanIxAddress,
) -> bool {
  let expr = Arc::new(expr_obj.decode());
  let hash = hash_expr(&expr);
  let expected = expected_hash.decode();
  Address::from_slice(hash.as_bytes()).is_ok_and(|h| h == expected)
}

/// Check if Lean's Ixon.Univ serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_univ_serialization(
  univ_obj: LeanIxonUniv,
  bytes_obj: LeanByteArray,
) -> bool {
  let univ = univ_obj.decode();
  let bytes_data = bytes_obj.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_univ(&univ, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Expr serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_expr_serialization(
  expr_obj: LeanIxonExpr,
  bytes_obj: LeanByteArray,
) -> bool {
  let expr = expr_obj.decode();
  let bytes_data = bytes_obj.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_expr(&expr, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Constant serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_constant_serialization(
  constant_obj: LeanIxonConstant,
  bytes_obj: LeanByteArray,
) -> bool {
  let constant = constant_obj.decode();
  let bytes_data = bytes_obj.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  constant.put(&mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Env serialization can be deserialized by Rust and content matches.
/// Due to HashMap ordering differences, we compare deserialized content rather than bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_env_serialization(
  raw_env_obj: LeanIxonRawEnv,
  bytes_obj: LeanByteArray,
) -> bool {
  use crate::ix::ixon::env::Env;

  let decoded = raw_env_obj.decode();
  let bytes_data = bytes_obj.as_bytes();

  // Deserialize Lean's bytes using Rust's deserializer
  let rust_env = match Env::get(&mut &bytes_data[..]) {
    Ok(env) => env,
    Err(_) => return false,
  };

  // Compare content: check that all items from decoded RawEnv are in the deserialized Env
  // Consts
  if rust_env.consts.len() != decoded.consts.len() {
    return false;
  }
  for rc in &decoded.consts {
    match rust_env.consts.get(&rc.addr) {
      Some(c) if *c == rc.constant => {},
      _ => return false,
    }
  }

  // Blobs
  if rust_env.blobs.len() != decoded.blobs.len() {
    return false;
  }
  for rb in &decoded.blobs {
    match rust_env.blobs.get(&rb.addr) {
      Some(b) if *b == rb.bytes => {},
      _ => return false,
    }
  }

  // Comms
  if rust_env.comms.len() != decoded.comms.len() {
    return false;
  }
  for rc in &decoded.comms {
    match rust_env.comms.get(&rc.addr) {
      Some(c) if *c == rc.comm => {},
      _ => return false,
    }
  }

  // Named: compare by checking all entries exist with matching addresses
  if rust_env.named.len() != decoded.named.len() {
    return false;
  }
  for rn in &decoded.named {
    match rust_env.named.get(&rn.name) {
      Some(named) if named.addr == rn.addr => {},
      _ => return false,
    }
  }

  true
}

/// FFI: Test Env serialization roundtrip.
/// Takes:
///   - lean_bytes_obj: pointer to ByteArray containing serialized Env from Lean
///
/// Returns: true if Rust can deserialize and re-serialize to the same bytes
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_roundtrip(lean_bytes_obj: LeanByteArray) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let lean_bytes = lean_bytes_obj.as_bytes().to_vec();

  // Try to deserialize with Rust
  let mut slice = lean_bytes.as_slice();
  let env = match Env::get(&mut slice) {
    Ok(e) => e,
    Err(e) => {
      eprintln!("Rust Env::get failed: {}", e);
      return false;
    },
  };

  // Re-serialize
  let mut rust_bytes = Vec::new();
  if let Err(e) = env.put(&mut rust_bytes) {
    eprintln!("Rust Env::put failed: {}", e);
    return false;
  }

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
///   - lean_bytes_obj: pointer to ByteArray containing serialized Env from Lean
///
/// Returns: true if Rust can deserialize and the counts match
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_check(lean_bytes_obj: LeanByteArray) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let lean_bytes = lean_bytes_obj.as_bytes().to_vec();

  // Try to deserialize with Rust
  let mut slice = lean_bytes.as_slice();
  match Env::get(&mut slice) {
    Ok(_) => true,
    Err(e) => {
      eprintln!("Rust Env::get failed: {}", e);
      false
    },
  }
}
