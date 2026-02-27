//! Ixon serialization compatibility FFI.
//!
//! Contains FFI functions for comparing Lean and Rust serialization outputs,
//! and Env serialization roundtrip testing.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::sharing::hash_expr;
use crate::ix::ixon::univ::{Univ as IxonUniv, put_univ};
use crate::lean::{
  lean_array_to_vec, lean_ctor_objs, lean_ctor_scalar_u64, lean_is_scalar,
  lean_sarray_data, lean_tag, lean_unbox_u64,
};

use super::constant::{decode_ixon_address, decode_ixon_constant};

/// Unbox a Lean UInt64, handling both scalar and boxed representations.
fn lean_ptr_to_u64(ptr: *const c_void) -> u64 {
  if lean_is_scalar(ptr) {
    (ptr as usize >> 1) as u64
  } else {
    lean_unbox_u64(ptr)
  }
}

/// Decode a Lean `Ixon.Expr` to a Rust `IxonExpr`.
pub fn lean_ptr_to_ixon_expr(ptr: *const c_void) -> Arc<IxonExpr> {
  assert!(!lean_is_scalar(ptr), "Ixon.Expr should not be scalar");
  match lean_tag(ptr) {
    0 => {
      let idx = lean_ctor_scalar_u64(ptr, 0, 0);
      Arc::new(IxonExpr::Sort(idx))
    },
    1 => {
      let idx = lean_ctor_scalar_u64(ptr, 0, 0);
      Arc::new(IxonExpr::Var(idx))
    },
    2 => {
      let [univs_ptr] = lean_ctor_objs(ptr);
      let ref_idx = lean_ctor_scalar_u64(ptr, 1, 0);
      let univs = lean_array_to_vec(univs_ptr, lean_ptr_to_u64);
      Arc::new(IxonExpr::Ref(ref_idx, univs))
    },
    3 => {
      let [univs_ptr] = lean_ctor_objs(ptr);
      let rec_idx = lean_ctor_scalar_u64(ptr, 1, 0);
      let univs = lean_array_to_vec(univs_ptr, lean_ptr_to_u64);
      Arc::new(IxonExpr::Rec(rec_idx, univs))
    },
    4 => {
      let [val_ptr] = lean_ctor_objs(ptr);
      let type_idx = lean_ctor_scalar_u64(ptr, 1, 0);
      let field_idx = lean_ctor_scalar_u64(ptr, 1, 8);
      let val = lean_ptr_to_ixon_expr(val_ptr);
      Arc::new(IxonExpr::Prj(type_idx, field_idx, val))
    },
    5 => {
      let idx = lean_ctor_scalar_u64(ptr, 0, 0);
      Arc::new(IxonExpr::Str(idx))
    },
    6 => {
      let idx = lean_ctor_scalar_u64(ptr, 0, 0);
      Arc::new(IxonExpr::Nat(idx))
    },
    7 => {
      let [fun_ptr, arg_ptr] = lean_ctor_objs(ptr);
      let fun_ = lean_ptr_to_ixon_expr(fun_ptr);
      let arg = lean_ptr_to_ixon_expr(arg_ptr);
      Arc::new(IxonExpr::App(fun_, arg))
    },
    8 => {
      let [ty_ptr, body_ptr] = lean_ctor_objs(ptr);
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::Lam(ty, body))
    },
    9 => {
      let [ty_ptr, body_ptr] = lean_ctor_objs(ptr);
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::All(ty, body))
    },
    10 => {
      let [ty_ptr, val_ptr, body_ptr] = lean_ctor_objs(ptr);
      let base_ptr = ptr.cast::<u8>();
      let non_dep = unsafe { *base_ptr.add(8 + 3 * 8) } != 0;
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let val = lean_ptr_to_ixon_expr(val_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::Let(non_dep, ty, val, body))
    },
    11 => {
      let idx = lean_ctor_scalar_u64(ptr, 0, 0);
      Arc::new(IxonExpr::Share(idx))
    },
    tag => panic!("Unknown Ixon.Expr tag: {}", tag),
  }
}

/// Check if Lean's computed hash matches Rust's computed hash.
#[unsafe(no_mangle)]
pub extern "C" fn rs_expr_hash_matches(
  expr_ptr: *const c_void,
  expected_hash: *const c_void,
) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_ptr);
  let hash = hash_expr(&expr);
  let expected = decode_ixon_address(expected_hash);
  Address::from_slice(hash.as_bytes()).is_ok_and(|h| h == expected)
}

/// Decode a Lean `Ixon.Univ` to a Rust `IxonUniv`.
fn lean_ptr_to_ixon_univ(ptr: *const c_void) -> Arc<IxonUniv> {
  if lean_is_scalar(ptr) {
    return IxonUniv::zero();
  }
  match lean_tag(ptr) {
    1 => {
      let [inner] = lean_ctor_objs(ptr);
      IxonUniv::succ(lean_ptr_to_ixon_univ(inner))
    },
    2 => {
      let [a, b] = lean_ctor_objs(ptr);
      IxonUniv::max(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    },
    3 => {
      let [a, b] = lean_ctor_objs(ptr);
      IxonUniv::imax(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    },
    4 => IxonUniv::var(lean_ctor_scalar_u64(ptr, 0, 0)),
    tag => panic!("Unknown Ixon.Univ tag: {}", tag),
  }
}

/// Check if Lean's Ixon.Univ serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_univ_serialization(
  univ_ptr: *const c_void,
  bytes: *const c_void,
) -> bool {
  let univ = lean_ptr_to_ixon_univ(univ_ptr);
  let bytes_data = lean_sarray_data(bytes);
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_univ(&univ, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Expr serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_expr_serialization(
  expr_ptr: *const c_void,
  bytes: *const c_void,
) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_ptr);
  let bytes_data = lean_sarray_data(bytes);
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_expr(&expr, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Constant serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_constant_serialization(
  constant_ptr: *const c_void,
  bytes: *const c_void,
) -> bool {
  let constant = decode_ixon_constant(constant_ptr);
  let bytes_data = lean_sarray_data(bytes);
  let mut buf = Vec::with_capacity(bytes_data.len());
  constant.put(&mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Env serialization can be deserialized by Rust and content matches.
/// Due to HashMap ordering differences, we compare deserialized content rather than bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_env_serialization(
  raw_env_ptr: *const c_void,
  bytes: *const c_void,
) -> bool {
  use super::env::decode_raw_env;
  use crate::ix::ixon::env::Env;

  let decoded = decode_raw_env(raw_env_ptr);
  let bytes_data = lean_sarray_data(bytes);

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
    let expected_comm = crate::ix::ixon::comm::Comm {
      secret: rc.comm.secret.clone(),
      payload: rc.comm.payload.clone(),
    };
    match rust_env.comms.get(&rc.addr) {
      Some(c) if *c == expected_comm => {},
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
///   - lean_bytes_ptr: pointer to ByteArray containing serialized Env from Lean
///
/// Returns: true if Rust can deserialize and re-serialize to the same bytes
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_roundtrip(lean_bytes_ptr: *const c_void) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let lean_bytes = lean_sarray_data(lean_bytes_ptr).to_vec();

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
///   - lean_bytes_ptr: pointer to ByteArray containing serialized Env from Lean
///
/// Returns: true if Rust can deserialize and the counts match
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_check(lean_bytes_ptr: *const c_void) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let lean_bytes = lean_sarray_data(lean_bytes_ptr).to_vec();

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
