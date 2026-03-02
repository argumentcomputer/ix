//! Ixon serialization compatibility FFI.
//!
//! Contains FFI functions for comparing Lean and Rust serialization outputs,
//! and Env serialization roundtrip testing.

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::sharing::hash_expr;
use crate::ix::ixon::univ::{Univ as IxonUniv, put_univ};
use crate::lean::obj::{LeanByteArray, LeanCtor, LeanObj};

use super::constant::{decode_ixon_address, decode_ixon_constant};

/// Unbox a Lean UInt64, handling both scalar and boxed representations.
fn lean_ptr_to_u64(obj: LeanObj) -> u64 {
  if obj.is_scalar() {
    obj.unbox_usize() as u64
  } else {
    obj.unbox_u64()
  }
}

/// Decode a Lean `Ixon.Expr` to a Rust `IxonExpr`.
pub fn lean_ptr_to_ixon_expr(obj: LeanObj) -> Arc<IxonExpr> {
  assert!(!obj.is_scalar(), "Ixon.Expr should not be scalar");
  let ctor = unsafe { LeanCtor::from_raw(obj.as_ptr()) };
  match ctor.tag() {
    0 => {
      let idx = ctor.scalar_u64(0, 0);
      Arc::new(IxonExpr::Sort(idx))
    },
    1 => {
      let idx = ctor.scalar_u64(0, 0);
      Arc::new(IxonExpr::Var(idx))
    },
    2 => {
      let ref_idx = ctor.scalar_u64(1, 0);
      let univs_arr =
        unsafe { crate::lean::obj::LeanArray::from_raw(ctor.get(0).as_ptr()) };
      let univs = univs_arr.map(lean_ptr_to_u64);
      Arc::new(IxonExpr::Ref(ref_idx, univs))
    },
    3 => {
      let rec_idx = ctor.scalar_u64(1, 0);
      let univs_arr =
        unsafe { crate::lean::obj::LeanArray::from_raw(ctor.get(0).as_ptr()) };
      let univs = univs_arr.map(lean_ptr_to_u64);
      Arc::new(IxonExpr::Rec(rec_idx, univs))
    },
    4 => {
      let type_idx = ctor.scalar_u64(1, 0);
      let field_idx = ctor.scalar_u64(1, 8);
      let val = lean_ptr_to_ixon_expr(ctor.get(0));
      Arc::new(IxonExpr::Prj(type_idx, field_idx, val))
    },
    5 => {
      let idx = ctor.scalar_u64(0, 0);
      Arc::new(IxonExpr::Str(idx))
    },
    6 => {
      let idx = ctor.scalar_u64(0, 0);
      Arc::new(IxonExpr::Nat(idx))
    },
    7 => {
      let [fun_obj, arg_obj] = ctor.objs::<2>();
      let fun_ = lean_ptr_to_ixon_expr(fun_obj);
      let arg = lean_ptr_to_ixon_expr(arg_obj);
      Arc::new(IxonExpr::App(fun_, arg))
    },
    8 => {
      let [ty_obj, body_obj] = ctor.objs::<2>();
      let ty = lean_ptr_to_ixon_expr(ty_obj);
      let body = lean_ptr_to_ixon_expr(body_obj);
      Arc::new(IxonExpr::Lam(ty, body))
    },
    9 => {
      let [ty_obj, body_obj] = ctor.objs::<2>();
      let ty = lean_ptr_to_ixon_expr(ty_obj);
      let body = lean_ptr_to_ixon_expr(body_obj);
      Arc::new(IxonExpr::All(ty, body))
    },
    10 => {
      let [ty_obj, val_obj, body_obj] = ctor.objs::<3>();
      let non_dep = ctor.scalar_bool(3, 0);
      let ty = lean_ptr_to_ixon_expr(ty_obj);
      let val = lean_ptr_to_ixon_expr(val_obj);
      let body = lean_ptr_to_ixon_expr(body_obj);
      Arc::new(IxonExpr::Let(non_dep, ty, val, body))
    },
    11 => {
      let idx = ctor.scalar_u64(0, 0);
      Arc::new(IxonExpr::Share(idx))
    },
    tag => panic!("Unknown Ixon.Expr tag: {tag}"),
  }
}

/// Check if Lean's computed hash matches Rust's computed hash.
#[unsafe(no_mangle)]
pub extern "C" fn rs_expr_hash_matches(
  expr_obj: LeanObj,
  expected_hash: LeanObj,
) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_obj);
  let hash = hash_expr(&expr);
  let expected = decode_ixon_address(expected_hash);
  Address::from_slice(hash.as_bytes()).is_ok_and(|h| h == expected)
}

/// Decode a Lean `Ixon.Univ` to a Rust `IxonUniv`.
fn lean_ptr_to_ixon_univ(obj: LeanObj) -> Arc<IxonUniv> {
  if obj.is_scalar() {
    return IxonUniv::zero();
  }
  let ctor = unsafe { LeanCtor::from_raw(obj.as_ptr()) };
  match ctor.tag() {
    1 => {
      let [inner] = ctor.objs::<1>();
      IxonUniv::succ(lean_ptr_to_ixon_univ(inner))
    },
    2 => {
      let [a, b] = ctor.objs::<2>();
      IxonUniv::max(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    },
    3 => {
      let [a, b] = ctor.objs::<2>();
      IxonUniv::imax(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    },
    4 => IxonUniv::var(ctor.scalar_u64(0, 0)),
    tag => panic!("Unknown Ixon.Univ tag: {tag}"),
  }
}

/// Check if Lean's Ixon.Univ serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_univ_serialization(
  univ_obj: LeanObj,
  bytes_obj: LeanObj,
) -> bool {
  let univ = lean_ptr_to_ixon_univ(univ_obj);
  let ba = unsafe { LeanByteArray::from_raw(bytes_obj.as_ptr()) };
  let bytes_data = ba.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_univ(&univ, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Expr serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_expr_serialization(
  expr_obj: LeanObj,
  bytes_obj: LeanObj,
) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_obj);
  let ba = unsafe { LeanByteArray::from_raw(bytes_obj.as_ptr()) };
  let bytes_data = ba.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_expr(&expr, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Constant serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_constant_serialization(
  constant_obj: LeanObj,
  bytes_obj: LeanObj,
) -> bool {
  let constant = decode_ixon_constant(constant_obj);
  let ba = unsafe { LeanByteArray::from_raw(bytes_obj.as_ptr()) };
  let bytes_data = ba.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  constant.put(&mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Env serialization can be deserialized by Rust and content matches.
/// Due to HashMap ordering differences, we compare deserialized content rather than bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_env_serialization(
  raw_env_obj: LeanObj,
  bytes_obj: LeanObj,
) -> bool {
  use super::env::decode_raw_env;
  use crate::ix::ixon::env::Env;

  let decoded = decode_raw_env(raw_env_obj);
  let ba = unsafe { LeanByteArray::from_raw(bytes_obj.as_ptr()) };
  let bytes_data = ba.as_bytes();

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
///   - lean_bytes_obj: pointer to ByteArray containing serialized Env from Lean
///
/// Returns: true if Rust can deserialize and re-serialize to the same bytes
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_roundtrip(lean_bytes_obj: LeanObj) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let ba = unsafe { LeanByteArray::from_raw(lean_bytes_obj.as_ptr()) };
  let lean_bytes = ba.as_bytes().to_vec();

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
extern "C" fn rs_env_serde_check(lean_bytes_obj: LeanObj) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let ba = unsafe { LeanByteArray::from_raw(lean_bytes_obj.as_ptr()) };
  let lean_bytes = ba.as_bytes().to_vec();

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
