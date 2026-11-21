//! Ixon serialization compatibility FFI.
//!
//! Contains FFI functions for comparing Lean and Rust serialization outputs.

use crate::lean::{
  LeanIxonConstant, LeanIxonExpr, LeanIxonRawEnv, LeanIxonUniv,
};
use ix_common::address::Address;
use ixon::serialize::put_expr;
use ixon::univ::put_univ;
use lean_ffi::object::{LeanBorrowed, LeanByteArray};

/// Check if Lean's Ixon.Univ serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_univ_serialization(
  univ_obj: LeanIxonUniv<LeanBorrowed<'_>>,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
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
  expr_obj: LeanIxonExpr<LeanBorrowed<'_>>,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
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
  constant_obj: LeanIxonConstant<LeanBorrowed<'_>>,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> bool {
  let constant = constant_obj.decode();
  let bytes_data = bytes_obj.as_bytes();
  let mut buf = Vec::with_capacity(bytes_data.len());
  constant.put(&mut buf);
  buf == bytes_data
}

/// Whether Rust reads `bytes` as one canonical record
/// (`Constant::get_canonical`): the codec reads them whole, the record
/// re-encodes to the same bytes, its level count and binder data are in
/// canonical form, and no theorem asserts anything, as Lean's
/// `Ixon.Canonical.deConstant` requires.
#[unsafe(no_mangle)]
pub extern "C" fn rs_constant_canonical(
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> bool {
  ixon::constant::Constant::get_canonical(bytes_obj.as_bytes()).is_ok()
}

/// Check if Lean's Ixon.Env serialization can be deserialized by Rust and content matches.
/// Due to HashMap ordering differences, we compare deserialized content rather than bytes.
///
/// On mismatch, emits a diagnostic line to stderr (gated on
/// `IX_DEBUG_SERDE=1`) identifying the section that differs. This is
/// invaluable for property-test counter-examples where "false does not
/// hold" is otherwise opaque.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_env_serialization(
  raw_env_obj: LeanIxonRawEnv<LeanBorrowed<'_>>,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> bool {
  use ixon::env::Env;

  let debug = std::env::var("IX_DEBUG_SERDE").is_ok();
  let decoded = raw_env_obj.decode();
  let bytes_data = bytes_obj.as_bytes();

  // Deserialize Lean's bytes using Rust's deserializer
  let rust_env = match Env::get(&mut &bytes_data[..]) {
    Ok(env) => env,
    Err(e) => {
      if debug {
        eprintln!("[rs_eq_env_serialization] Env::get failed: {e}");
      }
      return false;
    },
  };

  // Compare content: check that all items from decoded RawEnv are in the deserialized Env
  if rust_env.role_binding != decoded.role_binding {
    if debug {
      eprintln!("[rs_eq_env_serialization] role binding mismatch");
    }
    return false;
  }
  // Consts
  if rust_env.consts.len() != decoded.consts.len() {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] consts len mismatch: rust={}, decoded={}",
        rust_env.consts.len(),
        decoded.consts.len()
      );
    }
    return false;
  }
  for rc in &decoded.consts {
    // Materialize the lazy entry to compare structured `Constant` values.
    let stored = rust_env.get_const(&rc.addr);
    match stored {
      Some(c) if *c == rc.constant => {},
      Some(_) => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] const value mismatch for addr {}",
            rc.addr.hex(),
          );
        }
        return false;
      },
      None => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] const missing for addr {}",
            rc.addr.hex(),
          );
        }
        return false;
      },
    }
  }

  // Blobs
  if rust_env.blobs.len() != decoded.blobs.len() {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] blobs len mismatch: rust={}, decoded={}",
        rust_env.blobs.len(),
        decoded.blobs.len()
      );
    }
    return false;
  }
  for rb in &decoded.blobs {
    match rust_env.blobs.get(&rb.addr) {
      Some(b) if *b == rb.bytes => {},
      Some(b) => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] blob bytes mismatch for addr {}: \
             rust_len={}, decoded_len={}",
            rb.addr.hex(),
            b.len(),
            rb.bytes.len(),
          );
        }
        return false;
      },
      None => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] blob missing for addr {}",
            rb.addr.hex(),
          );
        }
        return false;
      },
    }
  }

  // Comms
  if rust_env.comms.len() != decoded.comms.len() {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] comms len mismatch: rust={}, decoded={}",
        rust_env.comms.len(),
        decoded.comms.len()
      );
    }
    return false;
  }
  for rc in &decoded.comms {
    match rust_env.comms.get(&rc.addr) {
      Some(c) if *c == rc.comm => {},
      _ => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] comm mismatch for addr {}",
            rc.addr.hex(),
          );
        }
        return false;
      },
    }
  }

  // Named: compare by checking all entries exist with matching addresses
  if rust_env.named.len() != decoded.named.len() {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] named len mismatch: rust={}, decoded={}",
        rust_env.named.len(),
        decoded.named.len()
      );
    }
    return false;
  }
  for rn in &decoded.named {
    match rust_env.named.get(&rn.name) {
      Some(named) if named.addr == rn.addr => {},
      Some(named) => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] named addr mismatch for name hash {}: \
             rust={}, decoded={}",
            Address::from_blake3_hash(*rn.name.get_hash()).hex(),
            named.addr.hex(),
            rn.addr.hex(),
          );
        }
        return false;
      },
      None => {
        if debug {
          eprintln!(
            "[rs_eq_env_serialization] named missing for name hash {}",
            Address::from_blake3_hash(*rn.name.get_hash()).hex(),
          );
        }
        return false;
      },
    }
  }

  // Bundle header fields.
  if rust_env.main != decoded.main {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] main mismatch: rust={:?}, decoded={:?}",
        rust_env.main.as_ref().map(Address::hex),
        decoded.main.as_ref().map(Address::hex),
      );
    }
    return false;
  }
  let decoded_assumptions: rustc_hash::FxHashSet<Address> =
    decoded.assumptions.iter().cloned().collect();
  if rust_env.assumptions != decoded_assumptions {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] assumptions mismatch: rust={}, decoded={}",
        rust_env.assumptions.len(),
        decoded_assumptions.len(),
      );
    }
    return false;
  }

  // Hints: `anon_hints` is the single home for hints (the writers
  // serialize the map directly), so the parsed env's map must equal
  // the decoded RawEnv's hints verbatim.
  let expected_hints: rustc_hash::FxHashMap<
    Address,
    ix_common::env::ReducibilityHints,
  > = decoded.anon_hints.iter().cloned().collect();
  let hints_match = rust_env.anon_hints.len() == expected_hints.len()
    && expected_hints
      .iter()
      .all(|(a, h)| rust_env.anon_hints.get(a).map(|r| *r) == Some(*h));
  if !hints_match {
    if debug {
      eprintln!(
        "[rs_eq_env_serialization] anon_hints mismatch: rust={}, expected={}",
        rust_env.anon_hints.len(),
        expected_hints.len(),
      );
    }
    return false;
  }

  true
}
