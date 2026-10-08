//! The primitive table in force for this process.
//!
//! The checker recognizes pinned declarations by content address, so a
//! binary carries the table of the toolchain it was built against. An
//! environment compiled under another toolchain is checked by pointing
//! `IX_PRIM_PROFILE` at a serialized `PrimProfile` object (written by
//! `ix prims export` from that toolchain's `.ixe`); the object's address
//! then names the binding the check ran under. A profile that fails to
//! load aborts: silently falling back to the built-in table would check
//! literals against the wrong `String`.

use std::sync::LazyLock;

use ix_common::address::Address;
use ix_common::prim_addrs::PrimAddrs;
use ixon::prim_profile::PrimProfile;

pub const PROFILE_ENV_VAR: &str = "IX_PRIM_PROFILE";

struct Current {
  addrs: PrimAddrs,
  address: Address,
  source: String,
}

static CURRENT: LazyLock<Current> =
  LazyLock::new(|| match std::env::var(PROFILE_ENV_VAR) {
    Ok(path) if !path.is_empty() => {
      let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("{PROFILE_ENV_VAR}={path}: {e}"));
      let profile = PrimProfile::from_bytes(&bytes)
        .unwrap_or_else(|e| panic!("{PROFILE_ENV_VAR}={path}: {e}"));
      let addrs = profile
        .to_addrs()
        .unwrap_or_else(|e| panic!("{PROFILE_ENV_VAR}={path}: {e}"));
      let address = profile.address();
      eprintln!("[prims] profile {} loaded from {path}", address.hex());
      Current { addrs, address, source: path }
    },
    _ => {
      let addrs = PrimAddrs::new();
      let address = PrimProfile::from_addrs(&addrs).address();
      Current { addrs, address, source: String::from("builtin") }
    },
  });

pub fn current() -> &'static PrimAddrs {
  &CURRENT.addrs
}

/// Address of the profile object the current table corresponds to, for
/// the built-in table as well as a loaded one.
pub fn current_address() -> &'static Address {
  &CURRENT.address
}

/// `builtin`, or the path the profile was loaded from.
pub fn current_source() -> &'static str {
  &CURRENT.source
}
