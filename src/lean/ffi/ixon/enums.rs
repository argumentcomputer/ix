//! Ixon enum types: DefKind, DefinitionSafety, QuotKind build/decode/roundtrip FFI.

use std::ffi::c_void;

use crate::ix::env::{DefinitionSafety, QuotKind};
use crate::ix::ixon::constant::DefKind;

/// Build Ixon.DefKind
/// | defn -- tag 0
/// | opaq -- tag 1
/// | thm  -- tag 2
/// Simple enums are represented as raw tag values (unboxed scalars).
pub fn build_def_kind(kind: &DefKind) -> *mut c_void {
  let tag = match kind {
    DefKind::Definition => 0,
    DefKind::Opaque => 1,
    DefKind::Theorem => 2,
  };
  tag as *mut c_void
}

/// Build Ixon.DefinitionSafety
/// | unsaf -- tag 0
/// | safe  -- tag 1
/// | part  -- tag 2
pub fn build_ixon_definition_safety(safety: &DefinitionSafety) -> *mut c_void {
  let tag = match safety {
    DefinitionSafety::Unsafe => 0,
    DefinitionSafety::Safe => 1,
    DefinitionSafety::Partial => 2,
  };
  tag as *mut c_void
}

/// Build Ixon.QuotKind
/// | type -- tag 0
/// | ctor -- tag 1
/// | lift -- tag 2
/// | ind  -- tag 3
pub fn build_ixon_quot_kind(kind: &QuotKind) -> *mut c_void {
  let tag = match kind {
    QuotKind::Type => 0,
    QuotKind::Ctor => 1,
    QuotKind::Lift => 2,
    QuotKind::Ind => 3,
  };
  tag as *mut c_void
}

// =============================================================================
// Decode Functions
// =============================================================================

/// Decode Ixon.DefKind (simple enum, raw tag value).
pub fn decode_ixon_def_kind(ptr: *const c_void) -> DefKind {
  let tag = ptr as usize;
  match tag {
    0 => DefKind::Definition,
    1 => DefKind::Opaque,
    2 => DefKind::Theorem,
    _ => panic!("Invalid Ixon.DefKind tag: {}", tag),
  }
}

/// Decode Ixon.DefinitionSafety (simple enum, raw tag value).
pub fn decode_ixon_definition_safety(ptr: *const c_void) -> DefinitionSafety {
  let tag = ptr as usize;
  match tag {
    0 => DefinitionSafety::Unsafe,
    1 => DefinitionSafety::Safe,
    2 => DefinitionSafety::Partial,
    _ => panic!("Invalid Ixon.DefinitionSafety tag: {}", tag),
  }
}

/// Decode Ixon.QuotKind (simple enum, raw tag value).
pub fn decode_ixon_quot_kind(ptr: *const c_void) -> QuotKind {
  let tag = ptr as usize;
  match tag {
    0 => QuotKind::Type,
    1 => QuotKind::Ctor,
    2 => QuotKind::Lift,
    3 => QuotKind::Ind,
    _ => panic!("Invalid Ixon.QuotKind tag: {}", tag),
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DefKind.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_def_kind(
  ptr: *const c_void,
) -> *mut c_void {
  let kind = decode_ixon_def_kind(ptr);
  build_def_kind(&kind)
}

/// Round-trip Ixon.DefinitionSafety.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_safety(
  ptr: *const c_void,
) -> *mut c_void {
  let safety = decode_ixon_definition_safety(ptr);
  build_ixon_definition_safety(&safety)
}

/// Round-trip Ixon.QuotKind.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quot_kind(
  ptr: *const c_void,
) -> *mut c_void {
  let kind = decode_ixon_quot_kind(ptr);
  build_ixon_quot_kind(&kind)
}
