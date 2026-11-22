//! Ixon simple enum types: DefKind, DefinitionSafety, QuotKind roundtrip FFI.
//!
//! In Lean 4's C ABI, inductive types with ≤ 256 nullary constructors are
//! represented as unboxed `uint8_t` tag values for both arguments and returns.

#[cfg(feature = "test-ffi")]
use ix_common::env::{DefinitionSafety, QuotKind};
#[cfg(feature = "test-ffi")]
use ixon::constant::DefKind;

#[cfg(feature = "test-ffi")]
fn def_kind_from_tag(tag: u8) -> DefKind {
  match tag {
    0 => DefKind::Definition,
    1 => DefKind::Opaque,
    2 => DefKind::Theorem,
    _ => panic!("Invalid Ixon.DefKind tag: {tag}"),
  }
}

#[cfg(feature = "test-ffi")]
fn def_kind_to_tag(kind: &DefKind) -> u8 {
  match kind {
    DefKind::Definition => 0,
    DefKind::Opaque => 1,
    DefKind::Theorem => 2,
  }
}

#[cfg(feature = "test-ffi")]
fn definition_safety_from_tag(tag: u8) -> DefinitionSafety {
  match tag {
    0 => DefinitionSafety::Unsafe,
    1 => DefinitionSafety::Safe,
    2 => DefinitionSafety::Partial,
    _ => panic!("Invalid Ixon.DefinitionSafety tag: {tag}"),
  }
}

#[cfg(feature = "test-ffi")]
fn definition_safety_to_tag(safety: &DefinitionSafety) -> u8 {
  match safety {
    DefinitionSafety::Unsafe => 0,
    DefinitionSafety::Safe => 1,
    DefinitionSafety::Partial => 2,
  }
}

#[cfg(feature = "test-ffi")]
fn quot_kind_from_tag(tag: u8) -> QuotKind {
  match tag {
    0 => QuotKind::Type,
    1 => QuotKind::Ctor,
    2 => QuotKind::Lift,
    3 => QuotKind::Ind,
    _ => panic!("Invalid Ixon.QuotKind tag: {tag}"),
  }
}

#[cfg(feature = "test-ffi")]
fn quot_kind_to_tag(kind: &QuotKind) -> u8 {
  match kind {
    QuotKind::Type => 0,
    QuotKind::Ctor => 1,
    QuotKind::Lift => 2,
    QuotKind::Ind => 3,
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DefKind.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_def_kind(tag: u8) -> u8 {
  let kind = def_kind_from_tag(tag);
  def_kind_to_tag(&kind)
}

/// Round-trip Ixon.DefinitionSafety.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_safety(tag: u8) -> u8 {
  let safety = definition_safety_from_tag(tag);
  definition_safety_to_tag(&safety)
}

/// Round-trip Ixon.QuotKind.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quot_kind(tag: u8) -> u8 {
  let kind = quot_kind_from_tag(tag);
  quot_kind_to_tag(&kind)
}
