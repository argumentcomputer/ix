//! Ixon enum types: DefKind, DefinitionSafety, QuotKind build/decode/roundtrip FFI.

use crate::ix::env::{DefinitionSafety, QuotKind};
use crate::ix::ixon::constant::DefKind;
use crate::lean::{
  LeanIxonDefKind, LeanIxonDefinitionSafety, LeanIxonQuotKind,
};
#[cfg(feature = "test-ffi")]
use lean_ffi::object::LeanBorrowed;
use lean_ffi::object::{LeanOwned, LeanRef};

impl LeanIxonDefKind<LeanOwned> {
  /// Build Ixon.DefKind
  /// | defn -- tag 0
  /// | opaq -- tag 1
  /// | thm  -- tag 2
  /// Simple enums are passed as raw (unboxed) tag values across Lean FFI.
  pub fn build(kind: &DefKind) -> Self {
    let tag = match kind {
      DefKind::Definition => 0,
      DefKind::Opaque => 1,
      DefKind::Theorem => 2,
    };
    Self::new(LeanOwned::from_enum_tag(tag))
  }
}

impl<R: LeanRef> LeanIxonDefKind<R> {
  /// Decode Ixon.DefKind (simple enum, raw unboxed tag value).
  pub fn decode(&self) -> DefKind {
    let tag = self.inner().as_enum_tag();
    match tag {
      0 => DefKind::Definition,
      1 => DefKind::Opaque,
      2 => DefKind::Theorem,
      _ => panic!("Invalid Ixon.DefKind tag: {}", tag),
    }
  }
}

impl LeanIxonDefinitionSafety<LeanOwned> {
  /// Build Ixon.DefinitionSafety
  /// | unsaf -- tag 0
  /// | safe  -- tag 1
  /// | part  -- tag 2
  pub fn build(safety: &DefinitionSafety) -> Self {
    let tag = match safety {
      DefinitionSafety::Unsafe => 0,
      DefinitionSafety::Safe => 1,
      DefinitionSafety::Partial => 2,
    };
    Self::new(LeanOwned::from_enum_tag(tag))
  }
}

impl<R: LeanRef> LeanIxonDefinitionSafety<R> {
  /// Decode Ixon.DefinitionSafety (simple enum, raw unboxed tag value).
  pub fn decode(&self) -> DefinitionSafety {
    let tag = self.inner().as_enum_tag();
    match tag {
      0 => DefinitionSafety::Unsafe,
      1 => DefinitionSafety::Safe,
      2 => DefinitionSafety::Partial,
      _ => panic!("Invalid Ixon.DefinitionSafety tag: {}", tag),
    }
  }
}

impl LeanIxonQuotKind<LeanOwned> {
  /// Build Ixon.QuotKind
  /// | type -- tag 0
  /// | ctor -- tag 1
  /// | lift -- tag 2
  /// | ind  -- tag 3
  pub fn build(kind: &QuotKind) -> Self {
    let tag = match kind {
      QuotKind::Type => 0,
      QuotKind::Ctor => 1,
      QuotKind::Lift => 2,
      QuotKind::Ind => 3,
    };
    Self::new(LeanOwned::from_enum_tag(tag))
  }
}

impl<R: LeanRef> LeanIxonQuotKind<R> {
  /// Decode Ixon.QuotKind (simple enum, raw unboxed tag value).
  pub fn decode(&self) -> QuotKind {
    let tag = self.inner().as_enum_tag();
    match tag {
      0 => QuotKind::Type,
      1 => QuotKind::Ctor,
      2 => QuotKind::Lift,
      3 => QuotKind::Ind,
      _ => panic!("Invalid Ixon.QuotKind tag: {}", tag),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DefKind.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_def_kind(
  obj: LeanIxonDefKind<LeanBorrowed<'_>>,
) -> LeanIxonDefKind<LeanOwned> {
  let kind = obj.decode();
  LeanIxonDefKind::build(&kind)
}

/// Round-trip Ixon.DefinitionSafety.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_safety(
  obj: LeanIxonDefinitionSafety<LeanBorrowed<'_>>,
) -> LeanIxonDefinitionSafety<LeanOwned> {
  let safety = obj.decode();
  LeanIxonDefinitionSafety::build(&safety)
}

/// Round-trip Ixon.QuotKind.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quot_kind(
  obj: LeanIxonQuotKind<LeanBorrowed<'_>>,
) -> LeanIxonQuotKind<LeanOwned> {
  let kind = obj.decode();
  LeanIxonQuotKind::build(&kind)
}
