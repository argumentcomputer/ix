//! Kernel mode metadata parameterization.
//!
//! All zero kernel types are parameterized by `M: KernelMode`, which controls
//! presence of metadata with `ZMode<META>`:
//!
//! - **type Meta = ZMode<true>**: metadata fields stored as `T`.
//! - **type Anon = ZMode<false>**: metadata fields erased to `()`.
//!
//! `MetaHash` provides serialization into `blake3::Hasher` so that metadata
//! contributes to content hashes in Meta mode. The `()` impl is a no-op,
//! so metadata vanishes from hashes in Anon mode.

use std::fmt::{self, Debug};
use std::hash::Hash;

use crate::ix::env::{BinderInfo, DataValue, Name, NameData};

/// Serialize a value into a `blake3::Hasher` for content hashing.
/// The `()` impl is a no-op, so erased metadata contributes nothing.
pub trait MetaHash {
  fn meta_hash(&self, hasher: &mut blake3::Hasher);
}

impl MetaHash for () {
  fn meta_hash(&self, _hasher: &mut blake3::Hasher) {}
}

impl MetaHash for Name {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    hasher.update(self.get_hash().as_bytes());
  }
}

impl MetaHash for BinderInfo {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    hasher.update(&[match self {
      BinderInfo::Default => 0,
      BinderInfo::Implicit => 1,
      BinderInfo::StrictImplicit => 2,
      BinderInfo::InstImplicit => 3,
    }]);
  }
}

impl MetaHash for DataValue {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    crate::ix::env::hash_data_value(self, hasher);
  }
}

impl<T: MetaHash> MetaHash for Vec<T> {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    for item in self {
      item.meta_hash(hasher);
    }
  }
}

impl<A: MetaHash, B: MetaHash> MetaHash for (A, B) {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    self.0.meta_hash(hasher);
    self.1.meta_hash(hasher);
  }
}

impl MetaHash for bool {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    hasher.update(&[*self as u8]);
  }
}

/// Check a metadata field for duplicate level parameter names.
/// `Vec<Name>` performs the real check; `()` (erased metadata) is a no-op.
pub trait CheckDupLevelParams {
  fn has_duplicate_level_params(&self) -> bool;
}

impl CheckDupLevelParams for Vec<Name> {
  fn has_duplicate_level_params(&self) -> bool {
    for (i, p) in self.iter().enumerate() {
      if self[i + 1..].contains(p) {
        return true;
      }
    }
    false
  }
}

impl CheckDupLevelParams for () {
  fn has_duplicate_level_params(&self) -> bool {
    false
  }
}

/// Display metadata conditionally across kernel modes.
///
/// In Meta mode, concrete types display their content. In Anon mode, `()` signals
/// no content via `has_meta() == false`, and callers provide a positional or hash
/// fallback. This enables a single generic `Display` impl per zero kernel type
/// instead of separate Meta/Anon impls.
pub trait MetaDisplay {
  /// Whether this field carries displayable metadata.
  /// `false` for `()` (Anon mode) and anonymous `Name`s.
  fn has_meta(&self) -> bool;

  /// Format the metadata value. Callers should check `has_meta()` first
  /// and provide a fallback (e.g., positional index) when `false`.
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl MetaDisplay for Name {
  fn has_meta(&self) -> bool {
    !matches!(self.as_data(), NameData::Anonymous(_))
  }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{self}")
  }
}

impl MetaDisplay for BinderInfo {
  fn has_meta(&self) -> bool { true }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      BinderInfo::Default => Ok(()),
      BinderInfo::Implicit => write!(f, "{{}}"),
      BinderInfo::StrictImplicit => write!(f, "⦃⦄"),
      BinderInfo::InstImplicit => write!(f, "[]"),
    }
  }
}

impl MetaDisplay for DataValue {
  fn has_meta(&self) -> bool { true }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{self:?}")
  }
}

impl<T: MetaDisplay> MetaDisplay for Vec<T> {
  fn has_meta(&self) -> bool { !self.is_empty() }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, item) in self.iter().enumerate() {
      if i > 0 { write!(f, ", ")?; }
      item.meta_fmt(f)?;
    }
    Ok(())
  }
}

impl<A: MetaDisplay, B: MetaDisplay> MetaDisplay for (A, B) {
  fn has_meta(&self) -> bool { self.0.has_meta() || self.1.has_meta() }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.meta_fmt(f)?;
    write!(f, ": ")?;
    self.1.meta_fmt(f)
  }
}

impl MetaDisplay for bool {
  fn has_meta(&self) -> bool { true }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{self}")
  }
}

impl MetaDisplay for () {
  fn has_meta(&self) -> bool { false }
  fn meta_fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) }
}

/// Controls metadata behavior for all zero kernel types.
pub trait KernelMode: 'static + Clone + Debug + Send + Sync {
  /// A metadata field: stores `T` in Meta mode, erased to `()` in Anon mode.
  type MField<T: MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync>:
    MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync;

  /// Wrap a value into a metadata field. In Anon mode, the value is discarded.
  fn meta_field<T: MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync>(
    val: T,
  ) -> Self::MField<T>;

}

/// Const-generic kernel mode. `META` controls metadata fields.
#[derive(Clone, Debug)]
pub struct ZMode<const META: bool>;

/// Full metadata. For debugging, roundtrip validation, and pretty printing.
pub type Meta = ZMode<true>;
/// No metadata. For anonymous structural mode.
pub type Anon = ZMode<false>;

impl KernelMode for ZMode<true> {
  type MField<T: MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync> =
    T;

  fn meta_field<
    T: MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync,
  >(
    val: T,
  ) -> T {
    val
  }

}

impl KernelMode for ZMode<false> {
  type MField<T: MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync> =
    ();

  fn meta_field<
    T: MetaHash + MetaDisplay + PartialEq + Clone + Debug + Hash + Send + Sync,
  >(
    _val: T,
  ) {
  }

}

#[cfg(test)]
mod tests {
  use super::*;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  #[test]
  fn meta_field_preserves_value() {
    let name = mk_name("x");
    let field = Meta::meta_field(name.clone());
    assert_eq!(field, name);
  }

  #[test]
  fn anon_field_erases_value() {
    let name = mk_name("x");
    let field = Anon::meta_field(name);
    assert_eq!(field, ());
  }

  #[test]
  fn meta_hash_name_writes_bytes() {
    let name = mk_name("x");
    let mut h = blake3::Hasher::new();
    name.meta_hash(&mut h);
    // Should have written 32 bytes (blake3 hash of name)
    let result = h.finalize();
    // Just check it's not the empty hash
    assert_ne!(*result.as_bytes(), *blake3::Hasher::new().finalize().as_bytes());
  }

  #[test]
  fn meta_hash_unit_is_noop() {
    let mut h1 = blake3::Hasher::new();
    let mut h2 = blake3::Hasher::new();
    ().meta_hash(&mut h1);
    // h1 and h2 should produce identical results
    assert_eq!(h1.finalize(), h2.finalize());
  }

  #[test]
  fn meta_hash_binder_info_distinct() {
    let variants = [
      BinderInfo::Default,
      BinderInfo::Implicit,
      BinderInfo::StrictImplicit,
      BinderInfo::InstImplicit,
    ];
    let hashes: Vec<blake3::Hash> = variants.iter().map(|bi| {
      let mut h = blake3::Hasher::new();
      bi.meta_hash(&mut h);
      h.finalize()
    }).collect();
    // All 4 should be distinct
    for i in 0..hashes.len() {
      for j in (i+1)..hashes.len() {
        assert_ne!(hashes[i], hashes[j], "BinderInfo variants {i} and {j} hash the same");
      }
    }
  }

  #[test]
  fn meta_hash_vec_sequential() {
    let names = vec![mk_name("a"), mk_name("b")];
    let mut h1 = blake3::Hasher::new();
    names.meta_hash(&mut h1);

    let mut h2 = blake3::Hasher::new();
    mk_name("a").meta_hash(&mut h2);
    mk_name("b").meta_hash(&mut h2);

    assert_eq!(h1.finalize(), h2.finalize());
  }

  #[test]
  fn meta_hash_bool() {
    let mut h_true = blake3::Hasher::new();
    let mut h_false = blake3::Hasher::new();
    true.meta_hash(&mut h_true);
    false.meta_hash(&mut h_false);
    assert_ne!(h_true.finalize(), h_false.finalize());
  }
}
