//! Lazy materialization of `Constant` from on-disk bytes.
//!
//! Stored inside `Env::consts`: `DashMap<Address, LazyConstant>`. The
//! `.ixe` loader reads each constant's bytes (preceded by a Tag0
//! length sidecar at the env-section level — see `Env::get`) into a
//! `LazyConstant::from_bytes`, deferring `Constant::get` until first
//! access via [`LazyConstant::get`]. Subsequent accesses return a
//! cached `Arc<Constant>`.
//!
//! Invariants:
//! - `raw_bytes()` returns exactly what `Constant::put` produces and
//!   `Address::hash` consumes — the Tag0 length prefix is *not*
//!   included.
//! - `Address::hash(self.raw_bytes()) == addr` for the address this
//!   lazy entry was stored under (`verify_address` checks this).
//! - Cache is shared across `Clone`s (`Arc<OnceLock<…>>`) so that
//!   materialization done through one handle is visible through all.

use std::sync::{Arc, OnceLock};

use crate::ix::address::Address;

use super::constant::Constant;

/// Lazy-materialized `Constant` backed by serialized bytes.
#[derive(Debug, Clone)]
pub struct LazyConstant {
  /// Tag4-encoded constant bytes (exactly the slice consumed by
  /// `Constant::get` and hashed by `Address::hash`).
  bytes: Arc<[u8]>,
  /// Cached materialization. Shared across clones via `Arc` so the
  /// first thread to materialize benefits every subsequent handle.
  cache: Arc<OnceLock<Arc<Constant>>>,
}

impl LazyConstant {
  /// Construct from already-serialized bytes (the lazy load path).
  ///
  /// The caller is responsible for ensuring `bytes` is exactly what
  /// `Constant::put` produced for the address this entry is stored
  /// under. Use [`Self::verify_address`] for an explicit check.
  pub fn from_bytes(bytes: Arc<[u8]>) -> Self {
    LazyConstant { bytes, cache: Arc::new(OnceLock::new()) }
  }

  /// Construct from a structured `Constant` (the in-memory build path,
  /// e.g. from the compiler). Serializes once and pre-populates the
  /// cache so `get()` is free and `raw_bytes()` is ready for
  /// `Env::put`.
  pub fn from_constant(c: Constant) -> Self {
    let mut buf = Vec::new();
    c.put(&mut buf);
    let bytes: Arc<[u8]> = buf.into();
    let arc: Arc<Constant> = Arc::new(c);
    let cache = OnceLock::new();
    // First `set` always succeeds on a fresh OnceLock.
    let _ = cache.set(arc);
    LazyConstant { bytes, cache: Arc::new(cache) }
  }

  /// Materialize the `Constant`, caching for subsequent calls.
  pub fn get(&self) -> Result<Arc<Constant>, String> {
    if let Some(c) = self.cache.get() {
      return Ok(c.clone());
    }
    let mut slice: &[u8] = &self.bytes;
    let parsed = Constant::get(&mut slice)
      .map_err(|e| format!("LazyConstant::get: {e}"))?;
    if !slice.is_empty() {
      return Err(format!(
        "LazyConstant::get: trailing {} bytes after Constant",
        slice.len()
      ));
    }
    let arc = Arc::new(parsed);
    // If another thread raced us and set first, that's fine — our
    // local `arc` is dropped and we pick up the winner below.
    let _ = self.cache.set(arc);
    Ok(self.cache.get().expect("cache just set").clone())
  }

  /// Raw serialized bytes (the Tag4 constant body, no length prefix).
  pub fn raw_bytes(&self) -> &[u8] {
    &self.bytes
  }

  /// Whether the structured `Constant` has been materialized.
  pub fn is_materialized(&self) -> bool {
    self.cache.get().is_some()
  }

  /// Verify that `Address::hash(self.raw_bytes()) == *expected`.
  pub fn verify_address(&self, expected: &Address) -> bool {
    Address::hash(&self.bytes) == *expected
  }
}

/// Bytes are deterministic for a given `Constant`, so byte-equality
/// implies `Constant`-equality.
impl PartialEq for LazyConstant {
  fn eq(&self, other: &Self) -> bool {
    self.bytes == other.bytes
  }
}
impl Eq for LazyConstant {}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::DefinitionSafety;
  use crate::ix::ixon::constant::{Axiom, ConstantInfo, DefKind, Definition};
  use crate::ix::ixon::expr::Expr;

  fn axiom_constant() -> Constant {
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Expr::sort(0),
    }))
  }

  fn defn_constant() -> Constant {
    Constant::new(ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 1,
      typ: Expr::sort(0),
      value: Expr::var(0),
    }))
  }

  #[test]
  fn from_constant_materializes_immediately() {
    let c = axiom_constant();
    let lazy = LazyConstant::from_constant(c.clone());
    assert!(lazy.is_materialized());
    assert_eq!(*lazy.get().unwrap(), c);
  }

  #[test]
  fn from_bytes_defers_materialization() {
    let c = defn_constant();
    let (addr, bytes) = c.commit();
    let lazy = LazyConstant::from_bytes(bytes.into());
    assert!(!lazy.is_materialized());
    assert!(lazy.verify_address(&addr));
    let arc = lazy.get().unwrap();
    assert_eq!(*arc, c);
    assert!(lazy.is_materialized());
  }

  #[test]
  fn cache_is_shared_across_clones() {
    let lazy = LazyConstant::from_bytes(axiom_constant().commit().1.into());
    assert!(!lazy.is_materialized());
    let cloned = lazy.clone();
    let _ = cloned.get().unwrap();
    // Materialization through `cloned` is visible through `lazy`
    // because both share the same `Arc<OnceLock<…>>` cache slot.
    assert!(lazy.is_materialized());
  }

  #[test]
  fn raw_bytes_equals_constant_put() {
    let c = defn_constant();
    let mut expected = Vec::new();
    c.put(&mut expected);
    let lazy = LazyConstant::from_constant(c);
    assert_eq!(lazy.raw_bytes(), &expected[..]);
  }

  #[test]
  fn from_bytes_then_get_roundtrips() {
    let c = defn_constant();
    let (_addr, bytes) = c.commit();
    let lazy = LazyConstant::from_bytes(bytes.into());
    let got = lazy.get().unwrap();
    assert_eq!(*got, c);
  }

  #[test]
  fn verify_address_detects_corruption() {
    let c = axiom_constant();
    let (_addr, mut bytes) = c.commit();
    // Flip the last byte
    let last = bytes.len() - 1;
    bytes[last] ^= 0xFF;
    let lazy = LazyConstant::from_bytes(bytes.into());
    // Address of mutated bytes shouldn't match the original
    let original_addr = c.commit().0;
    assert!(!lazy.verify_address(&original_addr));
  }

  #[test]
  fn equality_by_bytes() {
    let a = LazyConstant::from_constant(axiom_constant());
    let b = LazyConstant::from_constant(axiom_constant());
    assert_eq!(a, b);
    let d = LazyConstant::from_constant(defn_constant());
    assert_ne!(a, d);
  }

  #[test]
  fn trailing_bytes_rejected() {
    let mut bytes = axiom_constant().commit().1;
    bytes.push(0xAB);
    let lazy = LazyConstant::from_bytes(bytes.into());
    let err = lazy.get().unwrap_err();
    assert!(err.contains("trailing"), "got: {err}");
  }
}
