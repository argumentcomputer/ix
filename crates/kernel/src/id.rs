use std::fmt;
use std::hash::{Hash, Hasher};

use crate::ix::address::Address;
use crate::ix::env::Name;

use super::mode::{KernelMode, MetaDisplay, MetaHash};

/// Kernel identifier: bundles a content address with a metadata name.
/// In Meta mode, both fields participate in equality/hashing.
/// In Anon mode, the name is `()` so only the address matters.
#[derive(Clone, Debug)]
pub struct KId<M: KernelMode> {
  pub addr: Address,
  pub name: M::MField<Name>,
}

impl<M: KernelMode> KId<M> {
  pub fn new(addr: Address, name: M::MField<Name>) -> Self {
    KId { addr, name }
  }
}

impl<M: KernelMode> PartialEq for KId<M> {
  fn eq(&self, other: &Self) -> bool {
    self.addr == other.addr && self.name == other.name
  }
}

impl<M: KernelMode> Eq for KId<M> {}

impl<M: KernelMode> PartialOrd for KId<M> {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl<M: KernelMode> Ord for KId<M> {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.addr.cmp(&other.addr).then_with(|| meta_cmp(&self.name, &other.name))
  }
}

/// Derive ordering from MetaHash: hash both values and compare the digests.
/// For `()` (Anon mode), the hash is empty so all units compare equal.
fn meta_cmp<T: MetaHash>(a: &T, b: &T) -> std::cmp::Ordering {
  let hash = |v: &T| {
    let mut h = blake3::Hasher::new();
    v.meta_hash(&mut h);
    h.finalize()
  };
  hash(a).as_bytes().cmp(hash(b).as_bytes())
}

impl<M: KernelMode> Hash for KId<M> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.addr.hash(state);
    self.name.hash(state);
  }
}

impl<M: KernelMode> MetaHash for KId<M> {
  fn meta_hash(&self, hasher: &mut blake3::Hasher) {
    hasher.update(self.addr.as_bytes());
    self.name.meta_hash(hasher);
  }
}

impl<M: KernelMode> MetaDisplay for KId<M> {
  fn has_meta(&self) -> bool {
    self.name.has_meta()
  }
  fn meta_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let hex = self.addr.hex();
    let short = &hex[..8.min(hex.len())];
    if self.name.has_meta() {
      self.name.meta_fmt(f)?;
      write!(f, "@{short}")
    } else {
      write!(f, "{short}")
    }
  }
}

/// Meta mode: `Nat.add@a1b2c3d4`. Anon mode: `a1b2c3d4`.
impl<M: KernelMode> fmt::Display for KId<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let hex = self.addr.hex();
    let short = &hex[..8.min(hex.len())];
    if self.name.has_meta() {
      self.name.meta_fmt(f)?;
      write!(f, "@{short}")
    } else {
      write!(f, "{short}")
    }
  }
}

#[cfg(test)]
mod tests {
  use super::super::mode::{Anon, Meta};
  use super::*;

  fn mk_name(s: &str) -> Name {
    let mut name = Name::anon();
    for part in s.split('.') {
      name = Name::str(name, part.to_string());
    }
    name
  }

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  #[test]
  fn meta_named_shows_name_and_hash() {
    let id = KId::<Meta>::new(mk_addr("test"), mk_name("Nat.add"));
    let s = format!("{id}");
    assert!(s.starts_with("Nat.add@"), "expected 'Nat.add@...', got '{s}'");
    assert_eq!(s.len(), "Nat.add@".len() + 8);
  }

  #[test]
  fn meta_anonymous_shows_hash_only() {
    // Anonymous names have no displayable metadata, so KId falls back to hash.
    let id = KId::<Meta>::new(mk_addr("test"), Name::anon());
    let s = format!("{id}");
    assert_eq!(s.len(), 8, "expected 8-char hash, got '{s}'");
    assert!(!s.contains('@'), "anonymous should not contain '@', got '{s}'");
  }

  #[test]
  fn meta_nested_name() {
    let id = KId::<Meta>::new(mk_addr("x"), mk_name("Lean.Parser.Term.app"));
    let s = format!("{id}");
    assert!(s.starts_with("Lean.Parser.Term.app@"), "got '{s}'");
  }

  #[test]
  fn meta_single_component_name() {
    let id = KId::<Meta>::new(mk_addr("x"), mk_name("Nat"));
    let s = format!("{id}");
    assert!(s.starts_with("Nat@"), "got '{s}'");
  }

  #[test]
  fn anon_shows_hash_only() {
    let id = KId::<Anon>::new(mk_addr("test"), ());
    let s = format!("{id}");
    assert_eq!(s.len(), 8);
    assert!(!s.contains('@'), "anon mode should not contain '@', got '{s}'");
  }

  #[test]
  fn anon_same_display_regardless_of_addr() {
    let id1 = KId::<Anon>::new(mk_addr("foo"), ());
    let id2 = KId::<Anon>::new(mk_addr("bar"), ());
    // Different addresses produce different hashes
    assert_ne!(format!("{id1}"), format!("{id2}"));
  }

  #[test]
  fn meta_equality_includes_name() {
    let addr = mk_addr("test");
    let a = KId::<Meta>::new(addr.clone(), mk_name("Foo"));
    let b = KId::<Meta>::new(addr.clone(), mk_name("Bar"));
    let c = KId::<Meta>::new(addr.clone(), mk_name("Foo"));
    assert_ne!(a, b);
    assert_eq!(a, c);
  }

  #[test]
  fn anon_equality_ignores_erased_name() {
    let a = KId::<Anon>::new(mk_addr("test"), ());
    let b = KId::<Anon>::new(mk_addr("test"), ());
    let c = KId::<Anon>::new(mk_addr("other"), ());
    assert_eq!(a, b);
    assert_ne!(a, c);
  }
}
