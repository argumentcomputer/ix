//! Shared foundation types for the Ix toolkit.
//!
//! Provides content-addressed identifiers ([`Address`](address::Address)),
//! interned hierarchical names and scalar binder/constant metadata ([`env`]),
//! and primitive constant addresses ([`prim_addrs::PrimAddrs`]).

#![cfg_attr(target_arch = "riscv64", no_std)]

#[cfg(target_arch = "riscv64")]
extern crate alloc;

pub mod address;
#[cfg(not(target_arch = "riscv64"))]
pub mod prim_addrs;

/// Hierarchical names and scalar metadata shared across crates.
#[cfg(not(target_arch = "riscv64"))]
pub mod env {
  use std::hash::{Hash as StdHash, Hasher};
  use std::sync::Arc;

  use bignat::Nat;
  use blake3::Hash;

  /// Tag byte for [`NameData::Anonymous`].
  pub const NANON: u8 = 0x00;
  /// Tag byte for [`NameData::Str`].
  pub const NSTR: u8 = 0x01;
  /// Tag byte for [`NameData::Num`].
  pub const NNUM: u8 = 0x02;

  #[derive(PartialEq, Eq, Debug, Clone)]
  pub struct Name(pub Arc<NameData>);

  impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      Some(self.cmp(other))
    }
  }

  impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
      self.get_hash().as_bytes().cmp(other.get_hash().as_bytes())
    }
  }

  /// The underlying data for a [`Name`].
  ///
  /// A single component of a hierarchical name.
  #[derive(Debug, Clone, PartialEq, Eq)]
  pub enum NameComponent {
    Str(String),
    Num(Nat),
  }

  /// Each variant carries its precomputed Blake3 hash as the last field.
  #[derive(PartialEq, Eq, Debug)]
  pub enum NameData {
    /// The root (empty) name.
    Anonymous(Hash),
    /// A string component appended to a prefix name.
    Str(Name, String, Hash),
    /// A numeric component appended to a prefix name.
    Num(Name, Nat, Hash),
  }

  impl Name {
    /// Returns a reference to the inner [`NameData`].
    pub fn as_data(&self) -> &NameData {
      &self.0
    }

    /// Returns the precomputed Blake3 hash of this name.
    pub fn get_hash(&self) -> &Hash {
      match self.0.as_ref() {
        NameData::Anonymous(h)
        | NameData::Str(.., h)
        | NameData::Num(.., h) => h,
      }
    }
    /// Constructs the anonymous (root) name.
    pub fn anon() -> Self {
      let hash = blake3::hash(&[NANON]);
      Name(Arc::new(NameData::Anonymous(hash)))
    }

    /// Constructs a name by appending a string component to `pre`.
    pub fn str(pre: Name, s: String) -> Self {
      let mut hasher = blake3::Hasher::new();
      hasher.update(&[NSTR]);
      hasher.update(pre.get_hash().as_bytes());
      hasher.update(s.as_bytes());
      let hash = hasher.finalize();
      Name(Arc::new(NameData::Str(pre, s, hash)))
    }

    /// Constructs a name by appending a numeric component to `pre`.
    pub fn num(pre: Name, n: Nat) -> Name {
      let mut hasher = blake3::Hasher::new();
      hasher.update(&[NNUM]);
      hasher.update(pre.get_hash().as_bytes());
      hasher.update(&n.to_le_bytes());
      let hash = hasher.finalize();
      Name(Arc::new(NameData::Num(pre, n, hash)))
    }
    /// Decompose this name into its components (from root to leaf).
    pub fn components(&self) -> Vec<NameComponent> {
      let mut components = Vec::new();
      let mut current = self;
      loop {
        match current.as_data() {
          NameData::Anonymous(_) => break,
          NameData::Str(pre, s, _) => {
            components.push(NameComponent::Str(s.clone()));
            current = pre;
          },
          NameData::Num(pre, n, _) => {
            components.push(NameComponent::Num(n.clone()));
            current = pre;
          },
        }
      }
      components.reverse();
      components
    }

    /// Strip a prefix from this name, returning the suffix components.
    pub fn strip_prefix(&self, prefix: &Name) -> Option<Vec<NameComponent>> {
      let self_components = self.components();
      let prefix_components = prefix.components();
      if self_components.len() < prefix_components.len() {
        return None;
      }
      if self_components[..prefix_components.len()] != prefix_components[..] {
        return None;
      }
      Some(self_components[prefix_components.len()..].to_vec())
    }

    /// Append suffix components to this name.
    pub fn append_components(&self, suffix: &[NameComponent]) -> Name {
      let mut result = self.clone();
      for component in suffix {
        match component {
          NameComponent::Str(s) => result = Name::str(result, s.clone()),
          NameComponent::Num(n) => result = Name::num(result, n.clone()),
        }
      }
      result
    }

    /// Get the last string component of this name, if any.
    pub fn last_str(&self) -> Option<&str> {
      match self.as_data() {
        NameData::Str(_, s, _) => Some(s.as_str()),
        _ => None,
      }
    }

    /// Returns a dot-separated human-readable representation of this name.
    pub fn pretty(&self) -> String {
      let mut components = Vec::new();
      let mut current = self;

      loop {
        match current.as_data() {
          NameData::Anonymous(_) => break,
          NameData::Str(pre, s, _) => {
            components.push(s.as_str().to_owned());
            current = pre;
          },
          NameData::Num(pre, n, _) => {
            components.push(n.0.to_string());
            current = pre;
          },
        }
      }

      components.reverse();
      components.join(".")
    }
  }

  impl StdHash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
      self.get_hash().hash(state);
    }
  }

  impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.write_str(&self.pretty())
    }
  }

  /// Canonical key for cross-kernel displayed-name matching: Lean's
  /// `Name.toString` wraps non-identifier components in `«»`
  /// (`_private.….«0».…`, `Lean.Order.«term_⊑_»`) while [`Name::pretty`]
  /// renders them bare, so a fail-out file written by one side misses a
  /// string-keyed lookup on the other. Stripping the guillemets from BOTH
  /// the request and the candidate collapses the two renderings onto one
  /// key, at the cost of the same flattening ambiguity `pretty` already
  /// has. Mirrors `Ix.Cli.ConstsFile.normalizeName` on the Lean side.
  pub fn normalize_displayed_name(s: &str) -> String {
    if s.contains(['«', '»']) {
      s.chars().filter(|c| !matches!(c, '«' | '»')).collect()
    } else {
      s.to_string()
    }
  }

  /// How a binder parameter is supplied at call sites.
  #[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, StdHash, Default,
  )]
  pub enum BinderInfo {
    /// Explicit `(x : α)`.
    #[default]
    Default,
    /// Implicit `{x : α}`.
    Implicit,
    /// Strict-implicit `⦃x : α⦄`.
    StrictImplicit,
    /// Typeclass instance `[x : α]`.
    InstImplicit,
  }

  /// Hints that control how aggressively the kernel unfolds a definition.
  #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
  pub enum ReducibilityHints {
    /// Never unfold.
    #[default]
    Opaque,
    /// Always unfold (abbreviation).
    Abbrev,
    /// Unfold with the given priority height.
    Regular(u32),
  }

  /// Safety classification of a definition.
  #[derive(Debug, Clone, Copy, PartialEq, Eq, StdHash)]
  pub enum DefinitionSafety {
    /// Marked `unsafe`; no termination or totality guarantees.
    Unsafe,
    /// Fully safe and total.
    Safe,
    /// Partial definition; may not terminate on all inputs.
    Partial,
  }

  #[derive(Debug, Clone, Copy, PartialEq, Eq, StdHash)]
  pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
  }

  /// QuickCheck `Arbitrary` implementations for scalar environment types.
  #[cfg(any(test, feature = "quickcheck"))]
  pub mod arbitrary {
    use quickcheck::{Arbitrary, Gen};

    use super::*;

    const SHORT_ASCII: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789_";

    pub(crate) fn arbitrary_ident(g: &mut Gen) -> String {
      let len = (usize::arbitrary(g) % 8) + 1;
      (0..len)
        .map(|_| {
          let idx = usize::arbitrary(g) % SHORT_ASCII.len();
          SHORT_ASCII[idx] as char
        })
        .collect()
    }

    impl Arbitrary for Name {
      fn arbitrary(g: &mut Gen) -> Self {
        let depth = usize::arbitrary(g) % 4;
        let mut name = Name::anon();
        for _ in 0..depth {
          if bool::arbitrary(g) {
            name = Name::str(name, arbitrary_ident(g));
          } else {
            name = Name::num(name, Nat::from(u64::arbitrary(g) % 100));
          }
        }
        name
      }
    }

    impl Arbitrary for BinderInfo {
      fn arbitrary(g: &mut Gen) -> Self {
        match u8::arbitrary(g) % 4 {
          0 => BinderInfo::Default,
          1 => BinderInfo::Implicit,
          2 => BinderInfo::StrictImplicit,
          _ => BinderInfo::InstImplicit,
        }
      }
    }

    impl Arbitrary for ReducibilityHints {
      fn arbitrary(g: &mut Gen) -> Self {
        match u8::arbitrary(g) % 3 {
          0 => ReducibilityHints::Opaque,
          1 => ReducibilityHints::Abbrev,
          _ => ReducibilityHints::Regular(u32::arbitrary(g) % 100),
        }
      }
    }

    impl Arbitrary for DefinitionSafety {
      fn arbitrary(g: &mut Gen) -> Self {
        match u8::arbitrary(g) % 3 {
          0 => DefinitionSafety::Unsafe,
          1 => DefinitionSafety::Safe,
          _ => DefinitionSafety::Partial,
        }
      }
    }

    impl Arbitrary for QuotKind {
      fn arbitrary(g: &mut Gen) -> Self {
        match u8::arbitrary(g) % 4 {
          0 => QuotKind::Type,
          1 => QuotKind::Ctor,
          2 => QuotKind::Lift,
          _ => QuotKind::Ind,
        }
      }
    }
  }

  #[cfg(test)]
  mod scalar_structure_tests {
    use rustc_hash::FxHashMap;

    use super::*;

    /// Name tables hash a name by its digest and confirm a hit with the
    /// derived `==`, which compares the components: two names that share a
    /// digest are two keys. The Lean compiler's tables are keyed the same way
    /// (`Ix.Compile.ExactKey.ExactName`, `Ix.nameCompareExact`).
    #[test]
    fn name_tables_keep_names_with_one_digest_apart() {
      let x = Name::str(Name::anon(), "x".into());
      let forged =
        Name(Arc::new(NameData::Str(Name::anon(), "y".into(), *x.get_hash())));
      assert_eq!(x.get_hash(), forged.get_hash());
      assert_ne!(x, forged);
      let mut table: FxHashMap<Name, u64> = FxHashMap::default();
      table.insert(x.clone(), 1);
      table.insert(forged.clone(), 2);
      assert_eq!(table.len(), 2);
      assert_eq!(table.get(&x), Some(&1));
      assert_eq!(table.get(&forged), Some(&2));
      let absent =
        Name(Arc::new(NameData::Str(Name::anon(), "z".into(), *x.get_hash())));
      assert!(!table.contains_key(&absent));
      // Valid neighbour: an equal name built separately is found.
      assert_eq!(table.get(&Name::str(Name::anon(), "x".into())), Some(&1));
    }
  }
}
