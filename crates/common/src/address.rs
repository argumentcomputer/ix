//! Content-addressed identifiers based on Blake3 hashing.
//!
//! [`Address`] wraps a 32-byte Blake3 digest and is used throughout the Ix
//! pipeline to uniquely identify constants, blobs, and other data.

use blake3::Hash;
use core::array::TryFromSliceError;
use std::cmp::{Ordering, PartialOrd};
use std::hash::{Hash as StdHash, Hasher};

/// A 32-byte Blake3 content address.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
  hash: Hash,
}

impl Address {
  /// Constructs an address from a 32-byte slice.
  pub fn from_slice(input: &[u8]) -> Result<Self, TryFromSliceError> {
    Ok(Address { hash: Hash::from_slice(input)? })
  }
  /// Wraps an existing Blake3 hash as an address.
  pub fn from_blake3_hash(hash: Hash) -> Self {
    Address { hash }
  }
  /// Hashes arbitrary bytes with Blake3 and returns the resulting address.
  pub fn hash(input: &[u8]) -> Self {
    Address { hash: blake3::hash(input) }
  }
  /// Returns the address as a lowercase hexadecimal string.
  pub fn hex(&self) -> String {
    self.hash.to_hex().as_str().to_owned()
  }
  /// Returns the raw 32-byte digest.
  pub fn as_bytes(&self) -> &[u8; 32] {
    self.hash.as_bytes()
  }

  /// Build a deterministic, collision-resistant `Name` for this address:
  /// `Ix._#.<hex>`. Mirrors Lean-side `Ix.Address.toUniqueName`.
  ///
  /// Use this when you need to register a KId/Named entry at a synthetic
  /// name that can't collide with any Lean-originated name (e.g. for
  /// scratch `KEnv` entries that should not participate in the
  /// `name_to_addr` / `aux_name_to_addr` namespace).
  pub fn to_unique_name(&self) -> crate::ix::env::Name {
    use crate::ix::env::Name;
    Name::str(
      Name::str(Name::str(Name::anon(), "Ix".to_string()), "_#".to_string()),
      self.hex(),
    )
  }

  /// Inverse of `to_unique_name`. Returns `Some(Address)` iff `name` has
  /// shape `Ix._#.<hex>` with valid 64-char hex; otherwise `None`.
  pub fn from_unique_name(name: &crate::ix::env::Name) -> Option<Self> {
    use crate::ix::env::NameData;
    let (parent, hex) = match name.as_data() {
      NameData::Str(parent, s, _) => (parent.clone(), s.clone()),
      _ => return None,
    };
    let parent = match parent.as_data() {
      NameData::Str(pp, s, _) if s == "_#" => pp.clone(),
      _ => return None,
    };
    match parent.as_data() {
      NameData::Str(ppp, s, _) if s == "Ix" => match ppp.as_data() {
        NameData::Anonymous(_) => Address::from_hex(&hex),
        _ => None,
      },
      _ => None,
    }
  }

  /// Build a synthetic `Name` for a mutual block's `Named` entry:
  /// `Ix.<hex>.<first_member_name>`. Disambiguates alpha-equivalent blocks
  /// that share an `addr` but have different member names.
  ///
  /// Used by `compile/mutual.rs` to register each mutual block under a
  /// Muts-tagged meta so kernel ingress can discover and process it via
  /// `ingress_muts_block`.
  pub fn muts_name(
    &self,
    first_member: &crate::ix::env::Name,
  ) -> crate::ix::env::Name {
    use crate::ix::env::{Name, NameData};
    let base = Name::str(Name::str(Name::anon(), "Ix".to_string()), self.hex());
    // Append each component of `first_member` to the base, preserving
    // numeric vs string parts.
    fn go(base: Name, name: &Name) -> Name {
      match name.as_data() {
        NameData::Anonymous(_) => base,
        NameData::Str(parent, s, _) => Name::str(go(base, parent), s.clone()),
        NameData::Num(parent, n, _) => Name::num(go(base, parent), n.clone()),
      }
    }
    go(base, first_member)
  }

  /// Constructs an address from a 64-character hexadecimal string.
  pub fn from_hex(hex: &str) -> Option<Self> {
    if hex.len() != 64 {
      return None;
    }
    let mut bytes = [0u8; 32];
    for i in 0..32 {
      bytes[i] = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(Address { hash: Hash::from(bytes) })
  }
}

impl Ord for Address {
  fn cmp(&self, other: &Address) -> Ordering {
    self.as_bytes().cmp(other.as_bytes())
  }
}

impl PartialOrd for Address {
  fn partial_cmp(&self, other: &Address) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl StdHash for Address {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.as_bytes().hash(state);
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  impl Arbitrary for Address {
    fn arbitrary(g: &mut Gen) -> Self {
      let mut bytes = [0u8; 32];
      for b in &mut bytes {
        *b = u8::arbitrary(g);
      }
      Address::from_slice(&bytes).unwrap()
    }
  }
}
