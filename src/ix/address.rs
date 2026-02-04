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
