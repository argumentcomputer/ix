use blake3::Hash;
use std::cmp::{Ordering, PartialOrd};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
  pub hash: Hash,
}

impl Address {
  pub fn hash(input: &[u8]) -> Self {
    Address { hash: blake3::hash(input) }
  }
}

impl Ord for Address {
  fn cmp(&self, other: &Address) -> Ordering {
    self.hash.as_bytes().cmp(other.hash.as_bytes())
  }
}

impl PartialOrd for Address {
  fn partial_cmp(&self, other: &Address) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaAddress {
  pub data: Address,
  pub meta: Address,
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
      Address { hash: Hash::from_slice(&bytes).unwrap() }
    }
  }
}
