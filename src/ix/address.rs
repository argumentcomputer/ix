use blake3::Hash;
use core::array::TryFromSliceError;
use std::cmp::{Ordering, PartialOrd};
use std::hash::{Hash as StdHash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
  hash: Hash,
}

impl Address {
  pub fn from_slice(input: &[u8]) -> Result<Self, TryFromSliceError> {
    Ok(Address { hash: Hash::from_slice(input)? })
  }
  pub fn hash(input: &[u8]) -> Self {
    Address { hash: blake3::hash(input) }
  }
  pub fn hex(&self) -> String {
    self.hash.to_hex().as_str().to_owned()
  }
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MetaAddress {
  pub data: Address,
  pub meta: Address,
}

//impl Display for MetaAddress {}

// TODO: DELETEME
//impl Default for MetaAddress {
//  fn default() -> Self {
//    let addr = Address { hash: [0; 32].into() };
//    Self { data: addr.clone(), meta: addr }
//  }
//}

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
  impl Arbitrary for MetaAddress {
    fn arbitrary(g: &mut Gen) -> Self {
      MetaAddress { data: Address::arbitrary(g), meta: Address::arbitrary(g) }
    }
  }
}
