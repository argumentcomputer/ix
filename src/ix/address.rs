use blake3::Hash;
use std::cmp::{Ordering, PartialOrd};
use std::hash::{Hash as StdHash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
  pub hash: Hash,
}

impl Address {
  pub fn hash(input: &[u8]) -> Self {
    Address { hash: blake3::hash(input) }
  }
  pub fn hex(&self) -> String {
    self.hash.to_hex().as_str().to_owned()
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
impl StdHash for Address {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.hash.as_bytes().hash(state);
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaAddress {
  pub data: Address,
  pub meta: Address,
}

//impl Display for MetaAddress {}

//// TODO: DELETEME
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
      Address { hash: Hash::from_slice(&bytes).unwrap() }
    }
  }
  impl Arbitrary for MetaAddress {
    fn arbitrary(g: &mut Gen) -> Self {
      MetaAddress { data: Address::arbitrary(g), meta: Address::arbitrary(g) }
    }
  }
}
