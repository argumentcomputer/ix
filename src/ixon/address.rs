use crate::ixon::serialize::Serialize;
use blake3::Hash;
use std::cmp::{Ordering, PartialOrd};

#[derive(PartialEq, Eq, Clone)]
pub struct Address {
  pub hash: Hash,
}

impl Serialize for Address {
  fn put(self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(self.hash.as_bytes())
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(32) {
      Some((head, rest)) => {
        *buf = rest;
        Ok(Address { hash: Hash::from_slice(head).unwrap() })
      },
      None => Err("get Address out of input".to_string()),
    }
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
