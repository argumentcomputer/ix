//! Cryptographic commitments.

#![allow(clippy::map_err_ignore)]
#![allow(clippy::needless_pass_by_value)]

use crate::ix::address::Address;

use super::tag::Tag4;

/// Tag4 variant for Commitment (flag=0xE, size=5).
pub const VARIANT: u64 = 5;

/// A cryptographic commitment.
///
/// The commitment is computed as `blake3(Tag4{0xE,5} || secret || payload)` where:
/// - `secret` is the address of a random blinding factor (stored in blobs)
/// - `payload` is the address of the committed constant
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Comm {
  /// Address of the blinding secret (in blobs map)
  pub secret: Address,
  /// Address of the committed constant
  pub payload: Address,
}

impl Comm {
  pub fn new(secret: Address, payload: Address) -> Self {
    Comm { secret, payload }
  }

  /// Serialize without tag header (for use within Env section serialization).
  pub fn put(&self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(self.secret.as_bytes());
    buf.extend_from_slice(self.payload.as_bytes());
  }

  /// Deserialize without tag header (for use within Env section serialization).
  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    if buf.len() < 64 {
      return Err(format!("Comm::get: need 64 bytes, have {}", buf.len()));
    }
    let (secret_bytes, rest) = buf.split_at(32);
    let (payload_bytes, rest) = rest.split_at(32);
    *buf = rest;

    let secret = Address::from_slice(secret_bytes)
      .map_err(|_| "Comm::get: invalid secret")?;
    let payload = Address::from_slice(payload_bytes)
      .map_err(|_| "Comm::get: invalid payload")?;

    Ok(Comm { secret, payload })
  }

  /// Serialize with Tag4{0xE, 5} header.
  pub fn put_tagged(&self, buf: &mut Vec<u8>) {
    Tag4::new(0xE, VARIANT).put(buf);
    self.put(buf);
  }

  /// Deserialize with Tag4{0xE, 5} header.
  pub fn get_tagged(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != 0xE || tag.size != VARIANT {
      return Err(format!(
        "Comm::get_tagged: expected Tag4{{0xE, 5}}, got Tag4{{{}, {}}}",
        tag.flag, tag.size
      ));
    }
    Self::get(buf)
  }

  /// Serialize with tag and compute content address: `blake3(0xE5 + secret + payload)`.
  pub fn commit(&self) -> Address {
    let mut buf = Vec::new();
    self.put_tagged(&mut buf);
    Address::hash(&buf)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::Arbitrary;

  impl Arbitrary for Comm {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
      Comm::new(Address::arbitrary(g), Address::arbitrary(g))
    }
  }

  fn comm_roundtrip(c: &Comm) -> bool {
    let mut buf = Vec::new();
    c.put(&mut buf);
    match Comm::get(&mut buf.as_slice()) {
      Ok(c2) => c == &c2,
      Err(_) => false,
    }
  }

  fn comm_tagged_roundtrip(c: &Comm) -> bool {
    let mut buf = Vec::new();
    c.put_tagged(&mut buf);
    match Comm::get_tagged(&mut buf.as_slice()) {
      Ok(c2) => c == &c2,
      Err(_) => false,
    }
  }

  #[quickcheck]
  fn prop_comm_roundtrip(c: Comm) -> bool {
    comm_roundtrip(&c)
  }

  #[quickcheck]
  fn prop_comm_tagged_roundtrip(c: Comm) -> bool {
    comm_tagged_roundtrip(&c)
  }

  #[test]
  fn test_comm_roundtrip() {
    let comm = Comm::new(Address::hash(b"secret"), Address::hash(b"payload"));
    assert!(comm_roundtrip(&comm));
  }

  #[test]
  fn test_comm_tagged_roundtrip() {
    let comm = Comm::new(Address::hash(b"secret"), Address::hash(b"payload"));
    assert!(comm_tagged_roundtrip(&comm));
  }

  #[test]
  fn test_comm_tagged_tag_byte() {
    let comm = Comm::new(Address::hash(b"a"), Address::hash(b"b"));
    let mut buf = Vec::new();
    comm.put_tagged(&mut buf);
    assert_eq!(buf[0], 0xE5, "Comm tagged should start with 0xE5");
  }

  #[test]
  fn test_comm_commit() {
    let comm = Comm::new(Address::hash(b"secret"), Address::hash(b"payload"));
    let addr = comm.commit();
    // Commit should be deterministic
    let addr2 = comm.commit();
    assert_eq!(addr, addr2);
  }
}
