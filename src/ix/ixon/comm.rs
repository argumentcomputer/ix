//! Cryptographic commitments.

#![allow(clippy::map_err_ignore)]
#![allow(clippy::needless_pass_by_value)]

use crate::ix::address::Address;

/// A cryptographic commitment.
///
/// The commitment is computed as `blake3(secret || payload)` where:
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

  pub fn put(&self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(self.secret.as_bytes());
    buf.extend_from_slice(self.payload.as_bytes());
  }

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

  #[quickcheck]
  fn prop_comm_roundtrip(c: Comm) -> bool {
    comm_roundtrip(&c)
  }

  #[test]
  fn test_comm_roundtrip() {
    let comm = Comm::new(Address::hash(b"secret"), Address::hash(b"payload"));
    assert!(comm_roundtrip(&comm));
  }
}
