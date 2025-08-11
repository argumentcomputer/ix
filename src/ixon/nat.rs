use num_bigint::BigUint;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Nat(pub BigUint);

//impl Nat {}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::ixon::common::tests::gen_range;
  use quickcheck::{Arbitrary, Gen};

  pub fn arbitrary_nat(g: &mut Gen, size: usize) -> Nat {
    let mut bytes = vec![];

    let b = u8::arbitrary(g);

    if b == 0 {
      bytes.push(b + 1);
    } else {
      bytes.push(b);
    }

    for _ in 0..size {
      bytes.push(u8::arbitrary(g));
    }

    Nat(BigUint::from_bytes_be(&bytes))
  }

  impl Arbitrary for Nat {
    fn arbitrary(g: &mut Gen) -> Self {
      let size = gen_range(g, 0..4);
      arbitrary_nat(g, size)
    }
  }
}
