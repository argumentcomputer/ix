//use crate::ixon::serialize::Serialize;
//use crate::ixon::*;
use num_bigint::BigUint;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Nat(pub BigUint);

impl Nat {
    pub fn new_le(bytes: &[u8]) -> Self {
        Nat(BigUint::from_bytes_le(bytes))
    }
}

//impl Serialize for Nat {
//    fn put(&self, buf: &mut Vec<u8>) {
//        Ixon::Natl(self.clone()).put(buf)
//    }
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        match Ixon::get(buf) {
//            Ok(Ixon::Natl(x)) => Ok(x),
//            Ok(x) => Err(format!("get Nat invalid {x:?}")),
//            Err(e) => Err(e),
//        }
//    }
//}
//
impl<T> From<T> for Nat
where
    T: Into<BigUint>,
{
    fn from(x: T) -> Self {
        Nat(x.into())
    }
}
//
//#[cfg(test)]
//pub mod tests {
//    use super::*;
//    use crate::ixon::tests::gen_range;
//    use quickcheck::{Arbitrary, Gen};
//
//    pub fn arbitrary_nat(g: &mut Gen, size: usize) -> Nat {
//        let mut bytes = vec![];
//
//        let b = u8::arbitrary(g);
//
//        if b == 0 {
//            bytes.push(b + 1);
//        } else {
//            bytes.push(b);
//        }
//
//        for _ in 0..size {
//            bytes.push(u8::arbitrary(g));
//        }
//
//        Nat(BigUint::from_bytes_be(&bytes))
//    }
//
//    impl Arbitrary for Nat {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let size = gen_range(g, 0..4);
//            arbitrary_nat(g, size)
//        }
//    }
//}
