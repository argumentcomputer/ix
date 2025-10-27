use crate::ixon::nat::Nat;
//use crate::ixon::serialize::Serialize;
//use crate::ixon::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NamePart {
    Str(String),
    Num(Nat),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub parts: Vec<NamePart>,
}

//impl Serialize for NamePart {
//    fn put(&self, buf: &mut Vec<u8>) {
//        match self {
//            // TODO: do we need to clone here?
//            Self::Str(x) => Ixon::Strl(x.clone()).put(buf),
//            Self::Num(x) => Ixon::Natl(x.clone()).put(buf),
//        }
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        match Ixon::get(buf)? {
//            Ixon::Strl(x) => Ok(Self::Str(x)),
//            Ixon::Natl(x) => Ok(Self::Num(x)),
//            x => Err(format!("get NamePart invalid {x:?}")),
//        }
//    }
//}
//
//impl Serialize for Name {
//    fn put(&self, buf: &mut Vec<u8>) {
//        self.parts.put(buf)
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        Ok(Name {
//            parts: Serialize::get(buf)?,
//        })
//    }
//}
//
//#[cfg(test)]
//mod tests {
//    use super::*;
//    use crate::ixon::nat::tests::arbitrary_nat;
//    use crate::ixon::tests::{arbitrary_string, gen_range, gen_vec};
//    use quickcheck::{Arbitrary, Gen};
//
//    impl Arbitrary for NamePart {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..1);
//            let len = gen_range(g, 0..9);
//            match x {
//                0 => Self::Str(arbitrary_string(g, len)),
//                _ => Self::Num(arbitrary_nat(g, len)),
//            }
//        }
//    }
//
//    impl Arbitrary for Name {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let parts = gen_vec(g, 9, NamePart::arbitrary);
//            Name { parts }
//        }
//    }
//}
