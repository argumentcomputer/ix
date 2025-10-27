use crate::ixon::address::Address;
//use crate::ixon::serialize::Serialize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalClaim {
    pub lvls: Address,
    pub typ: Address,
    pub input: Address,
    pub output: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckClaim {
    pub lvls: Address,
    pub typ: Address,
    pub value: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Claim {
    Checks(CheckClaim),
    Evals(EvalClaim),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    pub claim: Claim,
    pub proof: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env {
    pub env: Vec<(Address, Address)>,
}

//impl Serialize for EvalClaim {
//    fn put(&self, buf: &mut Vec<u8>) {
//        self.lvls.put(buf);
//        self.typ.put(buf);
//        self.input.put(buf);
//        self.output.put(buf);
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        let lvls = Address::get(buf)?;
//        let typ = Address::get(buf)?;
//        let input = Address::get(buf)?;
//        let output = Address::get(buf)?;
//        Ok(Self {
//            lvls,
//            typ,
//            input,
//            output,
//        })
//    }
//}
//
//impl Serialize for CheckClaim {
//    fn put(&self, buf: &mut Vec<u8>) {
//        self.lvls.put(buf);
//        self.typ.put(buf);
//        self.value.put(buf);
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        let lvls = Address::get(buf)?;
//        let typ = Address::get(buf)?;
//        let value = Address::get(buf)?;
//        Ok(Self { lvls, typ, value })
//    }
//}
//
//impl Serialize for Claim {
//    fn put(&self, buf: &mut Vec<u8>) {
//        match self {
//            Self::Evals(x) => {
//                u8::put(&0xE2, buf);
//                x.put(buf)
//            }
//            Self::Checks(x) => {
//                u8::put(&0xE3, buf);
//                x.put(buf)
//            }
//        }
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        match buf.split_at_checked(1) {
//            Some((head, rest)) => {
//                *buf = rest;
//                match head[0] {
//                    0xE2 => {
//                        let x = EvalClaim::get(buf)?;
//                        Ok(Self::Evals(x))
//                    }
//                    0xE3 => {
//                        let x = CheckClaim::get(buf)?;
//                        Ok(Self::Checks(x))
//                    }
//                    x => Err(format!("get Claim invalid {x}")),
//                }
//            }
//            None => Err("get Claim EOF".to_string()),
//        }
//    }
//}
//
//impl Serialize for Proof {
//    fn put(&self, buf: &mut Vec<u8>) {
//        self.claim.put(buf);
//        self.proof.put(buf);
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        let claim = Claim::get(buf)?;
//        let proof = Serialize::get(buf)?;
//        Ok(Proof { claim, proof })
//    }
//}
//
//impl Serialize for Env {
//    fn put(&self, buf: &mut Vec<u8>) {
//        self.env.put(buf)
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        Ok(Env {
//            env: Serialize::get(buf)?,
//        })
//    }
//}
//
//#[cfg(test)]
//mod tests {
//    use super::*;
//    use crate::ixon::tests::gen_range;
//    use quickcheck::{Arbitrary, Gen};
//
//    impl Arbitrary for EvalClaim {
//        fn arbitrary(g: &mut Gen) -> Self {
//            Self {
//                lvls: Address::arbitrary(g),
//                typ: Address::arbitrary(g),
//                input: Address::arbitrary(g),
//                output: Address::arbitrary(g),
//            }
//        }
//    }
//
//    impl Arbitrary for CheckClaim {
//        fn arbitrary(g: &mut Gen) -> Self {
//            Self {
//                lvls: Address::arbitrary(g),
//                typ: Address::arbitrary(g),
//                value: Address::arbitrary(g),
//            }
//        }
//    }
//
//    impl Arbitrary for Claim {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..1);
//            match x {
//                0 => Self::Evals(EvalClaim::arbitrary(g)),
//                _ => Self::Checks(CheckClaim::arbitrary(g)),
//            }
//        }
//    }
//
//    impl Arbitrary for Proof {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..32);
//            let mut bytes = vec![];
//            for _ in 0..x {
//                bytes.push(u8::arbitrary(g));
//            }
//            Proof {
//                claim: Claim::arbitrary(g),
//                proof: bytes,
//            }
//        }
//    }
//
//    impl Arbitrary for Env {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..32);
//            let mut env = vec![];
//            for _ in 0..x {
//                env.push((Address::arbitrary(g), Address::arbitrary(g)));
//            }
//            Env { env }
//        }
//    }
//}
