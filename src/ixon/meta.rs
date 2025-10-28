use crate::ixon::address::Address;
//use crate::ixon::name::Name;
use crate::ixon::nat::Nat;
//use crate::ixon::serialize::Serialize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substring {
    pub str: Address,
    pub start_pos: Nat,
    pub stop_pos: Nat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceInfo {
    Original(Substring, Nat, Substring, Nat),
    Synthetic(Nat, Nat, bool),
    None,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Preresolved {
    Namespace(Address),
    Decl(Address, Vec<Address>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Syntax {
    Missing,
    Node(SourceInfo, Address, Vec<Address>),
    Atom(SourceInfo, Address),
    Ident(SourceInfo, Substring, Address, Vec<Preresolved>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DataValue {
    OfString(Address),
    OfBool(bool),
    OfName(Address),
    OfNat(Address),
    OfInt(Address),
    OfSyntax(Address),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
    AuxDecl,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Metadatum {
    Link(Address),
    Info(BinderInfo),
    Hints(ReducibilityHints),
    Links(Vec<Address>),
    Map(Vec<(Address, Address)>),
    KVMap(Vec<(Address, DataValue)>),
    Muts(Vec<Vec<Address>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Metadata {
    pub nodes: Vec<Metadatum>,
}

//impl Serialize for BinderInfo {
//    fn put(&self, buf: &mut Vec<u8>) {
//        match self {
//            Self::Default => buf.push(0),
//            Self::Implicit => buf.push(1),
//            Self::StrictImplicit => buf.push(2),
//            Self::InstImplicit => buf.push(3),
//            Self::AuxDecl => buf.push(3),
//        }
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        match buf.split_at_checked(1) {
//            Some((head, rest)) => {
//                *buf = rest;
//                match head[0] {
//                    0 => Ok(Self::Default),
//                    1 => Ok(Self::Implicit),
//                    2 => Ok(Self::StrictImplicit),
//                    3 => Ok(Self::InstImplicit),
//                    4 => Ok(Self::AuxDecl),
//                    x => Err(format!("get BinderInfo invalid {x}")),
//                }
//            }
//            None => Err("get BinderInfo EOF".to_string()),
//        }
//    }
//}
//
//impl Serialize for ReducibilityHints {
//    fn put(&self, buf: &mut Vec<u8>) {
//        match self {
//            Self::Opaque => buf.push(0),
//            Self::Abbrev => buf.push(1),
//            Self::Regular(x) => {
//                buf.push(2);
//                x.put(buf);
//            }
//        }
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        match buf.split_at_checked(1) {
//            Some((head, rest)) => {
//                *buf = rest;
//                match head[0] {
//                    0 => Ok(Self::Opaque),
//                    1 => Ok(Self::Abbrev),
//                    2 => {
//                        let x: u32 = Serialize::get(buf)?;
//                        Ok(Self::Regular(x))
//                    }
//                    x => Err(format!("get ReducibilityHints invalid {x}")),
//                }
//            }
//            None => Err("get ReducibilityHints EOF".to_string()),
//        }
//    }
//}

//impl Serialize for Metadatum {
//    fn put(&self, buf: &mut Vec<u8>) {
//        match self {
//            Self::Name(x) => {
//                buf.push(0);
//                x.put(buf);
//            }
//            Self::Info(x) => {
//                buf.push(1);
//                x.put(buf);
//            }
//            Self::Link(x) => {
//                buf.push(2);
//                x.put(buf);
//            }
//            Self::Hints(x) => {
//                buf.push(3);
//                x.put(buf);
//            }
//            Self::All(x) => {
//                buf.push(4);
//                x.put(buf);
//            }
//            Self::MutCtx(x) => {
//                buf.push(5);
//                x.put(buf);
//            }
//        }
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        match buf.split_at_checked(1) {
//            Some((head, rest)) => {
//                *buf = rest;
//                match head[0] {
//                    0 => {
//                        let x = Name::get(buf)?;
//                        Ok(Self::Name(x))
//                    }
//                    1 => {
//                        let x = BinderInfo::get(buf)?;
//                        Ok(Self::Info(x))
//                    }
//                    2 => {
//                        let x = Address::get(buf)?;
//                        Ok(Self::Link(x))
//                    }
//                    3 => {
//                        let x = ReducibilityHints::get(buf)?;
//                        Ok(Self::Hints(x))
//                    }
//                    4 => {
//                        let x = Serialize::get(buf)?;
//                        Ok(Self::All(x))
//                    }
//                    5 => {
//                        let x = Serialize::get(buf)?;
//                        Ok(Self::MutCtx(x))
//                    }
//                    x => Err(format!("get Metadata invalid {x}")),
//                }
//            }
//            None => Err("get Metadata EOF".to_string()),
//        }
//    }
//}

//impl Serialize for Metadata {
//    fn put(&self, buf: &mut Vec<u8>) {
//        Serialize::put(&self.map, buf)
//    }
//
//    fn get(buf: &mut &[u8]) -> Result<Self, String> {
//        Ok(Metadata {
//            map: Serialize::get(buf)?,
//        })
//    }
//}
//
//#[cfg(test)]
//mod tests {
//    use super::*;
//    use crate::ixon::tests::{gen_range, gen_vec};
//    use quickcheck::{Arbitrary, Gen};
//
//    impl Arbitrary for BinderInfo {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..4);
//            match x {
//                0 => Self::Default,
//                1 => Self::Implicit,
//                2 => Self::StrictImplicit,
//                3 => Self::InstImplicit,
//                _ => Self::AuxDecl,
//            }
//        }
//    }
//
//    impl Arbitrary for ReducibilityHints {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..2);
//            match x {
//                0 => Self::Opaque,
//                1 => Self::Abbrev,
//                _ => Self::Regular(Arbitrary::arbitrary(g)),
//            }
//        }
//    }
//
//    impl Arbitrary for Metadatum {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..5);
//            match x {
//                0 => Self::Name(Name::arbitrary(g)),
//                1 => Self::Info(BinderInfo::arbitrary(g)),
//                2 => Self::Link(Address::arbitrary(g)),
//                3 => Self::Hints(ReducibilityHints::arbitrary(g)),
//                4 => Self::All(gen_vec(g, 9, Arbitrary::arbitrary)),
//                _ => {
//                    let x = gen_range(g, 0..9);
//                    let mut res = vec![];
//                    for _ in 0..x {
//                        res.push(gen_vec(g, 9, Arbitrary::arbitrary))
//                    }
//                    Self::MutCtx(res)
//                }
//            }
//        }
//    }
//
//    impl Arbitrary for Metadata {
//        fn arbitrary(g: &mut Gen) -> Self {
//            let x = gen_range(g, 0..9);
//            let mut map = Vec::new();
//            for _ in 0..x {
//                map.push((Nat::arbitrary(g), gen_vec(g, 9, Metadatum::arbitrary)));
//            }
//            Metadata { map }
//        }
//    }
//}
