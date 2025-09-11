use crate::ixon::address::Address;
use crate::ixon::nat::Nat;
use crate::ixon::serialize::Serialize;
use crate::ixon::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Quotient {
    pub kind: QuotKind,
    pub lvls: Nat,
    pub typ: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axiom {
    pub is_unsafe: bool,
    pub lvls: Nat,
    pub typ: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefKind {
    Definition,
    Opaque,
    Theorem,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefSafety {
    Unsafe,
    Safe,
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub kind: DefKind,
    pub safety: DefSafety,
    pub lvls: Nat,
    pub typ: Address,
    pub value: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub is_unsafe: bool,
    pub lvls: Nat,
    pub cidx: Nat,
    pub params: Nat,
    pub fields: Nat,
    pub typ: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorRule {
    pub fields: Nat,
    pub rhs: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Recursor {
    pub k: bool,
    pub is_unsafe: bool,
    pub lvls: Nat,
    pub params: Nat,
    pub indices: Nat,
    pub motives: Nat,
    pub minors: Nat,
    pub typ: Address,
    pub rules: Vec<RecursorRule>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inductive {
    pub recr: bool,
    pub refl: bool,
    pub is_unsafe: bool,
    pub lvls: Nat,
    pub params: Nat,
    pub indices: Nat,
    pub nested: Nat,
    pub typ: Address,
    pub ctors: Vec<Constructor>,
    pub recrs: Vec<Recursor>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorProj {
    pub idx: Nat,
    pub cidx: Nat,
    pub block: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorProj {
    pub idx: Nat,
    pub ridx: Nat,
    pub block: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveProj {
    pub idx: Nat,
    pub block: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionProj {
    pub idx: Nat,
    pub block: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comm {
    pub secret: Address,
    pub payload: Address,
}

impl Serialize for QuotKind {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Type => buf.push(0),
            Self::Ctor => buf.push(1),
            Self::Lift => buf.push(2),
            Self::Ind => buf.push(3),
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Type),
                    1 => Ok(Self::Ctor),
                    2 => Ok(Self::Lift),
                    3 => Ok(Self::Ind),
                    x => Err(format!("get QuotKind invalid {x}")),
                }
            }
            None => Err("get QuotKind EOF".to_string()),
        }
    }
}

impl Serialize for Quotient {
    fn put(&self, buf: &mut Vec<u8>) {
        self.kind.put(buf);
        self.lvls.put(buf);
        self.typ.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let kind = QuotKind::get(buf)?;
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        Ok(Quotient { kind, lvls, typ })
    }
}

impl Serialize for Axiom {
    fn put(&self, buf: &mut Vec<u8>) {
        self.is_unsafe.put(buf);
        self.lvls.put(buf);
        self.typ.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let is_unsafe = bool::get(buf)?;
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        Ok(Axiom {
            lvls,
            typ,
            is_unsafe,
        })
    }
}

impl Serialize for DefKind {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Definition => buf.push(0),
            Self::Opaque => buf.push(1),
            Self::Theorem => buf.push(2),
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Definition),
                    1 => Ok(Self::Opaque),
                    2 => Ok(Self::Theorem),
                    x => Err(format!("get DefKind invalid {x}")),
                }
            }
            None => Err("get DefKind EOF".to_string()),
        }
    }
}

impl Serialize for DefSafety {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Unsafe => buf.push(0),
            Self::Safe => buf.push(1),
            Self::Partial => buf.push(2),
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Unsafe),
                    1 => Ok(Self::Safe),
                    2 => Ok(Self::Partial),
                    x => Err(format!("get DefSafety invalid {x}")),
                }
            }
            None => Err("get DefSafety EOF".to_string()),
        }
    }
}

impl Serialize for Definition {
    fn put(&self, buf: &mut Vec<u8>) {
        self.kind.put(buf);
        self.safety.put(buf);
        self.lvls.put(buf);
        self.typ.put(buf);
        self.value.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let kind = DefKind::get(buf)?;
        let safety = DefSafety::get(buf)?;
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let value = Address::get(buf)?;
        Ok(Definition {
            kind,
            safety,
            lvls,
            typ,
            value,
        })
    }
}

impl Serialize for Constructor {
    fn put(&self, buf: &mut Vec<u8>) {
        self.is_unsafe.put(buf);
        self.lvls.put(buf);
        self.cidx.put(buf);
        self.params.put(buf);
        self.fields.put(buf);
        self.typ.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let is_unsafe = bool::get(buf)?;
        let lvls = Nat::get(buf)?;
        let cidx = Nat::get(buf)?;
        let params = Nat::get(buf)?;
        let fields = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        Ok(Constructor {
            lvls,
            typ,
            cidx,
            params,
            fields,
            is_unsafe,
        })
    }
}

impl Serialize for RecursorRule {
    fn put(&self, buf: &mut Vec<u8>) {
        self.fields.put(buf);
        self.rhs.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let fields = Nat::get(buf)?;
        let rhs = Address::get(buf)?;
        Ok(RecursorRule { fields, rhs })
    }
}

impl Serialize for Recursor {
    fn put(&self, buf: &mut Vec<u8>) {
        Ixon::pack_bools(vec![self.k, self.is_unsafe]).put(buf);
        self.lvls.put(buf);
        self.params.put(buf);
        self.indices.put(buf);
        self.motives.put(buf);
        self.minors.put(buf);
        self.typ.put(buf);
        self.rules.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let bools = Ixon::unpack_bools(2, u8::get(buf)?);
        let lvls = Nat::get(buf)?;
        let params = Nat::get(buf)?;
        let indices = Nat::get(buf)?;
        let motives = Nat::get(buf)?;
        let minors = Nat::get(buf)?;
        let typ = Serialize::get(buf)?;
        let rules = Serialize::get(buf)?;
        Ok(Recursor {
            lvls,
            typ,
            params,
            indices,
            motives,
            minors,
            rules,
            k: bools[0],
            is_unsafe: bools[1],
        })
    }
}

impl Serialize for Inductive {
    fn put(&self, buf: &mut Vec<u8>) {
        Ixon::pack_bools(vec![self.recr, self.refl, self.is_unsafe]).put(buf);
        self.lvls.put(buf);
        self.params.put(buf);
        self.indices.put(buf);
        self.nested.put(buf);
        self.typ.put(buf);
        Serialize::put(&self.ctors, buf);
        Serialize::put(&self.recrs, buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let bools = Ixon::unpack_bools(3, u8::get(buf)?);
        let lvls = Nat::get(buf)?;
        let params = Nat::get(buf)?;
        let indices = Nat::get(buf)?;
        let nested = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let ctors = Serialize::get(buf)?;
        let recrs = Serialize::get(buf)?;
        Ok(Inductive {
            recr: bools[0],
            refl: bools[1],
            is_unsafe: bools[2],
            lvls,
            params,
            indices,
            nested,
            typ,
            ctors,
            recrs,
        })
    }
}

impl Serialize for InductiveProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.idx.put(buf);
        self.block.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let idx = Nat::get(buf)?;
        let block = Address::get(buf)?;
        Ok(InductiveProj { idx, block })
    }
}

impl Serialize for ConstructorProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.idx.put(buf);
        self.cidx.put(buf);
        self.block.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let idx = Nat::get(buf)?;
        let cidx = Nat::get(buf)?;
        let block = Address::get(buf)?;
        Ok(ConstructorProj { idx, cidx, block })
    }
}

impl Serialize for RecursorProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.idx.put(buf);
        self.ridx.put(buf);
        self.block.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let idx = Nat::get(buf)?;
        let ridx = Nat::get(buf)?;
        let block = Address::get(buf)?;
        Ok(RecursorProj { idx, ridx, block })
    }
}

impl Serialize for DefinitionProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.idx.put(buf);
        self.block.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let idx = Nat::get(buf)?;
        let block = Address::get(buf)?;
        Ok(DefinitionProj { idx, block })
    }
}

impl Serialize for Comm {
    fn put(&self, buf: &mut Vec<u8>) {
        self.secret.put(buf);
        self.payload.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let secret = Address::get(buf)?;
        let payload = Address::get(buf)?;
        Ok(Comm { secret, payload })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ixon::tests::gen_range;
    use quickcheck::{Arbitrary, Gen};

    use std::ptr;

    impl Arbitrary for QuotKind {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..3);
            match x {
                0 => Self::Type,
                1 => Self::Ctor,
                2 => Self::Lift,
                _ => Self::Ind,
            }
        }
    }

    impl Arbitrary for Quotient {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                kind: QuotKind::arbitrary(g),
            }
        }
    }

    impl Arbitrary for Axiom {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                is_unsafe: bool::arbitrary(g),
            }
        }
    }

    impl Arbitrary for DefKind {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..2);
            match x {
                0 => Self::Definition,
                1 => Self::Opaque,
                _ => Self::Theorem,
            }
        }
    }

    impl Arbitrary for DefSafety {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..2);
            match x {
                0 => Self::Unsafe,
                1 => Self::Safe,
                _ => Self::Partial,
            }
        }
    }

    impl Arbitrary for Definition {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                kind: DefKind::arbitrary(g),
                safety: DefSafety::arbitrary(g),
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                value: Address::arbitrary(g),
            }
        }
    }

    impl Arbitrary for Constructor {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                cidx: Nat::arbitrary(g),
                params: Nat::arbitrary(g),
                fields: Nat::arbitrary(g),
                is_unsafe: bool::arbitrary(g),
            }
        }
    }

    impl Arbitrary for RecursorRule {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                fields: Nat::arbitrary(g),
                rhs: Address::arbitrary(g),
            }
        }
    }

    impl Arbitrary for Recursor {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..9);
            let mut rules = vec![];
            for _ in 0..x {
                rules.push(RecursorRule::arbitrary(g));
            }
            Self {
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                params: Nat::arbitrary(g),
                indices: Nat::arbitrary(g),
                motives: Nat::arbitrary(g),
                minors: Nat::arbitrary(g),
                rules,
                k: bool::arbitrary(g),
                is_unsafe: bool::arbitrary(g),
            }
        }
    }

    impl Arbitrary for Inductive {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..9);
            let y = gen_range(g, 0..9);
            let mut ctors = vec![];
            let mut recrs = vec![];
            for _ in 0..x {
                ctors.push(Constructor::arbitrary(g));
            }
            for _ in 0..y {
                recrs.push(Recursor::arbitrary(g));
            }
            Self {
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                params: Nat::arbitrary(g),
                indices: Nat::arbitrary(g),
                ctors,
                recrs,
                nested: Nat::arbitrary(g),
                recr: bool::arbitrary(g),
                refl: bool::arbitrary(g),
                is_unsafe: bool::arbitrary(g),
            }
        }
    }

    impl Arbitrary for InductiveProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
            }
        }
    }

    impl Arbitrary for ConstructorProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
                cidx: Nat::arbitrary(g),
            }
        }
    }

    impl Arbitrary for RecursorProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
                ridx: Nat::arbitrary(g),
            }
        }
    }

    impl Arbitrary for DefinitionProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
            }
        }
    }

    impl Arbitrary for Comm {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                secret: Address::arbitrary(g),
                payload: Address::arbitrary(g),
            }
        }
    }
}
