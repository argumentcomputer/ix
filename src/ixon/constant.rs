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
    pub lvls: Nat,
    pub typ: Address,
    pub kind: QuotKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axiom {
    pub lvls: Nat,
    pub typ: Address,
    pub is_unsafe: bool,
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
    pub lvls: Nat,
    pub typ: Address,
    pub mode: DefKind,
    pub value: Address,
    pub safety: DefSafety,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub lvls: Nat,
    pub typ: Address,
    pub cidx: Nat,
    pub params: Nat,
    pub fields: Nat,
    pub is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorRule {
    pub fields: Nat,
    pub rhs: Address,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Recursor {
    pub lvls: Nat,
    pub typ: Address,
    pub params: Nat,
    pub indices: Nat,
    pub motives: Nat,
    pub minors: Nat,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inductive {
    pub lvls: Nat,
    pub typ: Address,
    pub params: Nat,
    pub indices: Nat,
    pub ctors: Vec<Constructor>,
    pub recrs: Vec<Recursor>,
    pub nested: Nat,
    pub recr: bool,
    pub refl: bool,
    pub is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveProj {
    pub block: Address,
    pub idx: Nat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorProj {
    pub block: Address,
    pub idx: Nat,
    pub cidx: Nat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorProj {
    pub block: Address,
    pub idx: Nat,
    pub ridx: Nat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionProj {
    pub block: Address,
    pub idx: Nat,
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
        self.lvls.put(buf);
        self.typ.put(buf);
        self.kind.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let kind = QuotKind::get(buf)?;
        Ok(Quotient { lvls, typ, kind })
    }
}

impl Serialize for Axiom {
    fn put(&self, buf: &mut Vec<u8>) {
        self.lvls.put(buf);
        self.typ.put(buf);
        self.is_unsafe.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let is_unsafe = bool::get(buf)?;
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
        self.lvls.put(buf);
        self.typ.put(buf);
        self.mode.put(buf);
        self.value.put(buf);
        self.safety.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let mode = DefKind::get(buf)?;
        let value = Address::get(buf)?;
        let safety = DefSafety::get(buf)?;
        Ok(Definition {
            lvls,
            typ,
            mode,
            value,
            safety,
        })
    }
}

impl Serialize for Constructor {
    fn put(&self, buf: &mut Vec<u8>) {
        self.lvls.put(buf);
        self.typ.put(buf);
        self.cidx.put(buf);
        self.params.put(buf);
        self.fields.put(buf);
        self.is_unsafe.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let cidx = Nat::get(buf)?;
        let params = Nat::get(buf)?;
        let fields = Nat::get(buf)?;
        let is_unsafe = bool::get(buf)?;
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
        self.lvls.put(buf);
        self.typ.put(buf);
        self.params.put(buf);
        self.indices.put(buf);
        self.motives.put(buf);
        self.minors.put(buf);
        self.rules.put(buf);
        Ixon::pack_bools(vec![self.k, self.is_unsafe]).put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Nat::get(buf)?;
        let typ = Serialize::get(buf)?;
        let params = Nat::get(buf)?;
        let indices = Nat::get(buf)?;
        let motives = Nat::get(buf)?;
        let minors = Nat::get(buf)?;
        let rules = Serialize::get(buf)?;
        let bools = Ixon::unpack_bools(2, u8::get(buf)?);
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
        self.lvls.put(buf);
        self.typ.put(buf);
        self.params.put(buf);
        self.indices.put(buf);
        Serialize::put(&self.ctors, buf);
        Serialize::put(&self.recrs, buf);
        self.nested.put(buf);
        Ixon::pack_bools(vec![self.recr, self.refl, self.is_unsafe]).put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let params = Nat::get(buf)?;
        let indices = Nat::get(buf)?;
        let ctors = Serialize::get(buf)?;
        let recrs = Serialize::get(buf)?;
        let nested = Nat::get(buf)?;
        let bools = Ixon::unpack_bools(3, u8::get(buf)?);
        Ok(Inductive {
            lvls,
            typ,
            params,
            indices,
            ctors,
            recrs,
            nested,
            recr: bools[0],
            refl: bools[1],
            is_unsafe: bools[2],
        })
    }
}

impl Serialize for InductiveProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.block.put(buf);
        self.idx.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let block = Address::get(buf)?;
        let idx = Nat::get(buf)?;
        Ok(InductiveProj { block, idx })
    }
}

impl Serialize for ConstructorProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.block.put(buf);
        self.idx.put(buf);
        self.cidx.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let block = Address::get(buf)?;
        let idx = Nat::get(buf)?;
        let cidx = Nat::get(buf)?;
        Ok(ConstructorProj { block, idx, cidx })
    }
}

impl Serialize for RecursorProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.block.put(buf);
        self.idx.put(buf);
        self.ridx.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let block = Address::get(buf)?;
        let idx = Nat::get(buf)?;
        let ridx = Nat::get(buf)?;
        Ok(RecursorProj { block, idx, ridx })
    }
}

impl Serialize for DefinitionProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.block.put(buf);
        self.idx.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let block = Address::get(buf)?;
        let idx = Nat::get(buf)?;
        Ok(DefinitionProj { block, idx })
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
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                mode: DefKind::arbitrary(g),
                value: Address::arbitrary(g),
                safety: DefSafety::arbitrary(g),
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
