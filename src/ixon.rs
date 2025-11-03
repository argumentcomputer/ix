use blake3::Hash;
use num_bigint::BigUint;

use crate::{
    lean::nat::*,
    lean_env::{BinderInfo, DefinitionSafety, Int, QuotKind, ReducibilityHints},
};

pub mod address;

use address::*;

pub trait Serialize: Sized {
    fn put(&self, buf: &mut Vec<u8>);
    fn get(buf: &mut &[u8]) -> Result<Self, String>;
}

impl Serialize for u8 {
    fn put(&self, buf: &mut Vec<u8>) {
        buf.push(*self)
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_first() {
            Some((&x, rest)) => {
                *buf = rest;
                Ok(x)
            }
            None => Err("get u8 EOF".to_string()),
        }
    }
}

impl Serialize for u16 {
    fn put(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(2) {
            Some((head, rest)) => {
                *buf = rest;
                Ok(u16::from_le_bytes([head[0], head[1]]))
            }
            None => Err("get u16 EOF".to_string()),
        }
    }
}

impl Serialize for u32 {
    fn put(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(4) {
            Some((head, rest)) => {
                *buf = rest;
                Ok(u32::from_le_bytes([head[0], head[1], head[2], head[3]]))
            }
            None => Err("get u32 EOF".to_string()),
        }
    }
}

impl Serialize for u64 {
    fn put(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(8) {
            Some((head, rest)) => {
                *buf = rest;
                Ok(u64::from_le_bytes([
                    head[0], head[1], head[2], head[3], head[4], head[5], head[6], head[7],
                ]))
            }
            None => Err("get u64 EOF".to_string()),
        }
    }
}

impl Serialize for bool {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            false => buf.push(0),
            true => buf.push(1),
        }
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(false),
                    1 => Ok(true),
                    x => Err(format!("get bool invalid {x}")),
                }
            }
            None => Err("get bool EOF".to_string()),
        }
    }
}

pub fn u64_byte_count(x: u64) -> u8 {
    match x {
        0 => 0,
        x if x < 0x0000000000000100 => 1,
        x if x < 0x0000000000010000 => 2,
        x if x < 0x0000000001000000 => 3,
        x if x < 0x0000000100000000 => 4,
        x if x < 0x0000010000000000 => 5,
        x if x < 0x0001000000000000 => 6,
        x if x < 0x0100000000000000 => 7,
        _ => 8,
    }
}

pub fn u64_put_trimmed_le(x: u64, buf: &mut Vec<u8>) {
    let n = u64_byte_count(x) as usize;
    buf.extend_from_slice(&x.to_le_bytes()[..n])
}

pub fn u64_get_trimmed_le(len: usize, buf: &mut &[u8]) -> Result<u64, String> {
    let mut res = [0u8; 8];
    if len > 8 {
        return Err("get trimmed_le_64 len > 8".to_string());
    }
    match buf.split_at_checked(len) {
        Some((head, rest)) => {
            *buf = rest;
            res[..len].copy_from_slice(head);
            Ok(u64::from_le_bytes(res))
        }
        None => Err(format!("get trimmed_le_u64 EOF {len} {buf:?}")),
    }
}

//  F := flag, L := large-bit, X := small-field, A := large_field
// 0xFFFF_LXXX {AAAA_AAAA, ...}
// "Tag" means the whole thing
// "Head" means the first byte of the tag
// "Flag" means the first nibble of the head
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag4 {
    flag: u8,
    size: u64,
}

impl Tag4 {
    #[allow(clippy::cast_possible_truncation)]
    pub fn encode_head(&self) -> u8 {
        if self.size < 8 {
            (self.flag << 4) + (self.size as u8)
        } else {
            (self.flag << 4) + 0b1000 + (u64_byte_count(self.size) - 1)
        }
    }
    pub fn decode_head(head: u8) -> (u8, bool, u8) {
        (head >> 4, head & 0b1000 != 0, head % 0b1000)
    }
}

impl Serialize for Tag4 {
    fn put(&self, buf: &mut Vec<u8>) {
        self.encode_head().put(buf);
        if self.size >= 8 {
            u64_put_trimmed_le(self.size, buf)
        }
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let head = u8::get(buf)?;
        let (flag, large, small) = Tag4::decode_head(head);
        let size = if large {
            u64_get_trimmed_le((small + 1) as usize, buf)?
        } else {
            small as u64
        };
        Ok(Tag4 { flag, size })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteArray(pub Vec<u8>);

impl ByteArray {
    fn put_slice(slice: &[u8], buf: &mut Vec<u8>) {
        Tag4 {
            flag: 0x9,
            size: slice.len() as u64,
        }
        .put(buf);
        buf.extend_from_slice(slice);
    }
}

impl Serialize for ByteArray {
    fn put(&self, buf: &mut Vec<u8>) {
        Self::put_slice(&self.0, buf);
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let tag = Tag4::get(buf)?;
        match tag {
            Tag4 { flag: 0x9, size } => {
                let mut res = vec![];
                for _ in 0..size {
                    res.push(u8::get(buf)?)
                }
                Ok(ByteArray(res))
            }
            _ => Err("expected Tag4 0x9 for Vec<u8>".to_string()),
        }
    }
}

impl Serialize for String {
    fn put(&self, buf: &mut Vec<u8>) {
        let bytes = self.as_bytes();
        Tag4 {
            flag: 0x9,
            size: bytes.len() as u64,
        }
        .put(buf);
        buf.extend_from_slice(bytes);
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let bytes = ByteArray::get(buf)?;
        String::from_utf8(bytes.0).map_err(|e| format!("Invalid UTF-8: {e}"))
    }
}

impl Serialize for Nat {
    fn put(&self, buf: &mut Vec<u8>) {
        let bytes = self.to_le_bytes();
        Tag4 {
            flag: 0x9,
            size: bytes.len() as u64,
        }
        .put(buf);
        buf.extend_from_slice(&bytes);
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let bytes = ByteArray::get(buf)?;
        Ok(Nat::from_le_bytes(&bytes.0))
    }
}

impl Serialize for Int {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::OfNat(x) => {
                buf.push(0);
                x.put(buf);
            }
            Self::NegSucc(x) => {
                buf.push(1);
                x.put(buf);
            }
        }
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::OfNat(Nat::get(buf)?)),
                    1 => Ok(Self::NegSucc(Nat::get(buf)?)),
                    x => Err(format!("get Int invalid {x}")),
                }
            }
            None => Err("get Int EOF".to_string()),
        }
    }
}

impl<S: Serialize> Serialize for Vec<S> {
    fn put(&self, buf: &mut Vec<u8>) {
        Nat(BigUint::from(self.len())).put(buf);
        for x in self {
            x.put(buf)
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let mut res = vec![];
        let len = Nat::get(buf)?.0;
        let mut i = BigUint::from(0u32);
        while i < len {
            res.push(S::get(buf)?);
            i += 1u32;
        }
        Ok(res)
    }
}

#[allow(clippy::cast_possible_truncation)]
pub fn pack_bools<I>(bools: I) -> u8
where
    I: IntoIterator<Item = bool>,
{
    let mut acc: u8 = 0;
    for (i, b) in bools.into_iter().take(8).enumerate() {
        if b {
            acc |= 1u8 << (i as u32);
        }
    }
    acc
}

pub fn unpack_bools(n: usize, b: u8) -> Vec<bool> {
    (0..8)
        .map(|i: u32| (b & (1u8 << i)) != 0)
        .take(n.min(8))
        .collect()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefKind {
    Definition,
    Opaque,
    Theorem,
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

impl Serialize for BinderInfo {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Default => buf.push(0),
            Self::Implicit => buf.push(1),
            Self::StrictImplicit => buf.push(2),
            Self::InstImplicit => buf.push(3),
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Default),
                    1 => Ok(Self::Implicit),
                    2 => Ok(Self::StrictImplicit),
                    3 => Ok(Self::InstImplicit),
                    x => Err(format!("get BinderInfo invalid {x}")),
                }
            }
            None => Err("get BinderInfo EOF".to_string()),
        }
    }
}

impl Serialize for ReducibilityHints {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Opaque => buf.push(0),
            Self::Abbrev => buf.push(1),
            Self::Regular(x) => {
                buf.push(2);
                x.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Opaque),
                    1 => Ok(Self::Abbrev),
                    2 => {
                        let x: u32 = Serialize::get(buf)?;
                        Ok(Self::Regular(x))
                    }
                    x => Err(format!("get ReducibilityHints invalid {x}")),
                }
            }
            None => Err("get ReducibilityHints EOF".to_string()),
        }
    }
}

impl Serialize for DefinitionSafety {
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

impl<A: Serialize, B: Serialize> Serialize for (A, B) {
    fn put(&self, buf: &mut Vec<u8>) {
        self.0.put(buf);
        self.1.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        Ok((A::get(buf)?, B::get(buf)?))
    }
}

impl Serialize for Address {
    fn put(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.hash.as_bytes())
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(32) {
            Some((head, rest)) => {
                *buf = rest;
                Ok(Address {
                    hash: Hash::from_slice(head).unwrap(),
                })
            }
            None => Err("get Address out of input".to_string()),
        }
    }
}

impl Serialize for MetaAddress {
    fn put(&self, buf: &mut Vec<u8>) {
        self.data.put(buf);
        self.meta.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let data = Address::get(buf)?;
        let meta = Address::get(buf)?;
        Ok(MetaAddress { data, meta })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Quotient {
    pub kind: QuotKind,
    pub lvls: Nat,
    pub typ: Address,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axiom {
    pub is_unsafe: bool,
    pub lvls: Nat,
    pub typ: Address,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub kind: DefKind,
    pub safety: DefinitionSafety,
    pub lvls: Nat,
    pub typ: Address,
    pub value: Address,
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
        let safety = DefinitionSafety::get(buf)?;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub is_unsafe: bool,
    pub lvls: Nat,
    pub cidx: Nat,
    pub params: Nat,
    pub fields: Nat,
    pub typ: Address,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorRule {
    pub fields: Nat,
    pub rhs: Address,
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

impl Serialize for Recursor {
    fn put(&self, buf: &mut Vec<u8>) {
        pack_bools(vec![self.k, self.is_unsafe]).put(buf);
        self.lvls.put(buf);
        self.params.put(buf);
        self.indices.put(buf);
        self.motives.put(buf);
        self.minors.put(buf);
        self.typ.put(buf);
        self.rules.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let bools = unpack_bools(2, u8::get(buf)?);
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
}

impl Serialize for Inductive {
    fn put(&self, buf: &mut Vec<u8>) {
        pack_bools(vec![self.recr, self.refl, self.is_unsafe]).put(buf);
        self.lvls.put(buf);
        self.params.put(buf);
        self.indices.put(buf);
        self.nested.put(buf);
        self.typ.put(buf);
        Serialize::put(&self.ctors, buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let bools = unpack_bools(3, u8::get(buf)?);
        let lvls = Nat::get(buf)?;
        let params = Nat::get(buf)?;
        let indices = Nat::get(buf)?;
        let nested = Nat::get(buf)?;
        let typ = Address::get(buf)?;
        let ctors = Serialize::get(buf)?;
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
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveProj {
    pub idx: Nat,
    pub block: Address,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorProj {
    pub idx: Nat,
    pub cidx: Nat,
    pub block: Address,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorProj {
    pub idx: Nat,
    pub block: Address,
}

impl Serialize for RecursorProj {
    fn put(&self, buf: &mut Vec<u8>) {
        self.idx.put(buf);
        self.block.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let idx = Nat::get(buf)?;
        let block = Address::get(buf)?;
        Ok(RecursorProj { idx, block })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionProj {
    pub idx: Nat,
    pub block: Address,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comm {
    pub secret: Address,
    pub payload: Address,
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalClaim {
    pub lvls: Address,
    pub typ: Address,
    pub input: Address,
    pub output: Address,
}

impl Serialize for EvalClaim {
    fn put(&self, buf: &mut Vec<u8>) {
        self.lvls.put(buf);
        self.typ.put(buf);
        self.input.put(buf);
        self.output.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Address::get(buf)?;
        let typ = Address::get(buf)?;
        let input = Address::get(buf)?;
        let output = Address::get(buf)?;
        Ok(Self {
            lvls,
            typ,
            input,
            output,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckClaim {
    pub lvls: Address,
    pub typ: Address,
    pub value: Address,
}

impl Serialize for CheckClaim {
    fn put(&self, buf: &mut Vec<u8>) {
        self.lvls.put(buf);
        self.typ.put(buf);
        self.value.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let lvls = Address::get(buf)?;
        let typ = Address::get(buf)?;
        let value = Address::get(buf)?;
        Ok(Self { lvls, typ, value })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Claim {
    Evals(EvalClaim),
    Checks(CheckClaim),
}

impl Serialize for Claim {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Evals(x) => {
                u8::put(&0xE1, buf);
                x.put(buf)
            }
            Self::Checks(x) => {
                u8::put(&0xE2, buf);
                x.put(buf)
            }
        }
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0xE1 => {
                        let x = EvalClaim::get(buf)?;
                        Ok(Self::Evals(x))
                    }
                    0xE2 => {
                        let x = CheckClaim::get(buf)?;
                        Ok(Self::Checks(x))
                    }
                    x => Err(format!("get Claim invalid {x}")),
                }
            }
            None => Err("get Claim EOF".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    pub claim: Claim,
    pub proof: Vec<u8>,
}

impl Serialize for Proof {
    fn put(&self, buf: &mut Vec<u8>) {
        self.claim.put(buf);
        ByteArray::put_slice(&self.proof, buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let claim = Claim::get(buf)?;
        let ByteArray(proof) = ByteArray::get(buf)?;
        Ok(Proof { claim, proof })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env {
    pub env: Vec<MetaAddress>,
}

impl Serialize for Env {
    fn put(&self, buf: &mut Vec<u8>) {
        self.env.put(buf)
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        Ok(Env {
            env: Serialize::get(buf)?,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substring {
    pub str: Address,
    pub start_pos: Nat,
    pub stop_pos: Nat,
}

impl Serialize for Substring {
    fn put(&self, buf: &mut Vec<u8>) {
        self.str.put(buf);
        self.start_pos.put(buf);
        self.stop_pos.put(buf);
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let str = Address::get(buf)?;
        let start_pos = Nat::get(buf)?;
        let stop_pos = Nat::get(buf)?;
        Ok(Substring {
            str,
            start_pos,
            stop_pos,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceInfo {
    Original(Substring, Nat, Substring, Nat),
    Synthetic(Nat, Nat, bool),
    None,
}

impl Serialize for SourceInfo {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Original(l, p, t, e) => {
                buf.push(0);
                l.put(buf);
                p.put(buf);
                t.put(buf);
                e.put(buf);
            }
            Self::Synthetic(p, e, c) => {
                buf.push(1);
                p.put(buf);
                e.put(buf);
                c.put(buf);
            }
            Self::None => {
                buf.push(2);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Original(
                        Substring::get(buf)?,
                        Nat::get(buf)?,
                        Substring::get(buf)?,
                        Nat::get(buf)?,
                    )),
                    1 => Ok(Self::Synthetic(
                        Nat::get(buf)?,
                        Nat::get(buf)?,
                        bool::get(buf)?,
                    )),
                    2 => Ok(Self::None),
                    x => Err(format!("get SourcInfo invalid {x}")),
                }
            }
            None => Err("get SourceInfo EOF".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Preresolved {
    Namespace(Address),
    Decl(Address, Vec<Address>),
}

impl Serialize for Preresolved {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Namespace(ns) => {
                buf.push(0);
                ns.put(buf);
            }
            Self::Decl(n, fields) => {
                buf.push(1);
                n.put(buf);
                fields.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Namespace(Address::get(buf)?)),
                    1 => Ok(Self::Decl(Address::get(buf)?, Vec::<Address>::get(buf)?)),
                    x => Err(format!("get Preresolved invalid {x}")),
                }
            }
            None => Err("get Preresolved EOF".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Syntax {
    Missing,
    Node(SourceInfo, Address, Vec<Address>),
    Atom(SourceInfo, Address),
    Ident(SourceInfo, Substring, Address, Vec<Preresolved>),
}

impl Serialize for Syntax {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Missing => {
                buf.push(0);
            }
            Self::Node(i, k, xs) => {
                buf.push(1);
                i.put(buf);
                k.put(buf);
                xs.put(buf);
            }
            Self::Atom(i, v) => {
                buf.push(2);
                i.put(buf);
                v.put(buf);
            }
            Self::Ident(i, r, v, ps) => {
                buf.push(3);
                i.put(buf);
                r.put(buf);
                v.put(buf);
                ps.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Missing),
                    1 => Ok(Self::Node(
                        SourceInfo::get(buf)?,
                        Address::get(buf)?,
                        Vec::<Address>::get(buf)?,
                    )),
                    2 => Ok(Self::Atom(SourceInfo::get(buf)?, Address::get(buf)?)),
                    3 => Ok(Self::Ident(
                        SourceInfo::get(buf)?,
                        Substring::get(buf)?,
                        Address::get(buf)?,
                        Vec::<Preresolved>::get(buf)?,
                    )),
                    x => Err(format!("get Syntax invalid {x}")),
                }
            }
            None => Err("get Syntax EOF".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutConst {
    Defn(Definition),
    Indc(Inductive),
    Recr(Recursor),
}

impl Serialize for MutConst {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Defn(x) => {
                buf.push(0);
                x.put(buf);
            }
            Self::Indc(x) => {
                buf.push(1);
                x.put(buf);
            }
            Self::Recr(x) => {
                buf.push(2);
                x.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Defn(Definition::get(buf)?)),
                    1 => Ok(Self::Indc(Inductive::get(buf)?)),
                    2 => Ok(Self::Recr(Recursor::get(buf)?)),
                    x => Err(format!("get MutConst invalid {x}")),
                }
            }
            None => Err("get MutConst EOF".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltIn {
    Obj,
    Neutral,
    Unreachable,
}

impl Serialize for BuiltIn {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Obj => buf.push(0),
            Self::Neutral => buf.push(1),
            Self::Unreachable => buf.push(2),
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Obj),
                    1 => Ok(Self::Neutral),
                    2 => Ok(Self::Unreachable),
                    x => Err(format!("get BuiltIn invalid {x}")),
                }
            }
            None => Err("get BuiltIn EOF".to_string()),
        }
    }
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

impl Serialize for DataValue {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::OfString(x) => {
                buf.push(0);
                x.put(buf);
            }
            Self::OfBool(x) => {
                buf.push(1);
                x.put(buf);
            }
            Self::OfName(x) => {
                buf.push(2);
                x.put(buf);
            }
            Self::OfNat(x) => {
                buf.push(3);
                x.put(buf);
            }
            Self::OfInt(x) => {
                buf.push(4);
                x.put(buf);
            }
            Self::OfSyntax(x) => {
                buf.push(5);
                x.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::OfString(Address::get(buf)?)),
                    1 => Ok(Self::OfBool(bool::get(buf)?)),
                    2 => Ok(Self::OfName(Address::get(buf)?)),
                    3 => Ok(Self::OfNat(Address::get(buf)?)),
                    4 => Ok(Self::OfInt(Address::get(buf)?)),
                    5 => Ok(Self::OfSyntax(Address::get(buf)?)),
                    x => Err(format!("get DataValue invalid {x}")),
                }
            }
            None => Err("get DataValue EOF".to_string()),
        }
    }
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

impl Serialize for Metadatum {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Link(x) => {
                buf.push(0);
                x.put(buf);
            }
            Self::Info(x) => {
                buf.push(1);
                x.put(buf);
            }
            Self::Hints(x) => {
                buf.push(2);
                x.put(buf);
            }
            Self::Links(x) => {
                buf.push(3);
                x.put(buf);
            }
            Self::Map(x) => {
                buf.push(4);
                x.put(buf);
            }
            Self::KVMap(x) => {
                buf.push(5);
                x.put(buf);
            }
            Self::Muts(x) => {
                buf.push(6);
                x.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        match buf.split_at_checked(1) {
            Some((head, rest)) => {
                *buf = rest;
                match head[0] {
                    0 => Ok(Self::Link(Address::get(buf)?)),
                    1 => Ok(Self::Info(BinderInfo::get(buf)?)),
                    2 => Ok(Self::Hints(ReducibilityHints::get(buf)?)),
                    3 => Ok(Self::Links(Vec::<Address>::get(buf)?)),
                    4 => Ok(Self::Map(Vec::<(Address, Address)>::get(buf)?)),
                    5 => Ok(Self::KVMap(Vec::<(Address, DataValue)>::get(buf)?)),
                    6 => Ok(Self::Muts(Vec::<Vec<Address>>::get(buf)?)),
                    x => Err(format!("get Metadatum invalid {x}")),
                }
            }
            None => Err("get Metadatum EOF".to_string()),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Metadata {
    pub nodes: Vec<Metadatum>,
}

impl Serialize for Metadata {
    fn put(&self, buf: &mut Vec<u8>) {
        Tag4 {
            flag: 0xF,
            size: self.nodes.len() as u64,
        }
        .put(buf);
        for n in self.nodes.iter() {
            n.put(buf)
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let tag = Tag4::get(buf)?;
        match tag {
            Tag4 { flag: 0xF, size } => {
                let mut nodes = vec![];
                for _ in 0..size {
                    nodes.push(Metadatum::get(buf)?)
                }
                Ok(Metadata { nodes })
            }
            x => Err(format!("get Metadata invalid {x:?}")),
        }
    }
}

#[rustfmt::skip]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Ixon {
    #[default]
    NAnon,                                 // 0x00, anonymous name
    NStr(Address, Address),                // 0x01, string name
    NNum(Address, Address),                // 0x02, number name
    UZero,                                 // 0x03, universe zero
    USucc(Address),                        // 0x04, universe successor
    UMax(Address, Address),                // 0x05, universe max
    UIMax(Address, Address),               // 0x06, universe impredicative max
    UVar(Nat),                             // 0x1X, universe variable
    EVar(Nat),                             // 0x2X, expression variable
    ERef(Address, Vec<Address>),           // 0x3X, expression reference
    ERec(Nat, Vec<Address>),               // 0x4X, expression recursion
    EPrj(Address, Nat, Address),           // 0x5X, expression projection
    ESort(Address),                        // 0x80, expression sort
    EStr(Address),                         // 0x81, expression string
    ENat(Address),                         // 0x82, expression natural
    EApp(Address, Address),                // 0x83, expression application
    ELam(Address, Address),                // 0x84, expression lambda
    EAll(Address, Address),                // 0x85, expression forall
    ELet(bool, Address, Address, Address), // 0x86, 0x87, expression let
    Blob(Vec<u8>),                         // 0x9X, tagged bytes
    Defn(Definition),                      // 0xA0, definition constant
    Recr(Recursor),                        // 0xA1, recursor constant
    Axio(Axiom),                           // 0xA2, axiom constant
    Quot(Quotient),                        // 0xA3, quotient constant
    CPrj(ConstructorProj),                 // 0xA4, constructor projection
    RPrj(RecursorProj),                    // 0xA5, recursor projection
    IPrj(InductiveProj),                   // 0xA6, inductive projection
    DPrj(DefinitionProj),                  // 0xA7, definition projection
    Muts(Vec<MutConst>),                   // 0xBX, mutual constants
    Prof(Proof),                           // 0xE0, zero-knowledge proof
    Eval(EvalClaim),                       // 0xE1, evaluation claim
    Chck(CheckClaim),                      // 0xE2, typechecking claim
    Comm(Comm),                            // 0xE3, cryptographic commitment
    Envn(Env),                             // 0xE4, multi-claim environment
    Prim(BuiltIn),                         // 0xE5, compiler built-ins
    Meta(Metadata),                        // 0xFX, metadata
}

impl Ixon {
    pub fn put_tag(flag: u8, size: u64, buf: &mut Vec<u8>) {
        Tag4 { flag, size }.put(buf);
    }

    pub fn puts<S: Serialize>(xs: &[S], buf: &mut Vec<u8>) {
        for x in xs {
            x.put(buf)
        }
    }

    pub fn gets<S: Serialize>(len: u64, buf: &mut &[u8]) -> Result<Vec<S>, String> {
        let mut vec = vec![];
        for _ in 0..len {
            let s = S::get(buf)?;
            vec.push(s);
        }
        Ok(vec)
    }
}

impl Serialize for Ixon {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::NAnon => Self::put_tag(0x0, 0, buf),
            Self::NStr(n, s) => {
                Self::put_tag(0x0, 1, buf);
                Serialize::put(n, buf);
                Serialize::put(s, buf);
            }
            Self::NNum(n, s) => {
                Self::put_tag(0x0, 2, buf);
                Serialize::put(n, buf);
                Serialize::put(s, buf);
            }
            Self::UZero => Self::put_tag(0x0, 3, buf),
            Self::USucc(x) => {
                Self::put_tag(0x0, 4, buf);
                Serialize::put(x, buf);
            }
            Self::UMax(x, y) => {
                Self::put_tag(0x0, 5, buf);
                Serialize::put(x, buf);
                Serialize::put(y, buf);
            }
            Self::UIMax(x, y) => {
                Self::put_tag(0x0, 6, buf);
                Serialize::put(x, buf);
                Serialize::put(y, buf);
            }
            Self::UVar(x) => {
                let bytes = x.0.to_bytes_le();
                Self::put_tag(0x1, bytes.len() as u64, buf);
                Self::puts(&bytes, buf)
            }
            Self::EVar(x) => {
                let bytes = x.0.to_bytes_le();
                Self::put_tag(0x2, bytes.len() as u64, buf);
                Self::puts(&bytes, buf)
            }
            Self::ERef(a, ls) => {
                Self::put_tag(0x3, ls.len() as u64, buf);
                a.put(buf);
                Self::puts(ls, buf)
            }
            Self::ERec(i, ls) => {
                Self::put_tag(0x4, ls.len() as u64, buf);
                i.put(buf);
                Self::puts(ls, buf)
            }
            Self::EPrj(t, n, x) => {
                let bytes = n.0.to_bytes_le();
                Self::put_tag(0x5, bytes.len() as u64, buf);
                t.put(buf);
                Self::puts(&bytes, buf);
                x.put(buf);
            }
            Self::ESort(u) => {
                Self::put_tag(0x8, 0, buf);
                u.put(buf);
            }
            Self::EStr(s) => {
                Self::put_tag(0x8, 1, buf);
                s.put(buf);
            }
            Self::ENat(n) => {
                Self::put_tag(0x8, 2, buf);
                n.put(buf);
            }
            Self::EApp(f, a) => {
                Self::put_tag(0x8, 3, buf);
                f.put(buf);
                a.put(buf);
            }
            Self::ELam(t, b) => {
                Self::put_tag(0x8, 4, buf);
                t.put(buf);
                b.put(buf);
            }
            Self::EAll(t, b) => {
                Self::put_tag(0x8, 5, buf);
                t.put(buf);
                b.put(buf);
            }
            Self::ELet(nd, t, d, b) => {
                if *nd {
                    Self::put_tag(0x8, 6, buf);
                } else {
                    Self::put_tag(0x8, 7, buf);
                }
                t.put(buf);
                d.put(buf);
                b.put(buf);
            }
            Self::Blob(xs) => {
                Self::put_tag(0x9, xs.len() as u64, buf);
                Self::puts(xs, buf);
            }
            Self::Defn(x) => {
                Self::put_tag(0xA, 0, buf);
                x.put(buf);
            }
            Self::Recr(x) => {
                Self::put_tag(0xA, 1, buf);
                x.put(buf);
            }
            Self::Axio(x) => {
                Self::put_tag(0xA, 2, buf);
                x.put(buf);
            }
            Self::Quot(x) => {
                Self::put_tag(0xA, 3, buf);
                x.put(buf);
            }
            Self::CPrj(x) => {
                Self::put_tag(0xA, 4, buf);
                x.put(buf);
            }
            Self::RPrj(x) => {
                Self::put_tag(0xA, 5, buf);
                x.put(buf);
            }
            Self::IPrj(x) => {
                Self::put_tag(0xA, 6, buf);
                x.put(buf);
            }
            Self::DPrj(x) => {
                Self::put_tag(0xA, 7, buf);
                x.put(buf);
            }
            Self::Muts(xs) => {
                Self::put_tag(0xB, xs.len() as u64, buf);
                Self::puts(xs, buf);
            }
            Self::Prof(x) => {
                Self::put_tag(0xE, 0, buf);
                x.put(buf);
            }
            Self::Eval(x) => {
                Self::put_tag(0xE, 1, buf);
                x.put(buf);
            }
            Self::Chck(x) => {
                Self::put_tag(0xE, 2, buf);
                x.put(buf);
            }
            Self::Comm(x) => {
                Self::put_tag(0xE, 3, buf);
                x.put(buf);
            }
            Self::Envn(x) => {
                Self::put_tag(0xE, 4, buf);
                x.put(buf);
            }
            Self::Prim(x) => {
                Self::put_tag(0xE, 5, buf);
                x.put(buf);
            }
            Self::Meta(x) => x.put(buf),
        }
    }
    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let tag = Tag4::get(buf)?;
        match tag {
            Tag4 { flag: 0x0, size: 0 } => Ok(Self::NAnon),
            Tag4 { flag: 0x0, size: 1 } => Ok(Self::NStr(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x0, size: 2 } => Ok(Self::NNum(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x0, size: 3 } => Ok(Self::UZero),
            Tag4 { flag: 0x0, size: 4 } => Ok(Self::USucc(Address::get(buf)?)),
            Tag4 { flag: 0x0, size: 5 } => Ok(Self::UMax(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x0, size: 6 } => Ok(Self::UIMax(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x1, size } => {
                let bytes: Vec<u8> = Self::gets(size, buf)?;
                Ok(Self::UVar(Nat::from_le_bytes(&bytes)))
            }
            Tag4 { flag: 0x2, size } => {
                let bytes: Vec<u8> = Self::gets(size, buf)?;
                Ok(Self::EVar(Nat::from_le_bytes(&bytes)))
            }
            Tag4 { flag: 0x3, size } => Ok(Self::ERef(Address::get(buf)?, Self::gets(size, buf)?)),
            Tag4 { flag: 0x4, size } => Ok(Self::ERec(Nat::get(buf)?, Self::gets(size, buf)?)),
            Tag4 { flag: 0x5, size } => Ok(Self::EPrj(
                Address::get(buf)?,
                Nat::from_le_bytes(&Self::gets(size, buf)?),
                Address::get(buf)?,
            )),
            Tag4 { flag: 0x8, size: 0 } => Ok(Self::ESort(Address::get(buf)?)),
            Tag4 { flag: 0x8, size: 1 } => Ok(Self::EStr(Address::get(buf)?)),
            Tag4 { flag: 0x8, size: 2 } => Ok(Self::ENat(Address::get(buf)?)),
            Tag4 { flag: 0x8, size: 3 } => Ok(Self::EApp(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x8, size: 4 } => Ok(Self::ELam(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x8, size: 5 } => Ok(Self::EAll(Address::get(buf)?, Address::get(buf)?)),
            Tag4 { flag: 0x8, size: 6 } => Ok(Self::ELet(
                true,
                Address::get(buf)?,
                Address::get(buf)?,
                Address::get(buf)?,
            )),
            Tag4 { flag: 0x8, size: 7 } => Ok(Self::ELet(
                false,
                Address::get(buf)?,
                Address::get(buf)?,
                Address::get(buf)?,
            )),
            Tag4 { flag: 0x9, size } => {
                let bytes: Vec<u8> = Self::gets(size, buf)?;
                Ok(Self::Blob(bytes))
            }
            Tag4 { flag: 0xA, size: 0 } => Ok(Self::Defn(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 1 } => Ok(Self::Recr(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 2 } => Ok(Self::Axio(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 3 } => Ok(Self::Quot(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 4 } => Ok(Self::CPrj(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 5 } => Ok(Self::RPrj(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 6 } => Ok(Self::IPrj(Serialize::get(buf)?)),
            Tag4 { flag: 0xA, size: 7 } => Ok(Self::DPrj(Serialize::get(buf)?)),
            Tag4 { flag: 0xB, size } => {
                let xs: Vec<MutConst> = Self::gets(size, buf)?;
                Ok(Self::Muts(xs))
            }
            Tag4 { flag: 0xE, size: 0 } => Ok(Self::Prof(Serialize::get(buf)?)),
            Tag4 { flag: 0xE, size: 1 } => Ok(Self::Eval(Serialize::get(buf)?)),
            Tag4 { flag: 0xE, size: 2 } => Ok(Self::Chck(Serialize::get(buf)?)),
            Tag4 { flag: 0xE, size: 3 } => Ok(Self::Comm(Serialize::get(buf)?)),
            Tag4 { flag: 0xE, size: 4 } => Ok(Self::Envn(Serialize::get(buf)?)),
            Tag4 { flag: 0xE, size: 5 } => Ok(Self::Prim(Serialize::get(buf)?)),
            Tag4 { flag: 0xF, size } => {
                let nodes: Vec<Metadatum> = Self::gets(size, buf)?;
                Ok(Self::Meta(Metadata { nodes }))
            }
            x => Err(format!("get Ixon invalid {x:?}")),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen};
    use std::ops::Range;

    pub fn gen_range(g: &mut Gen, range: Range<usize>) -> usize {
        let res: usize = Arbitrary::arbitrary(g);
        if range.is_empty() {
            0
        } else {
            (res % (range.end - range.start)) + range.start
        }
    }

    pub fn gen_vec<A, F>(g: &mut Gen, size: usize, mut f: F) -> Vec<A>
    where
        F: FnMut(&mut Gen) -> A,
    {
        let len = gen_range(g, 0..size);
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(f(g));
        }
        vec
    }
    #[test]
    fn unit_u64_trimmed() {
        fn test(input: u64, expected: &Vec<u8>) -> bool {
            let mut tmp = Vec::new();
            let n = u64_byte_count(input);
            u64_put_trimmed_le(input, &mut tmp);
            if tmp != *expected {
                return false;
            }
            match u64_get_trimmed_le(n as usize, &mut tmp.as_slice()) {
                Ok(out) => input == out,
                Err(e) => {
                    println!("err: {e}");
                    false
                }
            }
        }
        assert!(test(0x0, &vec![]));
        assert!(test(0x01, &vec![0x01]));
        assert!(test(0x0000000000000100, &vec![0x00, 0x01]));
        assert!(test(0x0000000000010000, &vec![0x00, 0x00, 0x01]));
        assert!(test(0x0000000001000000, &vec![0x00, 0x00, 0x00, 0x01]));
        assert!(test(
            0x0000000100000000,
            &vec![0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0000010000000000,
            &vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0001000000000000,
            &vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0100000000000000,
            &vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0102030405060708,
            &vec![0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
        ));
        assert!(test(
            0x57712D6CE2965701,
            &vec![0x01, 0x57, 0x96, 0xE2, 0x6C, 0x2D, 0x71, 0x57]
        ));
    }

    #[quickcheck]
    fn prop_u64_trimmed_le_readback(x: u64) -> bool {
        let mut buf = Vec::new();
        let n = u64_byte_count(x);
        u64_put_trimmed_le(x, &mut buf);
        match u64_get_trimmed_le(n as usize, &mut buf.as_slice()) {
            Ok(y) => x == y,
            Err(e) => {
                println!("err: {e}");
                false
            }
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn serialize_readback<S: Serialize + Eq>(x: S) -> bool {
        let mut buf = Vec::new();
        Serialize::put(&x, &mut buf);
        match S::get(&mut buf.as_slice()) {
            Ok(y) => x == y,
            Err(e) => {
                println!("err: {e}");
                false
            }
        }
    }

    #[quickcheck]
    fn prop_u8_readback(x: u8) -> bool {
        serialize_readback(x)
    }
    #[quickcheck]
    fn prop_u16_readback(x: u16) -> bool {
        serialize_readback(x)
    }
    #[quickcheck]
    fn prop_u32_readback(x: u32) -> bool {
        serialize_readback(x)
    }
    #[quickcheck]
    fn prop_u64_readback(x: u64) -> bool {
        serialize_readback(x)
    }
    #[quickcheck]
    fn prop_bool_readback(x: bool) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Tag4 {
        fn arbitrary(g: &mut Gen) -> Self {
            let flag = u8::arbitrary(g) % 16;
            Tag4 {
                flag,
                size: u64::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_tag4_readback(x: Tag4) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for ByteArray {
        fn arbitrary(g: &mut Gen) -> Self {
            ByteArray(gen_vec(g, 12, u8::arbitrary))
        }
    }

    #[quickcheck]
    fn prop_bytearray_readback(x: ByteArray) -> bool {
        serialize_readback(x)
    }

    #[quickcheck]
    fn prop_string_readback(x: String) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Nat {
        fn arbitrary(g: &mut Gen) -> Self {
            Nat::from_le_bytes(&gen_vec(g, 12, u8::arbitrary))
        }
    }

    #[quickcheck]
    fn prop_nat_readback(x: Nat) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Int {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 2 {
                0 => Int::OfNat(Nat::arbitrary(g)),
                1 => Int::NegSucc(Nat::arbitrary(g)),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_int_readback(x: Int) -> bool {
        serialize_readback(x)
    }

    #[quickcheck]
    fn prop_vec_bool_readback(x: Vec<bool>) -> bool {
        serialize_readback(x)
    }

    #[quickcheck]
    fn prop_pack_bool_readback(x: Vec<bool>) -> bool {
        let mut bools = x;
        bools.truncate(8);
        bools == unpack_bools(bools.len(), pack_bools(bools.clone()))
    }

    impl Arbitrary for QuotKind {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 4 {
                0 => Self::Type,
                1 => Self::Ctor,
                2 => Self::Lift,
                3 => Self::Ind,
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_quotkind_readback(x: QuotKind) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for DefKind {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 3 {
                0 => Self::Definition,
                1 => Self::Opaque,
                2 => Self::Theorem,
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_defkind_readback(x: DefKind) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for BinderInfo {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 4 {
                0 => Self::Default,
                1 => Self::Implicit,
                2 => Self::StrictImplicit,
                3 => Self::InstImplicit,
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_binderinfo_readback(x: BinderInfo) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for ReducibilityHints {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 3 {
                0 => Self::Opaque,
                1 => Self::Abbrev,
                2 => Self::Regular(u32::arbitrary(g)),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_reducibilityhints_readback(x: ReducibilityHints) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for DefinitionSafety {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 3 {
                0 => Self::Unsafe,
                1 => Self::Safe,
                2 => Self::Partial,
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_defsafety_readback(x: DefinitionSafety) -> bool {
        serialize_readback(x)
    }

    #[quickcheck]
    fn prop_address_readback(x: Address) -> bool {
        serialize_readback(x)
    }
    #[quickcheck]
    fn prop_metaaddress_readback(x: MetaAddress) -> bool {
        serialize_readback(x)
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

    #[quickcheck]
    fn prop_quotient_readback(x: Quotient) -> bool {
        serialize_readback(x)
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

    #[quickcheck]
    fn prop_axiom_readback(x: Axiom) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Definition {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                kind: DefKind::arbitrary(g),
                safety: DefinitionSafety::arbitrary(g),
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                value: Address::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_definition_readback(x: Definition) -> bool {
        serialize_readback(x)
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

    #[quickcheck]
    fn prop_constructor_readback(x: Constructor) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for RecursorRule {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                fields: Nat::arbitrary(g),
                rhs: Address::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_recursorrule_readback(x: RecursorRule) -> bool {
        serialize_readback(x)
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

    #[quickcheck]
    fn prop_recursor_readback(x: Recursor) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Inductive {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..9);
            let mut ctors = vec![];
            for _ in 0..x {
                ctors.push(Constructor::arbitrary(g));
            }
            Self {
                lvls: Nat::arbitrary(g),
                typ: Address::arbitrary(g),
                params: Nat::arbitrary(g),
                indices: Nat::arbitrary(g),
                ctors,
                nested: Nat::arbitrary(g),
                recr: bool::arbitrary(g),
                refl: bool::arbitrary(g),
                is_unsafe: bool::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_inductive_readback(x: Inductive) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for InductiveProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_inductiveproj_readback(x: InductiveProj) -> bool {
        serialize_readback(x)
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

    #[quickcheck]
    fn prop_constructorproj_readback(x: ConstructorProj) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for RecursorProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_recursorproj_readback(x: RecursorProj) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for DefinitionProj {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                block: Address::arbitrary(g),
                idx: Nat::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_definitionproj_readback(x: DefinitionProj) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Comm {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                secret: Address::arbitrary(g),
                payload: Address::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_comm_readback(x: Comm) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for EvalClaim {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                lvls: Address::arbitrary(g),
                typ: Address::arbitrary(g),
                input: Address::arbitrary(g),
                output: Address::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_evalclaim_readback(x: EvalClaim) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for CheckClaim {
        fn arbitrary(g: &mut Gen) -> Self {
            Self {
                lvls: Address::arbitrary(g),
                typ: Address::arbitrary(g),
                value: Address::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_checkclaim_readback(x: CheckClaim) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Claim {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..1);
            match x {
                0 => Self::Evals(EvalClaim::arbitrary(g)),
                _ => Self::Checks(CheckClaim::arbitrary(g)),
            }
        }
    }

    #[quickcheck]
    fn prop_claim_readback(x: Claim) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Proof {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..32);
            let mut bytes = vec![];
            for _ in 0..x {
                bytes.push(u8::arbitrary(g));
            }
            Proof {
                claim: Claim::arbitrary(g),
                proof: bytes,
            }
        }
    }

    #[quickcheck]
    fn prop_proof_readback(x: Proof) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Env {
        fn arbitrary(g: &mut Gen) -> Self {
            let x = gen_range(g, 0..32);
            let mut env = vec![];
            for _ in 0..x {
                env.push(MetaAddress::arbitrary(g));
            }
            Env { env }
        }
    }

    #[quickcheck]
    fn prop_env_readback(x: Env) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Substring {
        fn arbitrary(g: &mut Gen) -> Self {
            Substring {
                str: Address::arbitrary(g),
                start_pos: Nat::arbitrary(g),
                stop_pos: Nat::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_substring_readback(x: Substring) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for SourceInfo {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 3 {
                0 => Self::Original(
                    Substring::arbitrary(g),
                    Nat::arbitrary(g),
                    Substring::arbitrary(g),
                    Nat::arbitrary(g),
                ),
                1 => Self::Synthetic(Nat::arbitrary(g), Nat::arbitrary(g), bool::arbitrary(g)),
                2 => Self::None,
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_sourceinfo_readback(x: SourceInfo) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Preresolved {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 2 {
                0 => Self::Namespace(Address::arbitrary(g)),
                1 => Self::Decl(Address::arbitrary(g), gen_vec(g, 12, Address::arbitrary)),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_preresolved_readback(x: Preresolved) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Syntax {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 4 {
                0 => Self::Missing,
                1 => Self::Node(
                    SourceInfo::arbitrary(g),
                    Address::arbitrary(g),
                    gen_vec(g, 12, Address::arbitrary),
                ),
                2 => Self::Atom(SourceInfo::arbitrary(g), Address::arbitrary(g)),
                3 => Self::Ident(
                    SourceInfo::arbitrary(g),
                    Substring::arbitrary(g),
                    Address::arbitrary(g),
                    gen_vec(g, 12, Preresolved::arbitrary),
                ),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_syntax_readback(x: Syntax) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for MutConst {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 3 {
                0 => Self::Defn(Definition::arbitrary(g)),
                1 => Self::Indc(Inductive::arbitrary(g)),
                2 => Self::Recr(Recursor::arbitrary(g)),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_mutconst_readback(x: MutConst) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for BuiltIn {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 3 {
                0 => Self::Obj,
                1 => Self::Neutral,
                2 => Self::Unreachable,
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_builtin_readback(x: BuiltIn) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for DataValue {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 6 {
                0 => Self::OfString(Address::arbitrary(g)),
                1 => Self::OfBool(bool::arbitrary(g)),
                2 => Self::OfName(Address::arbitrary(g)),
                3 => Self::OfNat(Address::arbitrary(g)),
                4 => Self::OfInt(Address::arbitrary(g)),
                5 => Self::OfSyntax(Address::arbitrary(g)),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_datavalue_readback(x: DataValue) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Metadatum {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 7 {
                0 => Self::Link(Address::arbitrary(g)),
                1 => Self::Info(BinderInfo::arbitrary(g)),
                2 => Self::Hints(ReducibilityHints::arbitrary(g)),
                3 => Self::Links(gen_vec(g, 12, Address::arbitrary)),
                4 => Self::Map(gen_vec(g, 12, |g| {
                    (Address::arbitrary(g), Address::arbitrary(g))
                })),
                5 => Self::KVMap(gen_vec(g, 12, |g| {
                    (Address::arbitrary(g), DataValue::arbitrary(g))
                })),
                6 => Self::Muts(gen_vec(g, 12, |g| gen_vec(g, 12, Address::arbitrary))),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_metadatum_readback(x: Metadatum) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Metadata {
        fn arbitrary(g: &mut Gen) -> Self {
            Metadata {
                nodes: gen_vec(g, 12, Metadatum::arbitrary),
            }
        }
    }

    #[quickcheck]
    fn prop_metadata_readback(x: Metadata) -> bool {
        serialize_readback(x)
    }

    impl Arbitrary for Ixon {
        fn arbitrary(g: &mut Gen) -> Self {
            match u8::arbitrary(g) % 36 {
                0 => Self::NAnon,
                1 => Self::NStr(Address::arbitrary(g), Address::arbitrary(g)),
                2 => Self::NNum(Address::arbitrary(g), Address::arbitrary(g)),
                3 => Self::UZero,
                4 => Self::USucc(Address::arbitrary(g)),
                5 => Self::UMax(Address::arbitrary(g), Address::arbitrary(g)),
                6 => Self::UIMax(Address::arbitrary(g), Address::arbitrary(g)),
                7 => Self::UVar(Nat::arbitrary(g)),
                8 => Self::EVar(Nat::arbitrary(g)),
                9 => Self::ERef(Address::arbitrary(g), gen_vec(g, 12, Address::arbitrary)),
                10 => Self::ERec(Nat::arbitrary(g), gen_vec(g, 12, Address::arbitrary)),
                11 => Self::EPrj(
                    Address::arbitrary(g),
                    Nat::arbitrary(g),
                    Address::arbitrary(g),
                ),
                12 => Self::ESort(Address::arbitrary(g)),
                13 => Self::EStr(Address::arbitrary(g)),
                14 => Self::ENat(Address::arbitrary(g)),
                15 => Self::EApp(Address::arbitrary(g), Address::arbitrary(g)),
                16 => Self::ELam(Address::arbitrary(g), Address::arbitrary(g)),
                17 => Self::EAll(Address::arbitrary(g), Address::arbitrary(g)),
                18 => Self::ELet(
                    bool::arbitrary(g),
                    Address::arbitrary(g),
                    Address::arbitrary(g),
                    Address::arbitrary(g),
                ),
                19 => Self::Blob(gen_vec(g, 12, u8::arbitrary)),
                20 => Self::Defn(Definition::arbitrary(g)),
                21 => Self::Recr(Recursor::arbitrary(g)),
                22 => Self::Axio(Axiom::arbitrary(g)),
                23 => Self::Quot(Quotient::arbitrary(g)),
                24 => Self::CPrj(ConstructorProj::arbitrary(g)),
                25 => Self::RPrj(RecursorProj::arbitrary(g)),
                26 => Self::IPrj(InductiveProj::arbitrary(g)),
                27 => Self::DPrj(DefinitionProj::arbitrary(g)),
                28 => Self::Muts(gen_vec(g, 12, MutConst::arbitrary)),
                29 => Self::Prof(Proof::arbitrary(g)),
                30 => Self::Eval(EvalClaim::arbitrary(g)),
                31 => Self::Chck(CheckClaim::arbitrary(g)),
                32 => Self::Comm(Comm::arbitrary(g)),
                33 => Self::Envn(Env::arbitrary(g)),
                34 => Self::Prim(BuiltIn::arbitrary(g)),
                35 => Self::Meta(Metadata::arbitrary(g)),
                _ => unreachable!(),
            }
        }
    }

    #[quickcheck]
    fn prop_ixon_readback(x: Ixon) -> bool {
        serialize_readback(x)
    }
}
