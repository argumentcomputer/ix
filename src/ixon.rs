use crate::lean::nat::*;
use blake3::Hash;
use num_bigint::BigUint;

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
      },
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
      },
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
      },
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
          head[0], head[1], head[2], head[3], head[4], head[5], head[6],
          head[7],
        ]))
      },
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
      },
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
    },
    None => Err("get trimmed_le_u64 EOF".to_string()),
  }
}

//  F := flag, L := large-bit, X := small-field, A := large_field
// 0xFFFF_LXXX {AAAA_AAAA, ...}
// "Tag" means the whole thing
// "Head" means the first byte of the tag
// "Flag" means the first nibble of the head
#[derive(Clone, Debug)]
pub struct Tag4 {
  flag: u8,
  size: u64,
}

impl Tag4 {
  pub fn encode_head(&self) -> u8 {
    if self.size < 8 {
      (self.flag << 4) + (self.size as u8)
    } else {
      (self.flag << 4) + 0b1000 + u64_byte_count(self.size) - 1
    }
  }
  pub fn decode_head(head: u8) -> (u8, bool, u8) {
    (head >> 4, head & 0b1000 == 0, head % 0b1000)
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
pub struct ByteArray(pub Vec<u8>);

impl Serialize for ByteArray {
  fn put(&self, buf: &mut Vec<u8>) {
    Tag4 { flag: 0x9, size: self.0.len() as u64 }.put(buf);
    buf.extend_from_slice(&self.0);
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
      },
      _ => Err("expected Tag4 0x9 for Vec<u8>".to_string()),
    }
  }
}

impl Serialize for String {
  fn put(&self, buf: &mut Vec<u8>) {
    let bytes = self.as_bytes();
    Tag4 { flag: 0x9, size: bytes.len() as u64 }.put(buf);
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
    Tag4 { flag: 0x9, size: bytes.len() as u64 }.put(buf);
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
      },
      Self::NegSucc(x) => {
        buf.push(1);
        x.put(buf);
      },
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
      },
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
  (0..8).map(|i: u32| (b & (1u8 << i)) != 0).take(n.min(8)).collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
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
      },
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
      },
      None => Err("get DefKind EOF".to_string()),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplicit,
  InstImplicit,
  AuxDecl,
}

impl Serialize for BinderInfo {
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Default => buf.push(0),
      Self::Implicit => buf.push(1),
      Self::StrictImplicit => buf.push(2),
      Self::InstImplicit => buf.push(3),
      Self::AuxDecl => buf.push(3),
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
          4 => Ok(Self::AuxDecl),
          x => Err(format!("get BinderInfo invalid {x}")),
        }
      },
      None => Err("get BinderInfo EOF".to_string()),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReducibilityHints {
  Opaque,
  Abbrev,
  Regular(u32),
}

impl Serialize for ReducibilityHints {
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Opaque => buf.push(0),
      Self::Abbrev => buf.push(1),
      Self::Regular(x) => {
        buf.push(2);
        x.put(buf);
      },
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
          },
          x => Err(format!("get ReducibilityHints invalid {x}")),
        }
      },
      None => Err("get ReducibilityHints EOF".to_string()),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefSafety {
  Unsafe,
  Safe,
  Partial,
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
      },
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
        Ok(Address { hash: Hash::from_slice(head).unwrap() })
      },
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
    Ok(Axiom { lvls, typ, is_unsafe })
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
  pub kind: DefKind,
  pub safety: DefSafety,
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
    let safety = DefSafety::get(buf)?;
    let lvls = Nat::get(buf)?;
    let typ = Address::get(buf)?;
    let value = Address::get(buf)?;
    Ok(Definition { kind, safety, lvls, typ, value })
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
    Ok(Constructor { lvls, typ, cidx, params, fields, is_unsafe })
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
  pub ridx: Nat,
  pub block: Address,
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
    Ok(Self { lvls, typ, input, output })
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
  Checks(CheckClaim),
  Evals(EvalClaim),
}

impl Serialize for Claim {
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Evals(x) => {
        u8::put(&0xE2, buf);
        x.put(buf)
      },
      Self::Checks(x) => {
        u8::put(&0xE3, buf);
        x.put(buf)
      },
    }
  }
  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(1) {
      Some((head, rest)) => {
        *buf = rest;
        match head[0] {
          0xE2 => {
            let x = EvalClaim::get(buf)?;
            Ok(Self::Evals(x))
          },
          0xE3 => {
            let x = CheckClaim::get(buf)?;
            Ok(Self::Checks(x))
          },
          x => Err(format!("get Claim invalid {x}")),
        }
      },
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
    self.proof.put(buf);
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let claim = Claim::get(buf)?;
    let proof = Serialize::get(buf)?;
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
    Ok(Env { env: Serialize::get(buf)? })
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
    Ok(Substring { str, start_pos, stop_pos })
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
      },
      Self::Synthetic(p, e, c) => {
        buf.push(1);
        p.put(buf);
        e.put(buf);
        c.put(buf);
      },
      Self::None => {
        buf.push(2);
      },
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
          1 => {
            Ok(Self::Synthetic(Nat::get(buf)?, Nat::get(buf)?, bool::get(buf)?))
          },
          2 => Ok(Self::None),
          x => Err(format!("get SourcInfo invalid {x}")),
        }
      },
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
      },
      Self::Decl(n, fields) => {
        buf.push(1);
        n.put(buf);
        fields.put(buf);
      },
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
      },
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
      },
      Self::Node(i, k, xs) => {
        buf.push(1);
        i.put(buf);
        k.put(buf);
        xs.put(buf);
      },
      Self::Atom(i, v) => {
        buf.push(2);
        i.put(buf);
        v.put(buf);
      },
      Self::Ident(i, r, v, ps) => {
        buf.push(3);
        i.put(buf);
        r.put(buf);
        v.put(buf);
        ps.put(buf);
      },
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
      },
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
      },
      Self::Indc(x) => {
        buf.push(1);
        x.put(buf);
      },
      Self::Recr(x) => {
        buf.push(2);
        x.put(buf);
      },
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
      },
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
      },
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
      },
      Self::OfBool(x) => {
        buf.push(1);
        x.put(buf);
      },
      Self::OfName(x) => {
        buf.push(2);
        x.put(buf);
      },
      Self::OfNat(x) => {
        buf.push(3);
        x.put(buf);
      },
      Self::OfInt(x) => {
        buf.push(4);
        x.put(buf);
      },
      Self::OfSyntax(x) => {
        buf.push(5);
        x.put(buf);
      },
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
      },
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
      },
      Self::Info(x) => {
        buf.push(1);
        x.put(buf);
      },
      Self::Hints(x) => {
        buf.push(2);
        x.put(buf);
      },
      Self::Links(x) => {
        buf.push(3);
        x.put(buf);
      },
      Self::Map(x) => {
        buf.push(4);
        x.put(buf);
      },
      Self::KVMap(x) => {
        buf.push(5);
        x.put(buf);
      },
      Self::Muts(x) => {
        buf.push(6);
        x.put(buf);
      },
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
      },
      None => Err("get Metadatum EOF".to_string()),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Metadata {
  pub nodes: Vec<Metadatum>,
}

impl Serialize for Metadata {
  fn put(&self, buf: &mut Vec<u8>) {
    Tag4 { flag: 0x4, size: self.nodes.len() as u64 }.put(buf);
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
      },
      x => Err(format!("get Metadata invalid {x:?}")),
    }
  }
}

// TODO: Update Ixon

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ixon {
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

impl Default for Ixon {
  fn default() -> Self {
    Self::NAnon
  }
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

  pub fn gets<S: Serialize>(
    len: u64,
    buf: &mut &[u8],
  ) -> Result<Vec<S>, String> {
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
      },
      Self::NNum(n, s) => {
        Self::put_tag(0x0, 2, buf);
        Serialize::put(n, buf);
        Serialize::put(s, buf);
      },
      Self::UZero => Self::put_tag(0x0, 3, buf),
      Self::USucc(x) => {
        Self::put_tag(0x0, 4, buf);
        Serialize::put(x, buf);
      },
      Self::UMax(x, y) => {
        Self::put_tag(0x0, 5, buf);
        Serialize::put(x, buf);
        Serialize::put(y, buf);
      },
      Self::UIMax(x, y) => {
        Self::put_tag(0x0, 6, buf);
        Serialize::put(x, buf);
        Serialize::put(y, buf);
      },
      Self::UVar(x) => {
        let bytes = x.0.to_bytes_le();
        Self::put_tag(0x1, bytes.len() as u64, buf);
        Self::puts(&bytes, buf)
      },
      Self::EVar(x) => {
        let bytes = x.0.to_bytes_le();
        Self::put_tag(0x2, bytes.len() as u64, buf);
        Self::puts(&bytes, buf)
      },
      Self::ERef(a, ls) => {
        Self::put_tag(0x3, ls.len() as u64, buf);
        a.put(buf);
        Self::puts(ls, buf)
      },
      Self::ERec(i, ls) => {
        Self::put_tag(0x4, ls.len() as u64, buf);
        i.put(buf);
        Self::puts(ls, buf)
      },
      Self::EPrj(t, n, x) => {
        let bytes = n.0.to_bytes_le();
        Self::put_tag(0x5, bytes.len() as u64, buf);
        t.put(buf);
        Self::puts(&bytes, buf);
        x.put(buf);
      },
      Self::ESort(u) => {
        Self::put_tag(0x8, 0, buf);
        u.put(buf);
      },
      Self::EStr(s) => {
        Self::put_tag(0x8, 1, buf);
        s.put(buf);
      },
      Self::ENat(n) => {
        Self::put_tag(0x8, 2, buf);
        n.put(buf);
      },
      Self::EApp(f, a) => {
        Self::put_tag(0x8, 3, buf);
        f.put(buf);
        a.put(buf);
      },
      Self::ELam(t, b) => {
        Self::put_tag(0x8, 4, buf);
        t.put(buf);
        b.put(buf);
      },
      Self::EAll(t, b) => {
        Self::put_tag(0x8, 5, buf);
        t.put(buf);
        b.put(buf);
      },
      Self::ELet(nd, t, d, b) => {
        if *nd {
          Self::put_tag(0x8, 6, buf);
        } else {
          Self::put_tag(0x8, 7, buf);
        }
        t.put(buf);
        d.put(buf);
        b.put(buf);
      },
      Self::Blob(xs) => {
        Self::put_tag(0x9, xs.len() as u64, buf);
        Self::puts(xs, buf);
      },
      Self::Defn(x) => {
        Self::put_tag(0xA, 0, buf);
        x.put(buf);
      },
      Self::Recr(x) => {
        Self::put_tag(0xA, 1, buf);
        x.put(buf);
      },
      Self::Axio(x) => {
        Self::put_tag(0xA, 2, buf);
        x.put(buf);
      },
      Self::Quot(x) => {
        Self::put_tag(0xA, 3, buf);
        x.put(buf);
      },
      Self::CPrj(x) => {
        Self::put_tag(0xA, 4, buf);
        x.put(buf);
      },
      Self::RPrj(x) => {
        Self::put_tag(0xA, 5, buf);
        x.put(buf);
      },
      Self::IPrj(x) => {
        Self::put_tag(0xA, 6, buf);
        x.put(buf);
      },
      Self::DPrj(x) => {
        Self::put_tag(0xA, 7, buf);
        x.put(buf);
      },
      Self::Muts(xs) => {
        Self::put_tag(0xB, xs.len() as u64, buf);
        Self::puts(xs, buf);
      },
      Self::Prof(x) => {
        Self::put_tag(0xE, 0, buf);
        x.put(buf);
      },
      Self::Eval(x) => {
        Self::put_tag(0xE, 1, buf);
        x.put(buf);
      },
      Self::Chck(x) => {
        Self::put_tag(0xE, 2, buf);
        x.put(buf);
      },
      Self::Comm(x) => {
        Self::put_tag(0xE, 3, buf);
        x.put(buf);
      },
      Self::Envn(x) => {
        Self::put_tag(0xE, 4, buf);
        x.put(buf);
      },
      Self::Prim(x) => {
        Self::put_tag(0xE, 5, buf);
        x.put(buf);
      },
      Self::Meta(x) => {
        Self::put_tag(0xE, 5, buf);
        x.put(buf);
      },
    }
  }
  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    match tag {
      Tag4 { flag: 0x0, size: 0 } => Ok(Self::NAnon),
      Tag4 { flag: 0x0, size: 1 } => {
        Ok(Self::NStr(Address::get(buf)?, Address::get(buf)?))
      },
      Tag4 { flag: 0x0, size: 2 } => {
        Ok(Self::NNum(Address::get(buf)?, Address::get(buf)?))
      },
      Tag4 { flag: 0x0, size: 3 } => Ok(Self::UZero),
      Tag4 { flag: 0x0, size: 4 } => Ok(Self::USucc(Address::get(buf)?)),
      Tag4 { flag: 0x0, size: 5 } => {
        Ok(Self::UMax(Address::get(buf)?, Address::get(buf)?))
      },
      Tag4 { flag: 0x0, size: 6 } => {
        Ok(Self::UIMax(Address::get(buf)?, Address::get(buf)?))
      },
      Tag4 { flag: 0x1, size } => {
        let bytes: Vec<u8> = Self::gets(size, buf)?;
        Ok(Self::UVar(Nat::from_le_bytes(&bytes)))
      },
      Tag4 { flag: 0x3, size } => {
        let bytes: Vec<u8> = Self::gets(size, buf)?;
        Ok(Self::EVar(Nat::from_le_bytes(&bytes)))
      },
      Tag4 { flag: 0x4, size } => {
        Ok(Self::ERef(Address::get(buf)?, Self::gets(size, buf)?))
      },
      Tag4 { flag: 0x5, size } => {
        Ok(Self::ERec(Nat::get(buf)?, Self::gets(size, buf)?))
      },
      Tag4 { flag: 0x8, size: 0 } => Ok(Self::ESort(Address::get(buf)?)),
      Tag4 { flag: 0x8, size: 1 } => Ok(Self::EStr(Address::get(buf)?)),
      Tag4 { flag: 0x8, size: 2 } => Ok(Self::ENat(Address::get(buf)?)),
      Tag4 { flag: 0x8, size: 3 } => {
        Ok(Self::EApp(Address::get(buf)?, Address::get(buf)?))
      },
      Tag4 { flag: 0x8, size: 4 } => {
        Ok(Self::ELam(Address::get(buf)?, Address::get(buf)?))
      },
      Tag4 { flag: 0x8, size: 5 } => {
        Ok(Self::EAll(Address::get(buf)?, Address::get(buf)?))
      },
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
      },
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
      },
      Tag4 { flag: 0xE, size: 0 } => Ok(Self::Prof(Serialize::get(buf)?)),
      Tag4 { flag: 0xE, size: 1 } => Ok(Self::Eval(Serialize::get(buf)?)),
      Tag4 { flag: 0xE, size: 2 } => Ok(Self::Chck(Serialize::get(buf)?)),
      Tag4 { flag: 0xE, size: 3 } => Ok(Self::Comm(Serialize::get(buf)?)),
      Tag4 { flag: 0xE, size: 4 } => Ok(Self::Envn(Serialize::get(buf)?)),
      Tag4 { flag: 0xE, size: 5 } => Ok(Self::Prim(Serialize::get(buf)?)),
      Tag4 { flag: 0xF, size } => {
        let nodes: Vec<Metadatum> = Self::gets(size, buf)?;
        Ok(Self::Meta(Metadata { nodes }))
      },
      x => Err(format!("get Ixon invalid {x:?}")),
    }
  }
}
//
////impl Serialize for Ixon {
////    fn put(&self, buf: &mut Vec<u8>) {
////        match self {
////            Self::Vari(x) => Self::put_tag(0x0, *x, buf),
////            Self::Sort(x) => {
////                u8::put(&0x90, buf);
////                x.put(buf);
////            }
////            Self::Refr(addr, lvls) => {
////                Self::put_tag(0x1, lvls.len() as u64, buf);
////                addr.put(buf);
////                for l in lvls {
////                    l.put(buf);
////                }
////            }
////            Self::Recr(x, lvls) => {
////                Self::put_tag(0x2, *x, buf);
////                Ixon::put_array(lvls, buf);
////            }
////            Self::Apps(f, a, args) => {
////                Self::put_tag(0x3, args.len() as u64, buf);
////                f.put(buf);
////                a.put(buf);
////                for x in args {
////                    x.put(buf);
////                }
////            }
////            Self::Lams(ts, b) => {
////                Self::put_tag(0x4, ts.len() as u64, buf);
////                for t in ts {
////                    t.put(buf);
////                }
////                b.put(buf);
////            }
////            Self::Alls(ts, b) => {
////                Self::put_tag(0x5, ts.len() as u64, buf);
////                for t in ts {
////                    t.put(buf);
////                }
////                b.put(buf);
////            }
////            Self::Proj(t, n, x) => {
////                Self::put_tag(0x6, *n, buf);
////                t.put(buf);
////                x.put(buf);
////            }
////            Self::Strl(s) => {
////                let bytes = s.as_bytes();
////                Self::put_tag(0x7, bytes.len() as u64, buf);
////                buf.extend_from_slice(bytes);
////            }
////            Self::Natl(n) => {
////                let bytes = n.0.to_bytes_le();
////                Self::put_tag(0x8, bytes.len() as u64, buf);
////                buf.extend_from_slice(&bytes);
////            }
////            Self::LetE(nd, t, d, b) => {
////                if *nd {
////                    u8::put(&0x91, buf);
////                } else {
////                    u8::put(&0x92, buf);
////                }
////                t.put(buf);
////                d.put(buf);
////                b.put(buf);
////            }
////            Self::List(xs) => Ixon::put_array(xs, buf),
////            Self::Defn(x) => {
////                u8::put(&0xB0, buf);
////                x.put(buf);
////            }
////            Self::Axio(x) => {
////                u8::put(&0xB1, buf);
////                x.put(buf);
////            }
////            Self::Quot(x) => {
////                u8::put(&0xB2, buf);
////                x.put(buf);
////            }
////            Self::CPrj(x) => {
////                u8::put(&0xB3, buf);
////                x.put(buf);
////            }
////            Self::RPrj(x) => {
////                u8::put(&0xB4, buf);
////                x.put(buf);
////            }
////            Self::IPrj(x) => {
////                u8::put(&0xB5, buf);
////                x.put(buf);
////            }
////            Self::DPrj(x) => {
////                u8::put(&0xB6, buf);
////                x.put(buf);
////            }
////            Self::Inds(xs) => {
////                Self::put_tag(0xC, xs.len() as u64, buf);
////                for x in xs {
////                    x.put(buf);
////                }
////            }
////            Self::Defs(xs) => {
////                Self::put_tag(0xD, xs.len() as u64, buf);
////                for x in xs {
////                    x.put(buf);
////                }
////            }
////            Self::Meta(x) => {
////                u8::put(&0xE0, buf);
////                x.put(buf);
////            }
////            Self::Prof(x) => {
////                u8::put(&0xE1, buf);
////                x.put(buf);
////            }
////            Self::Eval(x) => {
////                u8::put(&0xE2, buf);
////                x.put(buf);
////            }
////            Self::Chck(x) => {
////                u8::put(&0xE3, buf);
////                x.put(buf);
////            }
////            Self::Comm(x) => {
////                u8::put(&0xE4, buf);
////                x.put(buf);
////            }
////            Self::Envn(x) => {
////                u8::put(&0xE5, buf);
////                x.put(buf);
////            }
////        }
////    }
////
////    fn get(buf: &mut &[u8]) -> Result<Self, String> {
////        let tag_byte = u8::get(buf)?;
////        let small_size = tag_byte & 0b111;
////        let is_large = tag_byte & 0b1000 != 0;
////        match tag_byte {
////            0x00..=0x0F => {
////                let x = Ixon::get_size(is_large, small_size, buf)?;
////                Ok(Self::Vari(x))
////            }
////            0x90 => {
////                let u = Univ::get(buf)?;
////                Ok(Self::Sort(Box::new(u)))
////            }
////            0x10..=0x1F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let a = Address::get(buf)?;
////                let mut lvls = Vec::new();
////                for _ in 0..n {
////                    let l = Univ::get(buf)?;
////                    lvls.push(l);
////                }
////                Ok(Self::Refr(a, lvls))
////            }
////            0x20..=0x2F => {
////                let x = Ixon::get_size(is_large, small_size, buf)?;
////                let lvls = Ixon::get_array(buf)?;
////                Ok(Self::Recr(x, lvls))
////            }
////            0x30..=0x3F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let f = Ixon::get(buf)?;
////                let a = Ixon::get(buf)?;
////                let mut args = Vec::new();
////                for _ in 0..n {
////                    let x = Ixon::get(buf)?;
////                    args.push(x);
////                }
////                Ok(Self::Apps(Box::new(f), Box::new(a), args))
////            }
////            0x40..=0x4F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let mut ts = Vec::new();
////                for _ in 0..n {
////                    let x = Ixon::get(buf)?;
////                    ts.push(x);
////                }
////                let b = Ixon::get(buf)?;
////                Ok(Self::Lams(ts, Box::new(b)))
////            }
////            0x50..=0x5F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let mut ts = Vec::new();
////                for _ in 0..n {
////                    let x = Ixon::get(buf)?;
////                    ts.push(x);
////                }
////                let b = Ixon::get(buf)?;
////                Ok(Self::Alls(ts, Box::new(b)))
////            }
////            0x60..=0x6F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let t = Address::get(buf)?;
////                let x = Ixon::get(buf)?;
////                Ok(Self::Proj(t, n, Box::new(x)))
////            }
////            0x70..=0x7F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                match buf.split_at_checked(n as usize) {
////                    Some((head, rest)) => {
////                        *buf = rest;
////                        match String::from_utf8(head.to_owned()) {
////                            Ok(s) => Ok(Ixon::Strl(s)),
////                            Err(e) => Err(format!("UTF8 Error: {e}")),
////                        }
////                    }
////                    None => Err("get Ixon Strl EOF".to_string()),
////                }
////            }
////            0x80..=0x8F => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                match buf.split_at_checked(n as usize) {
////                    Some((head, rest)) => {
////                        *buf = rest;
////                        Ok(Ixon::Natl(Nat(BigUint::from_bytes_le(head))))
////                    }
////                    None => Err("get Expr Natl EOF".to_string()),
////                }
////            }
////            0x91..=0x92 => {
////                let nd = tag_byte == 0x91;
////                let t = Ixon::get(buf)?;
////                let d = Ixon::get(buf)?;
////                let b = Ixon::get(buf)?;
////                Ok(Self::LetE(nd, Box::new(t), Box::new(d), Box::new(b)))
////            }
////            0xA0..=0xAF => {
////                let len = Self::get_size(is_large, small_size, buf)?;
////                let mut vec = vec![];
////                for _ in 0..len {
////                    let s = Ixon::get(buf)?;
////                    vec.push(s);
////                }
////                Ok(Self::List(vec))
////            }
////            0xB0 => Ok(Self::Defn(Definition::get(buf)?)),
////            0xB1 => Ok(Self::Axio(Axiom::get(buf)?)),
////            0xB2 => Ok(Self::Quot(Quotient::get(buf)?)),
////            0xB3 => Ok(Self::CPrj(ConstructorProj::get(buf)?)),
////            0xB4 => Ok(Self::RPrj(RecursorProj::get(buf)?)),
////            0xB5 => Ok(Self::IPrj(InductiveProj::get(buf)?)),
////            0xB6 => Ok(Self::DPrj(DefinitionProj::get(buf)?)),
////            0xC0..=0xCF => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let mut inds = Vec::new();
////                for _ in 0..n {
////                    let x = Inductive::get(buf)?;
////                    inds.push(x);
////                }
////                Ok(Self::Inds(inds))
////            }
////            0xD0..=0xDF => {
////                let n = Ixon::get_size(is_large, small_size, buf)?;
////                let mut defs = Vec::new();
////                for _ in 0..n {
////                    let x = Definition::get(buf)?;
////                    defs.push(x);
////                }
////                Ok(Self::Defs(defs))
////            }
////            0xE0 => Ok(Self::Meta(Metadata::get(buf)?)),
////            0xE1 => Ok(Self::Prof(Proof::get(buf)?)),
////            0xE2 => Ok(Self::Eval(EvalClaim::get(buf)?)),
////            0xE3 => Ok(Self::Chck(CheckClaim::get(buf)?)),
////            0xE4 => Ok(Self::Comm(Comm::get(buf)?)),
////            0xE5 => Ok(Self::Envn(Env::get(buf)?)),
////            x => Err(format!("get Ixon invalid tag {x}")),
////        }
////    }
////}
////
////#[cfg(test)]
////pub mod tests {
////    use super::*;
////    use crate::ixon::nat::tests::arbitrary_nat;
////    use crate::ixon::univ::tests::arbitrary_univ;
////    use quickcheck::{Arbitrary, Gen};
////    use std::fmt::Write;
////    use std::ops::Range;
////    use std::ptr;
////
////    pub fn gen_range(g: &mut Gen, range: Range<usize>) -> usize {
////        let res: usize = Arbitrary::arbitrary(g);
////        if range.is_empty() {
////            0
////        } else {
////            (res % (range.end - range.start)) + range.start
////        }
////    }
////
////    pub fn gen_vec<A, F>(g: &mut Gen, size: usize, mut f: F) -> Vec<A>
////    where
////        F: FnMut(&mut Gen) -> A,
////    {
////        let len = gen_range(g, 0..size);
////        let mut vec = Vec::with_capacity(len);
////        for _ in 0..len {
////            vec.push(f(g));
////        }
////        vec
////    }
////
////    pub fn next_case<A: Copy>(g: &mut Gen, gens: &Vec<(usize, A)>) -> A {
////        let sum: usize = gens.iter().map(|x| x.0).sum();
////        let mut weight: usize = gen_range(g, 1..sum);
////        for (n, case) in gens {
////            if *n == 0 {
////                continue;
////            } else {
////                match weight.checked_sub(*n) {
////                    None | Some(0) => {
////                        return *case;
////                    }
////                    _ => {
////                        weight -= *n;
////                    }
////                }
////            }
////        }
////        unreachable!()
////    }
////
////    #[test]
////    fn unit_u64_trimmed() {
////        fn test(input: u64, expected: Vec<u8>) -> bool {
////            let mut tmp = Vec::new();
////            let n = Ixon::u64_byte_count(input);
////            Ixon::u64_put_trimmed_le(input, &mut tmp);
////            if tmp != expected {
////                return false;
////            }
////            match Ixon::u64_get_trimmed_le(n as usize, &mut tmp.as_slice()) {
////                Ok(out) => input == out,
////                Err(e) => {
////                    println!("err: {e}");
////                    false
////                }
////            }
////        }
////        assert!(test(0x0, vec![]));
////        assert!(test(0x01, vec![0x01]));
////        assert!(test(0x0000000000000100, vec![0x00, 0x01]));
////        assert!(test(0x0000000000010000, vec![0x00, 0x00, 0x01]));
////        assert!(test(0x0000000001000000, vec![0x00, 0x00, 0x00, 0x01]));
////        assert!(test(0x0000000100000000, vec![0x00, 0x00, 0x00, 0x00, 0x01]));
////        assert!(test(
////            0x0000010000000000,
////            vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
////        ));
////        assert!(test(
////            0x0001000000000000,
////            vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
////        ));
////        assert!(test(
////            0x0100000000000000,
////            vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
////        ));
////        assert!(test(
////            0x0102030405060708,
////            vec![0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
////        ));
////    }
////
////    #[quickcheck]
////    fn prop_u64_trimmed_le_readback(x: u64) -> bool {
////        let mut buf = Vec::new();
////        let n = Ixon::u64_byte_count(x);
////        Ixon::u64_put_trimmed_le(x, &mut buf);
////        match Ixon::u64_get_trimmed_le(n as usize, &mut buf.as_slice()) {
////            Ok(y) => x == y,
////            Err(e) => {
////                println!("err: {e}");
////                false
////            }
////        }
////    }
////
////    #[derive(Debug, Clone, Copy)]
////    pub enum IxonCase {
////        Vari,
////        Sort,
////        Refr,
////        Recr,
////        Apps,
////        Lams,
////        Alls,
////        Proj,
////        Strl,
////        Natl,
////        LetE,
////        List,
////        Defn,
////        Axio,
////        Quot,
////        CPrj,
////        RPrj,
////        IPrj,
////        DPrj,
////        Defs,
////        Inds,
////        Meta,
////        Prof,
////        Eval,
////        Chck,
////        Comm,
////        Envn,
////    }
////
////    pub fn arbitrary_string(g: &mut Gen, cs: usize) -> String {
////        let mut s = String::new();
////        for _ in 0..cs {
////            s.push(char::arbitrary(g));
////        }
////        s
////    }
////
////    // incremental tree generation without recursion stack overflows
////    pub fn arbitrary_ixon(g: &mut Gen, ctx: u64) -> Ixon {
////        let mut root = Ixon::Vari(0);
////        let mut stack = vec![&mut root as *mut Ixon];
////
////        while let Some(ptr) = stack.pop() {
////            let gens: Vec<(usize, IxonCase)> = vec![
////                (100, IxonCase::Vari),
////                (100, IxonCase::Sort),
////                (15, IxonCase::Refr),
////                (15, IxonCase::Recr),
////                (15, IxonCase::Apps),
////                (15, IxonCase::Lams),
////                (15, IxonCase::Alls),
////                (20, IxonCase::LetE),
////                (50, IxonCase::Proj),
////                (100, IxonCase::Strl),
////                (100, IxonCase::Natl),
////                (10, IxonCase::List),
////                (100, IxonCase::Defn),
////                (100, IxonCase::Axio),
////                (100, IxonCase::Quot),
////                (100, IxonCase::CPrj),
////                (100, IxonCase::RPrj),
////                (100, IxonCase::IPrj),
////                (100, IxonCase::DPrj),
////                (15, IxonCase::Inds),
////                (15, IxonCase::Defs),
////                (100, IxonCase::Meta),
////                (100, IxonCase::Prof),
////                (100, IxonCase::Eval),
////                (100, IxonCase::Chck),
////                (100, IxonCase::Comm),
////                (100, IxonCase::Envn),
////            ];
////
////            match next_case(g, &gens) {
////                IxonCase::Vari => {
////                    let x: u64 = Arbitrary::arbitrary(g);
////                    unsafe {
////                        ptr::replace(ptr, Ixon::Vari(x));
////                    }
////                }
////                IxonCase::Sort => {
////                    let u = arbitrary_univ(g, ctx);
////                    unsafe {
////                        ptr::replace(ptr, Ixon::Sort(Box::new(u)));
////                    }
////                }
////                IxonCase::Refr => {
////                    let addr = Address::arbitrary(g);
////                    let mut lvls = vec![];
////                    for _ in 0..gen_range(g, 0..9) {
////                        lvls.push(arbitrary_univ(g, ctx));
////                    }
////                    unsafe {
////                        ptr::replace(ptr, Ixon::Refr(addr, lvls));
////                    }
////                }
////                IxonCase::Recr => {
////                    let n = u64::arbitrary(g);
////                    let mut lvls = vec![];
////                    for _ in 0..gen_range(g, 0..9) {
////                        lvls.push(arbitrary_univ(g, ctx));
////                    }
////                    unsafe {
////                        ptr::replace(ptr, Ixon::Recr(n, lvls));
////                    }
////                }
////                IxonCase::Apps => {
////                    let mut f_box = Box::new(Ixon::default());
////                    let f_ptr: *mut Ixon = &mut *f_box;
////                    stack.push(f_ptr);
////
////                    let mut a_box = Box::new(Ixon::default());
////                    let a_ptr: *mut Ixon = &mut *a_box;
////                    stack.push(a_ptr);
////
////                    let n = gen_range(g, 0..9);
////                    let mut xs: Vec<Ixon> = Vec::with_capacity(n);
////                    xs.resize(n, Ixon::Vari(0));
////                    for i in 0..n {
////                        let p = unsafe { xs.as_mut_ptr().add(i) };
////                        stack.push(p);
////                    }
////                    unsafe {
////                        std::ptr::replace(ptr, Ixon::Apps(f_box, a_box, xs));
////                    }
////                }
////                IxonCase::Lams => {
////                    let n = gen_range(g, 0..9);
////                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
////                    ts.resize(n, Ixon::Vari(0));
////                    for i in 0..n {
////                        let p = unsafe { ts.as_mut_ptr().add(i) };
////                        stack.push(p);
////                    }
////                    let mut b_box = Box::new(Ixon::default());
////                    let b_ptr: *mut Ixon = &mut *b_box;
////                    stack.push(b_ptr);
////                    unsafe {
////                        std::ptr::replace(ptr, Ixon::Lams(ts, b_box));
////                    }
////                }
////                IxonCase::Alls => {
////                    let n = gen_range(g, 0..9);
////                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
////                    ts.resize(n, Ixon::Vari(0));
////                    for i in 0..n {
////                        let p = unsafe { ts.as_mut_ptr().add(i) };
////                        stack.push(p);
////                    }
////                    let mut b_box = Box::new(Ixon::default());
////                    let b_ptr: *mut Ixon = &mut *b_box;
////                    stack.push(b_ptr);
////                    unsafe {
////                        std::ptr::replace(ptr, Ixon::Alls(ts, b_box));
////                    }
////                }
////                IxonCase::LetE => {
////                    let nd = bool::arbitrary(g);
////                    let mut t_box = Box::new(Ixon::default());
////                    let t_ptr: *mut Ixon = &mut *t_box;
////                    stack.push(t_ptr);
////                    let mut d_box = Box::new(Ixon::default());
////                    let d_ptr: *mut Ixon = &mut *d_box;
////                    stack.push(d_ptr);
////                    let mut b_box = Box::new(Ixon::default());
////                    let b_ptr: *mut Ixon = &mut *b_box;
////                    stack.push(b_ptr);
////                    unsafe {
////                        ptr::replace(ptr, Ixon::LetE(nd, t_box, d_box, b_box));
////                    }
////                }
////                IxonCase::Proj => {
////                    let addr = Address::arbitrary(g);
////                    let n = u64::arbitrary(g);
////                    let mut t_box = Box::new(Ixon::default());
////                    let t_ptr: *mut Ixon = &mut *t_box;
////                    stack.push(t_ptr);
////                    unsafe {
////                        ptr::replace(ptr, Ixon::Proj(addr, n, t_box));
////                    }
////                }
////                IxonCase::Strl => unsafe {
////                    let size = gen_range(g, 0..9);
////                    ptr::replace(ptr, Ixon::Strl(arbitrary_string(g, size)));
////                },
////                IxonCase::Natl => {
////                    let size = gen_range(g, 0..9);
////                    unsafe {
////                        ptr::replace(ptr, Ixon::Natl(arbitrary_nat(g, size)));
////                    }
////                }
////                IxonCase::List => {
////                    let n = gen_range(g, 0..9);
////                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
////                    ts.resize(n, Ixon::Vari(0));
////                    for i in 0..n {
////                        let p = unsafe { ts.as_mut_ptr().add(i) };
////                        stack.push(p);
////                    }
////                    unsafe {
////                        std::ptr::replace(ptr, Ixon::List(ts));
////                    }
////                }
////                IxonCase::Quot => unsafe {
////                    std::ptr::replace(ptr, Ixon::Quot(Quotient::arbitrary(g)));
////                },
////                IxonCase::Axio => unsafe {
////                    std::ptr::replace(ptr, Ixon::Axio(Axiom::arbitrary(g)));
////                },
////                IxonCase::Defn => unsafe {
////                    std::ptr::replace(ptr, Ixon::Defn(Definition::arbitrary(g)));
////                },
////                IxonCase::CPrj => unsafe {
////                    std::ptr::replace(ptr, Ixon::CPrj(ConstructorProj::arbitrary(g)));
////                },
////                IxonCase::RPrj => unsafe {
////                    std::ptr::replace(ptr, Ixon::RPrj(RecursorProj::arbitrary(g)));
////                },
////                IxonCase::DPrj => unsafe {
////                    std::ptr::replace(ptr, Ixon::DPrj(DefinitionProj::arbitrary(g)));
////                },
////                IxonCase::IPrj => unsafe {
////                    std::ptr::replace(ptr, Ixon::IPrj(InductiveProj::arbitrary(g)));
////                },
////                IxonCase::Inds => unsafe {
////                    let inds = gen_vec(g, 9, Inductive::arbitrary);
////                    std::ptr::replace(ptr, Ixon::Inds(inds));
////                },
////                IxonCase::Defs => unsafe {
////                    let defs = gen_vec(g, 9, Definition::arbitrary);
////                    std::ptr::replace(ptr, Ixon::Defs(defs));
////                },
////                IxonCase::Meta => unsafe {
////                    std::ptr::replace(ptr, Ixon::Meta(Metadata::arbitrary(g)));
////                },
////                IxonCase::Prof => unsafe {
////                    std::ptr::replace(ptr, Ixon::Prof(Proof::arbitrary(g)));
////                },
////                IxonCase::Eval => unsafe {
////                    std::ptr::replace(ptr, Ixon::Eval(EvalClaim::arbitrary(g)));
////                },
////                IxonCase::Chck => unsafe {
////                    std::ptr::replace(ptr, Ixon::Chck(CheckClaim::arbitrary(g)));
////                },
////                IxonCase::Comm => unsafe {
////                    std::ptr::replace(ptr, Ixon::Comm(Comm::arbitrary(g)));
////                },
////                IxonCase::Envn => unsafe {
////                    std::ptr::replace(ptr, Ixon::Envn(Env::arbitrary(g)));
////                },
////            }
////        }
////        root
////    }
////
////    impl Arbitrary for Ixon {
////        fn arbitrary(g: &mut Gen) -> Self {
////            let ctx: u64 = Arbitrary::arbitrary(g);
////            arbitrary_ixon(g, ctx)
////        }
////    }
////
////    #[quickcheck]
////    fn prop_ixon_readback(x: Ixon) -> bool {
////        let mut buf = Vec::new();
////        Ixon::put(&x, &mut buf);
////        match Ixon::get(&mut buf.as_slice()) {
////            Ok(y) => x == y,
////            Err(e) => {
////                println!("err: {e}");
////                false
////            }
////        }
////    }
////
////    /// Parse a hex string (optional `0x`/`0X` prefix, `_` separators OK) into bytes.
////    pub fn parse_hex(s: &str) -> Result<Vec<u8>, String> {
////        // Strip prefix, drop underscores, and require an even count of hex digits.
////        let s = s.trim();
////        let s = s
////            .strip_prefix("0x")
////            .or_else(|| s.strip_prefix("0X"))
////            .unwrap_or(s);
////        let clean: String = s.chars().filter(|&c| c != '_').collect();
////
////        if clean.len() % 2 != 0 {
////            return Err("odd number of hex digits".into());
////        }
////
////        // Parse each 2-char chunk as a byte.
////        (0..clean.len())
////            .step_by(2)
////            .map(|i| {
////                u8::from_str_radix(&clean[i..i + 2], 16)
////                    .map_err(|_| format!("invalid hex at chars {}..{}", i, i + 2))
////            })
////            .collect()
////    }
////
////    /// Format bytes as a lowercase hex string with a `0x` prefix.
////    pub fn to_hex(bytes: &[u8]) -> String {
////        let mut out = String::with_capacity(2 + bytes.len() * 2);
////        out.push_str("0x");
////        for b in bytes {
////            // `{:02x}` = two lowercase hex digits, zero-padded.
////            write!(&mut out, "{b:02x}").unwrap();
////        }
////        out
////    }
////
////    #[test]
////    fn unit_ixon() {
////        fn test(input: Ixon, expected: &str) -> bool {
////            let mut tmp = Vec::new();
////            let expect = parse_hex(expected).unwrap();
////            Serialize::put(&input, &mut tmp);
////            if tmp != expect {
////                println!(
////                    "serialied {input:?} as:\n {}\n test expects:\n {}",
////                    to_hex(&tmp),
////                    to_hex(&expect),
////                );
////                return false;
////            }
////            match Serialize::get(&mut tmp.as_slice()) {
////                Ok(output) => {
////                    if input != output {
////                        println!(
////                            "deserialized {} as {output:?}, expected {input:?}",
////                            to_hex(&tmp)
////                        );
////                        false
////                    } else {
////                        true
////                    }
////                }
////                Err(e) => {
////                    println!("err: {e}");
////                    false
////                }
////            }
////        }
////        assert!(test(Ixon::Vari(0x0), "0x00"));
////        assert!(test(Ixon::Vari(0x7), "0x07"));
////        assert!(test(Ixon::Vari(0x8), "0x0808"));
////        assert!(test(Ixon::Vari(0xff), "0x08FF"));
////        assert!(test(Ixon::Vari(0x0100), "0x090001"));
////        assert!(test(Ixon::Vari(0xFFFF), "0x09FFFF"));
////        assert!(test(Ixon::Vari(0x010000), "0x0A000001"));
////        assert!(test(Ixon::Vari(0xFFFFFF), "0x0AFFFFFF"));
////        assert!(test(Ixon::Vari(0x01000000), "0x0B00000001"));
////        assert!(test(Ixon::Vari(0xFFFFFFFF), "0x0BFFFFFFFF"));
////        assert!(test(Ixon::Vari(0x0100000000), "0x0C0000000001"));
////        assert!(test(Ixon::Vari(0xFFFFFFFFFF), "0x0CFFFFFFFFFF"));
////        assert!(test(Ixon::Vari(0x010000000000), "0x0D000000000001"));
////        assert!(test(Ixon::Vari(0xFFFFFFFFFFFF), "0x0DFFFFFFFFFFFF"));
////        assert!(test(Ixon::Vari(0x01000000000000), "0x0E00000000000001"));
////        assert!(test(Ixon::Vari(0xFFFFFFFFFFFFFF), "0x0EFFFFFFFFFFFFFF"));
////        assert!(test(Ixon::Vari(0x0100000000000000), "0x0F0000000000000001"));
////        assert!(test(Ixon::Vari(0xFFFFFFFFFFFFFFFF), "0x0FFFFFFFFFFFFFFFFF"));
////        // universes use 2-bit sub-tags
////        assert!(test(Ixon::Sort(Box::new(Univ::Const(0x0))), "0x9000"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Const(0x1F))), "0x901F"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Const(0x20))), "0x902020"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Const(0xFF))), "0x9020FF"));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x0100))),
////            "0x90210001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFF))),
////            "0x9021FFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x010000))),
////            "0x9022000001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFFFF))),
////            "0x9022FFFFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x01000000))),
////            "0x902300000001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFF))),
////            "0x9023FFFFFFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x0100000000))),
////            "0x90240000000001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFF))),
////            "0x9024FFFFFFFFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x010000000000))),
////            "0x9025000000000001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFFFF))),
////            "0x9025FFFFFFFFFFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x01000000000000))),
////            "0x902600000000000001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFFFFFF))),
////            "0x9026FFFFFFFFFFFFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0x0100000000000000))),
////            "0x90270000000000000001"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFFFFFFFF))),
////            "0x9027FFFFFFFFFFFFFFFF"
////        ));
////        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x0))), "0x9040"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x1F))), "0x905F"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x20))), "0x906020"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Var(0xFF))), "0x9060FF"));
////        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x0100))), "0x90610001"));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Var(0xFFFFFFFFFFFFFFFF))),
////            "0x9067FFFFFFFFFFFFFFFF"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Add(0x0, Box::new(Univ::Const(0x0))))),
////            "0x908000"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Add(0x0, Box::new(Univ::Var(0x0))))),
////            "0x908040"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Add(0x1F, Box::new(Univ::Var(0x0))))),
////            "0x909F40"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Add(0x20, Box::new(Univ::Var(0x0))))),
////            "0x90A02040"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Add(0xFF, Box::new(Univ::Var(0x0))))),
////            "0x90A0FF40"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Add(
////                0xFFFF_FFFF_FFFF_FFFF,
////                Box::new(Univ::Var(0x0))
////            ))),
////            "0x90A7FFFFFFFFFFFFFFFF40"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Max(
////                Box::new(Univ::Var(0x0)),
////                Box::new(Univ::Var(0x0))
////            ))),
////            "0x90C04040"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Max(
////                Box::new(Univ::Var(0x0)),
////                Box::new(Univ::Var(0x1))
////            ))),
////            "0x90C04041"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Max(
////                Box::new(Univ::Var(0x1)),
////                Box::new(Univ::Var(0x0))
////            ))),
////            "0x90C04140"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::Max(
////                Box::new(Univ::Var(0x1)),
////                Box::new(Univ::Var(0x1))
////            ))),
////            "0x90C04141"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::IMax(
////                Box::new(Univ::Var(0x0)),
////                Box::new(Univ::Var(0x0))
////            ))),
////            "0x90C14040"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::IMax(
////                Box::new(Univ::Var(0x0)),
////                Box::new(Univ::Var(0x1))
////            ))),
////            "0x90C14041"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::IMax(
////                Box::new(Univ::Var(0x1)),
////                Box::new(Univ::Var(0x0))
////            ))),
////            "0x90C14140"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::IMax(
////                Box::new(Univ::Var(0x1)),
////                Box::new(Univ::Var(0x1))
////            ))),
////            "0x90C14141"
////        ));
////        assert!(test(
////            Ixon::Sort(Box::new(Univ::IMax(
////                Box::new(Univ::Var(0x1)),
////                Box::new(Univ::Var(0x1))
////            ))),
////            "0x90C14141"
////        ));
////        assert!(test(
////            Ixon::Refr(Address::hash(&[]), vec![]),
////            "0x10af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::Refr(Address::hash(&[]), vec![Univ::Var(0x0)]),
////            "0x11af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326240"
////        ));
////        assert!(test(Ixon::Recr(0x0, vec![Univ::Var(0x0)]), "0x20A140"));
////        assert!(test(
////            Ixon::Recr(0x0, vec![Univ::Var(0x0), Univ::Var(0x1)]),
////            "0x20A24041"
////        ));
////        assert!(test(
////            Ixon::Recr(0x8, vec![Univ::Var(0x0), Univ::Var(0x1)]),
////            "0x2808A24041"
////        ));
////        assert!(test(
////            Ixon::Apps(Box::new(Ixon::Vari(0x0)), Box::new(Ixon::Vari(0x1)), vec![]),
////            "0x300001"
////        ));
////        assert!(test(
////            Ixon::Apps(
////                Box::new(Ixon::Vari(0x0)),
////                Box::new(Ixon::Vari(0x1)),
////                vec![Ixon::Vari(0x2)]
////            ),
////            "0x31000102"
////        ));
////        assert!(test(
////            Ixon::Apps(
////                Box::new(Ixon::Vari(0x0)),
////                Box::new(Ixon::Vari(0x1)),
////                vec![
////                    Ixon::Vari(0x2),
////                    Ixon::Vari(0x3),
////                    Ixon::Vari(0x4),
////                    Ixon::Vari(0x5),
////                    Ixon::Vari(0x6),
////                    Ixon::Vari(0x7),
////                    Ixon::Vari(0x8),
////                    Ixon::Vari(0x9),
////                ]
////            ),
////            "0x3808000102030405060708080809"
////        ));
////        assert!(test(
////            Ixon::Lams(vec![Ixon::Vari(0x0)], Box::new(Ixon::Vari(0x1))),
////            "0x410001"
////        ));
////        assert!(test(
////            Ixon::Lams(
////                vec![
////                    Ixon::Vari(0x0),
////                    Ixon::Vari(0x1),
////                    Ixon::Vari(0x2),
////                    Ixon::Vari(0x3),
////                    Ixon::Vari(0x4),
////                    Ixon::Vari(0x5),
////                    Ixon::Vari(0x6),
////                    Ixon::Vari(0x7)
////                ],
////                Box::new(Ixon::Vari(0x8))
////            ),
////            "0x480800010203040506070808"
////        ));
////        assert!(test(
////            Ixon::Alls(vec![Ixon::Vari(0x0)], Box::new(Ixon::Vari(0x1))),
////            "0x510001"
////        ));
////        assert!(test(
////            Ixon::Alls(
////                vec![
////                    Ixon::Vari(0x0),
////                    Ixon::Vari(0x1),
////                    Ixon::Vari(0x2),
////                    Ixon::Vari(0x3),
////                    Ixon::Vari(0x4),
////                    Ixon::Vari(0x5),
////                    Ixon::Vari(0x6),
////                    Ixon::Vari(0x7)
////                ],
////                Box::new(Ixon::Vari(0x8))
////            ),
////            "0x580800010203040506070808"
////        ));
////        assert!(test(
////            Ixon::Proj(Address::hash(&[]), 0x0, Box::new(Ixon::Vari(0x0))),
////            "0x60af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326200"
////        ));
////        assert!(test(
////            Ixon::Proj(Address::hash(&[]), 0x8, Box::new(Ixon::Vari(0x0))),
////            "0x6808af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326200"
////        ));
////        assert!(test(Ixon::Strl("".to_string()), "0x70"));
////        assert!(test(Ixon::Strl("foobar".to_string()), "0x76666f6f626172"));
////        assert!(test(Ixon::Natl(Nat::new_le(&[])), "0x8100"));
////        assert!(test(Ixon::Natl(Nat::new_le(&[0x0])), "0x8100"));
////        assert!(test(Ixon::Natl(Nat::new_le(&[0xFF])), "0x81FF"));
////        assert!(test(Ixon::Natl(Nat::new_le(&[0x00, 0x01])), "0x820001"));
////        assert!(test(
////            Ixon::LetE(
////                true,
////                Box::new(Ixon::Vari(0x0)),
////                Box::new(Ixon::Vari(0x1)),
////                Box::new(Ixon::Vari(0x2))
////            ),
////            "0x91000102"
////        ));
////        assert!(test(Ixon::List(vec![]), "0xA0"));
////        assert!(test(
////            Ixon::List(vec![Ixon::Vari(0x0), Ixon::Vari(0x1), Ixon::Vari(0x2)]),
////            "0xA3000102"
////        ));
////        assert!(test(
////            Ixon::Defn(Definition {
////                kind: DefKind::Definition,
////                safety: DefSafety::Unsafe,
////                lvls: 0u64.into(),
////                typ: Address::hash(&[]),
////                value: Address::hash(&[]),
////            }),
////            "0xB000008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::Defn(Definition {
////                kind: DefKind::Opaque,
////                safety: DefSafety::Safe,
////                lvls: 1u64.into(),
////                typ: Address::hash(&[]),
////                value: Address::hash(&[]),
////            }),
////            "0xB001018101af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::Axio(Axiom {
////                is_unsafe: true,
////                lvls: 0u64.into(),
////                typ: Address::hash(&[]),
////            }),
////            "0xB1018100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::Quot(Quotient {
////                kind: QuotKind::Type,
////                lvls: 0u64.into(),
////                typ: Address::hash(&[]),
////            }),
////            "0xB2008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::CPrj(ConstructorProj {
////                idx: 0u64.into(),
////                cidx: 0u64.into(),
////                block: Address::hash(&[]),
////            }),
////            "0xB381008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::RPrj(RecursorProj {
////                idx: 0u64.into(),
////                ridx: 0u64.into(),
////                block: Address::hash(&[]),
////            }),
////            "0xB481008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::IPrj(InductiveProj {
////                idx: 0u64.into(),
////                block: Address::hash(&[]),
////            }),
////            "0xB58100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::DPrj(DefinitionProj {
////                idx: 0u64.into(),
////                block: Address::hash(&[]),
////            }),
////            "0xB68100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(Ixon::Inds(vec![]), "0xC0"));
////        assert!(test(
////            Ixon::Inds(vec![Inductive {
////                recr: false,
////                refl: false,
////                is_unsafe: false,
////                lvls: 0u64.into(),
////                params: 0u64.into(),
////                indices: 0u64.into(),
////                nested: 0u64.into(),
////                typ: Address::hash(&[]),
////                ctors: vec![],
////                recrs: vec![],
////            }]),
////            "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A0A0"
////        ));
////        assert!(test(
////            Ixon::Inds(vec![Inductive {
////                recr: false,
////                refl: false,
////                is_unsafe: false,
////                lvls: 0u64.into(),
////                params: 0u64.into(),
////                indices: 0u64.into(),
////                nested: 0u64.into(),
////                typ: Address::hash(&[]),
////                ctors: vec![],
////                recrs: vec![],
////            }]),
////            "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A0A0"
////        ));
////        assert!(test(
////            Ixon::Inds(vec![Inductive {
////                recr: false,
////                refl: false,
////                is_unsafe: false,
////                lvls: 0u64.into(),
////                params: 0u64.into(),
////                indices: 0u64.into(),
////                nested: 0u64.into(),
////                typ: Address::hash(&[]),
////                ctors: vec![Constructor {
////                    is_unsafe: false,
////                    lvls: 0u64.into(),
////                    cidx: 0u64.into(),
////                    params: 0u64.into(),
////                    fields: 0u64.into(),
////                    typ: Address::hash(&[])
////                }],
////                recrs: vec![Recursor {
////                    k: false,
////                    is_unsafe: false,
////                    lvls: 0u64.into(),
////                    params: 0u64.into(),
////                    indices: 0u64.into(),
////                    motives: 0u64.into(),
////                    minors: 0u64.into(),
////                    typ: Address::hash(&[]),
////                    rules: vec![RecursorRule {
////                        fields: 0u64.into(),
////                        rhs: Address::hash(&[])
////                    }]
////                }],
////            }]),
////            "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A10081008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A18100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(Ixon::Defs(vec![]), "0xD0"));
////        assert!(test(
////            Ixon::Defs(vec![Definition {
////                kind: DefKind::Definition,
////                safety: DefSafety::Unsafe,
////                lvls: 0u64.into(),
////                typ: Address::hash(&[]),
////                value: Address::hash(&[]),
////            }]),
////            "0xD100008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(Ixon::Meta(Metadata { map: vec![] }), "0xE0A0"));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(0u64.into(), vec![])]
////            }),
////            "0xE0A18100A0"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(0u64.into(), vec![Metadatum::Name(Name { parts: vec![] })])]
////            }),
////            "0xE0A18100A100A0"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![Metadatum::Name(Name {
////                        parts: vec![NamePart::Str("a".to_string())]
////                    })]
////                )]
////            }),
////            "0xE0A18100A100A17161"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![Metadatum::Name(Name {
////                        parts: vec![
////                            NamePart::Str("a".to_string()),
////                            NamePart::Str("b".to_string()),
////                        ]
////                    })]
////                )]
////            }),
////            "0xE0A18100A100A271617162"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![Metadatum::Name(Name {
////                        parts: vec![
////                            NamePart::Str("a".to_string()),
////                            NamePart::Str("b".to_string()),
////                            NamePart::Str("c".to_string()),
////                        ]
////                    })]
////                )]
////            }),
////            "0xE0A18100A100A3716171627163"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![Metadatum::Name(Name {
////                        parts: vec![NamePart::Num(165851424810452359u64.into())]
////                    })]
////                )]
////            }),
////            "0xE0A18100A100A1880887C551FDFD384D02"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(0u64.into(), vec![Metadatum::Info(BinderInfo::Default)])]
////            }),
////            "0xE0A18100A10100"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(0u64.into(), vec![Metadatum::Link(Address::hash(&[]))])]
////            }),
////            "0xE0A18100A102af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![
////                        Metadatum::Name(Name {
////                            parts: vec![NamePart::Str("d".to_string())]
////                        }),
////                        Metadatum::Link(Address::hash(&[])),
////                        Metadatum::Hints(ReducibilityHints::Regular(576554452)),
////                        Metadatum::Link(Address::hash(&[]))
////                    ]
////                )]
////            }),
////            "0xe0a18100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![Metadatum::Hints(ReducibilityHints::Opaque)]
////                )]
////            }),
////            "0xE0A18100A10300"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(0u64.into(), vec![Metadatum::All(vec![])])]
////            }),
////            "0xE0A18100A104A0"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(0u64.into(), vec![Metadatum::MutCtx(vec![])])]
////            }),
////            "0xE0A18100A105A0"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![(
////                    0u64.into(),
////                    vec![Metadatum::Hints(ReducibilityHints::Regular(42))]
////                )]
////            }),
////            "0xe0a18100a103022a000000"
////        ));
////        assert!(test(
////            Ixon::Meta(Metadata {
////                map: vec![
////                    (
////                        0u64.into(),
////                        vec![
////                            Metadatum::Name(Name {
////                                parts: vec![NamePart::Str("d".to_string())]
////                            }),
////                            Metadatum::Link(Address::hash(&[])),
////                            Metadatum::Hints(ReducibilityHints::Regular(576554452)),
////                            Metadatum::Link(Address::hash(&[]))
////                        ]
////                    ),
////                    (
////                        1u64.into(),
////                        vec![
////                            Metadatum::Info(BinderInfo::InstImplicit),
////                            Metadatum::Info(BinderInfo::InstImplicit),
////                            Metadatum::Info(BinderInfo::StrictImplicit),
////                        ]
////                    ),
////                    (
////                        2u64.into(),
////                        vec![
////                            Metadatum::All(vec![Name {
////                                parts: vec![NamePart::Num(165851424810452359u64.into())]
////                            }]),
////                            Metadatum::Info(BinderInfo::Default)
////                        ]
////                    ),
////                    (3u64.into(), vec![]),
////                    (4u64.into(), vec![]),
////                    (
////                        5u64.into(),
////                        vec![Metadatum::Hints(ReducibilityHints::Opaque)]
////                    ),
////                    (
////                        6u64.into(),
////                        vec![Metadatum::Name(Name {
////                            parts: vec![NamePart::Num(871843802607008850u64.into())]
////                        })]
////                    )
////                ]
////            }),
////            "0xe0a78100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32628101a30103010301028102a204a1a1880887c551fdfd384d0201008103a08104a08105a103008106a100a18808523c04ba5169190c"
////        ));
////    }
////}
////
//////}
