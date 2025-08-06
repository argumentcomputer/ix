use crate::ixon::address::Address;
use crate::ixon::claim::{Claim, Claims, Proof};
use crate::ixon::expr::Expr;
use crate::ixon::meta::Metadata;
use crate::ixon::nat::Nat;

pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

pub struct Quotient {
  pub lvls: Nat,
  pub typ: Box<Expr>,
  pub kind: QuotKind,
}

pub struct Axiom {
  pub lvls: Nat,
  pub typ: Box<Expr>,
  pub is_unsafe: bool,
}

pub enum DefKind {
  Definition,
  Opaque,
  Theorem,
}

pub enum DefSafety {
  Unsafe,
  Safe,
  Partial,
}

pub struct Definition {
  pub lvls: Nat,
  pub typ: Box<Expr>,
  pub mode: DefKind,
  pub value: Box<Expr>,
  pub safety: DefSafety,
}

pub struct Constructor {
  pub lvls: Nat,
  pub typ: Box<Expr>,
  pub cidx: Nat,
  pub params: Nat,
  pub fields: Nat,
  pub is_unsafe: bool,
}

pub struct RecursorRule {
  pub fields: Nat,
  pub rhs: Box<Expr>,
}

pub struct Recursor {
  pub lvls: Nat,
  pub typ: Box<Expr>,
  pub params: Nat,
  pub indices: Nat,
  pub motives: Nat,
  pub minors: Nat,
  pub rules: Vec<RecursorRule>,
  pub k: bool,
  pub is_unsafe: bool,
}

pub struct Inductive {
  pub lvls: Nat,
  pub typ: Box<Expr>,
  pub params: Nat,
  pub indices: Nat,
  pub ctors: Vec<Constructor>,
  pub recrs: Vec<Recursor>,
  pub nested: Nat,
  pub recr: bool,
  pub refl: bool,
  pub is_unsafe: bool,
}

pub struct InductiveProj {
  pub block: Address,
  pub idx: Nat,
}

pub struct ConstructorProj {
  pub block: Address,
  pub idx: Nat,
  pub cidx: Nat,
}

pub struct RecursorProj {
  pub block: Address,
  pub idx: Nat,
  pub ridx: Nat,
}

pub struct DefinitionProj {
  pub block: Address,
  pub idx: Nat,
}

pub struct Comm {
  pub secret: Address,
  pub payload: Address,
}

pub enum Const {
  // 0xC0
  Defn(Definition),
  // 0xC1
  Axio(Axiom),
  // 0xC2
  Quot(Quotient),
  // 0xC3
  CtorProj(ConstructorProj),
  // 0xC4
  RecrProj(RecursorProj),
  // 0xC5
  IndcProj(InductiveProj),
  // 0xC6
  DefnProj(DefinitionProj),
  // 0xC7
  MutDef(Vec<Definition>),
  // 0xC8
  MutInd(Vec<Inductive>),
  // 0xC9
  Meta(Metadata),
  // 0xCA
  Proof(Proof),
  // 0xCB
  Claim(Claim),
  // 0xCC
  Comm(Comm),
  // 0xCD
  Env(Claims),
}
