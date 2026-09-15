use num_bigint::BigUint;
use std::{collections::BTreeMap, ops::Range};

/// These are functional execution limits, not approved circuit dimensions.
/// Even metadata remains arbitrary precision, as required by IXBF format 1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limits {
  pub functions: BigUint,
  pub constructors: BigUint,
  pub blocks: BigUint,
  pub locals: BigUint,
  pub operands: BigUint,
  pub continuations: BigUint,
  pub input_nodes: BigUint,
  pub nat_bits: BigUint,
  pub string_bytes: BigUint,
  pub byte_array_bytes: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstructorId {
  /// Exactly the original 32 little-endian bytes; not a source certificate.
  pub block: [u8; 32],
  pub member: BigUint,
  pub tag: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDeclaration {
  pub id: ConstructorId,
  pub fields: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Scalar<'a> {
  Nat(BigUint),
  String(&'a str),
  Bool(bool),
  Word32(u32),
  Goldilocks(u64),
  Extension([u64; 2]),
  Bytes(&'a [u8]),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand<'a> {
  Local(BigUint),
  Literal(Scalar<'a>),
  Erased,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operation<'a> {
  Copy(Operand<'a>),
  Primitive(super::Primitive, Vec<Operand<'a>>),
  Construct(usize, Vec<Operand<'a>>),
  Project(Operand<'a>, BigUint),
  Closure(usize, Vec<Operand<'a>>),
  Call(usize, Vec<Operand<'a>>),
  CallSelf(Vec<Operand<'a>>),
  Apply(Operand<'a>, Vec<Operand<'a>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alternative {
  pub constructor: usize,
  pub target: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instruction<'a> {
  Let(Operation<'a>, usize),
  Return(Operand<'a>),
  TailCall(usize, Vec<Operand<'a>>),
  TailCallSelf(Vec<Operand<'a>>),
  TailApply(Operand<'a>, Vec<Operand<'a>>),
  CaseConstructor(Operand<'a>, Vec<Alternative>),
  CaseNat(Operand<'a>, usize, usize),
  Branch(Operand<'a>, usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block<'a> {
  pub locals: BigUint,
  pub instruction: Instruction<'a>,
  /// Byte range in the original program file, including the local count.
  pub encoded: Range<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function<'a> {
  pub arity: BigUint,
  pub entry: usize,
  pub blocks: Vec<Block<'a>>,
}

/// Construction is private: callers receive immutable access only after
/// canonical decoding, whole-image validation, and exact re-encoding agree.
#[derive(Debug)]
pub struct Artifact<'a> {
  pub(super) source: &'a [u8],
  pub(super) limits: Limits,
  pub(super) max_steps: BigUint,
  pub(super) entry: usize,
  pub(super) constructors: Vec<ConstructorDeclaration>,
  pub(super) constructor_indices: BTreeMap<ConstructorId, usize>,
  pub(super) functions: Vec<Function<'a>>,
}

impl<'a> Artifact<'a> {
  pub fn source(&self) -> &'a [u8] {
    self.source
  }
  pub fn limits(&self) -> &Limits {
    &self.limits
  }
  pub fn max_steps(&self) -> &BigUint {
    &self.max_steps
  }
  pub fn entry(&self) -> usize {
    self.entry
  }
  pub fn constructors(&self) -> &[ConstructorDeclaration] {
    &self.constructors
  }
  pub fn functions(&self) -> &[Function<'a>] {
    &self.functions
  }

  /// Complete canonical encoding of the immutable admitted model.
  pub fn encode(&self) -> Vec<u8> {
    super::encode::program(self)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueKind<'a> {
  Scalar(Scalar<'a>),
  Constructor(ConstructorId),
  PartialApplication(usize),
  Erased,
}

/// Flat, decoder-owned preorder storage avoids recursive parse/drop stacks.
/// Children always have larger indices and each belongs to exactly one parent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueNode<'a> {
  pub kind: ValueKind<'a>,
  pub children: Vec<usize>,
}

#[derive(Debug)]
pub struct ValueForest<'a> {
  pub(super) nodes: Vec<ValueNode<'a>>,
  pub(super) roots: Vec<usize>,
  pub(super) depth: usize,
}

impl<'a> ValueForest<'a> {
  pub fn nodes(&self) -> &[ValueNode<'a>] {
    &self.nodes
  }
  pub fn roots(&self) -> &[usize] {
    &self.roots
  }
  pub fn depth(&self) -> usize {
    self.depth
  }
}

#[derive(Debug)]
pub struct Input<'a> {
  pub(super) source: &'a [u8],
  pub(super) values: ValueForest<'a>,
}

impl<'a> Input<'a> {
  pub fn source(&self) -> &'a [u8] {
    self.source
  }
  pub fn values(&self) -> &ValueForest<'a> {
    &self.values
  }
  pub fn encode(&self) -> Vec<u8> {
    super::encode::input(self)
  }
}

#[derive(Debug)]
pub struct Output<'a> {
  pub(super) source: &'a [u8],
  pub(super) values: ValueForest<'a>,
}

impl<'a> Output<'a> {
  pub fn source(&self) -> &'a [u8] {
    self.source
  }
  pub fn values(&self) -> &ValueForest<'a> {
    &self.values
  }
  pub fn encode(&self) -> Vec<u8> {
    super::encode::output(self)
  }
}
