//! Versioned binary encoding of a compiler artifact: the bytecode
//! [`Program`] and its [`TraceArtifact`], with identifying [`Metadata`].
//!
//! # Format, version 1
//!
//! All integers are little-endian. A file is `header ‖ sections ‖ digest`.
//!
//! - header: [`MAGIC`] (8 bytes), [`VERSION`] `u32`, flags `u32` (must be
//!   zero), field modulus `u64`.
//! - exactly four sections, in order, each `tag u32 ‖ length u64 ‖
//!   payload[length]`: 1 METADATA, 2 BYTECODE, 3 TRACE, 4 GROUPS. Each
//!   payload must be consumed exactly.
//! - digest: BLAKE3 of every preceding byte. Nothing may follow it. The
//!   digest is verified before any section is parsed.
//!
//! Primitives: `count` is a `u64` element count, rejected when it exceeds
//! the bytes remaining in the enclosing section (every element occupies at
//! least one byte), so no allocation exceeds the input. `usize` is a `u64`
//! that must fit the host's `usize`. `str` is `count ‖ UTF-8 bytes`. `bool`
//! is a byte 0 or 1. `option<T>` is a byte 0 (none) or 1 followed by `T`.
//! `field` is a `u64` strictly below the modulus; every field-element value
//! (literals, guard and branch test values, table rows, polynomial
//! constants) is a `field`. A vector is `count ‖ element*`.
//!
//! - `Type`: tag 0 Field, 1 Tuple(Type*), 2 Ptr(Type), 3 Enum(str).
//! - `IoType`: tag 0 Field, 1 Tuple(IoType*), 2 Array(IoType ‖ length
//!   usize), 3 Struct(name ‖ (str ‖ IoType)*), 4 Enum(name ‖ (str ‖
//!   IoType*)*). Types nest at most [`MAX_NESTING`] deep.
//! - `Polynomial`: `count (≥ 1) ‖ node*`, the polynomial being the last
//!   node. A node is tag 0 Const(field), 1 Var(usize), or 2 Add / 3 Sub /
//!   4 Mul(a usize ‖ b usize), where `a` and `b` index earlier nodes. Every
//!   node but the last is referenced exactly once, so the list is a tree.
//!   Encoding and decoding do not recurse: polynomials can be very deep.
//! - METADATA: name str ‖ compiler str ‖ source 32 bytes ‖ key str.
//! - BYTECODE ([`program_bytes`]): version u32 ‖ modulus u64 ‖ functions
//!   (name ‖ params Type* ‖ result Type ‖ registers usize ‖ code
//!   Instruction*) ‖ enums (name ‖ constructors (name ‖ fields Type*)) ‖
//!   tables (name ‖ Type ‖ rows (field*)*) ‖ maps (name ‖ params Type* ‖
//!   result Type ‖ input usize ‖ output usize) ‖ entries (name ‖ function
//!   usize ‖ inputs IoType* ‖ output option<IoType>).
//!   Instruction tags: 0 Literal(dest ‖ value field), 1 Copy(dest* ‖
//!   source*), 2 Neg(dest ‖ source), 3 Binary(dest ‖ operator u8 (0 Add,
//!   1 Sub, 2 Mul, 3 Div) ‖ left ‖ right), 4 Guard((usize ‖ field)* ‖
//!   message str), 5 Branch((usize ‖ field)* ‖ otherwise), 6 Jump(target),
//!   7 Call(function ‖ args* ‖ dest*), 8 Store(Type ‖ value* ‖ dest),
//!   9 Load(Type ‖ pointer ‖ dest*), 10 Hint(channel str ‖ Type ‖ key Type
//!   ‖ key* ‖ dest*), 11 AssertEq(left* ‖ right* ‖ message option<str> ‖
//!   runtime_check bool), 12 Ret(value*), 13 Fail(message str). Register
//!   and index operands are `usize`.
//! - TRACE: version u32 ‖ modulus u64 ‖ functions (name ‖ chip str ‖
//!   witnesses usize ‖ inputs usize* ‖ output usize* ‖ steps (guard
//!   Polynomial ‖ Action) ‖ writes (column ‖ source ‖ guard Polynomial)) ‖
//!   chips (name ‖ width ‖ activation ‖ inputs usize* ‖ output Polynomial*
//!   ‖ constraints Polynomial* ‖ sends (channel str ‖ args Polynomial* ‖
//!   result usize* ‖ enable Polynomial) ‖ memory (Type ‖ address
//!   Polynomial ‖ values Polynomial* ‖ enable Polynomial)).
//!   Action tags: 0 Assign(dest* ‖ values P*), 1 Inverse(dest ‖ value P),
//!   2 Choose(dest* ‖ tests (P*)*), 3 Failure(dest* ‖ differences P*),
//!   4 Call(name str ‖ args P* ‖ dest*), 5 Store(Type ‖ values P* ‖ dest),
//!   6 Load(Type ‖ address P ‖ dest*), 7 Hint(channel str ‖ instruction
//!   usize ‖ Type ‖ key Type ‖ key P* ‖ dest*).
//! - GROUPS: groups (name ‖ width usize ‖ activation P ‖ constraints P* ‖
//!   receive P* ‖ sends (enable P ‖ args P*) ‖ members (name ‖ columns
//!   usize* ‖ selector usize ‖ writes (column usize ‖ value P))).
//!
//! The header, bytecode and trace moduli must agree. Decoding validates
//! structure only; [`Program::check`] and [`crate::trace::TracePlan::new`]
//! validate meaning.
use crate::bytecode::{
  Binary, Constructor, Entry, Enum, Function, Instruction, Map, Program, Table,
  Type,
};
use crate::trace::{
  Action, Chip, ColumnWrite, FunctionGroup, FunctionPlan, GroupLookup,
  GroupMember, GroupWrite, MemoryLookup, Polynomial, PopulationStep, Send,
  TraceArtifact,
};
use crate::value::IoType;
use std::io::Write as _;
use std::path::Path;

pub const MAGIC: [u8; 8] = *b"AIURIMG\0";
pub const VERSION: u32 = 1;
/// The deepest nesting of a `Type` or `IoType` the decoder accepts.
pub const MAX_NESTING: usize = 256;

pub const SECTION_METADATA: u32 = 1;
pub const SECTION_BYTECODE: u32 = 2;
pub const SECTION_TRACE: u32 = 3;
pub const SECTION_GROUPS: u32 = 4;
const SECTIONS: [u32; 4] =
  [SECTION_METADATA, SECTION_BYTECODE, SECTION_TRACE, SECTION_GROUPS];

const HEADER_LEN: usize = 24;
const DIGEST_LEN: usize = 32;
const CONTENT_DOMAIN: &[u8] = b"aiur-image-content/1\0";

/// Identifies where an artifact came from. Not part of [`content_digest`].
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Metadata {
  pub name: String,
  pub compiler: String,
  pub source: [u8; 32],
  pub key: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Package {
  pub program: Program,
  pub trace: TraceArtifact,
  pub metadata: Metadata,
}

/// An append-only little-endian encoder. With a modulus, [`Writer::field`]
/// rejects noncanonical field elements; without one it accepts any word.
#[derive(Clone, Debug, Default)]
pub struct Writer {
  bytes: Vec<u8>,
  modulus: Option<u64>,
}

impl Writer {
  pub fn new() -> Self {
    Self::default()
  }
  pub fn with_modulus(modulus: u64) -> Self {
    Self { bytes: Vec::new(), modulus: Some(modulus) }
  }
  pub fn as_bytes(&self) -> &[u8] {
    &self.bytes
  }
  pub fn into_bytes(self) -> Vec<u8> {
    self.bytes
  }
  pub fn raw(&mut self, bytes: &[u8]) {
    self.bytes.extend_from_slice(bytes);
  }
  pub fn u8(&mut self, value: u8) {
    self.bytes.push(value);
  }
  pub fn u32(&mut self, value: u32) {
    self.raw(&value.to_le_bytes());
  }
  pub fn u64(&mut self, value: u64) {
    self.raw(&value.to_le_bytes());
  }
  pub fn usize(&mut self, value: usize) {
    self.u64(value as u64);
  }
  pub fn count(&mut self, count: usize) {
    self.usize(count);
  }
  pub fn bool(&mut self, value: bool) {
    self.u8(u8::from(value));
  }
  pub fn str(&mut self, value: &str) {
    self.count(value.len());
    self.raw(value.as_bytes());
  }
  /// A length-prefixed byte string.
  pub fn bytes(&mut self, value: &[u8]) {
    self.count(value.len());
    self.raw(value);
  }
  pub fn field(&mut self, value: u64) -> Result<(), String> {
    match self.modulus {
      Some(modulus) if value >= modulus => {
        Err(format!("noncanonical field element {value} for modulus {modulus}"))
      },
      _ => {
        self.u64(value);
        Ok(())
      },
    }
  }
  pub fn usizes(&mut self, values: &[usize]) {
    self.count(values.len());
    for &value in values {
      self.usize(value);
    }
  }
  pub fn sequence<T>(
    &mut self,
    items: &[T],
    mut item: impl FnMut(&mut Self, &T) -> Result<(), String>,
  ) -> Result<(), String> {
    self.count(items.len());
    items.iter().try_for_each(|x| item(self, x))
  }
}

/// A bounds-checked little-endian decoder over one byte slice.
#[derive(Clone, Debug)]
pub struct Reader<'a> {
  bytes: &'a [u8],
  position: usize,
  modulus: Option<u64>,
}

impl<'a> Reader<'a> {
  pub fn new(bytes: &'a [u8]) -> Self {
    Self { bytes, position: 0, modulus: None }
  }
  pub fn with_modulus(bytes: &'a [u8], modulus: u64) -> Self {
    Self { bytes, position: 0, modulus: Some(modulus) }
  }
  pub fn position(&self) -> usize {
    self.position
  }
  pub fn remaining(&self) -> usize {
    self.bytes.len() - self.position
  }
  /// Rejects unread bytes.
  pub fn finish(&self) -> Result<(), String> {
    match self.remaining() {
      0 => Ok(()),
      n => Err(format!("{n} unexpected trailing bytes")),
    }
  }
  pub fn take(&mut self, len: usize) -> Result<&'a [u8], String> {
    if len > self.remaining() {
      return Err("unexpected end of input".into());
    }
    let bytes = &self.bytes[self.position..self.position + len];
    self.position += len;
    Ok(bytes)
  }
  pub fn array<const N: usize>(&mut self) -> Result<[u8; N], String> {
    let mut out = [0; N];
    out.copy_from_slice(self.take(N)?);
    Ok(out)
  }
  pub fn u8(&mut self) -> Result<u8, String> {
    Ok(self.array::<1>()?[0])
  }
  pub fn u32(&mut self) -> Result<u32, String> {
    Ok(u32::from_le_bytes(self.array()?))
  }
  pub fn u64(&mut self) -> Result<u64, String> {
    Ok(u64::from_le_bytes(self.array()?))
  }
  pub fn usize(&mut self) -> Result<usize, String> {
    let value = self.u64()?;
    usize::try_from(value).map_err(|_| format!("{value} exceeds usize"))
  }
  /// An element count, bounded by the remaining input.
  pub fn count(&mut self) -> Result<usize, String> {
    let count = self.u64()?;
    match usize::try_from(count) {
      Ok(count) if count <= self.remaining() => Ok(count),
      _ => Err(format!("count {count} exceeds the remaining input")),
    }
  }
  pub fn bool(&mut self) -> Result<bool, String> {
    match self.u8()? {
      0 => Ok(false),
      1 => Ok(true),
      v => Err(format!("invalid boolean {v}")),
    }
  }
  pub fn str(&mut self) -> Result<String, String> {
    let len = self.count()?;
    let bytes = self.take(len)?;
    std::str::from_utf8(bytes)
      .map(str::to_owned)
      .map_err(|e| format!("invalid UTF-8: {e}"))
  }
  pub fn bytes(&mut self) -> Result<&'a [u8], String> {
    let len = self.count()?;
    self.take(len)
  }
  pub fn field(&mut self) -> Result<u64, String> {
    let value = self.u64()?;
    match self.modulus {
      Some(modulus) if value >= modulus => {
        Err(format!("noncanonical field element {value} for modulus {modulus}"))
      },
      _ => Ok(value),
    }
  }
  pub fn usizes(&mut self) -> Result<Vec<usize>, String> {
    self.sequence(Self::usize)
  }
  pub fn sequence<T>(
    &mut self,
    mut item: impl FnMut(&mut Self) -> Result<T, String>,
  ) -> Result<Vec<T>, String> {
    let count = self.count()?;
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
      out.push(item(self)?);
    }
    Ok(out)
  }
  pub fn option<T>(
    &mut self,
    item: impl FnOnce(&mut Self) -> Result<T, String>,
  ) -> Result<Option<T>, String> {
    match self.u8()? {
      0 => Ok(None),
      1 => item(self).map(Some),
      v => Err(format!("invalid option tag {v}")),
    }
  }
}

pub fn binary_tag(operator: Binary) -> u8 {
  match operator {
    Binary::Add => 0,
    Binary::Sub => 1,
    Binary::Mul => 2,
    Binary::Div => 3,
  }
}

fn read_binary(r: &mut Reader<'_>) -> Result<Binary, String> {
  match r.u8()? {
    0 => Ok(Binary::Add),
    1 => Ok(Binary::Sub),
    2 => Ok(Binary::Mul),
    3 => Ok(Binary::Div),
    v => Err(format!("invalid binary operator {v}")),
  }
}

pub fn write_type(w: &mut Writer, value: &Type) {
  match value {
    Type::Field => w.u8(0),
    Type::Tuple { items } => {
      w.u8(1);
      w.count(items.len());
      for item in items {
        write_type(w, item);
      }
    },
    Type::Ptr { target } => {
      w.u8(2);
      write_type(w, target);
    },
    Type::Enum { name } => {
      w.u8(3);
      w.str(name);
    },
  }
}

pub fn read_type(r: &mut Reader<'_>) -> Result<Type, String> {
  read_type_at(r, 0)
}

fn read_type_at(r: &mut Reader<'_>, depth: usize) -> Result<Type, String> {
  if depth >= MAX_NESTING {
    return Err("type nesting exceeds the limit".into());
  }
  match r.u8()? {
    0 => Ok(Type::Field),
    1 => Ok(Type::Tuple { items: r.sequence(|r| read_type_at(r, depth + 1))? }),
    2 => Ok(Type::Ptr { target: Box::new(read_type_at(r, depth + 1)?) }),
    3 => Ok(Type::Enum { name: r.str()? }),
    v => Err(format!("invalid type tag {v}")),
  }
}

pub fn write_io_type(w: &mut Writer, value: &IoType) {
  match value {
    IoType::Field => w.u8(0),
    IoType::Tuple { items } => {
      w.u8(1);
      w.count(items.len());
      for item in items {
        write_io_type(w, item);
      }
    },
    IoType::Array { element, length } => {
      w.u8(2);
      write_io_type(w, element);
      w.usize(*length);
    },
    IoType::Struct { name, fields } => {
      w.u8(3);
      w.str(name);
      w.count(fields.len());
      for (field, ty) in fields {
        w.str(field);
        write_io_type(w, ty);
      }
    },
    IoType::Enum { name, constructors } => {
      w.u8(4);
      w.str(name);
      w.count(constructors.len());
      for (constructor, fields) in constructors {
        w.str(constructor);
        w.count(fields.len());
        for ty in fields {
          write_io_type(w, ty);
        }
      }
    },
  }
}

pub fn read_io_type(r: &mut Reader<'_>) -> Result<IoType, String> {
  read_io_type_at(r, 0)
}

fn read_io_type_at(r: &mut Reader<'_>, depth: usize) -> Result<IoType, String> {
  if depth >= MAX_NESTING {
    return Err("IO type nesting exceeds the limit".into());
  }
  let next = |r: &mut Reader<'_>| read_io_type_at(r, depth + 1);
  match r.u8()? {
    0 => Ok(IoType::Field),
    1 => Ok(IoType::Tuple { items: r.sequence(next)? }),
    2 => {
      let element = Box::new(next(r)?);
      Ok(IoType::Array { element, length: r.usize()? })
    },
    3 => {
      let name = r.str()?;
      let fields = r.sequence(|r| Ok((r.str()?, next(r)?)))?;
      Ok(IoType::Struct { name, fields })
    },
    4 => {
      let name = r.str()?;
      let constructors = r.sequence(|r| Ok((r.str()?, r.sequence(next)?)))?;
      Ok(IoType::Enum { name, constructors })
    },
    v => Err(format!("invalid IO type tag {v}")),
  }
}

/// Writes `polynomial` as a post-order node list, without recursion.
pub fn write_polynomial(
  w: &mut Writer,
  polynomial: &Polynomial,
) -> Result<(), String> {
  let mut nodes = 0usize;
  let mut pending = vec![polynomial];
  while let Some(node) = pending.pop() {
    nodes += 1;
    if let Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) =
      node
    {
      pending.extend(xs.iter());
    }
  }
  w.count(nodes);
  let mut next = 0usize;
  let mut indices: Vec<usize> = Vec::new();
  let mut pending = vec![(polynomial, false)];
  while let Some((node, expanded)) = pending.pop() {
    match node {
      Polynomial::Const(value) => {
        w.u8(0);
        w.field(*value)?;
      },
      Polynomial::Var(index) => {
        w.u8(1);
        w.usize(*index);
      },
      Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
        if !expanded {
          pending.push((node, true));
          pending.push((&xs[1], false));
          pending.push((&xs[0], false));
          continue;
        }
        let (Some(b), Some(a)) = (indices.pop(), indices.pop()) else {
          unreachable!("both operands precede their node");
        };
        w.u8(match node {
          Polynomial::Add(_) => 2,
          Polynomial::Sub(_) => 3,
          _ => 4,
        });
        w.usize(a);
        w.usize(b);
      },
    }
    indices.push(next);
    next += 1;
  }
  Ok(())
}

pub fn read_polynomial(r: &mut Reader<'_>) -> Result<Polynomial, String> {
  let count = r.count()?;
  if count == 0 {
    return Err("empty polynomial".into());
  }
  let mut nodes: Vec<Option<Polynomial>> = Vec::with_capacity(count);
  let result = read_nodes(r, count, &mut nodes);
  let root = match result {
    Ok(()) => nodes.pop().flatten(),
    Err(e) => {
      nodes.drain(..).flatten().for_each(dismantle);
      return Err(e);
    },
  };
  if nodes.iter().any(Option::is_some) {
    nodes.drain(..).flatten().for_each(dismantle);
    root.into_iter().for_each(dismantle);
    return Err("unreferenced polynomial node".into());
  }
  root.ok_or_else(|| "polynomial has no root".into())
}

fn read_nodes(
  r: &mut Reader<'_>,
  count: usize,
  nodes: &mut Vec<Option<Polynomial>>,
) -> Result<(), String> {
  for index in 0..count {
    let node = match r.u8()? {
      0 => Polynomial::Const(r.field()?),
      1 => Polynomial::Var(r.usize()?),
      tag @ 2..=4 => {
        let a = r.usize()?;
        let b = r.usize()?;
        if a >= index || b >= index {
          return Err(format!(
            "polynomial node {index} references a later node"
          ));
        }
        let mut operand = |i: usize| {
          nodes
            .get_mut(i)
            .and_then(Option::take)
            .ok_or_else(|| format!("polynomial node {i} is shared"))
        };
        let left = operand(a)?;
        let right = match operand(b) {
          Ok(right) => right,
          Err(e) => {
            dismantle(left);
            return Err(e);
          },
        };
        let pair = Box::new([left, right]);
        match tag {
          2 => Polynomial::Add(pair),
          3 => Polynomial::Sub(pair),
          _ => Polynomial::Mul(pair),
        }
      },
      v => return Err(format!("invalid polynomial node tag {v}")),
    };
    nodes.push(Some(node));
  }
  Ok(())
}

/// Drops a polynomial without recursion; the derived drop of a deep tree
/// would exhaust the stack.
pub fn dismantle(polynomial: Polynomial) {
  let mut pending = vec![polynomial];
  while let Some(node) = pending.pop() {
    if let Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) =
      node
    {
      let [a, b] = *xs;
      pending.push(a);
      pending.push(b);
    }
  }
}

fn write_polynomials(w: &mut Writer, ps: &[Polynomial]) -> Result<(), String> {
  w.sequence(ps, write_polynomial)
}

fn read_polynomials(r: &mut Reader<'_>) -> Result<Vec<Polynomial>, String> {
  r.sequence(read_polynomial)
}

fn write_tests(w: &mut Writer, tests: &[(usize, u64)]) -> Result<(), String> {
  w.sequence(tests, |w, &(register, value)| {
    w.usize(register);
    w.field(value)
  })
}

fn read_tests(r: &mut Reader<'_>) -> Result<Vec<(usize, u64)>, String> {
  r.sequence(|r| Ok((r.usize()?, r.field()?)))
}

fn write_types(w: &mut Writer, types: &[Type]) {
  w.count(types.len());
  for ty in types {
    write_type(w, ty);
  }
}

fn write_instruction(
  w: &mut Writer,
  instruction: &Instruction,
) -> Result<(), String> {
  use Instruction as I;
  match instruction {
    I::Literal { dest, value } => {
      w.u8(0);
      w.usize(*dest);
      w.field(*value)?;
    },
    I::Copy { dest, source } => {
      w.u8(1);
      w.usizes(dest);
      w.usizes(source);
    },
    I::Neg { dest, source } => {
      w.u8(2);
      w.usize(*dest);
      w.usize(*source);
    },
    I::Binary { dest, operator, left, right } => {
      w.u8(3);
      w.usize(*dest);
      w.u8(binary_tag(*operator));
      w.usize(*left);
      w.usize(*right);
    },
    I::Guard { tests, message } => {
      w.u8(4);
      write_tests(w, tests)?;
      w.str(message);
    },
    I::Branch { tests, otherwise } => {
      w.u8(5);
      write_tests(w, tests)?;
      w.usize(*otherwise);
    },
    I::Jump { target } => {
      w.u8(6);
      w.usize(*target);
    },
    I::Call { function, args, dest } => {
      w.u8(7);
      w.usize(*function);
      w.usizes(args);
      w.usizes(dest);
    },
    I::Store { r#type, value, dest } => {
      w.u8(8);
      write_type(w, r#type);
      w.usizes(value);
      w.usize(*dest);
    },
    I::Load { r#type, pointer, dest } => {
      w.u8(9);
      write_type(w, r#type);
      w.usize(*pointer);
      w.usizes(dest);
    },
    I::Hint { channel, r#type, key_type, key, dest } => {
      w.u8(10);
      w.str(channel);
      write_type(w, r#type);
      write_type(w, key_type);
      w.usizes(key);
      w.usizes(dest);
    },
    I::AssertEq { left, right, message, runtime_check } => {
      w.u8(11);
      w.usizes(left);
      w.usizes(right);
      match message {
        None => w.u8(0),
        Some(message) => {
          w.u8(1);
          w.str(message);
        },
      }
      w.bool(*runtime_check);
    },
    I::Ret { value } => {
      w.u8(12);
      w.usizes(value);
    },
    I::Fail { message } => {
      w.u8(13);
      w.str(message);
    },
  }
  Ok(())
}

fn read_instruction(r: &mut Reader<'_>) -> Result<Instruction, String> {
  use Instruction as I;
  Ok(match r.u8()? {
    0 => I::Literal { dest: r.usize()?, value: r.field()? },
    1 => I::Copy { dest: r.usizes()?, source: r.usizes()? },
    2 => I::Neg { dest: r.usize()?, source: r.usize()? },
    3 => I::Binary {
      dest: r.usize()?,
      operator: read_binary(r)?,
      left: r.usize()?,
      right: r.usize()?,
    },
    4 => I::Guard { tests: read_tests(r)?, message: r.str()? },
    5 => I::Branch { tests: read_tests(r)?, otherwise: r.usize()? },
    6 => I::Jump { target: r.usize()? },
    7 => I::Call { function: r.usize()?, args: r.usizes()?, dest: r.usizes()? },
    8 => {
      I::Store { r#type: read_type(r)?, value: r.usizes()?, dest: r.usize()? }
    },
    9 => {
      I::Load { r#type: read_type(r)?, pointer: r.usize()?, dest: r.usizes()? }
    },
    10 => I::Hint {
      channel: r.str()?,
      r#type: read_type(r)?,
      key_type: read_type(r)?,
      key: r.usizes()?,
      dest: r.usizes()?,
    },
    11 => I::AssertEq {
      left: r.usizes()?,
      right: r.usizes()?,
      message: r.option(Reader::str)?,
      runtime_check: r.bool()?,
    },
    12 => I::Ret { value: r.usizes()? },
    13 => I::Fail { message: r.str()? },
    v => return Err(format!("invalid instruction tag {v}")),
  })
}

fn write_program(w: &mut Writer, program: &Program) -> Result<(), String> {
  w.u32(program.version);
  w.u64(program.modulus);
  w.sequence(&program.functions, |w, f| {
    w.str(&f.name);
    write_types(w, &f.params);
    write_type(w, &f.result);
    w.usize(f.registers);
    w.sequence(&f.code, write_instruction)
  })?;
  w.sequence(&program.enums, |w, e| {
    w.str(&e.name);
    w.sequence(&e.constructors, |w, c| {
      w.str(&c.name);
      write_types(w, &c.fields);
      Ok(())
    })
  })?;
  w.sequence(&program.tables, |w, t| {
    w.str(&t.name);
    write_type(w, &t.r#type);
    w.sequence(&t.rows, |w, row| w.sequence(row, |w, &v| w.field(v)))
  })?;
  w.sequence(&program.maps, |w, m| {
    w.str(&m.name);
    write_types(w, &m.params);
    write_type(w, &m.result);
    w.usize(m.input);
    w.usize(m.output);
    Ok(())
  })?;
  w.sequence(&program.entries, |w, e| {
    w.str(&e.name);
    w.usize(e.function);
    w.count(e.inputs.len());
    for input in &e.inputs {
      write_io_type(w, input);
    }
    match &e.output {
      None => w.u8(0),
      Some(output) => {
        w.u8(1);
        write_io_type(w, output);
      },
    }
    Ok(())
  })
}

fn read_program(r: &mut Reader<'_>, modulus: u64) -> Result<Program, String> {
  let version = r.u32()?;
  let program_modulus = r.u64()?;
  if program_modulus != modulus {
    return Err("bytecode modulus does not match the header".into());
  }
  let functions = r.sequence(|r| {
    Ok(Function {
      name: r.str()?,
      params: r.sequence(read_type)?,
      result: read_type(r)?,
      registers: r.usize()?,
      code: r.sequence(read_instruction)?,
    })
  })?;
  let enums = r.sequence(|r| {
    Ok(Enum {
      name: r.str()?,
      constructors: r.sequence(|r| {
        Ok(Constructor { name: r.str()?, fields: r.sequence(read_type)? })
      })?,
    })
  })?;
  let tables = r.sequence(|r| {
    Ok(Table {
      name: r.str()?,
      r#type: read_type(r)?,
      rows: r.sequence(|r| r.sequence(Reader::field))?,
    })
  })?;
  let maps = r.sequence(|r| {
    Ok(Map {
      name: r.str()?,
      params: r.sequence(read_type)?,
      result: read_type(r)?,
      input: r.usize()?,
      output: r.usize()?,
    })
  })?;
  let entries = r.sequence(|r| {
    Ok(Entry {
      name: r.str()?,
      function: r.usize()?,
      inputs: r.sequence(read_io_type)?,
      output: r.option(read_io_type)?,
    })
  })?;
  Ok(Program {
    version,
    modulus: program_modulus,
    functions,
    enums,
    tables,
    maps,
    entries,
  })
}

fn write_action(w: &mut Writer, action: &Action) -> Result<(), String> {
  match action {
    Action::Assign { dest, values } => {
      w.u8(0);
      w.usizes(dest);
      write_polynomials(w, values)
    },
    Action::Inverse { dest, value } => {
      w.u8(1);
      w.usize(*dest);
      write_polynomial(w, value)
    },
    Action::Choose { dest, tests } => {
      w.u8(2);
      w.usizes(dest);
      w.sequence(tests, |w, test| write_polynomials(w, test))
    },
    Action::Failure { dest, differences } => {
      w.u8(3);
      w.usizes(dest);
      write_polynomials(w, differences)
    },
    Action::Call { name, args, dest } => {
      w.u8(4);
      w.str(name);
      write_polynomials(w, args)?;
      w.usizes(dest);
      Ok(())
    },
    Action::Store { r#type, values, dest } => {
      w.u8(5);
      write_type(w, r#type);
      write_polynomials(w, values)?;
      w.usize(*dest);
      Ok(())
    },
    Action::Load { r#type, address, dest } => {
      w.u8(6);
      write_type(w, r#type);
      write_polynomial(w, address)?;
      w.usizes(dest);
      Ok(())
    },
    Action::Hint { channel, instruction, r#type, key_type, key, dest } => {
      w.u8(7);
      w.str(channel);
      w.usize(*instruction);
      write_type(w, r#type);
      write_type(w, key_type);
      write_polynomials(w, key)?;
      w.usizes(dest);
      Ok(())
    },
  }
}

fn read_action(r: &mut Reader<'_>) -> Result<Action, String> {
  Ok(match r.u8()? {
    0 => Action::Assign { dest: r.usizes()?, values: read_polynomials(r)? },
    1 => Action::Inverse { dest: r.usize()?, value: read_polynomial(r)? },
    2 => {
      Action::Choose { dest: r.usizes()?, tests: r.sequence(read_polynomials)? }
    },
    3 => {
      Action::Failure { dest: r.usizes()?, differences: read_polynomials(r)? }
    },
    4 => Action::Call {
      name: r.str()?,
      args: read_polynomials(r)?,
      dest: r.usizes()?,
    },
    5 => Action::Store {
      r#type: read_type(r)?,
      values: read_polynomials(r)?,
      dest: r.usize()?,
    },
    6 => Action::Load {
      r#type: read_type(r)?,
      address: read_polynomial(r)?,
      dest: r.usizes()?,
    },
    7 => Action::Hint {
      channel: r.str()?,
      instruction: r.usize()?,
      r#type: read_type(r)?,
      key_type: read_type(r)?,
      key: read_polynomials(r)?,
      dest: r.usizes()?,
    },
    v => return Err(format!("invalid action tag {v}")),
  })
}

fn write_trace(w: &mut Writer, trace: &TraceArtifact) -> Result<(), String> {
  w.u32(trace.version);
  w.u64(trace.modulus);
  w.sequence(&trace.functions, |w, f| {
    w.str(&f.name);
    w.str(&f.chip);
    w.usize(f.witnesses);
    w.usizes(&f.inputs);
    w.usizes(&f.output);
    w.sequence(&f.steps, |w, step| {
      write_polynomial(w, &step.guard)?;
      write_action(w, &step.action)
    })?;
    w.sequence(&f.writes, |w, write| {
      w.usize(write.column);
      w.usize(write.source);
      write_polynomial(w, &write.guard)
    })
  })?;
  w.sequence(&trace.chips, |w, c| {
    w.str(&c.name);
    w.usize(c.width);
    w.usize(c.activation);
    w.usizes(&c.inputs);
    write_polynomials(w, &c.output)?;
    write_polynomials(w, &c.constraints)?;
    w.sequence(&c.sends, |w, send| {
      w.str(&send.channel);
      write_polynomials(w, &send.args)?;
      w.usizes(&send.result);
      write_polynomial(w, &send.enable)
    })?;
    w.sequence(&c.memory, |w, lookup| {
      write_type(w, &lookup.r#type);
      write_polynomial(w, &lookup.address)?;
      write_polynomials(w, &lookup.values)?;
      write_polynomial(w, &lookup.enable)
    })
  })
}

fn read_trace(
  r: &mut Reader<'_>,
  modulus: u64,
) -> Result<TraceArtifact, String> {
  let version = r.u32()?;
  let trace_modulus = r.u64()?;
  if trace_modulus != modulus {
    return Err("trace modulus does not match the header".into());
  }
  let functions = r.sequence(|r| {
    Ok(FunctionPlan {
      name: r.str()?,
      chip: r.str()?,
      witnesses: r.usize()?,
      inputs: r.usizes()?,
      output: r.usizes()?,
      steps: r.sequence(|r| {
        Ok(PopulationStep {
          guard: read_polynomial(r)?,
          action: read_action(r)?,
        })
      })?,
      writes: r.sequence(|r| {
        Ok(ColumnWrite {
          column: r.usize()?,
          source: r.usize()?,
          guard: read_polynomial(r)?,
        })
      })?,
    })
  })?;
  let chips = r.sequence(|r| {
    Ok(Chip {
      name: r.str()?,
      width: r.usize()?,
      activation: r.usize()?,
      inputs: r.usizes()?,
      output: read_polynomials(r)?,
      constraints: read_polynomials(r)?,
      sends: r.sequence(|r| {
        Ok(Send {
          channel: r.str()?,
          args: read_polynomials(r)?,
          result: r.usizes()?,
          enable: read_polynomial(r)?,
        })
      })?,
      memory: r.sequence(|r| {
        Ok(MemoryLookup {
          r#type: read_type(r)?,
          address: read_polynomial(r)?,
          values: read_polynomials(r)?,
          enable: read_polynomial(r)?,
        })
      })?,
    })
  })?;
  Ok(TraceArtifact {
    version,
    modulus: trace_modulus,
    functions,
    chips,
    groups: Vec::new(),
  })
}

fn write_groups(
  w: &mut Writer,
  groups: &[FunctionGroup],
) -> Result<(), String> {
  w.sequence(groups, |w, g| {
    w.str(&g.name);
    w.usize(g.width);
    write_polynomial(w, &g.activation)?;
    write_polynomials(w, &g.constraints)?;
    write_polynomials(w, &g.receive)?;
    w.sequence(&g.sends, |w, send| {
      write_polynomial(w, &send.enable)?;
      write_polynomials(w, &send.args)
    })?;
    w.sequence(&g.members, |w, m| {
      w.str(&m.name);
      w.usizes(&m.columns);
      w.usize(m.selector);
      w.sequence(&m.writes, |w, write| {
        w.usize(write.column);
        write_polynomial(w, &write.value)
      })
    })
  })
}

fn read_groups(r: &mut Reader<'_>) -> Result<Vec<FunctionGroup>, String> {
  r.sequence(|r| {
    Ok(FunctionGroup {
      name: r.str()?,
      width: r.usize()?,
      activation: read_polynomial(r)?,
      constraints: read_polynomials(r)?,
      receive: read_polynomials(r)?,
      sends: r.sequence(|r| {
        Ok(GroupLookup {
          enable: read_polynomial(r)?,
          args: read_polynomials(r)?,
        })
      })?,
      members: r.sequence(|r| {
        Ok(GroupMember {
          name: r.str()?,
          columns: r.usizes()?,
          selector: r.usize()?,
          writes: r.sequence(|r| {
            Ok(GroupWrite { column: r.usize()?, value: read_polynomial(r)? })
          })?,
        })
      })?,
    })
  })
}

fn metadata_bytes(metadata: &Metadata) -> Vec<u8> {
  let mut w = Writer::new();
  w.str(&metadata.name);
  w.str(&metadata.compiler);
  w.raw(&metadata.source);
  w.str(&metadata.key);
  w.into_bytes()
}

fn read_metadata(r: &mut Reader<'_>) -> Result<Metadata, String> {
  Ok(Metadata {
    name: r.str()?,
    compiler: r.str()?,
    source: r.array()?,
    key: r.str()?,
  })
}

/// The canonical BYTECODE section payload.
pub fn program_bytes(program: &Program) -> Result<Vec<u8>, String> {
  let mut w = Writer::with_modulus(program.modulus);
  write_program(&mut w, program)?;
  Ok(w.into_bytes())
}

fn trace_payload(trace: &TraceArtifact) -> Result<Vec<u8>, String> {
  let mut w = Writer::with_modulus(trace.modulus);
  write_trace(&mut w, trace)?;
  Ok(w.into_bytes())
}

fn groups_payload(trace: &TraceArtifact) -> Result<Vec<u8>, String> {
  let mut w = Writer::with_modulus(trace.modulus);
  write_groups(&mut w, &trace.groups)?;
  Ok(w.into_bytes())
}

/// The canonical TRACE section payload followed by the GROUPS payload.
pub fn trace_bytes(trace: &TraceArtifact) -> Result<Vec<u8>, String> {
  let mut bytes = trace_payload(trace)?;
  bytes.extend(groups_payload(trace)?);
  Ok(bytes)
}

/// The semantic identity of a program and its trace artifact, independent
/// of metadata and of the file header.
pub fn content_digest(
  program: &Program,
  trace: &TraceArtifact,
) -> Result<[u8; 32], String> {
  let program = program_bytes(program)?;
  let trace = trace_bytes(trace)?;
  let mut hasher = blake3::Hasher::new();
  hasher.update(CONTENT_DOMAIN);
  hasher.update(&(program.len() as u64).to_le_bytes());
  hasher.update(&program);
  hasher.update(&(trace.len() as u64).to_le_bytes());
  hasher.update(&trace);
  Ok(*hasher.finalize().as_bytes())
}

pub fn encode(package: &Package) -> Result<Vec<u8>, String> {
  let modulus = package.program.modulus;
  if package.trace.modulus != modulus {
    return Err("program and trace moduli differ".into());
  }
  let sections = [
    metadata_bytes(&package.metadata),
    program_bytes(&package.program)?,
    trace_payload(&package.trace)?,
    groups_payload(&package.trace)?,
  ];
  let mut w = Writer::new();
  w.raw(&MAGIC);
  w.u32(VERSION);
  w.u32(0);
  w.u64(modulus);
  for (tag, payload) in SECTIONS.into_iter().zip(&sections) {
    w.u32(tag);
    w.bytes(payload);
  }
  let digest = blake3::hash(w.as_bytes());
  w.raw(digest.as_bytes());
  Ok(w.into_bytes())
}

/// The modulus and the four section payloads of a well-formed file.
fn frame(bytes: &[u8]) -> Result<(u64, [&[u8]; 4]), String> {
  let mut header = Reader::new(bytes);
  if header.array::<8>().ok() != Some(MAGIC) {
    return Err("not an Aiur artifact (bad magic)".into());
  }
  let version = header.u32()?;
  if version != VERSION {
    return Err(format!(
      "unsupported artifact version {version} (expected {VERSION})"
    ));
  }
  let flags = header.u32()?;
  if flags != 0 {
    return Err(format!("unsupported artifact flags {flags:#x}"));
  }
  let modulus = header.u64()?;
  if bytes.len() < HEADER_LEN + DIGEST_LEN {
    return Err("unexpected end of input".into());
  }
  let (body, digest) = bytes.split_at(bytes.len() - DIGEST_LEN);
  if blake3::hash(body).as_bytes() != digest {
    return Err("artifact digest mismatch".into());
  }
  let mut r = Reader::new(body.get(HEADER_LEN..).unwrap_or_default());
  let mut payloads: [&[u8]; 4] = [&[]; 4];
  for (expected, payload) in SECTIONS.into_iter().zip(&mut payloads) {
    let tag = r.u32()?;
    if tag != expected {
      return Err(format!("section tag {tag} where {expected} is expected"));
    }
    *payload = r.bytes()?;
  }
  r.finish().map_err(|e| format!("after the last section: {e}"))?;
  Ok((modulus, payloads))
}

/// The tag and payload length of each section of a well-formed file.
pub fn sections(bytes: &[u8]) -> Result<Vec<(u32, u64)>, String> {
  let (_, payloads) = frame(bytes)?;
  Ok(
    SECTIONS
      .into_iter()
      .zip(payloads)
      .map(|(t, p)| (t, p.len() as u64))
      .collect(),
  )
}

pub fn decode(bytes: &[u8]) -> Result<Package, String> {
  let (modulus, [metadata, bytecode, trace, groups]) = frame(bytes)?;
  fn section<T>(
    name: &str,
    payload: &[u8],
    modulus: u64,
    parse: impl FnOnce(&mut Reader<'_>) -> Result<T, String>,
  ) -> Result<T, String> {
    let mut r = Reader::with_modulus(payload, modulus);
    let value = parse(&mut r).and_then(|v| r.finish().map(|()| v));
    value.map_err(|e| format!("{name} section at byte {}: {e}", r.position()))
  }
  let metadata = section("metadata", metadata, modulus, read_metadata)?;
  let program =
    section("bytecode", bytecode, modulus, |r| read_program(r, modulus))?;
  let mut trace = section("trace", trace, modulus, |r| read_trace(r, modulus))?;
  trace.groups = section("groups", groups, modulus, read_groups)?;
  Ok(Package { program, trace, metadata })
}

fn is_json(bytes: &[u8]) -> bool {
  bytes.iter().find(|b| !b.is_ascii_whitespace()) == Some(&b'{')
}

pub fn read(path: &Path) -> Result<Package, String> {
  let bytes = std::fs::read(path)
    .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
  if is_json(&bytes) {
    return Err(format!(
      "{} is a JSON artifact; convert it with \
       `aiur-artifact convert <in.json> <out.aiur>`",
      path.display()
    ));
  }
  decode(&bytes).map_err(|e| format!("{}: {e}", path.display()))
}

/// Writes `package` to a temporary file beside `path`, syncs it and renames
/// it over `path`, so readers never observe a partial artifact.
pub fn write_atomic(path: &Path, package: &Package) -> Result<(), String> {
  let bytes = encode(package)?;
  let name = path
    .file_name()
    .ok_or_else(|| format!("{} has no file name", path.display()))?;
  let dir = match path.parent() {
    Some(dir) if !dir.as_os_str().is_empty() => dir,
    _ => Path::new("."),
  };
  let nanos = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .map_or(0, |d| d.as_nanos());
  let temp = dir.join(format!(
    ".{}.{}.{nanos}.tmp",
    name.to_string_lossy(),
    std::process::id()
  ));
  let result = (|| {
    let mut file =
      std::fs::OpenOptions::new().write(true).create_new(true).open(&temp)?;
    file.write_all(&bytes)?;
    file.sync_all()?;
    drop(file);
    std::fs::rename(&temp, path)?;
    if let Ok(dir) = std::fs::File::open(dir) {
      let _ = dir.sync_all();
    }
    Ok::<_, std::io::Error>(())
  })();
  result.map_err(|e| {
    let _ = std::fs::remove_file(&temp);
    format!("cannot write {}: {e}", path.display())
  })
}

#[derive(serde::Serialize)]
struct JsonPackageRef<'a> {
  program: &'a Program,
  trace: &'a TraceArtifact,
}

#[derive(serde::Deserialize)]
struct JsonPackage {
  program: Program,
  trace: TraceArtifact,
}

/// The first index at which two named lists differ, by name when available.
fn list<T: PartialEq>(
  what: &str,
  a: &[T],
  b: &[T],
  name: impl Fn(&T) -> &str,
) -> Option<String> {
  if let Some(i) = a.iter().zip(b).position(|(x, y)| x != y) {
    let (x, y) = (name(&a[i]), name(&b[i]));
    return Some(if x == y {
      format!("{what} {i} `{x}`")
    } else {
      format!("{what} {i} (`{x}` vs `{y}`)")
    });
  }
  (a.len() != b.len())
    .then(|| format!("{what} count ({} vs {})", a.len(), b.len()))
}

/// The first component in which two compiler outputs differ, named by
/// section, index and name; `None` when they are equal.
pub fn first_difference(
  (pa, ta): &(Program, TraceArtifact),
  (pb, tb): &(Program, TraceArtifact),
) -> Option<String> {
  if (pa.version, pa.modulus) != (pb.version, pb.modulus) {
    return Some("bytecode version or modulus".into());
  }
  list("bytecode function", &pa.functions, &pb.functions, |f| &f.name)
    .or_else(|| list("bytecode enum", &pa.enums, &pb.enums, |e| &e.name))
    .or_else(|| list("bytecode table", &pa.tables, &pb.tables, |t| &t.name))
    .or_else(|| list("bytecode map", &pa.maps, &pb.maps, |m| &m.name))
    .or_else(|| list("bytecode entry", &pa.entries, &pb.entries, |e| &e.name))
    .or_else(|| {
      ((ta.version, ta.modulus) != (tb.version, tb.modulus))
        .then(|| "trace version or modulus".into())
    })
    .or_else(|| {
      list("trace function", &ta.functions, &tb.functions, |f| &f.name)
    })
    .or_else(|| list("trace chip", &ta.chips, &tb.chips, |c| &c.name))
    .or_else(|| list("trace group", &ta.groups, &tb.groups, |g| &g.name))
}

/// Decodes the diagnostic JSON form `{"program": ..., "trace": ...}`.
pub fn from_json(bytes: &[u8]) -> Result<(Program, TraceArtifact), String> {
  let package: JsonPackage = crate::decode_artifact(bytes)
    .map_err(|e| format!("not a JSON compiler package: {e}"))?;
  Ok((package.program, package.trace))
}

/// The diagnostic JSON form read by [`from_json`].
pub fn to_json(
  program: &Program,
  trace: &TraceArtifact,
) -> Result<Vec<u8>, String> {
  serde_json::to_vec(&JsonPackageRef { program, trace })
    .map_err(|e| format!("cannot serialize the package: {e}"))
}

#[cfg(test)]
mod tests;
