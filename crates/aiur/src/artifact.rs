//! Compiled Aiur artifacts in Ixon serialization.
//!
//! Lean's exporters (`Aiur.Artifact`) write these files and every Rust host
//! reads them through this module. The grammar uses the Ixon primitives of
//! [`crate::ixon`]. Writers are canonical: they emit [`FORMAT_VERSION`], and
//! each pool holds every entry once, in first-reference order. Decoding
//! rejects unknown tags, values out of range for their Rust type or the
//! modulus, references that do not point back into a pool, oversized pools
//! and expansions, and trailing bytes; it does not require canonical pools,
//! so re-encoding reproduces the bytes of what a writer wrote. An artifact's
//! identity is the BLAKE3 digest of its complete file ([`Digest`]).
//!
//! ```text
//! package   = "IXAIURP\0" nat(2) program option(trace)
//! execution = "IXAIURX\0" nat(2) package nats(args) nats(invalid_args)
//!             list(hint)
//! groups    = "IXAIURG\0" nat(2) nodes list(group)
//!
//! invocation = "IXAIURI\0" nat(2) string(entry) nats(args)
//!              list(nat(channel) nats(key) nats(values))
//! cases      = "IXAIURT\0" nat(2) (1 case)* 0
//! case       = string(label) bool(accept) option(string(rejects_with))
//!              option(string(exercises)) invocation
//!
//! program   = nat(version) nat(modulus) list(function) list(enum)
//!             rows list(table) list(map) list(entry)
//! rows      = list(nats)                    distinct table rows
//! function  = string(name) list(type) type(result) nat(registers)
//!             list(instruction)
//! enum      = string(name) list(string(name) list(type))
//! table     = string(name) type nats(row)   row: an index into rows
//! map       = string(name) list(type) type(result) nat(input) nat(output)
//! entry     = string(name) nat(function) list(io_type) option(io_type)
//! type      = 0 | 1 list(type) | 2 type | 3 string          field tuple ptr enum
//! io_type   = 0 | 1 list(io_type) | 2 io_type nat            field tuple array
//!           | 3 string list(string io_type)                  struct
//!           | 4 string list(string list(io_type))            enum
//! instruction (tag, then fields)
//!   0 literal dest value        1 copy dests sources    2 neg dest source
//!   3 binary dest op left right (op: 0 add, 1 sub, 2 mul, 3 div)
//!   4 guard list(reg value) string                      5 branch tests target
//!   6 jump target               7 call function args dests
//!   8 store type values dest    9 load type pointer dests
//!   10 hint string(channel) type key_type keys dests
//!   11 assert_eq lefts rights option(string) bool       12 ret values
//!   13 fail string
//! hint      = string(channel) type type(key) nats(key) nats(output)
//!
//! trace     = nat(version) nat(modulus) nats(limbs) nodes list(plan)
//!             list(chip) list(group)
//! nodes     = list(node)                    distinct polynomial nodes
//! node      = 0 nat | 1 nat | 2 back back | 3 back back | 4 back back
//!             const   var     add           sub           mul
//! back      = nat     node i's operand is node i - back, 1 <= back <= i
//! poly      = nat     the index of its root in the file's nodes
//! plan      = string(name) string(chip) nat(witnesses) nats(inputs)
//!             nats(output) list(poly(guard) action)
//!             list(nat(column) nat(source) poly(guard))
//! action    0 assign dests polys     1 inverse dest poly
//!           2 choose dests list(polys)                  3 failure dests polys
//!           4 call string polys dests                   5 store type polys dest
//!           6 load type poly dests
//!           7 hint string(channel) nat(instruction) type type(key) polys dests
//! chip      = string(name) nat(width) nat(activation) nats(inputs)
//!             polys(output) polys(constraints)
//!             list(string(channel) polys(args) nats(result) poly(enable))
//!             list(type poly(address) polys(values) poly(enable))
//!             option(nat(depth column)) nat(rank) list(slot)
//! slot      = 0 | 1 | 2 nat(column) | 3 nat(column)   plain exact gap external
//! group     = string(name) nat(width) poly(activation) polys(constraints)
//!             polys(receive) list(poly(enable) polys(args))
//!             list(string(name) nats(columns) nat(selector)
//!                  list(nat(column) poly(value)))
//! ```
//!
//! A file has at most one node pool, its trace section's or its grouping's,
//! and at most one row pool, its program's. Writers list nodes in the order
//! a left-to-right post-order walk of every `poly`, in file order, first
//! completes them, and rows in the order tables first name them. Decoding
//! expands each `poly` into a [`Polynomial`] tree, without recursion and up
//! to 2^28 nodes per pool, and each table into its rows. A trace section's
//! constants and a program's table values must lie below their section's
//! modulus.
//!
//! Every magic still reads version 1, which has no `rows` or `nodes`: a
//! table lists its rows inline (`list(nats)`) and a polynomial is a tree,
//! `poly = 0 nat | 1 nat | 2 poly poly | 3 poly poly | 4 poly poly`.
//! Re-encoding a version 1 artifact writes version 2.
use crate::{
  bytecode::{
    Binary, Constructor, Entry, Enum, Function, Instruction, Map, Program,
    Table, Type,
  },
  hints::HintEntry,
  ixon::{Reader, Writer},
  library::io::{Invocation, Stream, Streams},
  trace::{
    Action, Chip, ChipDepth, ColumnWrite, DepthSlot, FunctionGroup,
    FunctionPlan, GroupLookup, GroupMember, GroupWrite, MemoryLookup,
    Polynomial, PopulationStep, Send, TraceArtifact,
  },
  value::IoType,
};
use pool::{Interner, Nodes, RowInterner, Rows};
use std::{fmt, path::Path};

mod pool;

/// A compiled program and, when circuits were exported, their trace plan.
pub const PACKAGE_MAGIC: &[u8; 8] = b"IXAIURP\0";
/// A package bundled with one invocation and its data hints (development).
pub const EXECUTION_MAGIC: &[u8; 8] = b"IXAIURX\0";
/// Checked function groups alone, replacing a package's grouping.
pub const GROUPS_MAGIC: &[u8; 8] = b"IXAIURG\0";
/// An entry point with its arguments and input streams (a host's input).
pub const INVOCATION_MAGIC: &[u8; 8] = b"IXAIURI\0";
/// Labelled invocations with their expected verdicts (`test`, `cases`).
pub const CASES_MAGIC: &[u8; 8] = b"IXAIURT\0";
/// The artifact grammar's version that writers emit. Every magic shares it.
pub const FORMAT_VERSION: u64 = 2;
/// The conventional file extension.
pub const EXTENSION: &str = "ixa";

/// The BLAKE3 digest of an artifact's complete bytes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Digest(pub [u8; 32]);

impl Digest {
  pub fn of(bytes: &[u8]) -> Self {
    Self(*blake3::hash(bytes).as_bytes())
  }

  pub fn from_hex(hex: &str) -> Result<Self, String> {
    let bytes = hex.as_bytes();
    if bytes.len() != 64 {
      return Err(format!("artifact digest {hex:?} is not 64 hex digits"));
    }
    let nibble = |c: u8| match c {
      b'0'..=b'9' => Ok(c - b'0'),
      b'a'..=b'f' => Ok(c - b'a' + 10),
      _ => Err(format!("artifact digest {hex:?} is not lowercase hex")),
    };
    let mut out = [0u8; 32];
    for (i, pair) in bytes.chunks(2).enumerate() {
      out[i] = nibble(pair[0])? << 4 | nibble(pair[1])?;
    }
    Ok(Self(out))
  }

  /// The digest a content-addressed file name claims: a stem that is, or
  /// ends with `-` followed by, 64 lowercase hex digits.
  pub fn named_by(path: &Path) -> Option<Self> {
    let stem = path.file_stem()?.to_str()?;
    let hex = stem.rsplit_once('-').map_or(stem, |(_, hex)| hex);
    Self::from_hex(hex).ok()
  }
}

impl fmt::Display for Digest {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.iter().try_for_each(|b| write!(f, "{b:02x}"))
  }
}

impl fmt::Debug for Digest {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Digest({self})")
  }
}

/// Read an artifact file and its digest. A content-addressed file name
/// ([`Digest::named_by`]) must match the contents: a mismatch fails closed.
pub fn read(path: &Path) -> Result<(Vec<u8>, Digest), String> {
  let bytes = std::fs::read(path)
    .map_err(|e| format!("cannot read artifact {}: {e}", path.display()))?;
  let digest = Digest::of(&bytes);
  if let Some(named) = Digest::named_by(path)
    && named != digest
  {
    return Err(format!(
      "artifact {} is named by digest {named} but its contents hash to {digest}",
      path.display()
    ));
  }
  Ok((bytes, digest))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Package {
  pub program: Program,
  pub trace: Option<TraceArtifact>,
}

impl Package {
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    let mut r = Reader::new(bytes);
    let package = Self::read(&mut r)?;
    r.finish()?;
    Ok(package)
  }

  pub fn encode(&self) -> Vec<u8> {
    let mut w = Writer::new();
    self.write(&mut w);
    w.into_bytes()
  }

  /// Load an artifact file; see [`read`]. Hosts report the digest.
  pub fn load(path: &Path) -> Result<(Self, Digest), String> {
    let (bytes, digest) = read(path)?;
    let package = Self::decode(&bytes)
      .map_err(|e| format!("invalid artifact {}: {e}", path.display()))?;
    Ok((package, digest))
  }

  /// The program and its trace plan; packages without circuits are refused.
  pub fn traced(self) -> Result<(Program, TraceArtifact), String> {
    let trace = self.trace.ok_or("artifact has no circuits")?;
    Ok((self.program, trace))
  }

  fn read(r: &mut Reader<'_>) -> Result<Self, String> {
    let format = header(r, PACKAGE_MAGIC)?;
    Ok(Self {
      program: program(r, format)?,
      trace: r.option(|r| trace(r, format))?,
    })
  }

  fn write(&self, w: &mut Writer) {
    w.raw(PACKAGE_MAGIC);
    w.nat(FORMAT_VERSION);
    put_program(w, &self.program);
    w.option(self.trace.as_ref(), put_trace);
  }
}

/// A package with one invocation's arguments and data hints, for the
/// development drivers. `invalid_args` names an input the program rejects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionPackage {
  pub package: Package,
  /// The digest of the embedded package's bytes, as a standalone artifact.
  pub package_digest: Digest,
  pub args: Vec<u64>,
  pub invalid_args: Vec<u64>,
  pub hints: Vec<HintEntry>,
}

impl ExecutionPackage {
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    let mut r = Reader::new(bytes);
    header(&mut r, EXECUTION_MAGIC)?;
    let start = r.offset();
    let package = Package::read(&mut r)?;
    let package_digest = Digest::of(r.since(start));
    let args = r.nats()?;
    let invalid_args = r.nats()?;
    let hints = r.list(hint)?;
    r.finish()?;
    Ok(Self { package, package_digest, args, invalid_args, hints })
  }

  pub fn encode(&self) -> Vec<u8> {
    let mut w = Writer::new();
    w.raw(EXECUTION_MAGIC);
    w.nat(FORMAT_VERSION);
    self.package.write(&mut w);
    w.nats(&self.args);
    w.nats(&self.invalid_args);
    w.list(&self.hints, put_hint);
    w.into_bytes()
  }

  pub fn load(path: &Path) -> Result<(Self, Digest), String> {
    let (bytes, digest) = read(path)?;
    let package = Self::decode(&bytes)
      .map_err(|e| format!("invalid artifact {}: {e}", path.display()))?;
    Ok((package, digest))
  }
}

/// A function grouping (`grouping_tune`'s output) to replace a trace plan's.
pub fn decode_groups(bytes: &[u8]) -> Result<Vec<FunctionGroup>, String> {
  let mut r = Reader::new(bytes);
  let format = header(&mut r, GROUPS_MAGIC)?;
  let mut polys = Polys::read(&mut r, format, None)?;
  let groups = r.list(|r| group(r, &mut polys))?;
  r.finish()?;
  Ok(groups)
}

pub fn encode_groups(groups: &[FunctionGroup]) -> Vec<u8> {
  let mut w = Writer::new();
  w.raw(GROUPS_MAGIC);
  w.nat(FORMAT_VERSION);
  put_with_nodes(&mut w, |w, nodes| {
    w.list(groups, |w, g| put_group(w, nodes, g));
  });
  w.into_bytes()
}

impl Invocation {
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    let mut r = Reader::new(bytes);
    let invocation = invocation(&mut r)?;
    r.finish()?;
    Ok(invocation)
  }

  pub fn encode(&self) -> Vec<u8> {
    let mut w = Writer::new();
    put_invocation(&mut w, self);
    w.into_bytes()
  }

  pub fn load(path: &Path) -> Result<Self, String> {
    let bytes = std::fs::read(path)
      .map_err(|e| format!("cannot read invocation {}: {e}", path.display()))?;
    Self::decode(&bytes)
      .map_err(|e| format!("invalid invocation {}: {e}", path.display()))
  }

  /// Write the invocation through a temporary file, so that no reader sees
  /// a partial one.
  pub fn store(&self, path: &Path) -> Result<(), String> {
    let mut tmp = path.as_os_str().to_owned();
    tmp.push(format!(".tmp.{}", std::process::id()));
    let tmp = std::path::PathBuf::from(tmp);
    std::fs::write(&tmp, self.encode())
      .and_then(|()| std::fs::rename(&tmp, path))
      .map_err(|e| format!("cannot write invocation {}: {e}", path.display()))
  }
}

fn put_invocation(w: &mut Writer, i: &Invocation) {
  w.raw(INVOCATION_MAGIC);
  w.nat(FORMAT_VERSION);
  w.str(&i.entry);
  w.nats(&i.args);
  w.list(&i.streams.0, |w, s| {
    w.nat(s.channel);
    w.nats(&s.key);
    w.nats(&s.values);
  });
}

fn invocation(r: &mut Reader<'_>) -> Result<Invocation, String> {
  header(r, INVOCATION_MAGIC)?;
  Ok(Invocation {
    entry: r.string()?,
    args: r.nats()?,
    streams: Streams(r.list(|r| {
      Ok(Stream { channel: r.nat()?, key: r.nats()?, values: r.nats()? })
    })?),
  })
}

/// A labelled invocation and the verdict a test driver expects of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Case {
  pub label: String,
  /// Whether the program must accept the invocation.
  pub accept: bool,
  /// For a rejection: text the execution error must contain, so that a case
  /// is not satisfied by a failure other than the one it targets.
  pub rejects_with: Option<String>,
  /// For an acceptance: a function the execution must call, so that a case
  /// is not satisfied without reaching the path it targets.
  pub exercises: Option<String>,
  pub invocation: Invocation,
}

/// A case file: each case follows a byte 1 and a byte 0 ends the file, so a
/// writer can append cases one at a time and a truncated file is refused.
pub fn decode_cases(bytes: &[u8]) -> Result<Vec<Case>, String> {
  let mut r = Reader::new(bytes);
  header(&mut r, CASES_MAGIC)?;
  let mut cases = Vec::new();
  while r.tag("case continuation", 2)? == 1 {
    cases.push(Case {
      label: r.string()?,
      accept: r.bool()?,
      rejects_with: r.option(Reader::string)?,
      exercises: r.option(Reader::string)?,
      invocation: invocation(&mut r)?,
    });
  }
  r.finish()?;
  Ok(cases)
}

pub fn encode_cases(cases: &[Case]) -> Vec<u8> {
  let mut w = Writer::new();
  w.raw(CASES_MAGIC);
  w.nat(FORMAT_VERSION);
  for c in cases {
    w.u8(1);
    w.str(&c.label);
    w.bool(c.accept);
    w.option(c.rejects_with.as_ref(), |w, s| w.str(s));
    w.option(c.exercises.as_ref(), |w, s| w.str(s));
    put_invocation(&mut w, &c.invocation);
  }
  w.u8(0);
  w.into_bytes()
}

pub fn load_cases(path: &Path) -> Result<Vec<Case>, String> {
  let bytes = std::fs::read(path)
    .map_err(|e| format!("cannot read cases {}: {e}", path.display()))?;
  decode_cases(&bytes)
    .map_err(|e| format!("invalid cases {}: {e}", path.display()))
}

/// Data hints in the same grammar, for the in-process FFI.
pub fn decode_hints(bytes: &[u8]) -> Result<Vec<HintEntry>, String> {
  let mut r = Reader::new(bytes);
  let hints = r.list(hint)?;
  r.finish()?;
  Ok(hints)
}

pub fn encode_hints(hints: &[HintEntry]) -> Vec<u8> {
  let mut w = Writer::new();
  w.list(hints, put_hint);
  w.into_bytes()
}

/// A grammar version the reader accepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Version {
  /// Polynomials as inline trees and table rows inline.
  V1,
  /// Polynomial nodes and table rows in pools ([`FORMAT_VERSION`]).
  V2,
}

fn header(r: &mut Reader<'_>, magic: &[u8; 8]) -> Result<Version, String> {
  let found = r.raw(magic.len()).map_err(|_e| "not an Aiur artifact")?;
  if found != magic {
    let kind = |m: &[u8]| {
      if m == PACKAGE_MAGIC {
        "a compiled package"
      } else if m == EXECUTION_MAGIC {
        "an execution package"
      } else if m == GROUPS_MAGIC {
        "a function grouping"
      } else if m == INVOCATION_MAGIC {
        "an invocation"
      } else if m == CASES_MAGIC {
        "a case file"
      } else {
        "not an Aiur artifact"
      }
    };
    return Err(format!("expected {}, found {}", kind(magic), kind(found)));
  }
  match r.nat()? {
    1 => Ok(Version::V1),
    FORMAT_VERSION => Ok(Version::V2),
    version => Err(format!(
      "unsupported Aiur artifact version {version} (expected 1 or {FORMAT_VERSION})"
    )),
  }
}

// ---------------------------------------------------------------------------
// Bytecode

pub(crate) fn put_type(w: &mut Writer, ty: &Type) {
  match ty {
    Type::Field => w.u8(0),
    Type::Tuple { items } => {
      w.u8(1);
      w.list(items, put_type);
    },
    Type::Ptr { target } => {
      w.u8(2);
      put_type(w, target);
    },
    Type::Enum { name } => {
      w.u8(3);
      w.str(name);
    },
  }
}

const MAX_TYPE_DEPTH: usize = 256;

pub(crate) fn ty(r: &mut Reader<'_>) -> Result<Type, String> {
  ty_depth(r, 0)
}

fn ty_depth(r: &mut Reader<'_>, depth: usize) -> Result<Type, String> {
  if depth > MAX_TYPE_DEPTH {
    return Err("type nesting exceeds maximum depth".into());
  }
  Ok(match r.tag("type", 4)? {
    0 => Type::Field,
    1 => Type::Tuple { items: r.list(|r| ty_depth(r, depth + 1))? },
    2 => Type::Ptr { target: Box::new(ty_depth(r, depth + 1)?) },
    _ => Type::Enum { name: r.string()? },
  })
}

fn put_io_type(w: &mut Writer, ty: &IoType) {
  match ty {
    IoType::Field => w.u8(0),
    IoType::Tuple { items } => {
      w.u8(1);
      w.list(items, put_io_type);
    },
    IoType::Array { element, length } => {
      w.u8(2);
      put_io_type(w, element);
      w.usize(*length);
    },
    IoType::Struct { name, fields } => {
      w.u8(3);
      w.str(name);
      w.list(fields, |w, (name, ty)| {
        w.str(name);
        put_io_type(w, ty);
      });
    },
    IoType::Enum { name, constructors } => {
      w.u8(4);
      w.str(name);
      w.list(constructors, |w, (name, fields)| {
        w.str(name);
        w.list(fields, put_io_type);
      });
    },
  }
}

fn io_type(r: &mut Reader<'_>) -> Result<IoType, String> {
  io_type_depth(r, 0)
}

fn io_type_depth(r: &mut Reader<'_>, depth: usize) -> Result<IoType, String> {
  if depth > MAX_TYPE_DEPTH {
    return Err("IO type nesting exceeds maximum depth".into());
  }
  Ok(match r.tag("IO type", 5)? {
    0 => IoType::Field,
    1 => IoType::Tuple { items: r.list(|r| io_type_depth(r, depth + 1))? },
    2 => IoType::Array {
      element: Box::new(io_type_depth(r, depth + 1)?),
      length: r.usize()?,
    },
    3 => IoType::Struct {
      name: r.string()?,
      fields: r.list(|r| Ok((r.string()?, io_type_depth(r, depth + 1)?)))?,
    },
    _ => IoType::Enum {
      name: r.string()?,
      constructors: r.list(|r| {
        Ok((r.string()?, r.list(|r| io_type_depth(r, depth + 1))?))
      })?,
    },
  })
}

fn put_tests(w: &mut Writer, tests: &[(usize, u64)]) {
  w.list(tests, |w, &(register, value)| {
    w.usize(register);
    w.nat(value);
  });
}

fn tests(r: &mut Reader<'_>) -> Result<Vec<(usize, u64)>, String> {
  r.list(|r| Ok((r.usize()?, r.nat()?)))
}

fn put_instruction(w: &mut Writer, op: &Instruction) {
  match op {
    Instruction::Literal { dest, value } => {
      w.u8(0);
      w.usize(*dest);
      w.nat(*value);
    },
    Instruction::Copy { dest, source } => {
      w.u8(1);
      w.usizes(dest);
      w.usizes(source);
    },
    Instruction::Neg { dest, source } => {
      w.u8(2);
      w.usize(*dest);
      w.usize(*source);
    },
    Instruction::Binary { dest, operator, left, right } => {
      w.u8(3);
      w.usize(*dest);
      w.u8(match operator {
        Binary::Add => 0,
        Binary::Sub => 1,
        Binary::Mul => 2,
        Binary::Div => 3,
      });
      w.usize(*left);
      w.usize(*right);
    },
    Instruction::Guard { tests, message } => {
      w.u8(4);
      put_tests(w, tests);
      w.str(message);
    },
    Instruction::Branch { tests, otherwise } => {
      w.u8(5);
      put_tests(w, tests);
      w.usize(*otherwise);
    },
    Instruction::Jump { target } => {
      w.u8(6);
      w.usize(*target);
    },
    Instruction::Call { function, args, dest } => {
      w.u8(7);
      w.usize(*function);
      w.usizes(args);
      w.usizes(dest);
    },
    Instruction::Store { r#type, value, dest } => {
      w.u8(8);
      put_type(w, r#type);
      w.usizes(value);
      w.usize(*dest);
    },
    Instruction::Load { r#type, pointer, dest } => {
      w.u8(9);
      put_type(w, r#type);
      w.usize(*pointer);
      w.usizes(dest);
    },
    Instruction::Hint { channel, r#type, key_type, key, dest } => {
      w.u8(10);
      w.str(channel);
      put_type(w, r#type);
      put_type(w, key_type);
      w.usizes(key);
      w.usizes(dest);
    },
    Instruction::AssertEq { left, right, message, runtime_check } => {
      w.u8(11);
      w.usizes(left);
      w.usizes(right);
      w.option(message.as_ref(), |w, m| w.str(m));
      w.bool(*runtime_check);
    },
    Instruction::Ret { value } => {
      w.u8(12);
      w.usizes(value);
    },
    Instruction::Fail { message } => {
      w.u8(13);
      w.str(message);
    },
  }
}

fn instruction(r: &mut Reader<'_>) -> Result<Instruction, String> {
  Ok(match r.tag("instruction", 14)? {
    0 => Instruction::Literal { dest: r.usize()?, value: r.nat()? },
    1 => Instruction::Copy { dest: r.usizes()?, source: r.usizes()? },
    2 => Instruction::Neg { dest: r.usize()?, source: r.usize()? },
    3 => Instruction::Binary {
      dest: r.usize()?,
      operator: match r.tag("binary operator", 4)? {
        0 => Binary::Add,
        1 => Binary::Sub,
        2 => Binary::Mul,
        _ => Binary::Div,
      },
      left: r.usize()?,
      right: r.usize()?,
    },
    4 => Instruction::Guard { tests: tests(r)?, message: r.string()? },
    5 => Instruction::Branch { tests: tests(r)?, otherwise: r.usize()? },
    6 => Instruction::Jump { target: r.usize()? },
    7 => Instruction::Call {
      function: r.usize()?,
      args: r.usizes()?,
      dest: r.usizes()?,
    },
    8 => Instruction::Store {
      r#type: ty(r)?,
      value: r.usizes()?,
      dest: r.usize()?,
    },
    9 => Instruction::Load {
      r#type: ty(r)?,
      pointer: r.usize()?,
      dest: r.usizes()?,
    },
    10 => Instruction::Hint {
      channel: r.string()?,
      r#type: ty(r)?,
      key_type: ty(r)?,
      key: r.usizes()?,
      dest: r.usizes()?,
    },
    11 => Instruction::AssertEq {
      left: r.usizes()?,
      right: r.usizes()?,
      message: r.option(Reader::string)?,
      runtime_check: r.bool()?,
    },
    12 => Instruction::Ret { value: r.usizes()? },
    _ => Instruction::Fail { message: r.string()? },
  })
}

fn put_program(w: &mut Writer, p: &Program) {
  w.nat(u64::from(p.version));
  w.nat(p.modulus);
  w.list(&p.functions, |w, f| {
    w.str(&f.name);
    w.list(&f.params, put_type);
    put_type(w, &f.result);
    w.usize(f.registers);
    w.list(&f.code, put_instruction);
  });
  w.list(&p.enums, |w, e| {
    w.str(&e.name);
    w.list(&e.constructors, |w, c| {
      w.str(&c.name);
      w.list(&c.fields, put_type);
    });
  });
  let mut rows = RowInterner::default();
  let tables: Vec<Vec<usize>> = p
    .tables
    .iter()
    .map(|t| t.rows.iter().map(|row| rows.intern(row)).collect())
    .collect();
  rows.put(w);
  w.usize(p.tables.len());
  for (t, indices) in p.tables.iter().zip(&tables) {
    w.str(&t.name);
    put_type(w, &t.r#type);
    w.usizes(indices);
  }
  w.list(&p.maps, |w, m| {
    w.str(&m.name);
    w.list(&m.params, put_type);
    put_type(w, &m.result);
    w.usize(m.input);
    w.usize(m.output);
  });
  w.list(&p.entries, |w, e| {
    w.str(&e.name);
    w.usize(e.function);
    w.list(&e.inputs, put_io_type);
    w.option(e.output.as_ref(), put_io_type);
  });
}

fn program(r: &mut Reader<'_>, format: Version) -> Result<Program, String> {
  let version = r.u32()?;
  let modulus = r.nat()?;
  Ok(Program {
    version,
    modulus,
    functions: r.list(|r| {
      Ok(Function {
        name: r.string()?,
        params: r.list(ty)?,
        result: ty(r)?,
        registers: r.usize()?,
        code: r.list(instruction)?,
      })
    })?,
    enums: r.list(|r| {
      Ok(Enum {
        name: r.string()?,
        constructors: r.list(|r| {
          Ok(Constructor { name: r.string()?, fields: r.list(ty)? })
        })?,
      })
    })?,
    tables: match format {
      Version::V1 => r.list(|r| {
        Ok(Table {
          name: r.string()?,
          r#type: ty(r)?,
          rows: r.list(Reader::nats)?,
        })
      })?,
      Version::V2 => {
        let mut rows = Rows::read(r, modulus)?;
        r.list(|r| {
          Ok(Table { name: r.string()?, r#type: ty(r)?, rows: rows.table(r)? })
        })?
      },
    },
    maps: r.list(|r| {
      Ok(Map {
        name: r.string()?,
        params: r.list(ty)?,
        result: ty(r)?,
        input: r.usize()?,
        output: r.usize()?,
      })
    })?,
    entries: r.list(|r| {
      Ok(Entry {
        name: r.string()?,
        function: r.usize()?,
        inputs: r.list(io_type)?,
        output: r.option(io_type)?,
      })
    })?,
  })
}

fn put_hint(w: &mut Writer, h: &HintEntry) {
  w.str(&h.channel);
  put_type(w, &h.r#type);
  put_type(w, &h.key_type);
  w.nats(&h.key);
  w.nats(&h.output);
}

fn hint(r: &mut Reader<'_>) -> Result<HintEntry, String> {
  Ok(HintEntry {
    channel: r.string()?,
    r#type: ty(r)?,
    key_type: ty(r)?,
    key: r.nats()?,
    output: r.nats()?,
  })
}

// ---------------------------------------------------------------------------
// Trace plans

/// How a section reads its polynomials: as inline trees (version 1), or as
/// root indices into the file's node pool.
enum Polys {
  Trees,
  Pool(Nodes),
}

impl Polys {
  /// The node pool that starts a section of `format`, if it has one. Its
  /// constants must lie below `modulus` when one is given.
  fn read(
    r: &mut Reader<'_>,
    format: Version,
    modulus: Option<u64>,
  ) -> Result<Self, String> {
    Ok(match format {
      Version::V1 => Self::Trees,
      Version::V2 => Self::Pool(Nodes::read(r, modulus)?),
    })
  }

  fn poly(&mut self, r: &mut Reader<'_>) -> Result<Polynomial, String> {
    match self {
      Self::Trees => tree(r),
      Self::Pool(nodes) => nodes.poly(r),
    }
  }

  fn polys(&mut self, r: &mut Reader<'_>) -> Result<Vec<Polynomial>, String> {
    r.list(|r| self.poly(r))
  }
}

/// A version 1 polynomial tree. Polynomials can nest thousands deep (long
/// sums), so this uses an explicit stack instead of recursion.
fn tree(r: &mut Reader<'_>) -> Result<Polynomial, String> {
  // Each frame is an operator awaiting its operands, with its left operand
  // once that is complete.
  let mut frames: Vec<(u8, Option<Polynomial>)> = vec![];
  loop {
    let mut done = match r.tag("polynomial", 5)? {
      0 => Polynomial::Const(r.nat()?),
      1 => Polynomial::Var(r.usize()?),
      op => {
        frames.push((op, None));
        continue;
      },
    };
    loop {
      match frames.pop() {
        None => return Ok(done),
        Some((op, None)) => {
          frames.push((op, Some(done)));
          break;
        },
        Some((op, Some(left))) => {
          let xs = Box::new([left, done]);
          done = match op {
            2 => Polynomial::Add(xs),
            3 => Polynomial::Sub(xs),
            _ => Polynomial::Mul(xs),
          };
        },
      }
    }
  }
}

/// Write `body`, whose polynomials are interned into `nodes`, after the
/// node pool it references.
fn put_with_nodes(
  w: &mut Writer,
  body: impl FnOnce(&mut Writer, &mut Interner),
) {
  let mut nodes = Interner::default();
  let mut section = Writer::new();
  body(&mut section, &mut nodes);
  nodes.put(w);
  w.raw(&section.into_bytes());
}

fn put_poly(w: &mut Writer, nodes: &mut Interner, p: &Polynomial) {
  w.usize(nodes.intern(p));
}

fn put_polys(w: &mut Writer, nodes: &mut Interner, ps: &[Polynomial]) {
  w.list(ps, |w, p| put_poly(w, nodes, p));
}

fn put_action(w: &mut Writer, nodes: &mut Interner, action: &Action) {
  match action {
    Action::Assign { dest, values } => {
      w.u8(0);
      w.usizes(dest);
      put_polys(w, nodes, values);
    },
    Action::Inverse { dest, value } => {
      w.u8(1);
      w.usize(*dest);
      put_poly(w, nodes, value);
    },
    Action::Choose { dest, tests } => {
      w.u8(2);
      w.usizes(dest);
      w.list(tests, |w, t| put_polys(w, nodes, t));
    },
    Action::Failure { dest, differences } => {
      w.u8(3);
      w.usizes(dest);
      put_polys(w, nodes, differences);
    },
    Action::Call { name, args, dest } => {
      w.u8(4);
      w.str(name);
      put_polys(w, nodes, args);
      w.usizes(dest);
    },
    Action::Store { r#type, values, dest } => {
      w.u8(5);
      put_type(w, r#type);
      put_polys(w, nodes, values);
      w.usize(*dest);
    },
    Action::Load { r#type, address, dest } => {
      w.u8(6);
      put_type(w, r#type);
      put_poly(w, nodes, address);
      w.usizes(dest);
    },
    Action::Hint { channel, instruction, r#type, key_type, key, dest } => {
      w.u8(7);
      w.str(channel);
      w.usize(*instruction);
      put_type(w, r#type);
      put_type(w, key_type);
      put_polys(w, nodes, key);
      w.usizes(dest);
    },
  }
}

fn action(r: &mut Reader<'_>, p: &mut Polys) -> Result<Action, String> {
  Ok(match r.tag("action", 8)? {
    0 => Action::Assign { dest: r.usizes()?, values: p.polys(r)? },
    1 => Action::Inverse { dest: r.usize()?, value: p.poly(r)? },
    2 => Action::Choose { dest: r.usizes()?, tests: r.list(|r| p.polys(r))? },
    3 => Action::Failure { dest: r.usizes()?, differences: p.polys(r)? },
    4 => {
      Action::Call { name: r.string()?, args: p.polys(r)?, dest: r.usizes()? }
    },
    5 => {
      Action::Store { r#type: ty(r)?, values: p.polys(r)?, dest: r.usize()? }
    },
    6 => {
      Action::Load { r#type: ty(r)?, address: p.poly(r)?, dest: r.usizes()? }
    },
    _ => Action::Hint {
      channel: r.string()?,
      instruction: r.usize()?,
      r#type: ty(r)?,
      key_type: ty(r)?,
      key: p.polys(r)?,
      dest: r.usizes()?,
    },
  })
}

fn put_trace(w: &mut Writer, t: &TraceArtifact) {
  w.nat(u64::from(t.version));
  w.nat(t.modulus);
  w.usizes(&t.limbs);
  put_with_nodes(w, |w, nodes| {
    w.list(&t.functions, |w, f| {
      w.str(&f.name);
      w.str(&f.chip);
      w.usize(f.witnesses);
      w.usizes(&f.inputs);
      w.usizes(&f.output);
      w.list(&f.steps, |w, s| {
        put_poly(w, nodes, &s.guard);
        put_action(w, nodes, &s.action);
      });
      w.list(&f.writes, |w, c| {
        w.usize(c.column);
        w.usize(c.source);
        put_poly(w, nodes, &c.guard);
      });
    });
    w.list(&t.chips, |w, c| put_chip(w, nodes, c));
    w.list(&t.groups, |w, g| put_group(w, nodes, g));
  });
}

fn put_chip(w: &mut Writer, nodes: &mut Interner, c: &Chip) {
  w.str(&c.name);
  w.usize(c.width);
  w.usize(c.activation);
  w.usizes(&c.inputs);
  put_polys(w, nodes, &c.output);
  put_polys(w, nodes, &c.constraints);
  w.list(&c.sends, |w, s| {
    w.str(&s.channel);
    put_polys(w, nodes, &s.args);
    w.usizes(&s.result);
    put_poly(w, nodes, &s.enable);
  });
  w.list(&c.memory, |w, m| {
    put_type(w, &m.r#type);
    put_poly(w, nodes, &m.address);
    put_polys(w, nodes, &m.values);
    put_poly(w, nodes, &m.enable);
  });
  w.option(c.depth.column.as_ref(), |w, c| w.usize(*c));
  w.nat(c.depth.rank);
  w.list(&c.depth.slots, |w, s| match s {
    DepthSlot::Plain => w.u8(0),
    DepthSlot::Exact => w.u8(1),
    DepthSlot::Gap { column } => {
      w.u8(2);
      w.usize(*column);
    },
    DepthSlot::External { column } => {
      w.u8(3);
      w.usize(*column);
    },
  });
}

fn put_group(w: &mut Writer, nodes: &mut Interner, g: &FunctionGroup) {
  w.str(&g.name);
  w.usize(g.width);
  put_poly(w, nodes, &g.activation);
  put_polys(w, nodes, &g.constraints);
  put_polys(w, nodes, &g.receive);
  w.list(&g.sends, |w, s| {
    put_poly(w, nodes, &s.enable);
    put_polys(w, nodes, &s.args);
  });
  w.list(&g.members, |w, m| {
    w.str(&m.name);
    w.usizes(&m.columns);
    w.usize(m.selector);
    w.list(&m.writes, |w, x| {
      w.usize(x.column);
      put_poly(w, nodes, &x.value);
    });
  });
}

fn trace(r: &mut Reader<'_>, format: Version) -> Result<TraceArtifact, String> {
  let version = r.u32()?;
  let modulus = r.nat()?;
  let limbs = r.usizes()?;
  let mut p = Polys::read(r, format, Some(modulus))?;
  let functions = r.list(|r| {
    Ok(FunctionPlan {
      name: r.string()?,
      chip: r.string()?,
      witnesses: r.usize()?,
      inputs: r.usizes()?,
      output: r.usizes()?,
      steps: r.list(|r| {
        Ok(PopulationStep { guard: p.poly(r)?, action: action(r, &mut p)? })
      })?,
      writes: r.list(|r| {
        Ok(ColumnWrite {
          column: r.usize()?,
          source: r.usize()?,
          guard: p.poly(r)?,
        })
      })?,
    })
  })?;
  let chips = r.list(|r| chip(r, &mut p))?;
  let groups = r.list(|r| group(r, &mut p))?;
  Ok(TraceArtifact { version, modulus, limbs, functions, chips, groups })
}

fn chip(r: &mut Reader<'_>, p: &mut Polys) -> Result<Chip, String> {
  Ok(Chip {
    name: r.string()?,
    width: r.usize()?,
    activation: r.usize()?,
    inputs: r.usizes()?,
    output: p.polys(r)?,
    constraints: p.polys(r)?,
    sends: r.list(|r| {
      Ok(Send {
        channel: r.string()?,
        args: p.polys(r)?,
        result: r.usizes()?,
        enable: p.poly(r)?,
      })
    })?,
    memory: r.list(|r| {
      Ok(MemoryLookup {
        r#type: ty(r)?,
        address: p.poly(r)?,
        values: p.polys(r)?,
        enable: p.poly(r)?,
      })
    })?,
    depth: ChipDepth {
      column: r.option(Reader::usize)?,
      rank: r.nat()?,
      slots: r.list(|r| {
        Ok(match r.tag("depth slot", 4)? {
          0 => DepthSlot::Plain,
          1 => DepthSlot::Exact,
          2 => DepthSlot::Gap { column: r.usize()? },
          _ => DepthSlot::External { column: r.usize()? },
        })
      })?,
    },
  })
}

fn group(r: &mut Reader<'_>, p: &mut Polys) -> Result<FunctionGroup, String> {
  Ok(FunctionGroup {
    name: r.string()?,
    width: r.usize()?,
    activation: p.poly(r)?,
    constraints: p.polys(r)?,
    receive: p.polys(r)?,
    sends: r
      .list(|r| Ok(GroupLookup { enable: p.poly(r)?, args: p.polys(r)? }))?,
    members: r.list(|r| {
      Ok(GroupMember {
        name: r.string()?,
        columns: r.usizes()?,
        selector: r.usize()?,
        writes: r
          .list(|r| Ok(GroupWrite { column: r.usize()?, value: p.poly(r)? }))?,
      })
    })?,
  })
}

#[cfg(test)]
mod tests;
