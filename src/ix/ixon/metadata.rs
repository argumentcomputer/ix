//! Arena-based metadata for preserving Lean source information.
//!
//! Metadata types use Address internally, but serialize with u64 indices
//! into a global name index for space efficiency.
//!
//! The arena stores metadata as a tree of ExprMetaData nodes, allocated
//! bottom-up (children before parents). Each ConstantMeta variant stores
//! an ExprMeta arena plus root indices for each expression position.

#![allow(clippy::cast_possible_truncation)]

use std::collections::HashMap;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::env::{self, BinderInfo, Name, ReducibilityHints};

use super::expr::Expr;
use super::serialize::{get_expr, put_expr};
use super::tag::Tag0;
use super::univ::{Univ, get_univ, put_univ};

// ===========================================================================
// Types (use Address internally)
// ===========================================================================

/// Key-value map for Lean.Expr.mdata
pub type KVMap = Vec<(Address, DataValue)>;

/// Entry in a `CallSite` metadata node, representing one source-order argument.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CallSiteEntry {
  /// Argument exists in canonical form at App-spine position `canon_idx`.
  /// `meta` is the arena index for this argument's metadata subtree.
  Kept { canon_idx: u64, meta: u64 },
  /// Argument was collapsed. Expression stored in `ConstantMeta.meta_sharing[sharing_idx]`.
  /// `meta` is the arena index for this argument's metadata subtree
  /// (may differ from the representative's metadata — different names, refs, etc.).
  Collapsed { sharing_idx: u64, meta: u64 },
}

/// Arena node for per-expression metadata.
///
/// Nodes are allocated bottom-up (children before parents) in the arena.
/// Arena indices are u64 values pointing into `ExprMeta.nodes`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExprMetaData {
  /// Leaf node: Var, Sort, Nat, Str (no metadata)
  Leaf,
  /// Application: children = [fun, arg]
  App { children: [u64; 2] },
  /// Lambda/ForAll binder: children = [type, body]
  Binder { name: Address, info: BinderInfo, children: [u64; 2] },
  /// Let binder: children = [type, value, body]
  LetBinder { name: Address, children: [u64; 3] },
  /// Const reference (Ref or Rec): leaf in the arena
  Ref { name: Address },
  /// Projection: child = struct value
  Prj { struct_name: Address, child: u64 },
  /// Mdata wrapper: always a separate node, never absorbed into Binder/Ref/Prj
  Mdata { mdata: Vec<KVMap>, child: u64 },
  /// Surgered call-site. Replaces the entire App-spine metadata chain
  /// (outermost App down to the Ref head) with a single node. Entries are
  /// in SOURCE order. The corresponding Ixon expression is a normal App
  /// telescope — only the metadata changes shape.
  ///
  /// Sits at the outermost position so both compiler and decompiler see it
  /// first, avoiding the need to recurse through App nodes to discover surgery.
  CallSite {
    /// Name address of the referenced auxiliary (doubles as Ref name metadata).
    name: Address,
    /// Source-order entries for the argument telescope.
    entries: Vec<CallSiteEntry>,
  },
}

/// Arena for expression metadata within a single constant.
///
/// Nodes are appended bottom-up. Arena indices are stable because the arena
/// is append-only and never reset during a constant's compilation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExprMeta {
  pub nodes: Vec<ExprMetaData>,
}

impl ExprMeta {
  /// Allocate a new node in the arena, returning its index.
  pub fn alloc(&mut self, node: ExprMetaData) -> u64 {
    let idx = self.nodes.len() as u64;
    self.nodes.push(node);
    idx
  }
}

/// Per-variant metadata payload for a constant.
///
/// Each variant stores an ExprMeta arena covering all expressions in
/// that constant, plus root indices pointing into the arena for each
/// expression position (type, value, rule RHS, etc.).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum ConstantMetaInfo {
  #[default]
  Empty,
  Def {
    name: Address,
    lvls: Vec<Address>,
    hints: ReducibilityHints,
    all: Vec<Address>,
    ctx: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
    value_root: u64,
  },
  Axio {
    name: Address,
    lvls: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
  },
  Quot {
    name: Address,
    lvls: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
  },
  Indc {
    name: Address,
    lvls: Vec<Address>,
    ctors: Vec<Address>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
  },
  Ctor {
    name: Address,
    lvls: Vec<Address>,
    induct: Address,
    arena: ExprMeta,
    type_root: u64,
  },
  Rec {
    name: Address,
    lvls: Vec<Address>,
    rules: Vec<Address>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
    rule_roots: Vec<u64>,
  },
  /// Synthetic metadata for a mutual block. Each inner `Vec` is an equivalence
  /// class of alpha-equivalent constants (same MutConst index), containing the
  /// name-hash addresses of all names in that class.
  Muts {
    all: Vec<Vec<Address>>,
  },
}

impl ConstantMetaInfo {
  /// Returns a short kind name for diagnostics.
  pub fn kind_name(&self) -> &'static str {
    match self {
      Self::Empty => "empty",
      Self::Def { .. } => "def",
      Self::Axio { .. } => "axio",
      Self::Quot { .. } => "quot",
      Self::Indc { .. } => "indc",
      Self::Ctor { .. } => "ctor",
      Self::Rec { .. } => "rec",
      Self::Muts { .. } => "muts",
    }
  }
}

/// Per-constant metadata wrapper: variant payload + extension tables.
///
/// Extension tables (`meta_sharing`, `meta_refs`, `meta_univs`) form a
/// virtual address space extending the primary `Constant` tables. They are
/// used by `CallSite` nodes in the metadata arena for call-site surgery
/// roundtrip: collapsed argument expressions reference these tables via
/// `Share(idx)`, `Ref(idx)`, and universe indices.
///
/// At decompile time, extension tables are appended to the block cache,
/// creating a contiguous address space.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstantMeta {
  pub info: ConstantMetaInfo,
  /// Compiled Ixon expressions for collapsed call-site arguments.
  /// May contain `Share(idx)` references into the extended sharing table.
  pub meta_sharing: Vec<Arc<Expr>>,
  /// Extension refs table (addresses referenced by collapsed arg expressions).
  pub meta_refs: Vec<Address>,
  /// Extension univs table (universe terms in collapsed arg expressions).
  pub meta_univs: Vec<Arc<Univ>>,
}

impl Default for ConstantMeta {
  fn default() -> Self {
    Self {
      info: ConstantMetaInfo::Empty,
      meta_sharing: Vec::new(),
      meta_refs: Vec::new(),
      meta_univs: Vec::new(),
    }
  }
}

impl ConstantMeta {
  /// Wrap a `ConstantMetaInfo` payload (no extension tables).
  pub fn new(info: ConstantMetaInfo) -> Self {
    Self {
      info,
      meta_sharing: Vec::new(),
      meta_refs: Vec::new(),
      meta_univs: Vec::new(),
    }
  }

  /// Whether this metadata has any surgery extension tables.
  pub fn has_extensions(&self) -> bool {
    !self.meta_sharing.is_empty()
      || !self.meta_refs.is_empty()
      || !self.meta_univs.is_empty()
  }

  /// Delegate indexed serialization to the inner enum, then serialize
  /// extension tables.
  pub fn put_indexed(
    &self,
    idx: &NameIndex,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    self.info.put_indexed(idx, buf)?;
    // Extension tables (backward-compatible: 0-length for old constants)
    put_vec_len(self.meta_sharing.len(), buf);
    for expr in &self.meta_sharing {
      put_expr(expr, buf);
    }
    put_vec_len(self.meta_refs.len(), buf);
    for addr in &self.meta_refs {
      put_address_raw(addr, buf);
    }
    put_vec_len(self.meta_univs.len(), buf);
    for univ in &self.meta_univs {
      put_univ(univ, buf);
    }
    Ok(())
  }

  /// Delegate indexed deserialization, then deserialize extension tables.
  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    let info = ConstantMetaInfo::get_indexed(buf, rev)?;
    // Extension tables: always present (put_indexed always writes them,
    // even when empty — three zero-length vectors).
    let sharing_len = get_vec_len(buf)?;
    let mut meta_sharing = Vec::with_capacity(sharing_len);
    for _ in 0..sharing_len {
      meta_sharing.push(get_expr(buf)?);
    }
    let refs_len = get_vec_len(buf)?;
    let mut meta_refs = Vec::with_capacity(refs_len);
    for _ in 0..refs_len {
      meta_refs.push(get_address_raw(buf)?);
    }
    let univs_len = get_vec_len(buf)?;
    let mut meta_univs = Vec::with_capacity(univs_len);
    for _ in 0..univs_len {
      meta_univs.push(get_univ(buf)?);
    }
    Ok(Self { info, meta_sharing, meta_refs, meta_univs })
  }
}

/// Data values for KVMap metadata.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DataValue {
  OfString(Address),
  OfBool(bool),
  OfName(Address),
  OfNat(Address),
  OfInt(Address),
  OfSyntax(Address),
}

/// Resolve an Ixon KVMap (address-based) to Lean-level MData (name/value pairs).
///
/// Used by kernel ingress to convert expression metadata from the
/// content-addressed Ixon representation to the named kernel representation.
pub fn resolve_kvmap(
  kvm: &KVMap,
  ixon_env: &super::env::Env,
) -> Vec<(Name, env::DataValue)> {
  kvm
    .iter()
    .filter_map(|(addr, dv)| {
      let name = ixon_env.get_name(addr)?;
      let resolved = match dv {
        DataValue::OfString(a) => {
          let bytes = ixon_env.get_blob(a)?;
          env::DataValue::OfString(String::from_utf8(bytes).ok()?)
        },
        DataValue::OfBool(b) => env::DataValue::OfBool(*b),
        DataValue::OfName(a) => {
          let n = ixon_env.get_name(a)?;
          env::DataValue::OfName(n)
        },
        DataValue::OfNat(a) => {
          let bytes = ixon_env.get_blob(a)?;
          env::DataValue::OfNat(lean_ffi::nat::Nat::from_le_bytes(&bytes))
        },
        DataValue::OfInt(a) => {
          let bytes = ixon_env.get_blob(a)?;
          let int = deser_int(&bytes)?;
          env::DataValue::OfInt(int)
        },
        DataValue::OfSyntax(a) => {
          // Deserialize the Syntax tree from its blob. Mirrors
          // `compile.rs::serialize_syntax_inner`; the deserializer only
          // needs `Env::get_blob` + `Env::get_name`, so it lives here
          // rather than in `decompile.rs` (which depends on CompileState).
          let bytes = ixon_env.get_blob(a)?;
          let mut buf = bytes.as_slice();
          let syn = deser_syntax(&mut buf, ixon_env)?;
          env::DataValue::OfSyntax(Box::new(syn))
        },
      };
      Some((name, resolved))
    })
    .collect()
}

// ===========================================================================
// Syntax deserialization from blobs
// ===========================================================================
//
// These mirror the compile-side `serialize_syntax_inner` /
// `serialize_source_info` / `serialize_substring` / `serialize_preresolved`
// in `src/ix/compile.rs`. They live here (not `decompile.rs`) so that
// `resolve_kvmap` can materialize `DataValue::OfSyntax` entries during
// kernel ingress — the decompile-side helpers depend on `CompileState`,
// which isn't available in the ingress path. All we need is the `Env`
// (for blob + name lookups).

fn deser_u8(buf: &mut &[u8]) -> Option<u8> {
  let (&x, rest) = buf.split_first()?;
  *buf = rest;
  Some(x)
}

fn deser_tag0(buf: &mut &[u8]) -> Option<u64> {
  Tag0::get(buf).ok().map(|t| t.size)
}

fn deser_addr(buf: &mut &[u8]) -> Option<Address> {
  if buf.len() < 32 {
    return None;
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).ok()
}

/// Deserialize a signed `Int` from bytes (mirrors compile-side encoding in
/// `compile_data_value` / `DataValue::OfInt`).
fn deser_int(bytes: &[u8]) -> Option<env::Int> {
  let (&tag, rest) = bytes.split_first()?;
  match tag {
    0 => Some(env::Int::OfNat(lean_ffi::nat::Nat::from_le_bytes(rest))),
    1 => Some(env::Int::NegSucc(lean_ffi::nat::Nat::from_le_bytes(rest))),
    _ => None,
  }
}

fn deser_substring(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::Substring> {
  let str_addr = deser_addr(buf)?;
  let s = String::from_utf8(ixon_env.get_blob(&str_addr)?).ok()?;
  let start_pos = lean_ffi::nat::Nat::from(deser_tag0(buf)?);
  let stop_pos = lean_ffi::nat::Nat::from(deser_tag0(buf)?);
  Some(env::Substring { str: s, start_pos, stop_pos })
}

fn deser_source_info(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::SourceInfo> {
  match deser_u8(buf)? {
    0 => {
      let leading = deser_substring(buf, ixon_env)?;
      let leading_pos = lean_ffi::nat::Nat::from(deser_tag0(buf)?);
      let trailing = deser_substring(buf, ixon_env)?;
      let trailing_pos = lean_ffi::nat::Nat::from(deser_tag0(buf)?);
      Some(env::SourceInfo::Original(
        leading,
        leading_pos,
        trailing,
        trailing_pos,
      ))
    },
    1 => {
      let start = lean_ffi::nat::Nat::from(deser_tag0(buf)?);
      let end = lean_ffi::nat::Nat::from(deser_tag0(buf)?);
      let canonical = deser_u8(buf)? != 0;
      Some(env::SourceInfo::Synthetic(start, end, canonical))
    },
    2 => Some(env::SourceInfo::None),
    _ => None,
  }
}

fn deser_preresolved(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::SyntaxPreresolved> {
  match deser_u8(buf)? {
    0 => {
      let name = ixon_env.get_name(&deser_addr(buf)?)?;
      Some(env::SyntaxPreresolved::Namespace(name))
    },
    1 => {
      let name = ixon_env.get_name(&deser_addr(buf)?)?;
      let count = deser_tag0(buf)? as usize;
      let mut fields = Vec::with_capacity(count);
      for _ in 0..count {
        let addr = deser_addr(buf)?;
        fields.push(String::from_utf8(ixon_env.get_blob(&addr)?).ok()?);
      }
      Some(env::SyntaxPreresolved::Decl(name, fields))
    },
    _ => None,
  }
}

fn deser_syntax(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::Syntax> {
  match deser_u8(buf)? {
    0 => Some(env::Syntax::Missing),
    1 => {
      let info = deser_source_info(buf, ixon_env)?;
      let kind = ixon_env.get_name(&deser_addr(buf)?)?;
      let arg_count = deser_tag0(buf)? as usize;
      let mut args = Vec::with_capacity(arg_count);
      for _ in 0..arg_count {
        args.push(deser_syntax(buf, ixon_env)?);
      }
      Some(env::Syntax::Node(info, kind, args))
    },
    2 => {
      let info = deser_source_info(buf, ixon_env)?;
      let val_addr = deser_addr(buf)?;
      let val = String::from_utf8(ixon_env.get_blob(&val_addr)?).ok()?;
      Some(env::Syntax::Atom(info, val))
    },
    3 => {
      let info = deser_source_info(buf, ixon_env)?;
      let raw_val = deser_substring(buf, ixon_env)?;
      let val = ixon_env.get_name(&deser_addr(buf)?)?;
      let pr_count = deser_tag0(buf)? as usize;
      let mut preresolved = Vec::with_capacity(pr_count);
      for _ in 0..pr_count {
        preresolved.push(deser_preresolved(buf, ixon_env)?);
      }
      Some(env::Syntax::Ident(info, raw_val, val, preresolved))
    },
    _ => None,
  }
}

// ===========================================================================
// Serialization helpers
// ===========================================================================

fn put_u8(x: u8, buf: &mut Vec<u8>) {
  buf.push(x);
}

fn get_u8(buf: &mut &[u8]) -> Result<u8, String> {
  match buf.split_first() {
    Some((&x, rest)) => {
      *buf = rest;
      Ok(x)
    },
    None => Err("get_u8: EOF".to_string()),
  }
}

fn put_bool(x: bool, buf: &mut Vec<u8>) {
  buf.push(if x { 1 } else { 0 });
}

fn get_bool(buf: &mut &[u8]) -> Result<bool, String> {
  match get_u8(buf)? {
    0 => Ok(false),
    1 => Ok(true),
    x => Err(format!("get_bool: invalid {x}")),
  }
}

/// Serialize a raw 32-byte address (for blob addresses not in the name index).
fn put_address_raw(addr: &Address, buf: &mut Vec<u8>) {
  buf.extend_from_slice(addr.as_bytes());
}

/// Deserialize a raw 32-byte address.
fn get_address_raw(buf: &mut &[u8]) -> Result<Address, String> {
  if buf.len() < 32 {
    return Err(format!("get_address_raw: need 32 bytes, have {}", buf.len()));
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes)
    .map_err(|_e| "get_address_raw: invalid".to_string())
}

fn put_u64(x: u64, buf: &mut Vec<u8>) {
  Tag0::new(x).put(buf);
}

fn get_u64(buf: &mut &[u8]) -> Result<u64, String> {
  Ok(Tag0::get(buf)?.size)
}

pub(super) fn put_vec_len(len: usize, buf: &mut Vec<u8>) {
  Tag0::new(len as u64).put(buf);
}

pub(super) fn get_vec_len(buf: &mut &[u8]) -> Result<usize, String> {
  Ok(Tag0::get(buf)?.size as usize)
}

// ===========================================================================
// BinderInfo and ReducibilityHints serialization
// ===========================================================================

impl BinderInfo {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Default => put_u8(0, buf),
      Self::Implicit => put_u8(1, buf),
      Self::StrictImplicit => put_u8(2, buf),
      Self::InstImplicit => put_u8(3, buf),
    }
  }

  pub fn get_ser(buf: &mut &[u8]) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Default),
      1 => Ok(Self::Implicit),
      2 => Ok(Self::StrictImplicit),
      3 => Ok(Self::InstImplicit),
      x => Err(format!("BinderInfo::get: invalid {x}")),
    }
  }
}

impl ReducibilityHints {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Opaque => put_u8(0, buf),
      Self::Abbrev => put_u8(1, buf),
      Self::Regular(x) => {
        put_u8(2, buf);
        Tag0::new(u64::from(*x)).put(buf);
      },
    }
  }

  pub fn get_ser(buf: &mut &[u8]) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Opaque),
      1 => Ok(Self::Abbrev),
      2 => {
        let tag = Tag0::get(buf)?;
        Ok(Self::Regular(tag.size as u32))
      },
      x => Err(format!("ReducibilityHints::get: invalid {x}")),
    }
  }
}

// ===========================================================================
// Indexed serialization (Address -> u64 index)
// ===========================================================================

/// Name index for serialization: Address -> u64
pub type NameIndex = HashMap<Address, u64>;

/// Reverse name index for deserialization: position -> Address
pub type NameReverseIndex = Vec<Address>;

pub(super) fn put_idx(
  addr: &Address,
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  let i = idx.get(addr).copied().ok_or_else(|| {
    format!(
      "put_idx: address {:?} not in name index (index has {} entries)",
      addr,
      idx.len()
    )
  })?;
  put_u64(i, buf);
  Ok(())
}

pub(super) fn get_idx(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<Address, String> {
  let i = get_u64(buf)? as usize;
  rev
    .get(i)
    .cloned()
    .ok_or_else(|| format!("invalid name index {i}, max {}", rev.len()))
}

fn put_idx_vec(
  addrs: &[Address],
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_vec_len(addrs.len(), buf);
  for a in addrs {
    put_idx(a, idx, buf)?;
  }
  Ok(())
}

fn get_idx_vec(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<Vec<Address>, String> {
  let len = get_vec_len(buf)?;
  let mut v = Vec::with_capacity(len);
  for _ in 0..len {
    v.push(get_idx(buf, rev)?);
  }
  Ok(v)
}

// ===========================================================================
// DataValue indexed serialization
// ===========================================================================

impl DataValue {
  pub fn put_indexed(
    &self,
    idx: &NameIndex,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    match self {
      // OfString, OfNat, OfInt, OfSyntax hold blob addresses (not in name index)
      Self::OfString(a) => {
        put_u8(0, buf);
        put_address_raw(a, buf);
      },
      Self::OfBool(b) => {
        put_u8(1, buf);
        put_bool(*b, buf);
      },
      // OfName holds a name address (in name index)
      Self::OfName(a) => {
        put_u8(2, buf);
        put_idx(a, idx, buf)?;
      },
      Self::OfNat(a) => {
        put_u8(3, buf);
        put_address_raw(a, buf);
      },
      Self::OfInt(a) => {
        put_u8(4, buf);
        put_address_raw(a, buf);
      },
      Self::OfSyntax(a) => {
        put_u8(5, buf);
        put_address_raw(a, buf);
      },
    }
    Ok(())
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::OfString(get_address_raw(buf)?)),
      1 => Ok(Self::OfBool(get_bool(buf)?)),
      2 => Ok(Self::OfName(get_idx(buf, rev)?)),
      3 => Ok(Self::OfNat(get_address_raw(buf)?)),
      4 => Ok(Self::OfInt(get_address_raw(buf)?)),
      5 => Ok(Self::OfSyntax(get_address_raw(buf)?)),
      x => Err(format!("DataValue::get: invalid tag {x}")),
    }
  }
}

// ===========================================================================
// KVMap and mdata indexed serialization
// ===========================================================================

fn put_kvmap_indexed(
  kvmap: &KVMap,
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_vec_len(kvmap.len(), buf);
  for (k, v) in kvmap {
    put_idx(k, idx, buf)?;
    v.put_indexed(idx, buf)?;
  }
  Ok(())
}

fn get_kvmap_indexed(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<KVMap, String> {
  let len = get_vec_len(buf)?;
  let mut kvmap = Vec::with_capacity(len);
  for _ in 0..len {
    kvmap.push((get_idx(buf, rev)?, DataValue::get_indexed(buf, rev)?));
  }
  Ok(kvmap)
}

fn put_mdata_stack_indexed(
  mdata: &[KVMap],
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_vec_len(mdata.len(), buf);
  for kv in mdata {
    put_kvmap_indexed(kv, idx, buf)?;
  }
  Ok(())
}

fn get_mdata_stack_indexed(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<Vec<KVMap>, String> {
  let len = get_vec_len(buf)?;
  let mut mdata = Vec::with_capacity(len);
  for _ in 0..len {
    mdata.push(get_kvmap_indexed(buf, rev)?);
  }
  Ok(mdata)
}

// ===========================================================================
// ExprMetaData indexed serialization
// ===========================================================================

impl ExprMetaData {
  // Tag 0: Leaf (no payload)
  // Tag 1: App { children: [u32, u32] }
  // Tags 2-5: Binder with BinderInfo packed into tag (2 + variant)
  // Tag 6: LetBinder { name_idx, children: [u32, u32, u32] }
  // Tag 7: Ref { name_idx }
  // Tag 8: Prj { struct_name_idx, child: u32 }
  // Tag 9: Mdata { kvmap_count, kvmaps..., child: u32 }

  pub fn put_indexed(
    &self,
    idx: &NameIndex,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    match self {
      Self::Leaf => put_u8(0, buf),
      Self::App { children } => {
        put_u8(1, buf);
        put_u64(children[0], buf);
        put_u64(children[1], buf);
      },
      Self::Binder { name, info, children } => {
        let tag = 2
          + match info {
            BinderInfo::Default => 0u8,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
          };
        put_u8(tag, buf);
        put_idx(name, idx, buf)?;
        put_u64(children[0], buf);
        put_u64(children[1], buf);
      },
      Self::LetBinder { name, children } => {
        put_u8(6, buf);
        put_idx(name, idx, buf)?;
        put_u64(children[0], buf);
        put_u64(children[1], buf);
        put_u64(children[2], buf);
      },
      Self::Ref { name } => {
        put_u8(7, buf);
        put_idx(name, idx, buf)?;
      },
      Self::Prj { struct_name, child } => {
        put_u8(8, buf);
        put_idx(struct_name, idx, buf)?;
        put_u64(*child, buf);
      },
      Self::Mdata { mdata, child } => {
        put_u8(9, buf);
        put_mdata_stack_indexed(mdata, idx, buf)?;
        put_u64(*child, buf);
      },
      Self::CallSite { name, entries } => {
        put_u8(10, buf);
        put_idx(name, idx, buf)?;
        put_vec_len(entries.len(), buf);
        for entry in entries {
          match entry {
            CallSiteEntry::Kept { canon_idx, meta } => {
              put_u8(0, buf);
              put_u64(*canon_idx, buf);
              put_u64(*meta, buf);
            },
            CallSiteEntry::Collapsed { sharing_idx, meta } => {
              put_u8(1, buf);
              put_u64(*sharing_idx, buf);
              put_u64(*meta, buf);
            },
          }
        }
      },
    }
    Ok(())
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Leaf),
      1 => {
        let c0 = get_u64(buf)?;
        let c1 = get_u64(buf)?;
        Ok(Self::App { children: [c0, c1] })
      },
      tag @ 2..=5 => {
        let info = match tag {
          2 => BinderInfo::Default,
          3 => BinderInfo::Implicit,
          4 => BinderInfo::StrictImplicit,
          5 => BinderInfo::InstImplicit,
          _ => unreachable!(),
        };
        let name = get_idx(buf, rev)?;
        let c0 = get_u64(buf)?;
        let c1 = get_u64(buf)?;
        Ok(Self::Binder { name, info, children: [c0, c1] })
      },
      6 => {
        let name = get_idx(buf, rev)?;
        let c0 = get_u64(buf)?;
        let c1 = get_u64(buf)?;
        let c2 = get_u64(buf)?;
        Ok(Self::LetBinder { name, children: [c0, c1, c2] })
      },
      7 => {
        let name = get_idx(buf, rev)?;
        Ok(Self::Ref { name })
      },
      8 => {
        let struct_name = get_idx(buf, rev)?;
        let child = get_u64(buf)?;
        Ok(Self::Prj { struct_name, child })
      },
      9 => {
        let mdata = get_mdata_stack_indexed(buf, rev)?;
        let child = get_u64(buf)?;
        Ok(Self::Mdata { mdata, child })
      },
      10 => {
        let name = get_idx(buf, rev)?;
        let n_entries = get_vec_len(buf)?;
        let mut entries = Vec::with_capacity(n_entries);
        for _ in 0..n_entries {
          let entry = match get_u8(buf)? {
            0 => {
              let canon_idx = get_u64(buf)?;
              let meta = get_u64(buf)?;
              CallSiteEntry::Kept { canon_idx, meta }
            },
            1 => {
              let sharing_idx = get_u64(buf)?;
              let meta = get_u64(buf)?;
              CallSiteEntry::Collapsed { sharing_idx, meta }
            },
            x => return Err(format!("CallSiteEntry::get: invalid tag {x}")),
          };
          entries.push(entry);
        }
        Ok(Self::CallSite { name, entries })
      },
      x => Err(format!("ExprMetaData::get: invalid tag {x}")),
    }
  }
}

// ===========================================================================
// ExprMeta (arena) indexed serialization
// ===========================================================================

impl ExprMeta {
  pub fn put_indexed(
    &self,
    idx: &NameIndex,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    put_vec_len(self.nodes.len(), buf);
    for node in &self.nodes {
      node.put_indexed(idx, buf)?;
    }
    Ok(())
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    let len = get_vec_len(buf)?;
    let mut nodes = Vec::with_capacity(len);
    for _ in 0..len {
      nodes.push(ExprMetaData::get_indexed(buf, rev)?);
    }
    Ok(ExprMeta { nodes })
  }
}

fn put_u64_vec(v: &[u64], buf: &mut Vec<u8>) {
  put_vec_len(v.len(), buf);
  for &x in v {
    put_u64(x, buf);
  }
}

fn get_u64_vec(buf: &mut &[u8]) -> Result<Vec<u64>, String> {
  let len = get_vec_len(buf)?;
  let mut v = Vec::with_capacity(len);
  for _ in 0..len {
    v.push(get_u64(buf)?);
  }
  Ok(v)
}

// ===========================================================================
// ConstantMeta indexed serialization
// ===========================================================================

impl ConstantMetaInfo {
  pub fn put_indexed(
    &self,
    idx: &NameIndex,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    match self {
      Self::Empty => put_u8(255, buf),
      Self::Def {
        name,
        lvls,
        hints,
        all,
        ctx,
        arena,
        type_root,
        value_root,
      } => {
        put_u8(0, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        hints.put(buf);
        put_idx_vec(all, idx, buf)?;
        put_idx_vec(ctx, idx, buf)?;
        arena.put_indexed(idx, buf)?;
        put_u64(*type_root, buf);
        put_u64(*value_root, buf);
      },
      Self::Axio { name, lvls, arena, type_root } => {
        put_u8(1, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        arena.put_indexed(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Quot { name, lvls, arena, type_root } => {
        put_u8(2, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        arena.put_indexed(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        put_u8(3, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx_vec(ctors, idx, buf)?;
        put_idx_vec(all, idx, buf)?;
        put_idx_vec(ctx, idx, buf)?;
        arena.put_indexed(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Ctor { name, lvls, induct, arena, type_root } => {
        put_u8(4, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx(induct, idx, buf)?;
        arena.put_indexed(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Rec {
        name,
        lvls,
        rules,
        all,
        ctx,
        arena,
        type_root,
        rule_roots,
      } => {
        put_u8(5, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx_vec(rules, idx, buf)?;
        put_idx_vec(all, idx, buf)?;
        put_idx_vec(ctx, idx, buf)?;
        arena.put_indexed(idx, buf)?;
        put_u64(*type_root, buf);
        put_u64_vec(rule_roots, buf);
      },
      Self::Muts { all } => {
        put_u8(6, buf);
        put_u64(all.len() as u64, buf);
        for cls in all {
          put_idx_vec(cls, idx, buf)?;
        }
      },
    }
    Ok(())
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    match get_u8(buf)? {
      255 => Ok(Self::Empty),
      0 => Ok(Self::Def {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        hints: ReducibilityHints::get_ser(buf)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_indexed(buf, rev)?,
        type_root: get_u64(buf)?,
        value_root: get_u64(buf)?,
      }),
      1 => Ok(Self::Axio {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_indexed(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      2 => Ok(Self::Quot {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_indexed(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      3 => Ok(Self::Indc {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        ctors: get_idx_vec(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_indexed(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      4 => Ok(Self::Ctor {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        induct: get_idx(buf, rev)?,
        arena: ExprMeta::get_indexed(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      5 => Ok(Self::Rec {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        rules: get_idx_vec(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_indexed(buf, rev)?,
        type_root: get_u64(buf)?,
        rule_roots: get_u64_vec(buf)?,
      }),
      6 => {
        let n = get_u64(buf)? as usize;
        let mut all = Vec::with_capacity(n);
        for _ in 0..n {
          all.push(get_idx_vec(buf, rev)?);
        }
        Ok(Self::Muts { all })
      },
      x => Err(format!("ConstantMetaInfo::get: invalid tag {x}")),
    }
  }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  impl Arbitrary for BinderInfo {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 4 {
        0 => Self::Default,
        1 => Self::Implicit,
        2 => Self::StrictImplicit,
        _ => Self::InstImplicit,
      }
    }
  }

  impl Arbitrary for ReducibilityHints {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 {
        0 => Self::Opaque,
        1 => Self::Abbrev,
        _ => Self::Regular(u32::arbitrary(g)),
      }
    }
  }

  #[test]
  fn test_binder_info_roundtrip() {
    for bi in [
      BinderInfo::Default,
      BinderInfo::Implicit,
      BinderInfo::StrictImplicit,
      BinderInfo::InstImplicit,
    ] {
      let mut buf = Vec::new();
      bi.put(&mut buf);
      assert_eq!(BinderInfo::get_ser(&mut buf.as_slice()).unwrap(), bi);
    }
  }

  #[test]
  fn test_reducibility_hints_roundtrip() {
    for h in [
      ReducibilityHints::Opaque,
      ReducibilityHints::Abbrev,
      ReducibilityHints::Regular(42),
    ] {
      let mut buf = Vec::new();
      h.put(&mut buf);
      assert_eq!(ReducibilityHints::get_ser(&mut buf.as_slice()).unwrap(), h);
    }
  }

  #[test]
  fn test_constant_meta_indexed_roundtrip() {
    // Create test addresses
    let addr1 = Address::from_slice(&[1u8; 32]).unwrap();
    let addr2 = Address::from_slice(&[2u8; 32]).unwrap();
    let addr3 = Address::from_slice(&[3u8; 32]).unwrap();

    // Build index
    let mut idx = NameIndex::new();
    idx.insert(addr1.clone(), 0);
    idx.insert(addr2.clone(), 1);
    idx.insert(addr3.clone(), 2);

    // Build reverse index
    let rev: NameReverseIndex =
      vec![addr1.clone(), addr2.clone(), addr3.clone()];

    // Test Def variant with arena
    let mut arena = ExprMeta::default();
    let leaf = arena.alloc(ExprMetaData::Leaf);
    let binder = arena.alloc(ExprMetaData::Binder {
      name: addr1.clone(),
      info: BinderInfo::Default,
      children: [leaf, leaf],
    });

    let meta = ConstantMeta::new(ConstantMetaInfo::Def {
      name: addr1.clone(),
      lvls: vec![addr2.clone(), addr3.clone()],
      hints: ReducibilityHints::Regular(10),
      all: vec![addr1.clone()],
      ctx: vec![addr2.clone()],
      arena,
      type_root: binder,
      value_root: leaf,
    });

    let mut buf = Vec::new();
    meta.put_indexed(&idx, &mut buf).unwrap();
    let recovered =
      ConstantMeta::get_indexed(&mut buf.as_slice(), &rev).unwrap();
    assert_eq!(meta, recovered);
  }

  #[test]
  fn test_expr_meta_arena_roundtrip() {
    let addr1 = Address::from_slice(&[1u8; 32]).unwrap();

    let mut idx = NameIndex::new();
    idx.insert(addr1.clone(), 0);
    let rev: NameReverseIndex = vec![addr1.clone()];

    let mut arena = ExprMeta::default();
    let leaf = arena.alloc(ExprMetaData::Leaf);
    let ref_node = arena.alloc(ExprMetaData::Ref { name: addr1.clone() });
    let app = arena.alloc(ExprMetaData::App { children: [leaf, ref_node] });
    let mdata = arena.alloc(ExprMetaData::Mdata {
      mdata: vec![vec![(addr1.clone(), DataValue::OfBool(true))]],
      child: app,
    });
    let _ = mdata;

    let mut buf = Vec::new();
    arena.put_indexed(&idx, &mut buf).unwrap();
    let recovered = ExprMeta::get_indexed(&mut buf.as_slice(), &rev).unwrap();
    assert_eq!(arena, recovered);
  }
}
