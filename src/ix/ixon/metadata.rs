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

use crate::ix::address::Address;
use crate::ix::env::{BinderInfo, ReducibilityHints};

use super::tag::Tag0;

// ===========================================================================
// Types (use Address internally)
// ===========================================================================

/// Key-value map for Lean.Expr.mdata
pub type KVMap = Vec<(Address, DataValue)>;

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

/// Per-constant metadata with arena-based expression metadata.
///
/// Each variant stores an ExprMeta arena covering all expressions in
/// that constant, plus root indices pointing into the arena for each
/// expression position (type, value, rule RHS, etc.).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum ConstantMeta {
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
  Address::from_slice(bytes).map_err(|_e| "get_address_raw: invalid".to_string())
}

fn put_u64(x: u64, buf: &mut Vec<u8>) {
  Tag0::new(x).put(buf);
}

fn get_u64(buf: &mut &[u8]) -> Result<u64, String> {
  Ok(Tag0::get(buf)?.size)
}

fn put_vec_len(len: usize, buf: &mut Vec<u8>) {
  Tag0::new(len as u64).put(buf);
}

fn get_vec_len(buf: &mut &[u8]) -> Result<usize, String> {
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
        buf.extend_from_slice(&x.to_le_bytes());
      },
    }
  }

  pub fn get_ser(buf: &mut &[u8]) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Opaque),
      1 => Ok(Self::Abbrev),
      2 => {
        if buf.len() < 4 {
          return Err("ReducibilityHints::get: need 4 bytes".to_string());
        }
        let (bytes, rest) = buf.split_at(4);
        *buf = rest;
        Ok(Self::Regular(u32::from_le_bytes([
          bytes[0], bytes[1], bytes[2], bytes[3],
        ])))
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

fn put_idx(addr: &Address, idx: &NameIndex, buf: &mut Vec<u8>) {
  let i = idx.get(addr).copied()
    .unwrap_or_else(|| panic!("put_idx: address {:?} not in name index", addr));
  put_u64(i, buf);
}

fn get_idx(buf: &mut &[u8], rev: &NameReverseIndex) -> Result<Address, String> {
  let i = get_u64(buf)? as usize;
  rev
    .get(i)
    .cloned()
    .ok_or_else(|| format!("invalid name index {i}, max {}", rev.len()))
}

fn put_idx_vec(addrs: &[Address], idx: &NameIndex, buf: &mut Vec<u8>) {
  put_vec_len(addrs.len(), buf);
  for a in addrs {
    put_idx(a, idx, buf);
  }
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
  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
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
        put_idx(a, idx, buf);
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

fn put_kvmap_indexed(kvmap: &KVMap, idx: &NameIndex, buf: &mut Vec<u8>) {
  put_vec_len(kvmap.len(), buf);
  for (k, v) in kvmap {
    put_idx(k, idx, buf);
    v.put_indexed(idx, buf);
  }
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
) {
  put_vec_len(mdata.len(), buf);
  for kv in mdata {
    put_kvmap_indexed(kv, idx, buf);
  }
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

  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
    match self {
      Self::Leaf => put_u8(0, buf),
      Self::App { children } => {
        put_u8(1, buf);
        put_u64(children[0], buf);
        put_u64(children[1], buf);
      },
      Self::Binder { name, info, children } => {
        let tag = 2 + match info {
          BinderInfo::Default => 0u8,
          BinderInfo::Implicit => 1,
          BinderInfo::StrictImplicit => 2,
          BinderInfo::InstImplicit => 3,
        };
        put_u8(tag, buf);
        put_idx(name, idx, buf);
        put_u64(children[0], buf);
        put_u64(children[1], buf);
      },
      Self::LetBinder { name, children } => {
        put_u8(6, buf);
        put_idx(name, idx, buf);
        put_u64(children[0], buf);
        put_u64(children[1], buf);
        put_u64(children[2], buf);
      },
      Self::Ref { name } => {
        put_u8(7, buf);
        put_idx(name, idx, buf);
      },
      Self::Prj { struct_name, child } => {
        put_u8(8, buf);
        put_idx(struct_name, idx, buf);
        put_u64(*child, buf);
      },
      Self::Mdata { mdata, child } => {
        put_u8(9, buf);
        put_mdata_stack_indexed(mdata, idx, buf);
        put_u64(*child, buf);
      },
    }
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
      x => Err(format!("ExprMetaData::get: invalid tag {x}")),
    }
  }
}

// ===========================================================================
// ExprMeta (arena) indexed serialization
// ===========================================================================

impl ExprMeta {
  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
    put_vec_len(self.nodes.len(), buf);
    for node in &self.nodes {
      node.put_indexed(idx, buf);
    }
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

impl ConstantMeta {
  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
    match self {
      Self::Empty => put_u8(255, buf),
      Self::Def { name, lvls, hints, all, ctx, arena, type_root, value_root } => {
        put_u8(0, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        hints.put(buf);
        put_idx_vec(all, idx, buf);
        put_idx_vec(ctx, idx, buf);
        arena.put_indexed(idx, buf);
        put_u64(*type_root, buf);
        put_u64(*value_root, buf);
      },
      Self::Axio { name, lvls, arena, type_root } => {
        put_u8(1, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        arena.put_indexed(idx, buf);
        put_u64(*type_root, buf);
      },
      Self::Quot { name, lvls, arena, type_root } => {
        put_u8(2, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        arena.put_indexed(idx, buf);
        put_u64(*type_root, buf);
      },
      Self::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        put_u8(3, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_idx_vec(ctors, idx, buf);
        put_idx_vec(all, idx, buf);
        put_idx_vec(ctx, idx, buf);
        arena.put_indexed(idx, buf);
        put_u64(*type_root, buf);
      },
      Self::Ctor { name, lvls, induct, arena, type_root } => {
        put_u8(4, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_idx(induct, idx, buf);
        arena.put_indexed(idx, buf);
        put_u64(*type_root, buf);
      },
      Self::Rec { name, lvls, rules, all, ctx, arena, type_root, rule_roots } => {
        put_u8(5, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_idx_vec(rules, idx, buf);
        put_idx_vec(all, idx, buf);
        put_idx_vec(ctx, idx, buf);
        arena.put_indexed(idx, buf);
        put_u64(*type_root, buf);
        put_u64_vec(rule_roots, buf);
      },
    }
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
      x => Err(format!("ConstantMeta::get: invalid tag {x}")),
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

    let meta = ConstantMeta::Def {
      name: addr1.clone(),
      lvls: vec![addr2.clone(), addr3.clone()],
      hints: ReducibilityHints::Regular(10),
      all: vec![addr1.clone()],
      ctx: vec![addr2.clone()],
      arena,
      type_root: binder,
      value_root: leaf,
    };

    let mut buf = Vec::new();
    meta.put_indexed(&idx, &mut buf);
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
    arena.put_indexed(&idx, &mut buf);
    let recovered =
      ExprMeta::get_indexed(&mut buf.as_slice(), &rev).unwrap();
    assert_eq!(arena, recovered);
  }
}
