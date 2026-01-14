//! Metadata for preserving Lean source information.
//!
//! Metadata types use Address internally, but serialize with u64 indices
//! into a global name index for space efficiency.

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

/// Per-expression metadata keyed by pre-order traversal index
pub type ExprMetas = HashMap<u64, ExprMeta>;

/// Per-expression metadata (keyed by pre-order traversal index within that expr)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprMeta {
  /// Lam/All binder
  Binder { name: Address, info: BinderInfo, mdata: Vec<KVMap> },
  /// Let binder
  LetBinder { name: Address, mdata: Vec<KVMap> },
  /// Const reference (for .mdata on const references)
  Ref { name: Address, mdata: Vec<KVMap> },
  /// Projection
  Prj { struct_name: Address, mdata: Vec<KVMap> },
  /// Just mdata wrapper (for Sort, Var, App, etc with .mdata)
  Mdata { mdata: Vec<KVMap> },
}

/// Constructor metadata (embedded in Indc for efficient access)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtorMeta {
  pub name: Address,
  pub lvls: Vec<Address>,
  pub type_meta: ExprMetas,
}

/// Per-constant metadata with ExprMetas embedded at each expression position
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
    type_meta: ExprMetas,
    value_meta: ExprMetas,
  },
  Axio {
    name: Address,
    lvls: Vec<Address>,
    type_meta: ExprMetas,
  },
  Quot {
    name: Address,
    lvls: Vec<Address>,
    type_meta: ExprMetas,
  },
  Indc {
    name: Address,
    lvls: Vec<Address>,
    ctors: Vec<Address>,
    ctor_metas: Vec<CtorMeta>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    type_meta: ExprMetas,
  },
  Ctor {
    name: Address,
    lvls: Vec<Address>,
    induct: Address,
    type_meta: ExprMetas,
  },
  Rec {
    name: Address,
    lvls: Vec<Address>,
    rules: Vec<Address>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    type_meta: ExprMetas,
  },
}

/// Data values for KVMap metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
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
  let i = idx.get(addr).copied().unwrap_or(0);
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
      Self::OfString(a) => {
        put_u8(0, buf);
        put_idx(a, idx, buf);
      },
      Self::OfBool(b) => {
        put_u8(1, buf);
        put_bool(*b, buf);
      },
      Self::OfName(a) => {
        put_u8(2, buf);
        put_idx(a, idx, buf);
      },
      Self::OfNat(a) => {
        put_u8(3, buf);
        put_idx(a, idx, buf);
      },
      Self::OfInt(a) => {
        put_u8(4, buf);
        put_idx(a, idx, buf);
      },
      Self::OfSyntax(a) => {
        put_u8(5, buf);
        put_idx(a, idx, buf);
      },
    }
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::OfString(get_idx(buf, rev)?)),
      1 => Ok(Self::OfBool(get_bool(buf)?)),
      2 => Ok(Self::OfName(get_idx(buf, rev)?)),
      3 => Ok(Self::OfNat(get_idx(buf, rev)?)),
      4 => Ok(Self::OfInt(get_idx(buf, rev)?)),
      5 => Ok(Self::OfSyntax(get_idx(buf, rev)?)),
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
// ExprMeta indexed serialization
// ===========================================================================

impl ExprMeta {
  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
    match self {
      Self::Binder { name, info, mdata } => {
        put_u8(0, buf);
        put_idx(name, idx, buf);
        info.put(buf);
        put_mdata_stack_indexed(mdata, idx, buf);
      },
      Self::LetBinder { name, mdata } => {
        put_u8(1, buf);
        put_idx(name, idx, buf);
        put_mdata_stack_indexed(mdata, idx, buf);
      },
      Self::Ref { name, mdata } => {
        put_u8(2, buf);
        put_idx(name, idx, buf);
        put_mdata_stack_indexed(mdata, idx, buf);
      },
      Self::Prj { struct_name, mdata } => {
        put_u8(3, buf);
        put_idx(struct_name, idx, buf);
        put_mdata_stack_indexed(mdata, idx, buf);
      },
      Self::Mdata { mdata } => {
        put_u8(4, buf);
        put_mdata_stack_indexed(mdata, idx, buf);
      },
    }
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Binder {
        name: get_idx(buf, rev)?,
        info: BinderInfo::get_ser(buf)?,
        mdata: get_mdata_stack_indexed(buf, rev)?,
      }),
      1 => Ok(Self::LetBinder {
        name: get_idx(buf, rev)?,
        mdata: get_mdata_stack_indexed(buf, rev)?,
      }),
      2 => Ok(Self::Ref {
        name: get_idx(buf, rev)?,
        mdata: get_mdata_stack_indexed(buf, rev)?,
      }),
      3 => Ok(Self::Prj {
        struct_name: get_idx(buf, rev)?,
        mdata: get_mdata_stack_indexed(buf, rev)?,
      }),
      4 => Ok(Self::Mdata { mdata: get_mdata_stack_indexed(buf, rev)? }),
      x => Err(format!("ExprMeta::get: invalid tag {x}")),
    }
  }
}

fn put_expr_metas_indexed(
  metas: &ExprMetas,
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) {
  put_vec_len(metas.len(), buf);
  for (i, meta) in metas {
    Tag0::new(*i).put(buf);
    meta.put_indexed(idx, buf);
  }
}

fn get_expr_metas_indexed(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<ExprMetas, String> {
  let len = get_vec_len(buf)?;
  let mut metas = HashMap::with_capacity(len);
  for _ in 0..len {
    let i = Tag0::get(buf)?.size;
    let meta = ExprMeta::get_indexed(buf, rev)?;
    metas.insert(i, meta);
  }
  Ok(metas)
}

// ===========================================================================
// CtorMeta indexed serialization
// ===========================================================================

impl CtorMeta {
  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
    put_idx(&self.name, idx, buf);
    put_idx_vec(&self.lvls, idx, buf);
    put_expr_metas_indexed(&self.type_meta, idx, buf);
  }

  pub fn get_indexed(
    buf: &mut &[u8],
    rev: &NameReverseIndex,
  ) -> Result<Self, String> {
    Ok(CtorMeta {
      name: get_idx(buf, rev)?,
      lvls: get_idx_vec(buf, rev)?,
      type_meta: get_expr_metas_indexed(buf, rev)?,
    })
  }
}

fn put_ctor_metas_indexed(
  metas: &[CtorMeta],
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) {
  put_vec_len(metas.len(), buf);
  for meta in metas {
    meta.put_indexed(idx, buf);
  }
}

fn get_ctor_metas_indexed(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<Vec<CtorMeta>, String> {
  let len = get_vec_len(buf)?;
  let mut metas = Vec::with_capacity(len);
  for _ in 0..len {
    metas.push(CtorMeta::get_indexed(buf, rev)?);
  }
  Ok(metas)
}

// ===========================================================================
// ConstantMeta indexed serialization
// ===========================================================================

impl ConstantMeta {
  pub fn put_indexed(&self, idx: &NameIndex, buf: &mut Vec<u8>) {
    match self {
      Self::Empty => put_u8(255, buf),
      Self::Def { name, lvls, hints, all, ctx, type_meta, value_meta } => {
        put_u8(0, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        hints.put(buf);
        put_idx_vec(all, idx, buf);
        put_idx_vec(ctx, idx, buf);
        put_expr_metas_indexed(type_meta, idx, buf);
        put_expr_metas_indexed(value_meta, idx, buf);
      },
      Self::Axio { name, lvls, type_meta } => {
        put_u8(1, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_expr_metas_indexed(type_meta, idx, buf);
      },
      Self::Quot { name, lvls, type_meta } => {
        put_u8(2, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_expr_metas_indexed(type_meta, idx, buf);
      },
      Self::Indc { name, lvls, ctors, ctor_metas, all, ctx, type_meta } => {
        put_u8(3, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_idx_vec(ctors, idx, buf);
        put_ctor_metas_indexed(ctor_metas, idx, buf);
        put_idx_vec(all, idx, buf);
        put_idx_vec(ctx, idx, buf);
        put_expr_metas_indexed(type_meta, idx, buf);
      },
      Self::Ctor { name, lvls, induct, type_meta } => {
        put_u8(4, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_idx(induct, idx, buf);
        put_expr_metas_indexed(type_meta, idx, buf);
      },
      Self::Rec { name, lvls, rules, all, ctx, type_meta } => {
        put_u8(5, buf);
        put_idx(name, idx, buf);
        put_idx_vec(lvls, idx, buf);
        put_idx_vec(rules, idx, buf);
        put_idx_vec(all, idx, buf);
        put_idx_vec(ctx, idx, buf);
        put_expr_metas_indexed(type_meta, idx, buf);
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
        type_meta: get_expr_metas_indexed(buf, rev)?,
        value_meta: get_expr_metas_indexed(buf, rev)?,
      }),
      1 => Ok(Self::Axio {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        type_meta: get_expr_metas_indexed(buf, rev)?,
      }),
      2 => Ok(Self::Quot {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        type_meta: get_expr_metas_indexed(buf, rev)?,
      }),
      3 => Ok(Self::Indc {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        ctors: get_idx_vec(buf, rev)?,
        ctor_metas: get_ctor_metas_indexed(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        type_meta: get_expr_metas_indexed(buf, rev)?,
      }),
      4 => Ok(Self::Ctor {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        induct: get_idx(buf, rev)?,
        type_meta: get_expr_metas_indexed(buf, rev)?,
      }),
      5 => Ok(Self::Rec {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        rules: get_idx_vec(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        type_meta: get_expr_metas_indexed(buf, rev)?,
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

    // Test Def variant
    let meta = ConstantMeta::Def {
      name: addr1.clone(),
      lvls: vec![addr2.clone(), addr3.clone()],
      hints: ReducibilityHints::Regular(10),
      all: vec![addr1.clone()],
      ctx: vec![addr2.clone()],
      type_meta: HashMap::new(),
      value_meta: HashMap::new(),
    };

    let mut buf = Vec::new();
    meta.put_indexed(&idx, &mut buf);
    let recovered =
      ConstantMeta::get_indexed(&mut buf.as_slice(), &rev).unwrap();
    assert_eq!(meta, recovered);
  }
}
