//! Decompilation from Ixon format back to Lean environment.
//!
//! This module decompiles alpha-invariant Ixon representations back to
//! Lean constants, expanding Share references and reattaching metadata.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::map_err_ignore)]
#![allow(clippy::match_same_arms)]

use crate::{
  ix::address::Address,
  ix::compile::CompileState,
  ix::env::{
    AxiomVal, BinderInfo, ConstantInfo as LeanConstantInfo, ConstantVal,
    ConstructorVal, DataValue as LeanDataValue, DefinitionSafety,
    DefinitionVal, Env as LeanEnv, Expr as LeanExpr, InductiveVal, Int, Level,
    Literal, Name, OpaqueVal, QuotVal, RecursorRule as LeanRecursorRule,
    RecursorVal, ReducibilityHints, SourceInfo, Substring, Syntax,
    SyntaxPreresolved, TheoremVal,
  },
  ix::ixon::{
    DecompileError, Tag0,
    constant::{
      Axiom, Constant, ConstantInfo, Constructor, DefKind, Definition,
      Inductive, MutConst, Quotient, Recursor,
    },
    env::Named,
    expr::Expr,
    metadata::{ConstantMeta, DataValue, ExprMeta, ExprMetaData, KVMap},
    univ::Univ,
  },
  ix::mutual::{MutCtx, all_to_ctx},
  lean::nat::Nat,
};
use dashmap::DashMap;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;
use std::sync::Arc;

#[derive(Default, Debug)]
pub struct DecompileState {
  /// Decompiled environment
  pub env: DashMap<Name, LeanConstantInfo>,
}

#[derive(Debug)]
pub struct DecompileStateStats {
  pub env: usize,
}

impl DecompileState {
  pub fn stats(&self) -> DecompileStateStats {
    DecompileStateStats { env: self.env.len() }
  }
}

/// Per-block decompilation cache.
#[derive(Default, Debug)]
pub struct BlockCache {
  /// Mutual context for resolving Rec references
  pub ctx: MutCtx,
  /// Sharing vector for expanding Share references
  pub sharing: Vec<Arc<Expr>>,
  /// Reference table for resolving Ref indices to addresses
  pub refs: Vec<Address>,
  /// Universe table for resolving universe indices
  pub univ_table: Vec<Arc<Univ>>,
  /// Cache for decompiled universes
  pub univ_cache: FxHashMap<*const Univ, Level>,
  /// Cache for decompiled expressions keyed by (Ixon pointer, arena index).
  /// Same Ixon expression at same arena index → same metadata → same result.
  /// Same Ixon expression at different arena index → different metadata → different cache key.
  pub expr_cache: FxHashMap<(*const Expr, u64), LeanExpr>,
  /// Current constant being decompiled (for error messages)
  pub current_const: String,
}

// ===========================================================================
// Blob reading utilities
// ===========================================================================

/// Read raw bytes from the blob store.
fn read_blob(
  addr: &Address,
  stt: &CompileState,
) -> Result<Vec<u8>, DecompileError> {
  stt.env.get_blob(addr).ok_or(DecompileError::BlobNotFound(addr.clone()))
}

/// Read a Nat from the blob store.
fn read_nat(addr: &Address, stt: &CompileState) -> Result<Nat, DecompileError> {
  let bytes = read_blob(addr, stt)?;
  Ok(Nat::from_le_bytes(&bytes))
}

/// Read a string from the blob store.
fn read_string(
  addr: &Address,
  stt: &CompileState,
) -> Result<String, DecompileError> {
  let bytes = read_blob(addr, stt)?;
  String::from_utf8(bytes).map_err(|_| DecompileError::BadBlobFormat {
    addr: addr.clone(),
    expected: "UTF-8 string".into(),
  })
}

/// Read a Constant from the const store.
fn read_const(
  addr: &Address,
  stt: &CompileState,
) -> Result<Constant, DecompileError> {
  stt.env.get_const(addr).ok_or(DecompileError::MissingAddress(addr.clone()))
}

// ===========================================================================
// DataValue and KVMap decompilation
// ===========================================================================

/// Decompile an Ixon DataValue (Address-based) to a Lean DataValue.
fn decompile_data_value(
  dv: &DataValue,
  stt: &CompileState,
) -> Result<LeanDataValue, DecompileError> {
  match dv {
    DataValue::OfString(addr) => {
      let s = read_string(addr, stt)?;
      Ok(LeanDataValue::OfString(s))
    },
    DataValue::OfBool(b) => Ok(LeanDataValue::OfBool(*b)),
    DataValue::OfName(addr) => {
      let name = decompile_name(addr, stt)?;
      Ok(LeanDataValue::OfName(name))
    },
    DataValue::OfNat(addr) => {
      let n = read_nat(addr, stt)?;
      Ok(LeanDataValue::OfNat(n))
    },
    DataValue::OfInt(addr) => {
      let bytes = read_blob(addr, stt)?;
      let int = deserialize_int(&bytes)?;
      Ok(LeanDataValue::OfInt(int))
    },
    DataValue::OfSyntax(addr) => {
      let bytes = read_blob(addr, stt)?;
      let syntax = deserialize_syntax(&bytes, stt)?;
      Ok(LeanDataValue::OfSyntax(Box::new(syntax)))
    },
  }
}

/// Deserialize an Int from bytes (mirrors compile-side serialization).
fn deserialize_int(bytes: &[u8]) -> Result<Int, DecompileError> {
  if bytes.is_empty() {
    return Err(DecompileError::BadConstantFormat {
      msg: "deserialize_int: empty".into(),
    });
  }
  match bytes[0] {
    0 => Ok(Int::OfNat(Nat::from_le_bytes(&bytes[1..]))),
    1 => Ok(Int::NegSucc(Nat::from_le_bytes(&bytes[1..]))),
    _ => Err(DecompileError::BadConstantFormat {
      msg: "deserialize_int: invalid tag".into(),
    }),
  }
}

/// Read a Tag0-encoded u64 from a byte slice, advancing the cursor.
fn read_tag0(buf: &mut &[u8]) -> Result<u64, DecompileError> {
  Tag0::get(buf).map(|t| t.size).map_err(|_| {
    DecompileError::BadConstantFormat {
      msg: "read_tag0: unexpected EOF".into(),
    }
  })
}

/// Read exactly 32 bytes (Address) from a byte slice, advancing the cursor.
fn read_addr_bytes(buf: &mut &[u8]) -> Result<Address, DecompileError> {
  if buf.len() < 32 {
    return Err(DecompileError::BadConstantFormat {
      msg: "read_addr: need 32 bytes".into(),
    });
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).map_err(|_| DecompileError::BadConstantFormat {
    msg: "read_addr: invalid".into(),
  })
}

/// Deserialize a Substring from bytes.
fn deserialize_substring(
  buf: &mut &[u8],
  stt: &CompileState,
) -> Result<Substring, DecompileError> {
  let str_addr = read_addr_bytes(buf)?;
  let s = read_string(&str_addr, stt)?;
  let start_pos = Nat::from(read_tag0(buf)?);
  let stop_pos = Nat::from(read_tag0(buf)?);
  Ok(Substring { str: s, start_pos, stop_pos })
}

/// Deserialize SourceInfo from bytes.
fn deserialize_source_info(
  buf: &mut &[u8],
  stt: &CompileState,
) -> Result<SourceInfo, DecompileError> {
  if buf.is_empty() {
    return Err(DecompileError::BadConstantFormat {
      msg: "source_info: empty".into(),
    });
  }
  let tag = buf[0];
  *buf = &buf[1..];
  match tag {
    0 => {
      let leading = deserialize_substring(buf, stt)?;
      let leading_pos = Nat::from(read_tag0(buf)?);
      let trailing = deserialize_substring(buf, stt)?;
      let trailing_pos = Nat::from(read_tag0(buf)?);
      Ok(SourceInfo::Original(leading, leading_pos, trailing, trailing_pos))
    },
    1 => {
      let start = Nat::from(read_tag0(buf)?);
      let end = Nat::from(read_tag0(buf)?);
      if buf.is_empty() {
        return Err(DecompileError::BadConstantFormat {
          msg: "source_info: missing canonical".into(),
        });
      }
      let canonical = buf[0] != 0;
      *buf = &buf[1..];
      Ok(SourceInfo::Synthetic(start, end, canonical))
    },
    2 => Ok(SourceInfo::None),
    _ => Err(DecompileError::BadConstantFormat {
      msg: "source_info: invalid tag".into(),
    }),
  }
}

/// Deserialize a SyntaxPreresolved from bytes.
fn deserialize_preresolved(
  buf: &mut &[u8],
  stt: &CompileState,
) -> Result<SyntaxPreresolved, DecompileError> {
  if buf.is_empty() {
    return Err(DecompileError::BadConstantFormat {
      msg: "preresolved: empty".into(),
    });
  }
  let tag = buf[0];
  *buf = &buf[1..];
  match tag {
    0 => {
      let name_addr = read_addr_bytes(buf)?;
      let name = decompile_name(&name_addr, stt)?;
      Ok(SyntaxPreresolved::Namespace(name))
    },
    1 => {
      let name_addr = read_addr_bytes(buf)?;
      let name = decompile_name(&name_addr, stt)?;
      let count = read_tag0(buf)? as usize;
      let mut fields = Vec::with_capacity(count);
      for _ in 0..count {
        let field_addr = read_addr_bytes(buf)?;
        let field = read_string(&field_addr, stt)?;
        fields.push(field);
      }
      Ok(SyntaxPreresolved::Decl(name, fields))
    },
    _ => Err(DecompileError::BadConstantFormat {
      msg: "preresolved: invalid tag".into(),
    }),
  }
}

/// Deserialize a Syntax from bytes (mirrors compile-side serialize_syntax).
fn deserialize_syntax(
  bytes: &[u8],
  stt: &CompileState,
) -> Result<Syntax, DecompileError> {
  let mut buf = bytes;
  deserialize_syntax_inner(&mut buf, stt)
}

/// Recursive inner deserializer for Syntax.
fn deserialize_syntax_inner(
  buf: &mut &[u8],
  stt: &CompileState,
) -> Result<Syntax, DecompileError> {
  if buf.is_empty() {
    return Err(DecompileError::BadConstantFormat {
      msg: "syntax: empty".into(),
    });
  }
  let tag = buf[0];
  *buf = &buf[1..];
  match tag {
    0 => Ok(Syntax::Missing),
    1 => {
      let info = deserialize_source_info(buf, stt)?;
      let kind_addr = read_addr_bytes(buf)?;
      let kind = decompile_name(&kind_addr, stt)?;
      let arg_count = read_tag0(buf)? as usize;
      let mut args = Vec::with_capacity(arg_count);
      for _ in 0..arg_count {
        args.push(deserialize_syntax_inner(buf, stt)?);
      }
      Ok(Syntax::Node(info, kind, args))
    },
    2 => {
      let info = deserialize_source_info(buf, stt)?;
      let val_addr = read_addr_bytes(buf)?;
      let val = read_string(&val_addr, stt)?;
      Ok(Syntax::Atom(info, val))
    },
    3 => {
      let info = deserialize_source_info(buf, stt)?;
      let raw_val = deserialize_substring(buf, stt)?;
      let val_addr = read_addr_bytes(buf)?;
      let val = decompile_name(&val_addr, stt)?;
      let pr_count = read_tag0(buf)? as usize;
      let mut preresolved = Vec::with_capacity(pr_count);
      for _ in 0..pr_count {
        preresolved.push(deserialize_preresolved(buf, stt)?);
      }
      Ok(Syntax::Ident(info, raw_val, val, preresolved))
    },
    _ => Err(DecompileError::BadConstantFormat {
      msg: "syntax: invalid tag".into(),
    }),
  }
}

/// Decompile an Ixon KVMap (Address-based) to a Lean KVMap (Name/DataValue).
fn decompile_kvmap(
  kvmap: &KVMap,
  stt: &CompileState,
) -> Result<Vec<(Name, LeanDataValue)>, DecompileError> {
  kvmap
    .iter()
    .map(|(k_addr, v)| {
      let name = decompile_name(k_addr, stt)?;
      let val = decompile_data_value(v, stt)?;
      Ok((name, val))
    })
    .collect()
}

/// Wrap a LeanExpr in pre-decompiled mdata layers.
///
/// The `lean_mdata` vec stores layers outermost-first.
/// We iterate in reverse to wrap innermost-first:
///   given [kv_outer, kv_inner], result is mdata(kv_outer, mdata(kv_inner, expr)).
fn apply_mdata(
  mut expr: LeanExpr,
  lean_mdata: Vec<Vec<(Name, LeanDataValue)>>,
) -> LeanExpr {
  for kvmap in lean_mdata.into_iter().rev() {
    expr = LeanExpr::mdata(kvmap, expr);
  }
  expr
}

// ===========================================================================
// Name decompilation
// ===========================================================================

/// Look up a Name by its address.
pub fn decompile_name(
  addr: &Address,
  stt: &CompileState,
) -> Result<Name, DecompileError> {
  stt
    .env
    .names
    .get(addr)
    .map(|r| r.clone())
    .ok_or(DecompileError::MissingAddress(addr.clone()))
}

// ===========================================================================
// Universe decompilation
// ===========================================================================

/// Decompile an Ixon Univ to a Lean Level.
pub fn decompile_univ(
  univ: &Arc<Univ>,
  lvl_names: &[Name],
  cache: &mut BlockCache,
) -> Result<Level, DecompileError> {
  let ptr = Arc::as_ptr(univ);
  if let Some(cached) = cache.univ_cache.get(&ptr) {
    return Ok(cached.clone());
  }

  let level = match univ.as_ref() {
    Univ::Zero => Level::zero(),
    Univ::Succ(inner) => {
      let inner_level = decompile_univ(inner, lvl_names, cache)?;
      Level::succ(inner_level)
    },
    Univ::Max(a, b) => {
      let la = decompile_univ(a, lvl_names, cache)?;
      let lb = decompile_univ(b, lvl_names, cache)?;
      Level::max(la, lb)
    },
    Univ::IMax(a, b) => {
      let la = decompile_univ(a, lvl_names, cache)?;
      let lb = decompile_univ(b, lvl_names, cache)?;
      Level::imax(la, lb)
    },
    Univ::Var(idx) => {
      let idx_usize = *idx as usize;
      let name = lvl_names
        .get(idx_usize)
        .ok_or_else(|| DecompileError::InvalidUnivVarIndex {
          idx: *idx,
          max: lvl_names.len(),
          constant: cache.current_const.clone(),
        })?
        .clone();
      Level::param(name)
    },
  };

  cache.univ_cache.insert(ptr, level.clone());
  Ok(level)
}

// ===========================================================================
// Expression decompilation
// ===========================================================================

/// Decompile an Ixon Expr to a Lean Expr with arena-based metadata restoration.
///
/// Traverses the arena tree following child pointers. Share references are
/// expanded with the same arena_idx (parent's child pointer already captures
/// the correct metadata subtree). Mdata arena nodes are collected and applied
/// as wrappers.
pub fn decompile_expr(
  expr: &Arc<Expr>,
  arena: &ExprMeta,
  arena_idx: u64,
  lvl_names: &[Name],
  cache: &mut BlockCache,
  stt: &CompileState,
  _dstt: &DecompileState,
) -> Result<LeanExpr, DecompileError> {
  // Lean mdata layers: Vec of KVMaps (outermost-first)
  type LeanMdata = Vec<Vec<(Name, LeanDataValue)>>;

  /// Default node for out-of-bounds arena access (empty arena or invalid index).
  const DEFAULT_NODE: ExprMetaData = ExprMetaData::Leaf;

  enum Frame {
    Decompile(Arc<Expr>, u64),
    BuildApp(LeanMdata),
    BuildLam(Name, BinderInfo, LeanMdata),
    BuildAll(Name, BinderInfo, LeanMdata),
    BuildLet(Name, bool, LeanMdata),
    BuildProj(Name, Nat, LeanMdata),
    CacheResult(*const Expr, u64),
  }

  let mut stack: Vec<Frame> = vec![Frame::Decompile(expr.clone(), arena_idx)];
  let mut results: Vec<LeanExpr> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Decompile(e, idx) => {
        // Expand Share transparently with the SAME arena_idx
        if let Expr::Share(share_idx) = e.as_ref() {
          let shared_expr = cache
            .sharing
            .get(*share_idx as usize)
            .ok_or_else(|| DecompileError::InvalidShareIndex {
              idx: *share_idx,
              max: cache.sharing.len(),
              constant: cache.current_const.clone(),
            })?
            .clone();
          stack.push(Frame::Decompile(shared_expr, idx));
          continue;
        }

        // Cache check: (Ixon pointer, arena index)
        let cache_key = (Arc::as_ptr(&e), idx);
        if let Some(cached) = cache.expr_cache.get(&cache_key) {
          results.push(cached.clone());
          continue;
        }

        // Follow Mdata chain in arena, collecting mdata layers
        let mut current_idx = idx;
        let mut mdata_layers: LeanMdata = Vec::new();
        while let ExprMetaData::Mdata { mdata, child } =
          arena.nodes.get(current_idx as usize).unwrap_or(&DEFAULT_NODE)
        {
          for kvm in mdata {
            mdata_layers.push(decompile_kvmap(kvm, stt)?);
          }
          current_idx = *child;
        }

        let node =
          arena.nodes.get(current_idx as usize).unwrap_or(&DEFAULT_NODE);

        // Push CacheResult frame
        stack.push(Frame::CacheResult(Arc::as_ptr(&e), idx));

        match (node, e.as_ref()) {
          // Leaf nodes: Var, Sort, Nat, Str
          (_, Expr::Var(v)) => {
            let expr = apply_mdata(LeanExpr::bvar(Nat::from(*v)), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Sort(univ_idx)) => {
            let univ = cache
              .univ_table
              .get(*univ_idx as usize)
              .ok_or_else(|| DecompileError::InvalidUnivIndex {
                idx: *univ_idx,
                univs_len: cache.univ_table.len(),
                constant: cache.current_const.clone(),
              })?
              .clone();
            let level = decompile_univ(&univ, lvl_names, cache)?;
            let expr = apply_mdata(LeanExpr::sort(level), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Nat(ref_idx)) => {
            let addr = cache.refs.get(*ref_idx as usize).ok_or_else(|| {
              DecompileError::InvalidRefIndex {
                idx: *ref_idx,
                refs_len: cache.refs.len(),
                constant: cache.current_const.clone(),
              }
            })?;
            let n = read_nat(addr, stt)?;
            let expr =
              apply_mdata(LeanExpr::lit(Literal::NatVal(n)), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Str(ref_idx)) => {
            let addr = cache.refs.get(*ref_idx as usize).ok_or_else(|| {
              DecompileError::InvalidRefIndex {
                idx: *ref_idx,
                refs_len: cache.refs.len(),
                constant: cache.current_const.clone(),
              }
            })?;
            let s = read_string(addr, stt)?;
            let expr =
              apply_mdata(LeanExpr::lit(Literal::StrVal(s)), mdata_layers);
            results.push(expr);
          },

          // Ref: resolve name from arena Ref node or fallback
          (
            ExprMetaData::Ref { name: name_addr },
            Expr::Ref(ref_idx, univ_indices),
          ) => {
            let name = decompile_name(name_addr, stt).unwrap_or_else(|_| {
              // Fallback: resolve from refs table
              cache
                .refs
                .get(*ref_idx as usize)
                .and_then(|addr| stt.env.get_name_by_addr(addr))
                .unwrap_or_else(Name::anon)
            });
            let levels =
              decompile_univ_indices(univ_indices, lvl_names, cache)?;
            let expr = apply_mdata(LeanExpr::cnst(name, levels), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Ref(ref_idx, univ_indices)) => {
            // No Ref metadata — resolve from refs table
            let addr = cache.refs.get(*ref_idx as usize).ok_or_else(|| {
              DecompileError::InvalidRefIndex {
                idx: *ref_idx,
                refs_len: cache.refs.len(),
                constant: cache.current_const.clone(),
              }
            })?;
            let name = stt
              .env
              .get_name_by_addr(addr)
              .ok_or(DecompileError::MissingAddress(addr.clone()))?;
            let levels =
              decompile_univ_indices(univ_indices, lvl_names, cache)?;
            let expr = apply_mdata(LeanExpr::cnst(name, levels), mdata_layers);
            results.push(expr);
          },

          // Rec: resolve name from arena Ref node or fallback
          (
            ExprMetaData::Ref { name: name_addr },
            Expr::Rec(rec_idx, univ_indices),
          ) => {
            let name = decompile_name(name_addr, stt).unwrap_or_else(|_| {
              cache
                .ctx
                .iter()
                .find(|(_, i)| i.to_u64() == Some(*rec_idx))
                .map_or_else(Name::anon, |(n, _)| n.clone())
            });
            let levels =
              decompile_univ_indices(univ_indices, lvl_names, cache)?;
            let expr = apply_mdata(LeanExpr::cnst(name, levels), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Rec(rec_idx, univ_indices)) => {
            let name = cache
              .ctx
              .iter()
              .find(|(_, i)| i.to_u64() == Some(*rec_idx))
              .map(|(n, _)| n.clone())
              .ok_or_else(|| DecompileError::InvalidRecIndex {
                idx: *rec_idx,
                ctx_size: cache.ctx.len(),
                constant: cache.current_const.clone(),
              })?;
            let levels =
              decompile_univ_indices(univ_indices, lvl_names, cache)?;
            let expr = apply_mdata(LeanExpr::cnst(name, levels), mdata_layers);
            results.push(expr);
          },

          // App: follow arena children
          (ExprMetaData::App { children }, Expr::App(f, a)) => {
            stack.push(Frame::BuildApp(mdata_layers));
            stack.push(Frame::Decompile(a.clone(), children[1]));
            stack.push(Frame::Decompile(f.clone(), children[0]));
          },

          (_, Expr::App(f, a)) => {
            // No App metadata — use dummy indices (Leaf fallback)
            stack.push(Frame::BuildApp(mdata_layers));
            stack.push(Frame::Decompile(a.clone(), u64::MAX));
            stack.push(Frame::Decompile(f.clone(), u64::MAX));
          },

          // Lam: extract binder name/info from arena
          (
            ExprMetaData::Binder { name: name_addr, info, children },
            Expr::Lam(ty, body),
          ) => {
            let binder_name =
              decompile_name(name_addr, stt).unwrap_or_else(|_| Name::anon());
            stack.push(Frame::BuildLam(
              binder_name,
              info.clone(),
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), children[1]));
            stack.push(Frame::Decompile(ty.clone(), children[0]));
          },

          (_, Expr::Lam(ty, body)) => {
            stack.push(Frame::BuildLam(
              Name::anon(),
              BinderInfo::Default,
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), u64::MAX));
            stack.push(Frame::Decompile(ty.clone(), u64::MAX));
          },

          // All: extract binder name/info from arena
          (
            ExprMetaData::Binder { name: name_addr, info, children },
            Expr::All(ty, body),
          ) => {
            let binder_name =
              decompile_name(name_addr, stt).unwrap_or_else(|_| Name::anon());
            stack.push(Frame::BuildAll(
              binder_name,
              info.clone(),
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), children[1]));
            stack.push(Frame::Decompile(ty.clone(), children[0]));
          },

          (_, Expr::All(ty, body)) => {
            stack.push(Frame::BuildAll(
              Name::anon(),
              BinderInfo::Default,
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), u64::MAX));
            stack.push(Frame::Decompile(ty.clone(), u64::MAX));
          },

          // Let: extract name from arena
          (
            ExprMetaData::LetBinder { name: name_addr, children },
            Expr::Let(non_dep, ty, val, body),
          ) => {
            let let_name =
              decompile_name(name_addr, stt).unwrap_or_else(|_| Name::anon());
            stack.push(Frame::BuildLet(let_name, *non_dep, mdata_layers));
            stack.push(Frame::Decompile(body.clone(), children[2]));
            stack.push(Frame::Decompile(val.clone(), children[1]));
            stack.push(Frame::Decompile(ty.clone(), children[0]));
          },

          (_, Expr::Let(non_dep, ty, val, body)) => {
            stack.push(Frame::BuildLet(Name::anon(), *non_dep, mdata_layers));
            stack.push(Frame::Decompile(body.clone(), u64::MAX));
            stack.push(Frame::Decompile(val.clone(), u64::MAX));
            stack.push(Frame::Decompile(ty.clone(), u64::MAX));
          },

          // Prj: extract struct name from arena
          (
            ExprMetaData::Prj { struct_name, child },
            Expr::Prj(_type_ref_idx, field_idx, struct_val),
          ) => {
            let type_name = decompile_name(struct_name, stt)?;
            stack.push(Frame::BuildProj(
              type_name,
              Nat::from(*field_idx),
              mdata_layers,
            ));
            stack.push(Frame::Decompile(struct_val.clone(), *child));
          },

          (_, Expr::Prj(type_ref_idx, field_idx, struct_val)) => {
            // Fallback: look up from refs table
            let addr =
              cache.refs.get(*type_ref_idx as usize).ok_or_else(|| {
                DecompileError::InvalidRefIndex {
                  idx: *type_ref_idx,
                  refs_len: cache.refs.len(),
                  constant: cache.current_const.clone(),
                }
              })?;
            let named = stt
              .env
              .get_named_by_addr(addr)
              .ok_or(DecompileError::MissingAddress(addr.clone()))?;
            let type_name = decompile_name_from_meta(&named.meta, stt)?;
            stack.push(Frame::BuildProj(
              type_name,
              Nat::from(*field_idx),
              mdata_layers,
            ));
            stack.push(Frame::Decompile(struct_val.clone(), u64::MAX));
          },

          (_, Expr::Share(_)) => unreachable!("Share handled above"),
        }
      },

      Frame::BuildApp(mdata) => {
        let a = results.pop().expect("BuildApp missing arg");
        let f = results.pop().expect("BuildApp missing fun");
        results.push(apply_mdata(LeanExpr::app(f, a), mdata));
      },

      Frame::BuildLam(name, info, mdata) => {
        let body = results.pop().expect("BuildLam missing body");
        let ty = results.pop().expect("BuildLam missing ty");
        results.push(apply_mdata(LeanExpr::lam(name, ty, body, info), mdata));
      },

      Frame::BuildAll(name, info, mdata) => {
        let body = results.pop().expect("BuildAll missing body");
        let ty = results.pop().expect("BuildAll missing ty");
        results.push(apply_mdata(LeanExpr::all(name, ty, body, info), mdata));
      },

      Frame::BuildLet(name, non_dep, mdata) => {
        let body = results.pop().expect("BuildLet missing body");
        let val = results.pop().expect("BuildLet missing val");
        let ty = results.pop().expect("BuildLet missing ty");
        results.push(apply_mdata(
          LeanExpr::letE(name, ty, val, body, non_dep),
          mdata,
        ));
      },

      Frame::BuildProj(name, idx, mdata) => {
        let s = results.pop().expect("BuildProj missing struct");
        results.push(apply_mdata(LeanExpr::proj(name, idx, s), mdata));
      },

      Frame::CacheResult(e_ptr, arena_idx) => {
        if let Some(result) = results.last() {
          cache.expr_cache.insert((e_ptr, arena_idx), result.clone());
        }
      },
    }
  }

  results
    .pop()
    .ok_or(DecompileError::BadConstantFormat { msg: "empty result".into() })
}

/// Helper: decompile universe indices to Lean levels.
fn decompile_univ_indices(
  univ_indices: &[u64],
  lvl_names: &[Name],
  cache: &mut BlockCache,
) -> Result<Vec<Level>, DecompileError> {
  univ_indices
    .iter()
    .map(|ui| {
      let univ = cache
        .univ_table
        .get(*ui as usize)
        .ok_or_else(|| DecompileError::InvalidUnivIndex {
          idx: *ui,
          univs_len: cache.univ_table.len(),
          constant: cache.current_const.clone(),
        })?
        .clone();
      decompile_univ(&univ, lvl_names, cache)
    })
    .collect()
}

/// Extract the name address from ConstantMeta.
fn get_name_addr_from_meta(meta: &ConstantMeta) -> Option<&Address> {
  match meta {
    ConstantMeta::Empty => None,
    ConstantMeta::Def { name, .. } => Some(name),
    ConstantMeta::Axio { name, .. } => Some(name),
    ConstantMeta::Quot { name, .. } => Some(name),
    ConstantMeta::Indc { name, .. } => Some(name),
    ConstantMeta::Ctor { name, .. } => Some(name),
    ConstantMeta::Rec { name, .. } => Some(name),
  }
}

/// Extract level param name addresses from ConstantMeta.
fn get_lvls_from_meta(meta: &ConstantMeta) -> &[Address] {
  match meta {
    ConstantMeta::Empty => &[],
    ConstantMeta::Def { lvls, .. } => lvls,
    ConstantMeta::Axio { lvls, .. } => lvls,
    ConstantMeta::Quot { lvls, .. } => lvls,
    ConstantMeta::Indc { lvls, .. } => lvls,
    ConstantMeta::Ctor { lvls, .. } => lvls,
    ConstantMeta::Rec { lvls, .. } => lvls,
  }
}

/// Extract arena and type_root from ConstantMeta.
fn get_arena_and_type_root(meta: &ConstantMeta) -> (&ExprMeta, u64) {
  static EMPTY_ARENA: ExprMeta = ExprMeta { nodes: Vec::new() };
  match meta {
    ConstantMeta::Def { arena, type_root, .. } => (arena, *type_root),
    ConstantMeta::Axio { arena, type_root, .. } => (arena, *type_root),
    ConstantMeta::Quot { arena, type_root, .. } => (arena, *type_root),
    ConstantMeta::Indc { arena, type_root, .. } => (arena, *type_root),
    ConstantMeta::Ctor { arena, type_root, .. } => (arena, *type_root),
    ConstantMeta::Rec { arena, type_root, .. } => (arena, *type_root),
    ConstantMeta::Empty => (&EMPTY_ARENA, 0),
  }
}

/// Extract the all field from ConstantMeta (original Lean all field for roundtrip).
fn get_all_from_meta(meta: &ConstantMeta) -> &[Address] {
  match meta {
    ConstantMeta::Def { all, .. } => all,
    ConstantMeta::Indc { all, .. } => all,
    ConstantMeta::Rec { all, .. } => all,
    _ => &[],
  }
}

/// Extract the ctx field from ConstantMeta (MutCtx used during compilation for Rec expr decompilation).
fn get_ctx_from_meta(meta: &ConstantMeta) -> &[Address] {
  match meta {
    ConstantMeta::Def { ctx, .. } => ctx,
    ConstantMeta::Indc { ctx, .. } => ctx,
    ConstantMeta::Rec { ctx, .. } => ctx,
    _ => &[],
  }
}

/// Decompile a name from ConstantMeta.
fn decompile_name_from_meta(
  meta: &ConstantMeta,
  stt: &CompileState,
) -> Result<Name, DecompileError> {
  match get_name_addr_from_meta(meta) {
    Some(addr) => decompile_name(addr, stt),
    None => {
      Err(DecompileError::BadConstantFormat { msg: "empty metadata".into() })
    },
  }
}

/// Extract level param names from ConstantMeta.
fn decompile_level_names_from_meta(
  meta: &ConstantMeta,
  stt: &CompileState,
) -> Result<Vec<Name>, DecompileError> {
  get_lvls_from_meta(meta).iter().map(|a| decompile_name(a, stt)).collect()
}

// ===========================================================================
// Constant decompilation
// ===========================================================================

/// Decompile a ConstantVal (name, level_params, type).
fn decompile_const_val(
  typ: &Arc<Expr>,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstantVal, DecompileError> {
  let name = decompile_name_from_meta(meta, stt)?;
  let level_params = decompile_level_names_from_meta(meta, stt)?;
  let (arena, type_root) = get_arena_and_type_root(meta);
  let typ =
    decompile_expr(typ, arena, type_root, &level_params, cache, stt, dstt)?;
  Ok(ConstantVal { name, level_params, typ })
}

/// Decompile a Definition.
fn decompile_definition(
  def: &Definition,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanConstantInfo, DecompileError> {
  let name = decompile_name_from_meta(meta, stt)?;
  let level_params = decompile_level_names_from_meta(meta, stt)?;

  let (arena, type_root, value_root) = match meta {
    ConstantMeta::Def { arena, type_root, value_root, .. } => {
      (arena, *type_root, *value_root)
    },
    _ => {
      static EMPTY: ExprMeta = ExprMeta { nodes: Vec::new() };
      (&EMPTY, 0, 0)
    },
  };

  let typ = decompile_expr(
    &def.typ,
    arena,
    type_root,
    &level_params,
    cache,
    stt,
    dstt,
  )?;
  let value = decompile_expr(
    &def.value,
    arena,
    value_root,
    &level_params,
    cache,
    stt,
    dstt,
  )?;

  let (hints, all) = match meta {
    ConstantMeta::Def { hints, all, .. } => {
      let all_names: Result<Vec<Name>, _> =
        all.iter().map(|a| decompile_name(a, stt)).collect();
      (*hints, all_names?)
    },
    _ => (ReducibilityHints::Opaque, vec![]),
  };

  let cnst = ConstantVal { name, level_params, typ };

  match def.kind {
    DefKind::Definition => Ok(LeanConstantInfo::DefnInfo(DefinitionVal {
      cnst,
      value,
      hints,
      safety: def.safety,
      all,
    })),
    DefKind::Theorem => {
      Ok(LeanConstantInfo::ThmInfo(TheoremVal { cnst, value, all }))
    },
    DefKind::Opaque => Ok(LeanConstantInfo::OpaqueInfo(OpaqueVal {
      cnst,
      value,
      is_unsafe: def.safety == DefinitionSafety::Unsafe,
      all,
    })),
  }
}

/// Decompile a Recursor.
/// Arena covers type + all rule RHS expressions with rule_roots.
fn decompile_recursor(
  rec: &Recursor,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanConstantInfo, DecompileError> {
  let name = decompile_name_from_meta(meta, stt)?;
  let level_params = decompile_level_names_from_meta(meta, stt)?;

  let (arena, type_root, rule_roots, rule_addrs, all_addrs) = match meta {
    ConstantMeta::Rec { arena, type_root, rule_roots, rules, all, .. } => (
      arena,
      *type_root,
      rule_roots.as_slice(),
      rules.as_slice(),
      all.as_slice(),
    ),
    _ => {
      static EMPTY: ExprMeta = ExprMeta { nodes: Vec::new() };
      (&EMPTY, 0u64, &[] as &[u64], &[] as &[Address], &[] as &[Address])
    },
  };

  let typ = decompile_expr(
    &rec.typ,
    arena,
    type_root,
    &level_params,
    cache,
    stt,
    dstt,
  )?;

  let rule_names = rule_addrs
    .iter()
    .map(|a| decompile_name(a, stt))
    .collect::<Result<Vec<_>, _>>()?;
  let all = all_addrs
    .iter()
    .map(|a| decompile_name(a, stt))
    .collect::<Result<Vec<_>, _>>()
    .unwrap_or_else(|_| vec![name.clone()]);

  let mut rules = Vec::with_capacity(rec.rules.len());
  for (i, (rule, ctor_name)) in
    rec.rules.iter().zip(rule_names.iter()).enumerate()
  {
    let rhs_root = rule_roots.get(i).copied().unwrap_or(0);
    let rhs = decompile_expr(
      &rule.rhs,
      arena,
      rhs_root,
      &level_params,
      cache,
      stt,
      dstt,
    )?;
    rules.push(LeanRecursorRule {
      ctor: ctor_name.clone(),
      n_fields: Nat::from(rule.fields),
      rhs,
    });
  }

  let cnst = ConstantVal { name, level_params, typ };

  Ok(LeanConstantInfo::RecInfo(RecursorVal {
    cnst,
    all,
    num_params: Nat::from(rec.params),
    num_indices: Nat::from(rec.indices),
    num_motives: Nat::from(rec.motives),
    num_minors: Nat::from(rec.minors),
    rules,
    k: rec.k,
    is_unsafe: rec.is_unsafe,
  }))
}

/// Decompile a Constructor.
/// Constructor metadata is in its own ConstantMeta::Ctor (resolved from Named entries).
fn decompile_constructor(
  ctor: &Constructor,
  meta: &ConstantMeta,
  induct_name: Name,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstructorVal, DecompileError> {
  let name = decompile_name_from_meta(meta, stt)?;
  let level_params = decompile_level_names_from_meta(meta, stt)?;

  let (arena, type_root) = get_arena_and_type_root(meta);
  let typ = decompile_expr(
    &ctor.typ,
    arena,
    type_root,
    &level_params,
    cache,
    stt,
    dstt,
  )?;

  let cnst = ConstantVal { name, level_params, typ };

  Ok(ConstructorVal {
    cnst,
    induct: induct_name,
    cidx: Nat::from(ctor.cidx),
    num_params: Nat::from(ctor.params),
    num_fields: Nat::from(ctor.fields),
    is_unsafe: ctor.is_unsafe,
  })
}

/// Decompile an Inductive.
/// Constructor metadata is resolved from Named entries, not from CtorMeta.
fn decompile_inductive(
  ind: &Inductive,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(InductiveVal, Vec<ConstructorVal>), DecompileError> {
  let name = decompile_name_from_meta(meta, stt)?;
  let level_params = decompile_level_names_from_meta(meta, stt)?;

  let (arena, type_root) = get_arena_and_type_root(meta);
  let typ = decompile_expr(
    &ind.typ,
    arena,
    type_root,
    &level_params,
    cache,
    stt,
    dstt,
  )?;

  // Extract constructor name addresses and all from metadata
  let (ctor_name_addrs, all) = match meta {
    ConstantMeta::Indc { ctors, all: all_addrs, .. } => {
      let all = all_addrs
        .iter()
        .map(|a| decompile_name(a, stt))
        .collect::<Result<Vec<_>, _>>()?;
      (ctors.as_slice(), all)
    },
    _ => (&[] as &[Address], vec![name.clone()]),
  };

  let mut ctors = Vec::with_capacity(ind.ctors.len());
  let mut ctor_names = Vec::new();

  for (i, ctor) in ind.ctors.iter().enumerate() {
    // Clear expr_cache: each constructor has its own arena, so cached entries
    // from the inductive's arena (or a previous constructor's arena) would
    // produce stale hits when arena indices coincide.
    cache.expr_cache.clear();

    // Look up constructor's Named entry for its ConstantMeta::Ctor
    let ctor_meta = if let Some(addr) = ctor_name_addrs.get(i) {
      if let Ok(ctor_name) = decompile_name(addr, stt) {
        stt
          .env
          .named
          .get(&ctor_name)
          .map(|n| n.meta.clone())
          .unwrap_or_default()
      } else {
        ConstantMeta::Empty
      }
    } else {
      ConstantMeta::Empty
    };

    let ctor_val =
      decompile_constructor(ctor, &ctor_meta, name.clone(), cache, stt, dstt)?;
    ctor_names.push(ctor_val.cnst.name.clone());
    ctors.push(ctor_val);
  }

  let cnst = ConstantVal { name, level_params, typ };

  let ind_val = InductiveVal {
    cnst,
    num_params: Nat::from(ind.params),
    num_indices: Nat::from(ind.indices),
    all,
    ctors: ctor_names,
    num_nested: Nat::from(ind.nested),
    is_rec: ind.recr,
    is_reflexive: ind.refl,
    is_unsafe: ind.is_unsafe,
  };

  Ok((ind_val, ctors))
}

/// Decompile an Axiom.
fn decompile_axiom(
  ax: &Axiom,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanConstantInfo, DecompileError> {
  let cnst = decompile_const_val(&ax.typ, meta, cache, stt, dstt)?;
  Ok(LeanConstantInfo::AxiomInfo(AxiomVal { cnst, is_unsafe: ax.is_unsafe }))
}

/// Decompile a Quotient.
fn decompile_quotient(
  quot: &Quotient,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanConstantInfo, DecompileError> {
  let cnst = decompile_const_val(&quot.typ, meta, cache, stt, dstt)?;
  Ok(LeanConstantInfo::QuotInfo(QuotVal { cnst, kind: quot.kind }))
}

// ===========================================================================
// Mutual block decompilation
// ===========================================================================

/// Decompile a mutual block (Vec<MutConst>).
/// Decompile a single projection, given the block data and sharing.
#[allow(clippy::too_many_arguments)]
fn decompile_projection(
  name: &Name,
  named: &Named,
  cnst: &Constant,
  mutuals: &[MutConst],
  block_sharing: &[Arc<Expr>],
  block_refs: &[Address],
  block_univs: &[Arc<Univ>],
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  // Build ctx from metadata's ctx field
  let ctx_addrs = get_ctx_from_meta(&named.meta);
  let ctx_names: Vec<Name> =
    ctx_addrs.iter().filter_map(|a| decompile_name(a, stt).ok()).collect();

  // Set up cache with sharing, refs, univs, and ctx
  let mut cache = BlockCache {
    sharing: block_sharing.to_vec(),
    refs: block_refs.to_vec(),
    univ_table: block_univs.to_vec(),
    ctx: all_to_ctx(&ctx_names),
    current_const: name.pretty(),
    ..Default::default()
  };

  match &cnst.info {
    ConstantInfo::DPrj(proj) => {
      if let Some(MutConst::Defn(def)) = mutuals.get(proj.idx as usize) {
        let info =
          decompile_definition(def, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), info);
      }
    },

    ConstantInfo::IPrj(_proj) => {
      if let Some(MutConst::Indc(ind)) = mutuals.get(_proj.idx as usize) {
        let (ind_val, ctors) =
          decompile_inductive(ind, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), LeanConstantInfo::InductInfo(ind_val));
        for ctor in ctors {
          dstt
            .env
            .insert(ctor.cnst.name.clone(), LeanConstantInfo::CtorInfo(ctor));
        }
      }
    },

    ConstantInfo::RPrj(proj) => {
      if let Some(MutConst::Recr(rec)) = mutuals.get(proj.idx as usize) {
        let info = decompile_recursor(rec, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), info);
      }
    },

    _ => {},
  }

  Ok(())
}

/// Decompile a single constant (non-mutual).
fn decompile_const(
  name: &Name,
  named: &Named,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  let cnst = read_const(&named.addr, stt)?;

  // Build ctx from metadata's all field
  let all_addrs = get_all_from_meta(&named.meta);
  let all_names: Vec<Name> =
    all_addrs.iter().filter_map(|a| decompile_name(a, stt).ok()).collect();
  let ctx = all_to_ctx(&all_names);
  let current_const = name.pretty();

  match cnst {
    Constant {
      info: ConstantInfo::Defn(def),
      ref sharing,
      ref refs,
      ref univs,
    } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx: ctx.clone(),
        current_const: current_const.clone(),
        ..Default::default()
      };
      let info =
        decompile_definition(&def, &named.meta, &mut cache, stt, dstt)?;
      dstt.env.insert(name.clone(), info);
    },

    Constant {
      info: ConstantInfo::Recr(rec),
      ref sharing,
      ref refs,
      ref univs,
    } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx: ctx.clone(),
        current_const: current_const.clone(),
        ..Default::default()
      };
      let info = decompile_recursor(&rec, &named.meta, &mut cache, stt, dstt)?;
      dstt.env.insert(name.clone(), info);
    },

    Constant {
      info: ConstantInfo::Axio(ax),
      ref sharing,
      ref refs,
      ref univs,
    } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx: ctx.clone(),
        current_const: current_const.clone(),
        ..Default::default()
      };
      let info = decompile_axiom(&ax, &named.meta, &mut cache, stt, dstt)?;
      dstt.env.insert(name.clone(), info);
    },

    Constant {
      info: ConstantInfo::Quot(quot),
      ref sharing,
      ref refs,
      ref univs,
    } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx,
        current_const,
        ..Default::default()
      };
      let info = decompile_quotient(&quot, &named.meta, &mut cache, stt, dstt)?;
      dstt.env.insert(name.clone(), info);
    },

    Constant { info: ConstantInfo::DPrj(_), .. }
    | Constant { info: ConstantInfo::IPrj(_), .. }
    | Constant { info: ConstantInfo::RPrj(_), .. }
    | Constant { info: ConstantInfo::CPrj(_), .. } => {
      // Projections are handled by decompile_block
    },

    Constant { info: ConstantInfo::Muts(_), .. } => {
      // Mutual blocks are handled separately
    },
  }

  Ok(())
}

// ===========================================================================
// Main entry point
// ===========================================================================

/// Decompile an Ixon environment back to Lean format.
pub fn decompile_env(
  stt: &CompileState,
) -> Result<DecompileState, DecompileError> {
  let dstt = DecompileState::default();

  // Constructor metadata is now embedded directly in ConstantMeta::Indc,
  // so no pre-indexing is needed.

  // Single pass through all named constants
  stt.env.named.par_iter().try_for_each(|entry| {
    let (name, named) = (entry.key(), entry.value());

    if let Some(cnst) = stt.env.get_const(&named.addr) {
      match &cnst.info {
        // Direct constants - decompile immediately
        ConstantInfo::Defn(_)
        | ConstantInfo::Recr(_)
        | ConstantInfo::Axio(_)
        | ConstantInfo::Quot(_) => decompile_const(name, named, stt, &dstt),

        // Projections - get the block and decompile
        ConstantInfo::DPrj(proj) => {
          if let Some(Constant {
            info: ConstantInfo::Muts(mutuals),
            ref sharing,
            ref refs,
            ref univs,
          }) = stt.env.get_const(&proj.block)
          {
            decompile_projection(
              name, named, &cnst, &mutuals, sharing, refs, univs, stt, &dstt,
            )
          } else {
            Err(DecompileError::MissingAddress(proj.block.clone()))
          }
        },

        ConstantInfo::IPrj(proj) => {
          if let Some(Constant {
            info: ConstantInfo::Muts(mutuals),
            ref sharing,
            ref refs,
            ref univs,
          }) = stt.env.get_const(&proj.block)
          {
            decompile_projection(
              name, named, &cnst, &mutuals, sharing, refs, univs, stt, &dstt,
            )
          } else {
            Err(DecompileError::MissingAddress(proj.block.clone()))
          }
        },

        ConstantInfo::RPrj(proj) => {
          if let Some(Constant {
            info: ConstantInfo::Muts(mutuals),
            ref sharing,
            ref refs,
            ref univs,
          }) = stt.env.get_const(&proj.block)
          {
            decompile_projection(
              name, named, &cnst, &mutuals, sharing, refs, univs, stt, &dstt,
            )
          } else {
            Err(DecompileError::MissingAddress(proj.block.clone()))
          }
        },

        // Constructor projections are handled when their parent inductive is decompiled
        ConstantInfo::CPrj(_) => Ok(()),

        // Mutual blocks themselves don't need separate handling
        ConstantInfo::Muts(_) => Ok(()),
      }
    } else {
      Ok(())
    }
  })?;

  Ok(dstt)
}

/// Result of checking a decompiled environment against the original.
#[derive(Debug)]
pub struct CheckResult {
  pub matches: usize,
  pub mismatches: usize,
  pub missing: usize,
}

/// Check that decompiled environment matches the original.
/// Counts and logs hash mismatches (which indicate metadata loss or decompilation errors).
pub fn check_decompile(
  original: &LeanEnv,
  _stt: &CompileState,
  dstt: &DecompileState,
) -> Result<CheckResult, DecompileError> {
  use std::sync::atomic::{AtomicUsize, Ordering};

  let mismatches = AtomicUsize::new(0);
  let matches = AtomicUsize::new(0);
  let missing = AtomicUsize::new(0);

  if original.len() != dstt.env.len() {
    eprintln!(
      "check_decompile: size mismatch: original={}, decompiled={}",
      original.len(),
      dstt.env.len()
    );
  }

  dstt.env.par_iter().try_for_each(|entry| {
    let (name, info) = (entry.key(), entry.value());
    match original.get(name) {
      Some(orig_info) if orig_info.get_hash() == info.get_hash() => {
        matches.fetch_add(1, Ordering::Relaxed);
        Ok::<(), DecompileError>(())
      },
      Some(orig_info) => {
        // Hash mismatch - log the constant name and hashes
        let count = mismatches.fetch_add(1, Ordering::Relaxed);
        if count < 20 {
          eprintln!(
            "check_decompile: hash mismatch for {}: original={:?}, decompiled={:?}",
            name.pretty(),
            orig_info.get_hash(),
            info.get_hash()
          );
        }
        Ok(())
      },
      None => {
        missing.fetch_add(1, Ordering::Relaxed);
        Ok(())
      },
    }
  })?;

  let result = CheckResult {
    matches: matches.load(Ordering::Relaxed),
    mismatches: mismatches.load(Ordering::Relaxed),
    missing: missing.load(Ordering::Relaxed),
  };
  eprintln!(
    "check_decompile: {} matches, {} mismatches, {} not in original",
    result.matches, result.mismatches, result.missing
  );

  Ok(result)
}
