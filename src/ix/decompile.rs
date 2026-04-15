//! Decompilation from Ixon format back to Lean environment.
//!
//! This module decompiles alpha-invariant Ixon representations back to
//! Lean constants, expanding Share references and reattaching metadata.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::map_err_ignore)]
#![allow(clippy::match_same_arms)]

use lean_ffi::nat::Nat;

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
      DefinitionProj, Inductive, InductiveProj, MutConst, Quotient, Recursor,
      RecursorProj,
    },
    env::Named,
    expr::Expr,
    metadata::{
      ConstantMeta, ConstantMetaInfo, DataValue, ExprMeta, ExprMetaData, KVMap,
    },
    univ::Univ,
  },
  ix::mutual::{Def, Ind, MutConst as LeanMutConst, MutCtx, all_to_ctx},
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

          // Ref: resolve name from arena Ref node
          (
            ExprMetaData::Ref { name: name_addr },
            Expr::Ref(ref_idx, univ_indices),
          ) => {
            let name = decompile_name(name_addr, stt).map_err(|_| {
              DecompileError::BadConstantFormat {
                msg: format!(
                  "Ref metadata name resolution failed in '{}' (ref_idx={}, arena has Ref but name addr {:.12} not found)",
                  cache.current_const, ref_idx, name_addr.hex(),
                ),
              }
            })?;
            let levels =
              decompile_univ_indices(univ_indices, lvl_names, cache)?;
            let expr = apply_mdata(LeanExpr::cnst(name, levels), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Ref(ref_idx, _univ_indices)) => {
            // No Ref metadata — this is a metadata mismatch (the arena
            // should always have a Ref node for Ref expressions).
            return Err(DecompileError::BadConstantFormat {
              msg: format!(
                "missing Ref metadata for Expr::Ref in '{}' (ref_idx={}, arena node={:?})",
                cache.current_const,
                ref_idx,
                arena.nodes.get(current_idx as usize).unwrap_or(&DEFAULT_NODE),
              ),
            });
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

          (_, Expr::Prj(type_ref_idx, _field_idx, _struct_val)) => {
            // Fallback: look up from refs table
            let addr =
              cache.refs.get(*type_ref_idx as usize).ok_or_else(|| {
                DecompileError::InvalidRefIndex {
                  idx: *type_ref_idx,
                  refs_len: cache.refs.len(),
                  constant: cache.current_const.clone(),
                }
              })?;
            // No Prj metadata — this is a metadata mismatch.
            return Err(DecompileError::BadConstantFormat {
              msg: format!(
                "missing Prj metadata for Expr::Prj in '{}' (type_ref_idx={}, addr={:.12})",
                cache.current_const,
                type_ref_idx,
                addr.hex(),
              ),
            });
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
  match &meta.info {
    ConstantMetaInfo::Empty => None,
    ConstantMetaInfo::Def { name, .. } => Some(name),
    ConstantMetaInfo::Axio { name, .. } => Some(name),
    ConstantMetaInfo::Quot { name, .. } => Some(name),
    ConstantMetaInfo::Indc { name, .. } => Some(name),
    ConstantMetaInfo::Ctor { name, .. } => Some(name),
    ConstantMetaInfo::Rec { name, .. } => Some(name),
    ConstantMetaInfo::Muts { .. } => None,
  }
}

/// Extract level param name addresses from ConstantMeta.
fn get_lvls_from_meta(meta: &ConstantMeta) -> &[Address] {
  match &meta.info {
    ConstantMetaInfo::Empty => &[],
    ConstantMetaInfo::Def { lvls, .. } => lvls,
    ConstantMetaInfo::Axio { lvls, .. } => lvls,
    ConstantMetaInfo::Quot { lvls, .. } => lvls,
    ConstantMetaInfo::Indc { lvls, .. } => lvls,
    ConstantMetaInfo::Ctor { lvls, .. } => lvls,
    ConstantMetaInfo::Rec { lvls, .. } => lvls,
    ConstantMetaInfo::Muts { .. } => &[],
  }
}

/// Extract arena and type_root from ConstantMeta.
fn get_arena_and_type_root(meta: &ConstantMeta) -> (&ExprMeta, u64) {
  static EMPTY_ARENA: ExprMeta = ExprMeta { nodes: Vec::new() };
  match &meta.info {
    ConstantMetaInfo::Def { arena, type_root, .. } => (arena, *type_root),
    ConstantMetaInfo::Axio { arena, type_root, .. } => (arena, *type_root),
    ConstantMetaInfo::Quot { arena, type_root, .. } => (arena, *type_root),
    ConstantMetaInfo::Indc { arena, type_root, .. } => (arena, *type_root),
    ConstantMetaInfo::Ctor { arena, type_root, .. } => (arena, *type_root),
    ConstantMetaInfo::Rec { arena, type_root, .. } => (arena, *type_root),
    ConstantMetaInfo::Empty => (&EMPTY_ARENA, 0),
    ConstantMetaInfo::Muts { .. } => (&EMPTY_ARENA, 0),
  }
}

/// Extract the all field from ConstantMeta (original Lean all field for roundtrip).
fn get_all_from_meta(meta: &ConstantMeta) -> &[Address] {
  match &meta.info {
    ConstantMetaInfo::Def { all, .. } => all,
    ConstantMetaInfo::Indc { all, .. } => all,
    ConstantMetaInfo::Rec { all, .. } => all,
    _ => &[],
  }
}

/// Extract the ctx field from ConstantMeta (MutCtx used during compilation for Rec expr decompilation).
fn get_ctx_from_meta(meta: &ConstantMeta) -> &[Address] {
  match &meta.info {
    ConstantMetaInfo::Def { ctx, .. } => ctx,
    ConstantMetaInfo::Indc { ctx, .. } => ctx,
    ConstantMetaInfo::Rec { ctx, .. } => ctx,
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

  let (arena, type_root, value_root) = match &meta.info {
    ConstantMetaInfo::Def { arena, type_root, value_root, .. } => {
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

  let (hints, all) = match &meta.info {
    ConstantMetaInfo::Def { hints, all, .. } => {
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

  let (arena, type_root, rule_roots, rule_addrs, all_addrs) = match &meta.info {
    ConstantMetaInfo::Rec {
      arena, type_root, rule_roots, rules, all, ..
    } => (
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
/// Constructor metadata is in its own ConstantMetaInfo::Ctor (resolved from Named entries).
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
  let (ctor_name_addrs, all) = match &meta.info {
    ConstantMetaInfo::Indc { ctors, all: all_addrs, .. } => {
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

    // Look up constructor's Named entry for its ConstantMetaInfo::Ctor
    let ctor_meta = if let Some(addr) = ctor_name_addrs.get(i) {
      if let Ok(ctor_name) = decompile_name(addr, stt) {
        stt
          .env
          .named
          .get(&ctor_name)
          .map(|n| {
            // Use original metadata when available (aux_gen roundtrip path).
            // The canonical metadata (n.meta) may have a different arena
            // structure (e.g., alpha-collapsed with fewer motives) than the
            // expression being decompiled. The original metadata matches the
            // un-collapsed block structure.
            n.original
              .as_ref()
              .map_or_else(|| n.meta.clone(), |(_, m)| m.clone())
          })
          .unwrap_or_default()
      } else {
        ConstantMeta::default()
      }
    } else {
      ConstantMeta::default()
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
    ConstantInfo::DPrj(proj) => match mutuals.get(proj.idx as usize) {
      Some(MutConst::Defn(def)) => {
        let info =
          decompile_definition(def, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), info);
      },
      other => {
        let has_addr = stt.name_to_addr.contains_key(name);
        let has_aux = stt.aux_name_to_addr.contains_key(name);
        let has_original =
          stt.env.named.get(name).map(|n| n.original.is_some());
        eprintln!(
          "[decompile] DPrj {} idx={} failed: got {:?} (mutuals.len={}, addr={}, aux={}, orig={:?})",
          name.pretty(),
          proj.idx,
          other.map(std::mem::discriminant),
          mutuals.len(),
          has_addr,
          has_aux,
          has_original,
        );
      },
    },

    ConstantInfo::IPrj(proj) => match mutuals.get(proj.idx as usize) {
      Some(MutConst::Indc(ind)) => {
        let (ind_val, ctors) =
          decompile_inductive(ind, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), LeanConstantInfo::InductInfo(ind_val));
        for ctor in ctors {
          dstt
            .env
            .insert(ctor.cnst.name.clone(), LeanConstantInfo::CtorInfo(ctor));
        }
      },
      other => {
        let has_addr = stt.name_to_addr.contains_key(name);
        let has_aux = stt.aux_name_to_addr.contains_key(name);
        let has_original =
          stt.env.named.get(name).map(|n| n.original.is_some());
        eprintln!(
          "[decompile] IPrj {} idx={} failed: got {:?} (mutuals.len={}, addr={}, aux={}, orig={:?})",
          name.pretty(),
          proj.idx,
          other.map(std::mem::discriminant),
          mutuals.len(),
          has_addr,
          has_aux,
          has_original,
        );
      },
    },

    ConstantInfo::RPrj(proj) => match mutuals.get(proj.idx as usize) {
      Some(MutConst::Recr(rec)) => {
        let info = decompile_recursor(rec, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), info);
      },
      other => {
        let has_addr = stt.name_to_addr.contains_key(name);
        let has_aux = stt.aux_name_to_addr.contains_key(name);
        let has_original =
          stt.env.named.get(name).map(|n| n.original.is_some());
        eprintln!(
          "[decompile] RPrj {} idx={} failed: got {:?} (mutuals.len={}, addr={}, aux={}, orig={:?})",
          name.pretty(),
          proj.idx,
          other.map(std::mem::discriminant),
          mutuals.len(),
          has_addr,
          has_aux,
          has_original,
        );
      },
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
// Aux_gen decompilation (Pass 2)
// ===========================================================================

/// Recognized aux_gen suffix kinds, ordered by dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AuxKind {
  Rec,
  RecOn,
  CasesOn,
  Below,
  BelowRec,
  BRecOnGo,
  BRecOn,
  BRecOnEq,
}

/// Check whether a constant name has an aux_gen suffix that should be
/// regenerated rather than decompiled from Ixon.
fn is_aux_gen_suffix(name: &Name) -> bool {
  classify_aux_gen(name).is_some()
}

/// Classify an aux_gen constant by suffix, returning (kind, root_inductive).
/// The root inductive is the base inductive the auxiliary is derived from.
fn classify_aux_gen(name: &Name) -> Option<(AuxKind, Name)> {
  use crate::ix::env::NameData;
  let s1 = name.last_str()?;
  let p1 = match name.as_data() {
    NameData::Str(parent, _, _) => parent.clone(),
    _ => return None,
  };

  match s1 {
    s if s == "rec" || s.starts_with("rec_") => {
      // X.rec / X.rec_N or X.below.rec
      if let Some(ps) = p1.last_str()
        && (ps == "below" || ps.starts_with("below_"))
      {
        let root = match p1.as_data() {
          NameData::Str(gp, _, _) => gp.clone(),
          _ => return None,
        };
        Some((AuxKind::BelowRec, root))
      } else {
        Some((AuxKind::Rec, p1))
      }
    },
    s if s == "recOn" || s.starts_with("recOn_") => Some((AuxKind::RecOn, p1)),
    s if s == "casesOn" || s.starts_with("casesOn_") => {
      Some((AuxKind::CasesOn, p1))
    },
    s if s == "below" || s.starts_with("below_") => Some((AuxKind::Below, p1)),
    s if s == "brecOn" || s.starts_with("brecOn_") => {
      Some((AuxKind::BRecOn, p1))
    },
    "go" => {
      // X.brecOn.go or X.brecOn_N.go (nested auxiliary)
      if let Some(parent_str) = p1.last_str()
        && (parent_str == "brecOn" || parent_str.starts_with("brecOn_"))
      {
        let root = match p1.as_data() {
          NameData::Str(gp, _, _) => gp.clone(),
          _ => return None,
        };
        Some((AuxKind::BRecOnGo, root))
      } else {
        None
      }
    },
    "eq" => {
      // X.brecOn.eq or X.brecOn_N.eq (nested auxiliary)
      if let Some(parent_str) = p1.last_str()
        && (parent_str == "brecOn" || parent_str.starts_with("brecOn_"))
      {
        let root = match p1.as_data() {
          NameData::Str(gp, _, _) => gp.clone(),
          _ => return None,
        };
        Some((AuxKind::BRecOnEq, root))
      } else {
        None
      }
    },
    _ => None,
  }
}

/// Build a `LeanEnv` subset containing inductives and constructors for the
/// given names. Used to prepare the environment for aux_gen regeneration.
fn build_block_env(all_names: &[Name], lean_env: &LeanEnv) -> LeanEnv {
  let mut env = LeanEnv::default();
  for ind_name in all_names {
    if let Some(ci) = lean_env.get(ind_name) {
      env.insert(ind_name.clone(), ci.clone());
      if let LeanConstantInfo::InductInfo(v) = ci {
        for ctor_name in &v.ctors {
          if let Some(ctor_ci) = lean_env.get(ctor_name) {
            env.insert(ctor_name.clone(), ctor_ci.clone());
          }
        }
      }
    }
  }
  env
}

/// Convert a `BelowDef` (Type-level `.below`) to a `LeanConstantInfo`.
fn below_def_to_lean(
  def: &crate::ix::compile::aux_gen::below::BelowDef,
) -> LeanConstantInfo {
  LeanConstantInfo::DefnInfo(DefinitionVal {
    cnst: ConstantVal {
      name: def.name.clone(),
      level_params: def.level_params.clone(),
      typ: def.typ.clone(),
    },
    value: def.value.clone(),
    hints: ReducibilityHints::Abbrev,
    safety: DefinitionSafety::Safe,
    all: vec![def.name.clone()],
  })
}

/// Convert a `BelowIndc` (Prop-level `.below`) to an `InductiveVal` and its constructors.
fn below_indc_to_lean(
  indc: &crate::ix::compile::aux_gen::below::BelowIndc,
  all_below_names: &[Name],
) -> (InductiveVal, Vec<ConstructorVal>) {
  let ctor_names: Vec<Name> =
    indc.ctors.iter().map(|c| c.name.clone()).collect();
  let ind_val = InductiveVal {
    cnst: ConstantVal {
      name: indc.name.clone(),
      level_params: indc.level_params.clone(),
      typ: indc.typ.clone(),
    },
    num_params: Nat::from(indc.n_params as u64),
    num_indices: Nat::from(indc.n_indices as u64),
    all: all_below_names.to_vec(),
    ctors: ctor_names,
    num_nested: Nat::from(0u64),
    is_rec: true,
    is_reflexive: false,
    is_unsafe: false,
  };
  let ctors: Vec<ConstructorVal> = indc
    .ctors
    .iter()
    .enumerate()
    .map(|(cidx, c)| ConstructorVal {
      cnst: ConstantVal {
        name: c.name.clone(),
        level_params: indc.level_params.clone(),
        typ: c.typ.clone(),
      },
      induct: indc.name.clone(),
      cidx: Nat::from(cidx as u64),
      num_params: Nat::from(c.n_params as u64),
      num_fields: Nat::from(c.n_fields as u64),
      is_unsafe: false,
    })
    .collect();
  (ind_val, ctors)
}

/// Convert a `BRecOnDef` to a `LeanConstantInfo`.
/// `as_theorem` controls whether to produce ThmInfo (Prop-level brecOn)
/// or DefnInfo (Type-level brecOn).
fn brecon_def_to_lean(
  def: &crate::ix::compile::aux_gen::brecon::BRecOnDef,
  as_theorem: bool,
) -> LeanConstantInfo {
  let cnst = ConstantVal {
    name: def.name.clone(),
    level_params: def.level_params.clone(),
    typ: def.typ.clone(),
  };
  if as_theorem {
    LeanConstantInfo::ThmInfo(TheoremVal {
      cnst,
      value: def.value.clone(),
      all: vec![def.name.clone()],
    })
  } else {
    LeanConstantInfo::DefnInfo(DefinitionVal {
      cnst,
      value: def.value.clone(),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![def.name.clone()],
    })
  }
}

fn ci_kind(ci: &LeanConstantInfo) -> &'static str {
  match ci {
    LeanConstantInfo::AxiomInfo(_) => "Axiom",
    LeanConstantInfo::DefnInfo(_) => "Defn",
    LeanConstantInfo::ThmInfo(_) => "Thm",
    LeanConstantInfo::OpaqueInfo(_) => "Opaque",
    LeanConstantInfo::QuotInfo(_) => "Quot",
    LeanConstantInfo::InductInfo(_) => "Induct",
    LeanConstantInfo::CtorInfo(_) => "Ctor",
    LeanConstantInfo::RecInfo(_) => "Rec",
  }
}

/// Print a three-way diagnostic comparison: generated (raw aux_gen) vs
/// decompiled (post-roundtrip) vs original (Lean). Only prints when the
/// decompiled version differs from the original. If `generated` is None,
/// only compares decompiled vs original.
///
/// `orig_env` is the immutable original Lean environment from the compiler.
/// When `None` (production/no-debug path), this is a no-op.
fn print_const_comparison(
  name: &Name,
  decompiled: &LeanConstantInfo,
  generated: Option<&LeanConstantInfo>,
  orig_env: Option<&LeanEnv>,
) {
  let Some(orig_env) = orig_env else { return };
  let Some(lean_ci) = orig_env.get(name) else { return };
  if std::mem::discriminant(decompiled) != std::mem::discriminant(lean_ci) {
    eprintln!(
      "[aux_gen diff] {}: kind decompiled={} original={}",
      name.pretty(),
      ci_kind(decompiled),
      ci_kind(lean_ci),
    );
    return;
  }

  let dec_type = decompiled.get_type();
  let lean_type = lean_ci.get_type();
  let type_match = dec_type.get_hash() == lean_type.get_hash();

  let dec_val = get_value(decompiled);
  let lean_val = get_value(lean_ci);
  let val_match = match (&dec_val, &lean_val) {
    (Some(g), Some(l)) => g.get_hash() == l.get_hash(),
    (None, None) => true,
    _ => false,
  };

  if type_match && val_match {
    return;
  }

  eprintln!("[aux_gen diff] {}", name.pretty());
  if !type_match {
    eprintln!("  type DIFFER:");
    if let Some(regen) = generated {
      eprintln!("    generated:  {}", regen.get_type().pretty());
    }
    eprintln!("    decompiled: {}", dec_type.pretty());
    eprintln!("    original:   {}", lean_type.pretty());
  }
  if !val_match {
    match (&dec_val, &lean_val) {
      (Some(d), Some(l)) => {
        eprintln!("  value DIFFER:");
        if let Some(regen) = generated
          && let Some(gv) = get_value(regen)
        {
          eprintln!("    generated:  {}", gv.pretty());
        }
        eprintln!("    decompiled: {}", d.pretty());
        eprintln!("    original:   {}", l.pretty());
      },
      (Some(_), None) => {
        eprintln!("  value: decompiled has value, original does not")
      },
      (None, Some(_)) => {
        eprintln!("  value: original has value, decompiled does not")
      },
      _ => {},
    }
  }
}

/// Extract the value expression from a ConstantInfo, if it has one.
fn get_value(ci: &LeanConstantInfo) -> Option<&LeanExpr> {
  match ci {
    LeanConstantInfo::DefnInfo(v) => Some(&v.value),
    LeanConstantInfo::ThmInfo(v) => Some(&v.value),
    LeanConstantInfo::OpaqueInfo(v) => Some(&v.value),
    _ => None,
  }
}

// ===========================================================================
// Compile→decompile roundtrip for binder name restoration
// ===========================================================================

/// Compute the content-address (blake3 hash of serialized bytes) of a Constant.
fn ixon_content_address(constant: &Constant) -> Address {
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  Address::hash(&bytes)
}

/// Validate both the Ixon-level and Lean-level hashes after a roundtrip.
///
/// - **Ixon check**: the recompiled projection hash should match `named.original.0`
/// - **Lean check**: the decompiled constant's hash should match the original Lean constant
///
/// On mismatch, prints detailed structural comparison.
///
/// `orig_env` is the immutable original Lean environment from the compiler.
/// When `None` (production/no-debug path), only the Ixon check runs.
fn _validate_roundtrip(
  name: &Name,
  decompiled: &LeanConstantInfo,
  orig_addr: Option<&Address>,
  recompiled_proj_addr: Option<&Address>,
  orig_env: Option<&LeanEnv>,
) {
  // Ixon projection hash check.
  if let (Some(orig), Some(recomp)) = (orig_addr, recompiled_proj_addr)
    && orig != recomp
  {
    eprintln!(
      "[roundtrip ixon] {} proj mismatch: orig={:.12} recomp={:.12}",
      name.pretty(),
      orig.hex(),
      recomp.hex(),
    );
  }

  // Decompiled Lean hash check (only with original environment).
  if let Some(orig_env) = orig_env
    && let Some(lean_ci) = orig_env.get(name)
  {
    let dec_hash = decompiled.get_hash();
    let lean_hash = lean_ci.get_hash();
    if dec_hash != lean_hash {
      eprintln!(
        "[roundtrip lean] {} hash mismatch: dec={:.12} lean={:.12}",
        name.pretty(),
        format!("{:?}", dec_hash),
        format!("{:?}", lean_hash),
      );
      // Print detailed diff.
      print_const_comparison(name, decompiled, None, Some(orig_env));
    }
  }
}

/// Compile a batch of regenerated `MutConst`s as a mutual block (mirroring
/// `compile_aux_block`), then decompile each member with original metadata
/// from `named.original` to restore binder names.
///
/// Returns a map from constant name to decompiled `LeanConstantInfo`.
/// Constructor entries from inductives are included under their own names.
///
/// `orig_env` is the immutable original Lean environment from the compiler,
/// used only for diagnostic hash comparisons. When `None` (production/no-debug
/// path), hash comparisons against originals are skipped — the roundtrip still
/// produces correct constants via metadata restoration.
fn roundtrip_block(
  consts: &[LeanMutConst],
  generated_consts: &FxHashMap<Name, LeanConstantInfo>,
  orig_env: Option<&LeanEnv>,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<FxHashMap<Name, LeanConstantInfo>, DecompileError> {
  use crate::ix::compile::{
    BlockCache as CompileBlockCache, compile_definition, compile_inductive,
    compile_mutual_block, compile_recursor, sort_consts,
  };
  use crate::ix::mutual::ctx_to_all;

  let mut results: FxHashMap<Name, LeanConstantInfo> = FxHashMap::default();
  if consts.is_empty() {
    return Ok(results);
  }

  // ------------------------------------------------------------------
  // Phase A: Compile to Ixon (mirrors compile_aux_block lines 69-121)
  // ------------------------------------------------------------------
  let mut cache = CompileBlockCache::default();

  let refs: Vec<&LeanMutConst> = consts.iter().collect();
  let sorted_classes = sort_consts(&refs, &mut cache, stt).map_err(|e| {
    DecompileError::BadConstantFormat {
      msg: format!("roundtrip sort_consts: {e}"),
    }
  })?;
  let mut_ctx = LeanMutConst::ctx(&sorted_classes);

  // Map from name → (class_idx, MutConst kind) for projection construction.
  let mut name_to_class: FxHashMap<Name, usize> = FxHashMap::default();
  let mut all_metas: FxHashMap<Name, ConstantMeta> = FxHashMap::default();
  let mut ixon_mutuals: Vec<MutConst> = Vec::new();

  for (class_idx, class) in sorted_classes.iter().enumerate() {
    let mut rep_pushed = false;
    for cnst in class {
      name_to_class.insert(cnst.name(), class_idx);
      match cnst {
        LeanMutConst::Recr(rec) => {
          let (data, meta) = compile_recursor(rec, &mut_ctx, &mut cache, stt)
            .map_err(|e| {
            DecompileError::BadConstantFormat {
              msg: format!(
                "roundtrip compile_rec {}: {e}",
                rec.cnst.name.pretty()
              ),
            }
          })?;
          if !rep_pushed {
            ixon_mutuals.push(MutConst::Recr(data));
            rep_pushed = true;
          }
          all_metas.insert(rec.cnst.name.clone(), meta);
        },
        LeanMutConst::Defn(def) => {
          let (data, meta) = compile_definition(def, &mut_ctx, &mut cache, stt)
            .map_err(|e| DecompileError::BadConstantFormat {
              msg: format!("roundtrip compile_def {}: {e}", def.name.pretty()),
            })?;
          if !rep_pushed {
            ixon_mutuals.push(MutConst::Defn(data));
            rep_pushed = true;
          }
          all_metas.insert(def.name.clone(), meta);
        },
        LeanMutConst::Indc(ind) => {
          let (data, meta, ctor_metas) =
            compile_inductive(ind, &mut_ctx, &mut cache, stt).map_err(|e| {
              DecompileError::BadConstantFormat {
                msg: format!(
                  "roundtrip compile_indc {}: {e}",
                  ind.ind.cnst.name.pretty()
                ),
              }
            })?;
          if !rep_pushed {
            ixon_mutuals.push(MutConst::Indc(data));
            rep_pushed = true;
          }
          all_metas.insert(ind.ind.cnst.name.clone(), meta);
          for (ctor, cm) in ind.ctors.iter().zip(ctor_metas) {
            all_metas.insert(ctor.cnst.name.clone(), cm);
            name_to_class.insert(ctor.cnst.name.clone(), class_idx);
          }
        },
      }
    }
  }

  // Singleton non-inductive: use apply_sharing_to_definition/recursor_with_stats
  // (matching compile_single_def/recursor) instead of compile_mutual_block.
  // This ensures the sharing analysis and arena match the original compilation.
  let singleton = sorted_classes.len() == 1
    && !consts.iter().any(|c| matches!(c, LeanMutConst::Indc(_)));

  let block_refs: Vec<Address> = cache.refs.iter().cloned().collect();
  let block_univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
  let name_str = consts[0].name().pretty();

  let (block_constant, block_addr) = if singleton && ixon_mutuals.len() == 1 {
    // Singleton: compile as bare constant (no Muts wrapper).
    let result = match &ixon_mutuals[0] {
      MutConst::Defn(def) => {
        crate::ix::compile::apply_sharing_to_definition_with_stats(
          def.clone(),
          block_refs,
          block_univs,
          Some(&name_str),
        )
      },
      MutConst::Recr(rec) => {
        crate::ix::compile::apply_sharing_to_recursor_with_stats(
          rec.clone(),
          block_refs,
          block_univs,
        )
      },
      MutConst::Indc(_) => unreachable!("singleton guard excludes inductives"),
    };
    let mut bytes = Vec::new();
    result.constant.put(&mut bytes);
    let addr = Address::hash(&bytes);
    (result.constant, addr)
  } else {
    // Multi-class or inductive: compile as mutual block (Muts wrapper).
    let compiled = compile_mutual_block(
      ixon_mutuals,
      block_refs,
      block_univs,
      Some(&name_str),
    );
    let addr = compiled.addr.clone();
    (compiled.constant, addr)
  };

  // Verify recompiled hash matches original. If they differ, the
  // regenerated expression has different structure from the original,
  // and the original metadata arena won't align with the recompiled data.
  //
  // For singletons, block_addr IS the constant's compiled address.
  // For mutual blocks, each member has a projection address (not block_addr),
  // so we compare the block_addr against the original block stored in the
  // first member's projection metadata.
  {
    let first_name = consts[0].name();
    let orig_addr = if singleton {
      // Singleton: compare directly against the constant's original address.
      stt.env.named.get(&first_name).map(|named| {
        if let Some((ref orig_a, _)) = named.original {
          orig_a.clone()
        } else {
          named.addr.clone()
        }
      })
    } else {
      // Mutual block: compare against the original block address.
      // The original block addr is stored in the projection's block field.
      stt.env.named.get(&first_name).and_then(|named| {
        let addr = if let Some((ref orig_a, _)) = named.original {
          orig_a
        } else {
          &named.addr
        };
        stt.env.get_const(addr).and_then(|c| match &c.info {
          crate::ix::ixon::constant::ConstantInfo::RPrj(p) => {
            Some(p.block.clone())
          },
          crate::ix::ixon::constant::ConstantInfo::DPrj(p) => {
            Some(p.block.clone())
          },
          crate::ix::ixon::constant::ConstantInfo::IPrj(p) => {
            Some(p.block.clone())
          },
          _ => Some(addr.clone()), // bare constant, not a projection
        })
      })
    };
    if let Some(orig) = orig_addr {
      if block_addr != orig {
        return Err(DecompileError::BadConstantFormat {
          msg: format!(
            "roundtrip recompile hash mismatch for '{}': recompiled={:.12} original={:.12}",
            first_name.pretty(),
            block_addr.hex(),
            orig.hex(),
          ),
        });
      }
    }
  }

  // Build the decompile ctx from the compiled MutCtx.
  let ctx_names = ctx_to_all(&mut_ctx);
  let dec_ctx = all_to_ctx(&ctx_names);

  // ------------------------------------------------------------------
  // Phase B: Decompile each member with original metadata
  // ------------------------------------------------------------------

  // Extract the Muts members (or the singleton constant).
  let muts_vec: Option<&Vec<MutConst>> = match &block_constant.info {
    ConstantInfo::Muts(v) => Some(v),
    _ => None,
  };

  for class in &sorted_classes {
    for cnst in class {
      let name = cnst.name();

      // Look up original metadata from compile_const_no_aux. If not
      // available, fall back to Phase A metadata from the current compilation.
      let orig_meta = match stt.env.named.get(&name) {
        Some(ref named) if named.original.is_some() => {
          named.original.as_ref().unwrap().1.clone()
        },
        _ => {
          // No original metadata — try Phase A (all_metas) as fallback.
          if let Some(meta) = all_metas.get(&name) {
            meta.clone()
          } else {
            continue;
          }
        },
      };

      // Build decompile cache with block tables.
      let mut dec_cache = BlockCache {
        ctx: dec_ctx.clone(),
        sharing: block_constant.sharing.clone(),
        refs: block_constant.refs.clone(),
        univ_table: block_constant.univs.clone(),
        current_const: name.pretty(),
        ..Default::default()
      };

      // Find the Ixon data for this constant.
      let class_idx = name_to_class.get(&name).copied().unwrap_or(0);

      let decompiled = if let Some(muts) = muts_vec {
        // Multi-class (Muts-wrapped): index into Muts vec.
        match (muts.get(class_idx), cnst) {
          (Some(MutConst::Recr(rec)), LeanMutConst::Recr(_)) => {
            decompile_recursor(rec, &orig_meta, &mut dec_cache, stt, dstt)
              .map(|ci| vec![(name.clone(), ci)])
          },
          (Some(MutConst::Defn(def)), LeanMutConst::Defn(_)) => {
            decompile_definition(def, &orig_meta, &mut dec_cache, stt, dstt)
              .map(|ci| vec![(name.clone(), ci)])
          },
          (Some(MutConst::Indc(ind)), LeanMutConst::Indc(_)) => {
            let (iv, cvs) =
              decompile_inductive(ind, &orig_meta, &mut dec_cache, stt, dstt)?;
            let mut entries =
              vec![(name.clone(), LeanConstantInfo::InductInfo(iv))];
            for cv in cvs {
              entries
                .push((cv.cnst.name.clone(), LeanConstantInfo::CtorInfo(cv)));
            }
            Ok(entries)
          },
          _ => continue,
        }
      } else {
        // Singleton (bare constant, no Muts wrapper). Matches compile_single_def path.
        match (&block_constant.info, cnst) {
          (ConstantInfo::Defn(def), LeanMutConst::Defn(_)) => {
            decompile_definition(def, &orig_meta, &mut dec_cache, stt, dstt)
              .map(|ci| vec![(name.clone(), ci)])
          },
          (ConstantInfo::Recr(rec), LeanMutConst::Recr(_)) => {
            decompile_recursor(rec, &orig_meta, &mut dec_cache, stt, dstt)
              .map(|ci| vec![(name.clone(), ci)])
          },
          _ => continue,
        }
      };

      match decompiled {
        Ok(entries) => {
          for (n, ci) in entries {
            // Validate Lean-level hash against the original environment.
            // Only possible when the original is available (debug path).
            if let Some(orig) = orig_env
              && let Some(lean_ci) = orig.get(&n)
              && ci.get_hash() != lean_ci.get_hash()
            {
              print_const_comparison(
                &n,
                &ci,
                generated_consts.get(&n),
                orig_env,
              );
              return Err(DecompileError::BadConstantFormat {
                msg: format!(
                  "roundtrip hash mismatch for '{}' (decompiled={} original={})",
                  n.pretty(),
                  ci_kind(&ci),
                  ci_kind(lean_ci),
                ),
              });
            }
            // Validate Ixon projection hash for the primary constant
            // (not constructors — they have CPrj addresses that depend on
            // parent+cidx, validated separately).
            let is_primary = !matches!(&ci, LeanConstantInfo::CtorInfo(_));
            if is_primary
              && let Some(ref named) = stt.env.named.get(&n)
              && let Some((ref orig_addr, _)) = named.original
            {
              let proj_addr = match cnst {
                LeanMutConst::Recr(_) => {
                  let proj = Constant::new(ConstantInfo::RPrj(RecursorProj {
                    idx: class_idx as u64,
                    block: block_addr.clone(),
                  }));
                  ixon_content_address(&proj)
                },
                LeanMutConst::Defn(_) => {
                  let proj =
                    Constant::new(ConstantInfo::DPrj(DefinitionProj {
                      idx: class_idx as u64,
                      block: block_addr.clone(),
                    }));
                  ixon_content_address(&proj)
                },
                LeanMutConst::Indc(_) => {
                  let proj = Constant::new(ConstantInfo::IPrj(InductiveProj {
                    idx: class_idx as u64,
                    block: block_addr.clone(),
                  }));
                  ixon_content_address(&proj)
                },
              };
              if &proj_addr != orig_addr {
                // The original might be a singleton (bare constant, not
                // Muts-wrapped projection) while roundtrip always wraps in
                // Muts. Skip the mismatch if the original is a singleton
                // (non-projection) or not stored (compile_const_no_aux
                // with aux=false doesn't store singleton constants).
                let orig_is_singleton =
                  stt.env.get_const(orig_addr).is_none_or(|c| {
                    !matches!(
                      &c.info,
                      ConstantInfo::IPrj(_)
                        | ConstantInfo::RPrj(_)
                        | ConstantInfo::DPrj(_)
                        | ConstantInfo::CPrj(_)
                    )
                  }); // not found → singleton (not stored)
                if !orig_is_singleton {
                  // Show block + idx details
                  let orig_detail =
                    stt.env.get_const(orig_addr).map(|c| match &c.info {
                      ConstantInfo::RPrj(p) => format!(
                        "RPrj(idx={}, block={:.12})",
                        p.idx,
                        p.block.hex()
                      ),
                      ConstantInfo::IPrj(p) => format!(
                        "IPrj(idx={}, block={:.12})",
                        p.idx,
                        p.block.hex()
                      ),
                      ConstantInfo::DPrj(p) => format!(
                        "DPrj(idx={}, block={:.12})",
                        p.idx,
                        p.block.hex()
                      ),
                      other => {
                        format!("{:?}", std::mem::discriminant(other))
                      },
                    });
                  eprintln!(
                    "[roundtrip ixon] {} proj mismatch: orig={:.12} [{:?}] recomp={:.12} [idx={}, block={:.12}]",
                    n.pretty(),
                    orig_addr.hex(),
                    orig_detail,
                    proj_addr.hex(),
                    class_idx,
                    block_addr.hex(),
                  );
                }
              }
            }
            results.insert(n, ci);
          }
        },
        Err(e) => {
          eprintln!("[roundtrip] decompile failed for {}: {e}", name.pretty());
          return Err(e);
        },
      }
    }
  }

  Ok(results)
}

/// Print a diagnostic comparison of a regenerated recursor vs the original Lean
/// constant. Only prints if there is any difference; omits matching fields.
/// Compare a generated recursor against the original Lean recursor.
///
/// `orig_env` is the immutable original Lean environment from the compiler.
/// When `None` (production/no-debug path), this is a no-op.
fn print_rec_comparison(
  rec_name: &Name,
  gen_rv: &RecursorVal,
  orig_env: Option<&LeanEnv>,
) {
  let Some(orig_env) = orig_env else { return };
  let Some(LeanConstantInfo::RecInfo(lean_rv)) = orig_env.get(rec_name) else {
    return;
  };

  let type_hash_match =
    gen_rv.cnst.typ.get_hash() == lean_rv.cnst.typ.get_hash();
  let motives_match = gen_rv.num_motives == lean_rv.num_motives;
  let minors_match = gen_rv.num_minors == lean_rv.num_minors;
  let rules_len_match = gen_rv.rules.len() == lean_rv.rules.len();
  let k_match = gen_rv.k == lean_rv.k;
  let params_match = gen_rv.num_params == lean_rv.num_params;
  let indices_match = gen_rv.num_indices == lean_rv.num_indices;
  let lvls_match = gen_rv.cnst.level_params == lean_rv.cnst.level_params;

  // Per-rule comparison.
  let mut rule_diffs: Vec<String> = Vec::new();
  for (i, (gr, lr)) in gen_rv.rules.iter().zip(lean_rv.rules.iter()).enumerate()
  {
    let rhs_match = gr.rhs.get_hash() == lr.rhs.get_hash();
    let ctor_match = gr.ctor == lr.ctor;
    let fields_match = gr.n_fields == lr.n_fields;
    if !(rhs_match && ctor_match && fields_match) {
      rule_diffs.push(format!(
        "  rule[{}] ctor gen={} lean={} fields gen={} lean={} rhs {}",
        i,
        gr.ctor.pretty(),
        lr.ctor.pretty(),
        gr.n_fields,
        lr.n_fields,
        if rhs_match { "OK" } else { "DIFFER" }
      ));
      if !rhs_match {
        rule_diffs.push(format!("    gen rhs:  {}", gr.rhs.pretty()));
        rule_diffs.push(format!("    lean rhs: {}", lr.rhs.pretty()));
      }
    }
  }
  // Extra rules in gen or lean.
  for (i, gr) in gen_rv.rules.iter().enumerate().skip(lean_rv.rules.len()) {
    rule_diffs.push(format!(
      "  rule[{}] gen-only ctor={} fields={}",
      i,
      gr.ctor.pretty(),
      gr.n_fields
    ));
  }
  for (i, lr) in lean_rv.rules.iter().enumerate().skip(gen_rv.rules.len()) {
    rule_diffs.push(format!(
      "  rule[{}] lean-only ctor={} fields={}",
      i,
      lr.ctor.pretty(),
      lr.n_fields
    ));
  }

  let all_match = type_hash_match
    && motives_match
    && minors_match
    && rules_len_match
    && k_match
    && params_match
    && indices_match
    && lvls_match
    && rule_diffs.is_empty();

  if all_match {
    return;
  }

  eprintln!("[aux_gen diff] {}", rec_name.pretty());
  if !params_match {
    eprintln!(
      "  params: gen={} lean={}",
      gen_rv.num_params, lean_rv.num_params
    );
  }
  if !indices_match {
    eprintln!(
      "  indices: gen={} lean={}",
      gen_rv.num_indices, lean_rv.num_indices
    );
  }
  if !motives_match {
    eprintln!(
      "  motives: gen={} lean={}",
      gen_rv.num_motives, lean_rv.num_motives
    );
  }
  if !minors_match {
    eprintln!(
      "  minors: gen={} lean={}",
      gen_rv.num_minors, lean_rv.num_minors
    );
  }
  if !k_match {
    eprintln!("  k: gen={} lean={}", gen_rv.k, lean_rv.k);
  }
  if !lvls_match {
    let gen_lvls: Vec<String> =
      gen_rv.cnst.level_params.iter().map(|n| n.pretty()).collect();
    let lean_lvls: Vec<String> =
      lean_rv.cnst.level_params.iter().map(|n| n.pretty()).collect();
    eprintln!(
      "  lvls: gen=[{}] lean=[{}]",
      gen_lvls.join(", "),
      lean_lvls.join(", ")
    );
  }
  if !rules_len_match {
    eprintln!(
      "  rules count: gen={} lean={}",
      gen_rv.rules.len(),
      lean_rv.rules.len()
    );
  }
  if !type_hash_match {
    eprintln!("  type DIFFER:");
    eprintln!("    gen:  {}", gen_rv.cnst.typ.pretty());
    eprintln!("    lean: {}", lean_rv.cnst.typ.pretty());
  }
  for line in &rule_diffs {
    eprintln!("{line}");
  }
}

/// Regenerate aux_gen constants from parent inductives.
///
/// Instead of decompiling aux_gen constants (`.rec`, `.below`, `.brecOn`) from
/// their canonical (alpha-collapsed) Ixon — which has incompatible structure —
/// we regenerate them using the original mutual block structure. The parent
/// inductives' `all` field (from metadata) gives us the un-collapsed class list.
///
/// Phases (dependency-ordered):
///   1. `.rec` — from parent inductives
///   2. `.below` — from parent inductives
///   3. `.below.rec` — from regenerated `.below` inductives (Prop only)
///   4. `.brecOn.go` / `.brecOn` / `.brecOn.eq` — from `.below` + `.rec`
fn decompile_aux_gen_constants(
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  use crate::ix::compile::KernelCtx;
  use crate::ix::compile::aux_gen::{
    below::{BelowConstant, generate_below_constants},
    brecon::generate_brecon_constants,
    cases_on::generate_cases_on,
    expr_utils, populate_canon_kenv_with_below,
    recursor::generate_canonical_recursors_with_overlay,
  };

  // Two distinct environments:
  //
  // 1. `orig_env` — immutable reference to the original Lean environment
  //    inherited from the compiler. Used ONLY for diagnostic comparisons
  //    (verifying regenerated constants match Lean's originals). `None` in
  //    production (the no-debug/serialize-roundtrip path).
  //
  // 2. `work_env` — mutable working environment for generation lookups.
  //    Starts from dstt.env (constants decompiled in Pass 1) and grows
  //    incrementally as each phase generates new constants. Later phases
  //    see earlier phases' output (e.g., casesOn needs .rec, brecOn
  //    needs .below).
  let orig_env: Option<&LeanEnv> =
    stt.lean_env.as_ref().map(|arc| arc.as_ref());

  let mut work_env: LeanEnv = {
    let mut env = LeanEnv::default();
    for entry in dstt.env.iter() {
      env.insert(entry.key().clone(), entry.value().clone());
    }
    env
  };

  // Ephemeral kernel context for original-structure auxiliary regeneration.
  // Shared across all blocks so that accumulated constants (PUnit, PProd,
  // parent inductives, .below types) are visible to subsequent blocks.
  let kctx = KernelCtx::new();
  expr_utils::ensure_prelude_in_kenv_of(stt, &kctx);

  // Collect aux_gen constants grouped by mutual block.
  // Key: first name in the `all` field (canonical block identifier).
  // Value: (all_names, list of (AuxKind, constant_name)).
  let mut blocks: FxHashMap<Name, (Vec<Name>, Vec<(AuxKind, Name)>)> =
    FxHashMap::default();

  for entry in stt.env.named.iter() {
    let (name, named) = (entry.key(), entry.value());
    if named.original.is_none() {
      continue;
    }

    let Some((kind, root)) = classify_aux_gen(name) else {
      continue;
    };

    // Look up the root inductive's `all` field from the working env.
    let all_names = match work_env.get(&root) {
      Some(LeanConstantInfo::InductInfo(ind)) => ind.all.clone(),
      _ => continue,
    };

    if all_names.is_empty() {
      continue;
    }

    let block_key = all_names[0].clone();
    blocks
      .entry(block_key)
      .or_insert_with(|| (all_names, Vec::new()))
      .1
      .push((kind, name.clone()));
  }

  // Process each mutual block. Collect errors per-block so one failure
  // doesn't abort the entire decompilation — all errors are reported at the end.
  let mut aux_gen_errors: Vec<(Name, DecompileError)> = Vec::new();

  for (all_names, aux_members) in blocks.values() {
    // Map from name → raw generated LeanConstantInfo (before roundtrip).
    // Used for three-way diagnostic: generated vs decompiled vs original.
    let mut generated_consts: FxHashMap<Name, LeanConstantInfo> =
      FxHashMap::default();

    // Build un-collapsed classes: each inductive in its own singleton class.
    // This produces auxiliaries with the original Lean structure (N motives
    // for N inductives, not fewer from alpha-collapse).
    let classes: Vec<Vec<Name>> =
      all_names.iter().map(|n| vec![n.clone()]).collect();

    // Build env with all inductives + constructors from the working block.
    let _block_env = build_block_env(all_names, &work_env);

    // Ingress parent inductives into the ephemeral kenv so the TC can
    // resolve them during sort-level inference in recursor/brecOn generation.
    for ind_name in all_names {
      expr_utils::ensure_in_kenv_of(ind_name, &work_env, stt, &kctx);
    }

    // Determine what kinds of aux constants this block needs.
    let needs_rec = aux_members.iter().any(|(k, _)| *k == AuxKind::Rec);
    let needs_below = aux_members.iter().any(|(k, _)| *k == AuxKind::Below);
    let needs_below_rec =
      aux_members.iter().any(|(k, _)| *k == AuxKind::BelowRec);
    let needs_cases_on =
      aux_members.iter().any(|(k, _)| *k == AuxKind::CasesOn);
    let needs_brecon = aux_members.iter().any(|(k, _)| {
      matches!(k, AuxKind::BRecOn | AuxKind::BRecOnGo | AuxKind::BRecOnEq)
    });

    // Phase 1: Generate canonical recursors.
    let needs_rec_on = aux_members.iter().any(|(k, _)| *k == AuxKind::RecOn);
    let (canonical_recs, is_prop) = if needs_rec
      || needs_rec_on
      || needs_cases_on
      || needs_below
      || needs_below_rec
      || needs_brecon
    {
      // Use the full work_env (not block_env) so nested inductive detection
      // can look up external inductives like List. work_env contains
      // previously decompiled constants and earlier phases' output.
      match generate_canonical_recursors_with_overlay(
        &classes, &work_env, None, stt, &kctx,
      ) {
        Ok(result) => result,
        Err(e) => {
          aux_gen_errors.push((
            all_names[0].clone(),
            DecompileError::BadConstantFormat {
              msg: format!(
                "aux_gen rec failed for {}: {}",
                all_names[0].pretty(),
                e
              ),
            },
          ));
          continue;
        },
      }
    } else {
      (vec![], false)
    };

    // Record generated .rec constants for diagnostics.
    for (n, rv) in &canonical_recs {
      generated_consts.insert(n.clone(), LeanConstantInfo::RecInfo(rv.clone()));
    }

    // Insert .rec constants via roundtrip_block.
    if needs_rec {
      let rec_members: Vec<&Name> = aux_members
        .iter()
        .filter(|(k, _)| *k == AuxKind::Rec)
        .map(|(_, n)| n)
        .collect();
      // Include ALL generated recursors (not just seeded rec_members) so the
      // mutual context matches the original compilation. For nested inductives,
      // canonical_recs includes both Tree.rec AND Tree.rec_1; they must be
      // compiled together to produce the same MutCtx as compile_aux_block.
      let rec_mut_consts: Vec<LeanMutConst> = canonical_recs
        .iter()
        .map(|(_, rv)| LeanMutConst::Recr(rv.clone()))
        .collect();
      match roundtrip_block(
        &rec_mut_consts,
        &generated_consts,
        orig_env,
        stt,
        dstt,
      ) {
        Ok(roundtripped) => {
          for (n, ci) in &roundtripped {
            if let LeanConstantInfo::RecInfo(rv) = ci {
              print_rec_comparison(n, rv, orig_env);
            }
          }
          for (n, ci) in roundtripped {
            // Only insert constants that exist in the working env or are
            // seeded members. Nested auxiliaries like TreeB.rec_1 are only
            // generated under all[0] (TreeA.rec_1) in Lean.
            if rec_members.contains(&&n) || work_env.contains_key(&n) {
              dstt.env.insert(n, ci);
            }
          }
        },
        Err(e) => {
          eprintln!("[decompile] roundtrip_block .rec failed: {e}");
          // Fallback: insert regenerated constants directly.
          for (n, rv) in &canonical_recs {
            if rec_members.contains(&n) {
              dstt.env.insert(n.clone(), LeanConstantInfo::RecInfo(rv.clone()));
            }
          }
        },
      }
    }

    // Insert ALL generated constants into work_env so later phases can find
    // them. Each phase's output must be visible to subsequent phases:
    //   .rec → needed by casesOn, below, brecOn
    //   .casesOn → needed by brecOn.eq
    //   .below → needed by below.rec, brecOn
    //   .brecOn → needed by brecOn.eq
    for (n, rv) in &canonical_recs {
      work_env.insert(n.clone(), LeanConstantInfo::RecInfo(rv.clone()));
    }
    for (n, ci) in &generated_consts {
      work_env.entry(n.clone()).or_insert_with(|| ci.clone());
    }

    // Phase 1b: Generate .casesOn definitions.
    if needs_cases_on {
      let cases_on_members: Vec<&Name> = aux_members
        .iter()
        .filter(|(k, _)| *k == AuxKind::CasesOn)
        .map(|(_, n)| n)
        .collect();

      // Use the full work_env so each casesOn gets the correct recursor
      // for its specific inductive (including those generated in Phase 1).
      let work_env_arc = Arc::new(work_env.clone());
      for co_name in &cases_on_members {
        // Look up the recursor for this specific inductive.
        let ind_name = match co_name.as_data() {
          crate::ix::env::NameData::Str(parent, _, _) => parent.clone(),
          _ => continue,
        };
        let rec_name = Name::str(ind_name.clone(), "rec".to_string());
        let rec_val = match work_env.get(&rec_name) {
          Some(LeanConstantInfo::RecInfo(rv)) => rv,
          _ => continue,
        };
        if let Some(aux_def) =
          generate_cases_on(co_name, rec_val, &work_env_arc)
        {
          // Record for congruence check.
          let as_defn = LeanConstantInfo::DefnInfo(DefinitionVal {
            cnst: ConstantVal {
              name: aux_def.name.clone(),
              level_params: aux_def.level_params.clone(),
              typ: aux_def.typ.clone(),
            },
            value: aux_def.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![aux_def.name.clone()],
          });
          generated_consts.insert(aux_def.name.clone(), as_defn);

          // Roundtrip as singleton.
          let mc = LeanMutConst::Defn(Def {
            name: aux_def.name.clone(),
            level_params: aux_def.level_params.clone(),
            typ: aux_def.typ.clone(),
            kind: DefKind::Definition,
            value: aux_def.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
          });
          match roundtrip_block(&[mc], &generated_consts, orig_env, stt, dstt) {
            Ok(roundtripped) if !roundtripped.is_empty() => {
              for (n, ci) in roundtripped {
                dstt.env.insert(n, ci);
              }
            },
            Ok(_) | Err(_) => {
              // Fallback: insert generated constant directly.
              if let Some(ci) = generated_consts.get(&aux_def.name) {
                dstt.env.insert(aux_def.name.clone(), ci.clone());
              }
            },
          }
        }
      }
    }

    // Phase 1c: Generate .recOn definitions (arg-reordered .rec wrapper).
    if needs_rec_on {
      use crate::ix::compile::aux_gen::rec_on::generate_rec_on;

      let rec_on_members: Vec<&Name> = aux_members
        .iter()
        .filter(|(k, _)| *k == AuxKind::RecOn)
        .map(|(_, n)| n)
        .collect();

      for ro_name in &rec_on_members {
        let ind_name = match ro_name.as_data() {
          crate::ix::env::NameData::Str(parent, _, _) => parent.clone(),
          _ => continue,
        };
        let rec_name = Name::str(ind_name, "rec".to_string());
        let rec_val = match work_env.get(&rec_name) {
          Some(LeanConstantInfo::RecInfo(rv)) => rv,
          _ => continue,
        };
        if let Some(aux_def) = generate_rec_on(ro_name, rec_val) {
          let as_defn = LeanConstantInfo::DefnInfo(DefinitionVal {
            cnst: ConstantVal {
              name: aux_def.name.clone(),
              level_params: aux_def.level_params.clone(),
              typ: aux_def.typ.clone(),
            },
            value: aux_def.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![aux_def.name.clone()],
          });
          generated_consts.insert(aux_def.name.clone(), as_defn);

          let mc = LeanMutConst::Defn(Def {
            name: aux_def.name.clone(),
            level_params: aux_def.level_params.clone(),
            typ: aux_def.typ.clone(),
            kind: DefKind::Definition,
            value: aux_def.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
          });
          match roundtrip_block(&[mc], &generated_consts, orig_env, stt, dstt) {
            Ok(roundtripped) if !roundtripped.is_empty() => {
              for (n, ci) in roundtripped {
                dstt.env.insert(n, ci);
              }
            },
            Ok(_) | Err(_) => {
              if let Some(ci) = generated_consts.get(&aux_def.name) {
                dstt.env.insert(aux_def.name.clone(), ci.clone());
              }
            },
          }
        }
      }
    }

    // Phase 2: Generate .below constants.
    let below_consts = if needs_below || needs_below_rec || needs_brecon {
      match generate_below_constants(
        &classes,
        &canonical_recs,
        &work_env,
        is_prop,
        Some(stt),
      ) {
        Ok(consts) => consts,
        Err(e) => {
          aux_gen_errors.push((
            all_names[0].clone(),
            DecompileError::BadConstantFormat {
              msg: format!(
                "aux_gen below failed for {}: {}",
                all_names[0].pretty(),
                e
              ),
            },
          ));
          vec![]
        },
      }
    } else {
      vec![]
    };

    // Record generated .below constants for diagnostics.
    {
      let all_below_names: Vec<Name> = below_consts
        .iter()
        .map(|bc| match bc {
          BelowConstant::Indc(i) => i.name.clone(),
          BelowConstant::Def(d) => d.name.clone(),
        })
        .collect();
      for bc in &below_consts {
        match bc {
          BelowConstant::Def(d) => {
            generated_consts.insert(d.name.clone(), below_def_to_lean(d));
          },
          BelowConstant::Indc(i) => {
            let (ind_val, ctors) = below_indc_to_lean(i, &all_below_names);
            generated_consts
              .insert(i.name.clone(), LeanConstantInfo::InductInfo(ind_val));
            for ctor in ctors {
              generated_consts.insert(
                ctor.cnst.name.clone(),
                LeanConstantInfo::CtorInfo(ctor),
              );
            }
          },
        }
      }
    }

    // Sync generated constants into work_env for subsequent phases.
    for (n, ci) in &generated_consts {
      work_env.entry(n.clone()).or_insert_with(|| ci.clone());
    }

    // Insert .below constants via roundtrip_block.
    if needs_below {
      let below_members: Vec<&Name> = aux_members
        .iter()
        .filter(|(k, _)| *k == AuxKind::Below)
        .map(|(_, n)| n)
        .collect();

      let all_below_names: Vec<Name> = below_consts
        .iter()
        .map(|bc| match bc {
          BelowConstant::Indc(i) => i.name.clone(),
          BelowConstant::Def(d) => d.name.clone(),
        })
        .collect();

      // Split roundtrip by constant type:
      // - BelowIndc (Prop-level): mutual inductive block, roundtrip together
      // - BelowDef (Type-level): Lean generates as standalone singletons, roundtrip individually

      // BelowIndc: bundle ALL generated below inductives into one
      // roundtrip_block (mutual block). Include nested auxiliaries (e.g.,
      // below_1) so the mutual context matches the original compilation.
      let below_indc_consts: Vec<LeanMutConst> = below_consts
        .iter()
        .filter_map(|bc| match bc {
          BelowConstant::Indc(i) => {
            let (ind_val, ctors) = below_indc_to_lean(i, &all_below_names);
            Some(LeanMutConst::Indc(Ind { ind: ind_val, ctors }))
          },
          _ => None,
        })
        .collect();

      if !below_indc_consts.is_empty() {
        match roundtrip_block(
          &below_indc_consts,
          &generated_consts,
          orig_env,
          stt,
          dstt,
        ) {
          Ok(roundtripped) => {
            for (n, ci) in roundtripped {
              dstt.env.insert(n, ci);
            }
          },
          Err(e) => {
            for bc in &below_consts {
              if let BelowConstant::Indc(i) = bc
                && below_members.contains(&&i.name)
              {
                aux_gen_errors.push((i.name.clone(), e.clone()));
              }
            }
          },
        }
      }

      // BelowDef: roundtrip through compile(regen, orig_metadata) → decompile.
      // Batch ALL BelowDefs together so sort_consts can detect alpha-equivalence
      // and collapse them, matching compile_aux_block's behavior.
      let below_def_consts: Vec<LeanMutConst> = below_consts
        .iter()
        .filter_map(|bc| match bc {
          BelowConstant::Def(d) => Some(LeanMutConst::Defn(Def {
            name: d.name.clone(),
            level_params: d.level_params.clone(),
            typ: d.typ.clone(),
            kind: DefKind::Definition,
            value: d.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
          })),
          _ => None,
        })
        .collect();

      if !below_def_consts.is_empty() {
        match roundtrip_block(
          &below_def_consts,
          &generated_consts,
          orig_env,
          stt,
          dstt,
        ) {
          Ok(roundtripped) => {
            for (n, ci) in roundtripped {
              dstt.env.insert(n, ci);
            }
          },
          Err(e) => {
            for mc in &below_def_consts {
              aux_gen_errors.push((mc.name(), e.clone()));
            }
          },
        }
      }
    }

    // Phase 3: Generate .below.rec (Prop-level .below inductives only).
    if needs_below_rec && is_prop {
      let mut below_env = build_block_env(all_names, &work_env);
      let mut below_classes: Vec<Vec<Name>> = Vec::new();

      let all_below_names: Vec<Name> = below_consts
        .iter()
        .filter_map(|bc| match bc {
          BelowConstant::Indc(i) => Some(i.name.clone()),
          _ => None,
        })
        .collect();

      for bc in &below_consts {
        if let BelowConstant::Indc(i) = bc {
          let (ind_val, ctors) = below_indc_to_lean(i, &all_below_names);
          below_env
            .insert(i.name.clone(), LeanConstantInfo::InductInfo(ind_val));
          for ctor in &ctors {
            below_env.insert(
              ctor.cnst.name.clone(),
              LeanConstantInfo::CtorInfo(ctor.clone()),
            );
          }
          below_classes.push(vec![i.name.clone()]);
        }
      }

      if !below_classes.is_empty() {
        match generate_canonical_recursors_with_overlay(
          &below_classes,
          &below_env,
          None,
          stt,
          &kctx,
        ) {
          Ok((below_recs, _)) => {
            let below_rec_members: Vec<&Name> = aux_members
              .iter()
              .filter(|(k, _)| *k == AuxKind::BelowRec)
              .map(|(_, n)| n)
              .collect();
            let below_rec_mut_consts: Vec<LeanMutConst> = below_recs
              .iter()
              .filter(|(n, _)| below_rec_members.contains(&n))
              .map(|(_, rv)| LeanMutConst::Recr(rv.clone()))
              .collect();
            match roundtrip_block(
              &below_rec_mut_consts,
              &generated_consts,
              orig_env,
              stt,
              dstt,
            ) {
              Ok(roundtripped) => {
                for (n, ci) in roundtripped {
                  dstt.env.insert(n, ci);
                }
              },
              Err(_) => {
                for (n, rv) in &below_recs {
                  if below_rec_members.contains(&n) {
                    dstt
                      .env
                      .insert(n.clone(), LeanConstantInfo::RecInfo(rv.clone()));
                  }
                }
              },
            }
          },
          Err(e) => {
            aux_gen_errors.push((
              all_names[0].clone(),
              DecompileError::BadConstantFormat {
                msg: format!(
                  "aux_gen below.rec failed for {}: {}",
                  all_names[0].pretty(),
                  e
                ),
              },
            ));
          },
        }
      }
    }

    // Sync generated constants (below, below.rec) into work_env for brecOn.
    for (n, ci) in &generated_consts {
      work_env.entry(n.clone()).or_insert_with(|| ci.clone());
    }

    // Populate the ephemeral kenv with .below types so brecOn's TcScope
    // can infer PProd(motive, I.below ...) during sort level inference.
    if !below_consts.is_empty() {
      let work_env_arc = std::sync::Arc::new(work_env.clone());
      populate_canon_kenv_with_below(
        &below_consts,
        &classes,
        &work_env_arc,
        stt,
        &kctx,
      );
    }

    // Phase 4: Generate .brecOn / .brecOn.go / .brecOn.eq.
    if needs_brecon {
      match generate_brecon_constants(
        &classes,
        &canonical_recs,
        &below_consts,
        &work_env,
        is_prop,
        stt,
        &kctx,
      ) {
        Ok(brecon_defs) => {
          // Record generated brecOn constants for congruence check.
          // .brecOn.eq is ALWAYS a theorem (proof of equality).
          // .brecOn and .brecOn.go are theorems for Prop, definitions for Type.
          for d in &brecon_defs {
            let is_eq =
              matches!(classify_aux_gen(&d.name), Some((AuxKind::BRecOnEq, _)));
            let as_thm = is_prop || is_eq;
            generated_consts
              .insert(d.name.clone(), brecon_def_to_lean(d, as_thm));
          }

          let brecon_members: Vec<&Name> = aux_members
            .iter()
            .filter(|(k, _)| {
              matches!(
                k,
                AuxKind::BRecOn | AuxKind::BRecOnGo | AuxKind::BRecOnEq
              )
            })
            .map(|(_, n)| n)
            .collect();

          // Roundtrip each brecOn INDIVIDUALLY as a singleton.
          // The original compilation (`compile_const_no_aux`) compiles each
          // brecOn as a singleton definition. If we batch alpha-equivalent
          // brecOn constants together, `sort_consts` collapses them into
          // fewer classes, producing a different block structure than the
          // singleton original. Individual roundtrip ensures the arena
          // structure matches the original metadata.
          // Only roundtrip constants that were seeded (present in compiled env).
          for d in
            brecon_defs.iter().filter(|d| brecon_members.contains(&&d.name))
          {
            let is_eq =
              matches!(classify_aux_gen(&d.name), Some((AuxKind::BRecOnEq, _)));
            let kind = if is_prop || is_eq {
              DefKind::Theorem
            } else {
              DefKind::Definition
            };
            let mc = LeanMutConst::Defn(Def {
              name: d.name.clone(),
              level_params: d.level_params.clone(),
              typ: d.typ.clone(),
              kind,
              value: d.value.clone(),
              hints: ReducibilityHints::Abbrev,
              safety: DefinitionSafety::Safe,
              all: vec![],
            });
            match roundtrip_block(&[mc], &generated_consts, orig_env, stt, dstt)
            {
              Ok(roundtripped) if !roundtripped.is_empty() => {
                for (n, ci) in roundtripped {
                  dstt.env.insert(n, ci);
                }
              },
              Ok(_) | Err(_) => {
                // Fallback: insert the generated constant directly.
                let is_eq_fb = matches!(
                  classify_aux_gen(&d.name),
                  Some((AuxKind::BRecOnEq, _))
                );
                dstt.env.insert(
                  d.name.clone(),
                  brecon_def_to_lean(d, is_prop || is_eq_fb),
                );
              },
            }
          }
        },
        Err(e) => {
          aux_gen_errors.push((
            all_names[0].clone(),
            DecompileError::BadConstantFormat {
              msg: format!(
                "aux_gen brecOn failed for {}: {}",
                all_names[0].pretty(),
                e
              ),
            },
          ));
        },
      }
    }

    // Congruence check: verify generated constants are alpha-equivalent to originals.
    // Only possible when the original environment is available (debug path).
    if let Some(orig) = orig_env {
      for (name, generated_ci) in &generated_consts {
        if let Some(orig_ci) = orig.get(name)
          && let Err(e) =
            crate::ix::congruence::const_alpha_eq(generated_ci, orig_ci)
        {
          aux_gen_errors.push((
            name.clone(),
            DecompileError::BadConstantFormat {
              msg: format!("congruence: {e}"),
            },
          ));
        }
      }
    }
  }

  // Report all collected errors (but don't abort — caller gets the partial decompile).
  if !aux_gen_errors.is_empty() {
    eprintln!(
      "[decompile] aux_gen roundtrip errors ({}):",
      aux_gen_errors.len(),
    );
    for (name, e) in &aux_gen_errors {
      eprintln!("  {}: {e}", name.pretty());
    }
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

  // Constructor metadata is now embedded directly in ConstantMetaInfo::Indc,
  // so no pre-indexing is needed.

  // Pass 1: Decompile non-aux_gen constants (parallel).
  // Constants with `named.original.is_some()` are aux_gen-rewritten. We only
  // skip those with a recognized aux_gen suffix (.rec, .below, .brecOn, etc.)
  // — they'll be regenerated in pass 2. Parent inductives/constructors with
  // `original` are still decompiled here (they have correct `all` in metadata).
  stt.env.named.par_iter().try_for_each(|entry| {
    let (name, named) = (entry.key(), entry.value());

    if named.original.is_some() && is_aux_gen_suffix(name) {
      return Ok(());
    }

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

  // Pass 2: Regenerate aux_gen constants from parent inductives.
  // TODO: parallelize — blocks are independent (each only needs its own
  // inductives + external deps from the complete dstt.env). Only the
  // phases within a block (.rec → .below → .brecOn) are sequential.
  decompile_aux_gen_constants(stt, &dstt)?;

  Ok(dstt)
}

/// Result of checking a decompiled environment against the original.
#[derive(Debug)]
pub struct CheckResult {
  pub matches: usize,
  pub mismatches: usize,
  /// Constants in decompiled but not in original.
  pub missing: usize,
  /// Names of constants in decompiled but not in original.
  pub extra_names: Vec<String>,
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
          if name.pretty().contains("brecOn_1.eq") {
            eprintln!(
              "check_decompile: {} type_hash orig={:?} dec={:?} | val_hash orig={:?} dec={:?} | kind orig={} dec={}",
              name.pretty(),
              orig_info.get_type().get_hash(),
              info.get_type().get_hash(),
              orig_info.get_value().map(|v| *v.get_hash()),
              info.get_value().map(|v| *v.get_hash()),
              ci_kind(orig_info),
              ci_kind(info),
            );
          }
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

  // Report constants in original but missing from decompiled.
  {
    let mut missing_names: Vec<String> = original
      .iter()
      .filter(|(name, _)| !dstt.env.contains_key(name))
      .map(|(name, _)| name.pretty())
      .collect();
    missing_names.sort();
    if !missing_names.is_empty() {
      eprintln!(
        "check_decompile: {} constants missing from decompiled:",
        missing_names.len()
      );
      for name in &missing_names {
        eprintln!("  missing: {name}");
      }
    }
  }

  // Report constants in decompiled but not in original.
  let mut extra_names: Vec<String> = dstt
    .env
    .iter()
    .filter(|entry| !original.contains_key(entry.key()))
    .map(|entry| entry.key().pretty())
    .collect();
  extra_names.sort();
  if !extra_names.is_empty() {
    eprintln!(
      "check_decompile: {} constants in decompiled but not in original:",
      extra_names.len()
    );
    for name in &extra_names {
      eprintln!("  extra: {name}");
    }
  }

  let result = CheckResult {
    matches: matches.load(Ordering::Relaxed),
    mismatches: mismatches.load(Ordering::Relaxed),
    missing: missing.load(Ordering::Relaxed),
    extra_names,
  };
  eprintln!(
    "check_decompile: {} matches, {} mismatches, {} not in original",
    result.matches, result.mismatches, result.missing
  );

  Ok(result)
}
