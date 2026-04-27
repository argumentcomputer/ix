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
      CallSiteEntry, ConstantMeta, ConstantMetaInfo, DataValue, ExprMeta,
      ExprMetaData, KVMap,
    },
    univ::Univ,
  },
  ix::mutual::{Def, Ind, MutConst as LeanMutConst, MutCtx, all_to_ctx},
};
use dashmap::DashMap;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
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
///
/// Index-space invariants (see `load_meta_extensions` for details):
/// - `sharing` holds the block `Constant.sharing` table and is the target
///   of `Expr::Share(idx)` lookups produced by whole-block sharing
///   analysis (`apply_sharing_to_*`). These indices start at 0 and are
///   block-wide.
/// - `meta_sharing` holds the per-constant `ConstantMeta.meta_sharing`
///   table — collapsed call-site argument expressions — and is the
///   target of `CallSiteEntry::Collapsed.sharing_idx` lookups. These
///   indices also start at 0 but live in a SEPARATE namespace from the
///   block sharing: compile writes them as `surgery_sharing.len() +
///   collapsed_idx` where `surgery_sharing` is reset per constant (see
///   `src/ix/compile.rs::compile_expr` BuildCallSite path).
///
/// Treating them as the same vector would make a `sharing_idx` in `[0,
/// block_sharing.len())` silently return the wrong block subtree
/// (typically a lambda/forall rather than the intended Ref/App
/// motive/minor), producing the "Binder arena vs Expr::Ref Ixon"
/// mismatch on any mutual block with shared bodies AND surgered
/// call-sites (every `_sizeOf_N` in a reordered/collapsed mutual
/// inductive).
#[derive(Default, Debug)]
pub struct BlockCache {
  /// Mutual context for resolving Rec references
  pub ctx: MutCtx,
  /// Block-level sharing table: target of `Expr::Share(idx)` in
  /// post-`apply_sharing` body exprs. Initialized from
  /// `Constant.sharing`.
  pub sharing: Vec<Arc<Expr>>,
  /// Per-constant surgery sharing table: target of
  /// `CallSiteEntry::Collapsed.sharing_idx` lookups inside `CallSite`
  /// metadata arena nodes. Populated by `load_meta_extensions` from
  /// `ConstantMeta.meta_sharing`. Empty for constants without surgery
  /// (non-aux_gen singleton defs and all `roundtrip_block` callers).
  pub meta_sharing: Vec<Arc<Expr>>,
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

impl BlockCache {
  /// Install per-constant metadata extension tables.
  ///
  /// - `meta_sharing` → dedicated `self.meta_sharing` (separate from the
  ///   block sharing, see struct docs). Overwrites any previous
  ///   per-constant table so the cache can be reused across constants
  ///   within a projection-bearing block.
  /// - `meta_refs` / `meta_univs` — these are never populated by the
  ///   current compiler (grep: only pushed by serde paths in
  ///   `src/ix/ixon/metadata.rs`), but extend the primary tables when
  ///   present so we match the documented virtual-address contract for
  ///   any future compiler that starts emitting them.
  pub fn load_meta_extensions(&mut self, meta: &ConstantMeta) {
    self.meta_sharing = meta.meta_sharing.clone();
    self.refs.extend(meta.meta_refs.iter().cloned());
    self.univ_table.extend(meta.meta_univs.iter().cloned());
  }
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

/// Pop a result from the decompilation stack, returning a structured error
/// instead of panicking if the stack is empty (malformed Ixon data).
fn pop_result(
  results: &mut Vec<LeanExpr>,
  msg: &str,
  constant: &str,
) -> Result<LeanExpr, DecompileError> {
  results.pop().ok_or_else(|| DecompileError::BadConstantFormat {
    msg: format!("{msg} in '{constant}'"),
  })
}

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

  /// Default node for "no metadata" sentinel. Semantically equivalent
  /// to a Leaf — no names, no binder info, no metadata to reattach.
  const DEFAULT_NODE: ExprMetaData = ExprMetaData::Leaf;

  /// Look up an arena node by index.
  ///
  /// `u64::MAX` is the legitimate "no metadata" sentinel used by
  /// fallback paths when the caller has no metadata to attach (see
  /// e.g. the `(_, Expr::App(..))` arm below that has no matching
  /// `ExprMetaData::App`). In that case we return a `Leaf`.
  ///
  /// Any other out-of-bounds index indicates arena corruption — either
  /// a malformed `ExprMeta` produced during compile, or an
  /// `ExprMetaData` child pointer that overshoots the arena. We reject
  /// these loudly rather than silently degrading to `Leaf`, which would
  /// strip metadata from the subtree.
  fn arena_lookup<'a>(
    arena: &'a ExprMeta,
    idx: u64,
    constant: &str,
  ) -> Result<&'a ExprMetaData, DecompileError> {
    if idx == u64::MAX {
      return Ok(&DEFAULT_NODE);
    }
    arena.nodes.get(idx as usize).ok_or_else(|| {
      DecompileError::BadConstantFormat {
        msg: format!(
          "arena index {idx} out of bounds (arena has {} nodes) in '{constant}'",
          arena.nodes.len(),
        ),
      }
    })
  }

  fn collect_ixon_telescope_expanding_shares(
    expr: &Arc<Expr>,
    cache: &BlockCache,
  ) -> Result<(Arc<Expr>, Vec<Arc<Expr>>), DecompileError> {
    let mut args: Vec<Arc<Expr>> = Vec::new();
    let mut cur = expr.clone();
    loop {
      while let Expr::Share(share_idx) = cur.as_ref() {
        cur = cache
          .sharing
          .get(*share_idx as usize)
          .ok_or_else(|| DecompileError::InvalidShareIndex {
            idx: *share_idx,
            max: cache.sharing.len(),
            constant: cache.current_const.clone(),
          })?
          .clone();
      }
      match cur.as_ref() {
        Expr::App(f, a) => {
          args.push(a.clone());
          cur = f.clone();
        },
        _ => break,
      }
    }
    args.reverse();
    Ok((cur, args))
  }

  enum Frame {
    Decompile(Arc<Expr>, u64),
    BuildApp(LeanMdata),
    BuildLam(Name, BinderInfo, LeanMdata),
    BuildAll(Name, BinderInfo, LeanMdata),
    BuildLet(Name, bool, LeanMdata),
    BuildProj(Name, Nat, LeanMdata),
    CacheResult(*const Expr, u64),
    /// Assemble a source-order App spine from head + N decompiled args.
    BuildTelescope {
      n_args: usize,
      mdata: LeanMdata,
    },
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
          arena_lookup(arena, current_idx, &cache.current_const)?
        {
          for kvm in mdata {
            mdata_layers.push(decompile_kvmap(kvm, stt)?);
          }
          current_idx = *child;
        }

        let node = arena_lookup(arena, current_idx, &cache.current_const)?;

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
            // Fallback to cache.ctx is a legitimate recovery path when
            // the global name index does not yet know this address —
            // typically mid-block compilation where the rec's own name
            // isn't registered globally but IS in the local mutual
            // context. If neither source yields a name, we return an
            // explicit `InvalidRecIndex` error rather than falling back
            // to `Name::anon()` (which would round-trip to an unknown
            // constant reference and fail much later in kernel
            // type-check with a hard-to-attribute error).
            let name = match decompile_name(name_addr, stt) {
              Ok(n) => n,
              Err(_) => {
                #[cfg(debug_assertions)]
                eprintln!(
                  "[decompile] Rec name address {:?} not in global index; \
                   falling back to cache.ctx (rec_idx={}, constant={})",
                  name_addr, rec_idx, cache.current_const
                );
                cache
                  .ctx
                  .iter()
                  .find(|(_, i)| i.to_u64() == Some(*rec_idx))
                  .map(|(n, _)| n.clone())
                  .ok_or_else(|| DecompileError::InvalidRecIndex {
                    idx: *rec_idx,
                    ctx_size: cache.ctx.len(),
                    constant: cache.current_const.clone(),
                  })?
              },
            };
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

          // CallSite: surgered call-site — reconstruct source-order telescope
          (ExprMetaData::CallSite { name, entries, canon_meta: _ }, _) => {
            // Collect the canonical Ixon App telescope
            let (head_ixon, canonical_args) =
              collect_ixon_telescope_expanding_shares(&e, cache)?;

            // Most CallSites have one Kept entry per canonical arg. Split-SCC
            // minor adaptation is the exception: the canonical arg is a
            // synthesized wrapper, while the source-order argument is stored
            // as Collapsed metadata for roundtrip. In that case canonical
            // args may outnumber Kept entries, but every Kept entry still
            // must point at an existing canonical slot.
            let kept_count = entries
              .iter()
              .filter(|e| matches!(e, CallSiteEntry::Kept { .. }))
              .count();
            if kept_count > canonical_args.len() {
              return Err(DecompileError::BadConstantFormat {
                msg: format!(
                  "CallSite in '{}': {} Kept entries but canonical telescope has only {} args",
                  cache.current_const,
                  kept_count,
                  canonical_args.len()
                ),
              });
            }

            // Decompile head: resolve name from CallSite. This must succeed —
            // a CallSite metadata node without a resolvable head indicates
            // compiler/decompiler corruption, not malformed user input.
            let head_name = decompile_name(name, stt).map_err(|_| {
              DecompileError::BadConstantFormat {
                msg: format!(
                  "CallSite in '{}': head name address does not resolve",
                  cache.current_const
                ),
              }
            })?;
            // Extract univ args from head
            let levels = match head_ixon.as_ref() {
              Expr::Ref(_, univ_indices) | Expr::Rec(_, univ_indices) => {
                decompile_univ_indices(univ_indices, lvl_names, cache)?
              },
              _ => vec![],
            };
            // Push the bare head (Mdata is applied by BuildTelescope to
            // the entire spine, not just the head — wrapping here would
            // produce `App(App(mdata(head), a), b)` instead of the
            // correct `mdata(App(App(head, a), b))` and break roundtrip
            // hash equality).
            results.push(LeanExpr::cnst(head_name, levels));

            // Push BuildTelescope to assemble source-order App spine.
            // `mdata_layers` travels with the telescope so the final
            // spine is wrapped as a whole — matches how the compiler
            // produced this CallSite node.
            //
            // NOTE: the outer `Frame::CacheResult(Arc::as_ptr(&e), idx)`
            // was already pushed at the top of `Frame::Decompile` (see
            // ~30 lines above). Do NOT push another here — a duplicate
            // would fire against a partial result (the last arg, since
            // BuildTelescope hasn't built the spine yet) before being
            // overwritten by the outer CacheResult. Last-write-wins
            // hides the issue today, but intermediate cache reads would
            // return the wrong value.
            stack.push(Frame::BuildTelescope {
              n_args: entries.len(),
              mdata: mdata_layers,
            });

            // Push Decompile for each entry in REVERSE source order.
            // Every entry must resolve to an Ixon expression: Kept indices
            // into the canonical telescope, Collapsed into the sharing
            // vector. Silent skips would desync `BuildTelescope`.
            for entry in entries.iter().rev() {
              match entry {
                CallSiteEntry::Kept { canon_idx, meta } => {
                  let arg_ixon = canonical_args
                    .get(*canon_idx as usize)
                    .ok_or_else(|| DecompileError::BadConstantFormat {
                      msg: format!(
                        "CallSite in '{}': Kept canon_idx {} out of bounds \
                         (canonical telescope has {} args)",
                        cache.current_const,
                        canon_idx,
                        canonical_args.len()
                      ),
                    })?;
                  stack.push(Frame::Decompile(arg_ixon.clone(), *meta));
                },
                CallSiteEntry::Collapsed { sharing_idx, meta } => {
                  // `sharing_idx` addresses `ConstantMeta.meta_sharing`
                  // (per-constant, 0-based), NOT the block's primary
                  // sharing table — see `BlockCache` docs. Reading it
                  // from `cache.sharing` silently returned the wrong
                  // subtree whenever the block had any `apply_sharing`
                  // output, producing the "Binder arena vs Expr::Ref"
                  // mismatch on surgered `_sizeOf_N` constants.
                  let arg_ixon = cache
                    .meta_sharing
                    .get(*sharing_idx as usize)
                    .ok_or_else(|| DecompileError::InvalidShareIndex {
                      idx: *sharing_idx,
                      max: cache.meta_sharing.len(),
                      constant: cache.current_const.clone(),
                    })?
                    .clone();
                  stack.push(Frame::Decompile(arg_ixon, *meta));
                },
              }
            }
            // The outer `Frame::CacheResult` pushed at the top of
            // `Frame::Decompile` will fire after BuildTelescope finishes,
            // caching the fully-assembled spine.
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
            // Binder name address must resolve. The compiler registers
            // every binder name it emits; a missing entry here means
            // the name index was built inconsistently with the arena.
            // Silently defaulting to anon would lose user-level names
            // cosmetically and mask the real corruption.
            let binder_name = decompile_name(name_addr, stt)?;
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
            // See Lam arm above: binder address must resolve.
            let binder_name = decompile_name(name_addr, stt)?;
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
            // See Lam arm above: binder address must resolve.
            let let_name = decompile_name(name_addr, stt)?;
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
        let a = pop_result(
          &mut results,
          "BuildApp missing arg",
          &cache.current_const,
        )?;
        let f = pop_result(
          &mut results,
          "BuildApp missing fun",
          &cache.current_const,
        )?;
        results.push(apply_mdata(LeanExpr::app(f, a), mdata));
      },

      Frame::BuildLam(name, info, mdata) => {
        let body = pop_result(
          &mut results,
          "BuildLam missing body",
          &cache.current_const,
        )?;
        let ty = pop_result(
          &mut results,
          "BuildLam missing ty",
          &cache.current_const,
        )?;
        results.push(apply_mdata(LeanExpr::lam(name, ty, body, info), mdata));
      },

      Frame::BuildAll(name, info, mdata) => {
        let body = pop_result(
          &mut results,
          "BuildAll missing body",
          &cache.current_const,
        )?;
        let ty = pop_result(
          &mut results,
          "BuildAll missing ty",
          &cache.current_const,
        )?;
        results.push(apply_mdata(LeanExpr::all(name, ty, body, info), mdata));
      },

      Frame::BuildLet(name, non_dep, mdata) => {
        let body = pop_result(
          &mut results,
          "BuildLet missing body",
          &cache.current_const,
        )?;
        let val = pop_result(
          &mut results,
          "BuildLet missing val",
          &cache.current_const,
        )?;
        let ty = pop_result(
          &mut results,
          "BuildLet missing ty",
          &cache.current_const,
        )?;
        results.push(apply_mdata(
          LeanExpr::letE(name, ty, val, body, non_dep),
          mdata,
        ));
      },

      Frame::BuildProj(name, idx, mdata) => {
        let s = pop_result(
          &mut results,
          "BuildProj missing struct",
          &cache.current_const,
        )?;
        results.push(apply_mdata(LeanExpr::proj(name, idx, s), mdata));
      },

      Frame::BuildTelescope { n_args, mdata } => {
        // Pop n_args results. They were pushed to the stack in reverse
        // source order (`entries.iter().rev()`), so Decompile frames fire
        // in source order and their results land on `results` in source
        // order. Popping here reverses that order (LIFO) — i.e.
        // `args[0]` comes from the last-pushed result = last
        // source-order arg. Reverse the pop order before folding so the
        // resulting App spine is `App(… App(head, arg[0]), arg[N-1])`.
        // Without the reverse, the spine was built in reverse order,
        // which kept the constant's hash stable *only* by accident when
        // all args were symmetric — any surgered `_sizeOf_N` etc. with
        // asymmetric args hashed differently than the Lean original,
        // causing the Phase 7 / 7b roundtrip failures.
        let mut args = Vec::with_capacity(n_args);
        for _ in 0..n_args {
          args.push(pop_result(
            &mut results,
            "BuildTelescope missing arg",
            &cache.current_const,
          )?);
        }
        args.reverse();
        // Pop head (pushed before the args)
        let head = pop_result(
          &mut results,
          "BuildTelescope missing head",
          &cache.current_const,
        )?;
        // Build App spine: foldl
        let mut expr = head;
        for arg in args {
          expr = LeanExpr::app(expr, arg);
        }
        results.push(apply_mdata(expr, mdata));
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
    } => {
      // Rec metadata must have one rule_root per recursor rule.
      // A mismatch means the arena was produced inconsistently with
      // the recursor value; subsequent rule RHS decompilation would
      // silently use a Leaf default (losing rule-level metadata) if
      // we didn't validate here.
      if rule_roots.len() != rec.rules.len() {
        return Err(DecompileError::BadConstantFormat {
          msg: format!(
            "recursor metadata for '{}': rule_roots has {} entries but \
             recursor has {} rules",
            name.pretty(),
            rule_roots.len(),
            rec.rules.len(),
          ),
        });
      }
      (
        arena,
        *type_root,
        rule_roots.as_slice(),
        rules.as_slice(),
        all.as_slice(),
      )
    },
    _ => {
      // No Rec metadata: graceful degradation. Arena is empty and
      // rule_roots is empty, so rule RHS decompilation proceeds with
      // the u64::MAX sentinel via `rule_roots.get(i).unwrap_or(&...)`
      // below falling through to Leaf. Only allowed when the recursor
      // has no rules; otherwise data loss would be silent.
      if !rec.rules.is_empty() {
        return Err(DecompileError::BadConstantFormat {
          msg: format!(
            "recursor has {} rules but no Rec metadata was supplied",
            rec.rules.len()
          ),
        });
      }
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
  // Propagate resolution failures rather than silently degrading to
  // `vec![name.clone()]`. If a name in `.all` can't be resolved, the
  // recursor's mutual-block structure is incorrect — masking that with
  // a singleton fallback produces a plausible-looking but wrong
  // recursor that may pass later checks by coincidence.
  let all = all_addrs
    .iter()
    .map(|a| decompile_name(a, stt))
    .collect::<Result<Vec<_>, _>>()?;

  let mut rules = Vec::with_capacity(rec.rules.len());
  for (i, (rule, ctor_name)) in
    rec.rules.iter().zip(rule_names.iter()).enumerate()
  {
    // Safe: lengths validated against rec.rules above. If rule_roots
    // is empty, rec.rules is also empty and this loop doesn't run.
    let rhs_root = rule_roots[i];
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

  // Extract constructor name addresses and all from metadata. The
  // non-Indc arm should be unreachable — `decompile_inductive` is only
  // called when the meta is an Indc variant. If we ever get here with
  // a different variant shape, that's structural corruption, not a
  // silently recoverable condition.
  let (ctor_name_addrs, all) = match &meta.info {
    ConstantMetaInfo::Indc { ctors, all: all_addrs, .. } => {
      let all = all_addrs
        .iter()
        .map(|a| decompile_name(a, stt))
        .collect::<Result<Vec<_>, _>>()?;
      (ctors.as_slice(), all)
    },
    other => {
      return Err(DecompileError::BadConstantFormat {
        msg: format!(
          "decompile_inductive for '{}': expected ConstantMetaInfo::Indc, \
           got variant with discriminant {:?}",
          name.pretty(),
          std::mem::discriminant(other),
        ),
      });
    },
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

    // Constructor metadata is per-constructor, not inherited from the parent
    // inductive. In particular, aux-generated `.below` constructors can carry
    // CallSite metadata whose Collapsed entries point into the constructor's
    // own `meta_sharing` table. Install those extensions only while walking
    // this constructor so they do not leak across sibling constructor arenas.
    let saved_meta_sharing = std::mem::replace(
      &mut cache.meta_sharing,
      ctor_meta.meta_sharing.clone(),
    );
    let refs_len = cache.refs.len();
    let univs_len = cache.univ_table.len();
    cache.refs.extend(ctor_meta.meta_refs.iter().cloned());
    cache.univ_table.extend(ctor_meta.meta_univs.iter().cloned());

    let ctor_result =
      decompile_constructor(ctor, &ctor_meta, name.clone(), cache, stt, dstt);

    cache.meta_sharing = saved_meta_sharing;
    cache.refs.truncate(refs_len);
    cache.univ_table.truncate(univs_len);

    let ctor_val = ctor_result?;
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
  let ctx_names: Vec<Name> = ctx_addrs
    .iter()
    .map(|a| decompile_name(a, stt))
    .collect::<Result<Vec<_>, _>>()?;

  // Set up cache with sharing, refs, univs, and ctx
  let mut cache = BlockCache {
    sharing: block_sharing.to_vec(),
    refs: block_refs.to_vec(),
    univ_table: block_univs.to_vec(),
    ctx: all_to_ctx(&ctx_names),
    current_const: name.pretty(),
    ..Default::default()
  };
  // Projection metadata can carry surgery extensions (notably
  // `meta_sharing` for `CallSite::Collapsed` lookups). Without this,
  // every `_sizeOf_N` — which is a DPrj into its mutual block and
  // whose body's `.rec` surgery produces `Collapsed` entries under
  // alpha-collapse — would fail with shape mismatches on decompile.
  cache.load_meta_extensions(&named.meta);

  // Each projection variant must land on the matching `MutConst` kind
  // at its block index. A silent fall-through would leave `name`
  // unregistered in `dstt.env`, and downstream references would fail
  // far from the real point of corruption.
  match &cnst.info {
    ConstantInfo::DPrj(proj) => match mutuals.get(proj.idx as usize) {
      Some(MutConst::Defn(def)) => {
        let info =
          decompile_definition(def, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), info);
      },
      other => {
        return Err(projection_mismatch_error(
          "DPrj",
          name,
          proj.idx,
          other,
          mutuals.len(),
          stt,
        ));
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
        return Err(projection_mismatch_error(
          "IPrj",
          name,
          proj.idx,
          other,
          mutuals.len(),
          stt,
        ));
      },
    },

    ConstantInfo::RPrj(proj) => match mutuals.get(proj.idx as usize) {
      Some(MutConst::Recr(rec)) => {
        let info = decompile_recursor(rec, &named.meta, &mut cache, stt, dstt)?;
        dstt.env.insert(name.clone(), info);
      },
      other => {
        return Err(projection_mismatch_error(
          "RPrj",
          name,
          proj.idx,
          other,
          mutuals.len(),
          stt,
        ));
      },
    },

    // Non-projection constants are ignored here; they're handled by
    // the generic decompile paths.
    _ => {},
  }

  Ok(())
}

/// Format a projection kind/index mismatch as a `BadConstantFormat`
/// error. Extracted to avoid triplicate bodies in `decompile_projection`.
fn projection_mismatch_error(
  kind: &str,
  name: &Name,
  idx: u64,
  other: Option<&MutConst>,
  mutuals_len: usize,
  stt: &CompileState,
) -> DecompileError {
  let has_addr = stt.name_to_addr.contains_key(name);
  let has_aux = stt.aux_name_to_addr.contains_key(name);
  let has_original =
    stt.env.named.get(name).is_some_and(|n| n.original.is_some());
  DecompileError::BadConstantFormat {
    msg: format!(
      "{kind} '{}' idx={idx} landed on {:?} (mutuals.len={mutuals_len}, \
       addr={has_addr}, aux={has_aux}, has_original={has_original})",
      name.pretty(),
      other.map(std::mem::discriminant),
    ),
  }
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
  let all_names: Vec<Name> = all_addrs
    .iter()
    .map(|a| decompile_name(a, stt))
    .collect::<Result<Vec<_>, _>>()?;
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
      cache.load_meta_extensions(&named.meta);
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
      // Recursor rule RHSs can carry surgery extensions (e.g. a rule
      // calling a collapsed `.rec`). Same rationale as `decompile_const`
      // Defn branch above — omitting this desyncs
      // `CallSiteEntry::Collapsed.sharing_idx` from the intended
      // `meta_sharing` slot.
      cache.load_meta_extensions(&named.meta);
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
      // Axioms have only a type (no body), so no surgery today — but
      // load extensions for consistency with the other branches.
      cache.load_meta_extensions(&named.meta);
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
      // Quotient types have only a type signature — same story as
      // axioms. Load extensions for consistency.
      cache.load_meta_extensions(&named.meta);
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
///
/// Used by both the decompile-time "skip in Pass 1" logic here and the
/// compile-time surgery guard (`compile_expr`) — a constant whose body
/// we're going to regenerate anyway should never have its call-sites
/// surgered, since the regenerated body is emitted in canonical order
/// by construction.
pub(crate) fn is_aux_gen_suffix(name: &Name) -> bool {
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

/// Map an `is_unsafe` flag to a `DefinitionSafety`. The decompile side uses
/// this to stay in lock-step with `ix::compile::mutual::def_safety`; if we
/// ever want to represent `Partial` explicitly we can refine both sides.
fn def_safety(is_unsafe: bool) -> DefinitionSafety {
  if is_unsafe { DefinitionSafety::Unsafe } else { DefinitionSafety::Safe }
}

/// Convert a `BelowDef` (Type-level `.below`) to a `LeanConstantInfo`.
///
/// Safety mirrors the parent inductive's `is_unsafe` flag (propagated via
/// `BelowDef::is_unsafe`) — Lean builds `.below` via
/// `mkDefinitionValInferringUnsafe`, which always flips to `Unsafe` when the
/// parent inductive is unsafe (the value references the parent's `.rec`).
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
    safety: def_safety(def.is_unsafe),
    all: vec![def.name.clone()],
  })
}

/// Convert a `BelowIndc` (Prop-level `.below`) to an `InductiveVal` and its constructors.
///
/// Safety mirrors the parent via `BelowIndc::is_unsafe` (see the Prop-level
/// branch of `IndPredBelow`). The constructor `is_unsafe` matches the
/// enclosing inductive — the kernel rejects mixed safety within an inductive.
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
    // Reflexivity is inherited from the parent (see `build_below_indc`).
    // The `ConstantInfo::InductInfo` hash includes `is_reflexive`, so the
    // regenerated `.below` must carry the same flag as Lean's original.
    is_reflexive: indc.is_reflexive,
    is_unsafe: indc.is_unsafe,
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
      is_unsafe: indc.is_unsafe,
    })
    .collect();
  (ind_val, ctors)
}

/// Convert a `BRecOnDef` to a `LeanConstantInfo`.
///
/// Replicates Lean's `Lean/Meta/Constructions/BRecOn.lean` per-kind decisions:
///
/// | Shape                 | Emits                    | Hints    |
/// |-----------------------|--------------------------|----------|
/// | `.brecOn` (Prop, safe)   | `ThmInfo`                   | —        |
/// | `.brecOn` (Prop, unsafe) | `DefnInfo` (`Unsafe`)       | `Opaque` |
/// | `.brecOn` (Type)         | `DefnInfo` (`Safe`/`Unsafe`) | `Abbrev` |
/// | `.brecOn.go`             | `DefnInfo` (`Safe`/`Unsafe`) | `Abbrev` |
/// | `.brecOn.eq` (safe)      | `ThmInfo`                   | —        |
/// | `.brecOn.eq` (unsafe)    | `DefnInfo` (`Unsafe`)       | `Opaque` |
///
/// The unsafe-`.eq` flip mirrors Lean's `mkThmOrUnsafeDef`
/// (`Lean/Environment.lean:2797`), which replaces a theorem with an unsafe
/// definition whenever `env.hasUnsafe` fires on the type or value.
fn brecon_def_to_lean(
  def: &crate::ix::compile::aux_gen::brecon::BRecOnDef,
) -> LeanConstantInfo {
  let cnst = ConstantVal {
    name: def.name.clone(),
    level_params: def.level_params.clone(),
    typ: def.typ.clone(),
  };

  let is_eq = def.name.last_str() == Some("eq");
  // Emit `ThmInfo` when Lean would have emitted `.thmDecl`: Prop-level
  // `.brecOn` or safe Type-level `.brecOn.eq`. Unsafe cases always flatten
  // into an unsafe `DefnInfo` with opaque reducibility.
  let as_theorem = (def.is_prop || is_eq) && !def.is_unsafe;

  if as_theorem {
    LeanConstantInfo::ThmInfo(TheoremVal {
      cnst,
      value: def.value.clone(),
      all: vec![def.name.clone()],
    })
  } else {
    // Hints: `.opaque` matches Lean's `mkThmOrUnsafeDef` for the unsafe-eq
    // flip (and unsafe Prop-level `.brecOn`, which in practice never
    // happens — Lean forbids `unsafe` in Prop — but we honor the flag).
    // `.abbrev` matches `mkDefinitionValInferringUnsafe … .abbrev` for
    // `.brecOn` / `.brecOn.go`.
    let hints = if def.is_unsafe && (def.is_prop || is_eq) {
      ReducibilityHints::Opaque
    } else {
      ReducibilityHints::Abbrev
    };
    LeanConstantInfo::DefnInfo(DefinitionVal {
      cnst,
      value: def.value.clone(),
      hints,
      safety: def_safety(def.is_unsafe),
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
  let Some(lean_ci_ref) = orig_env.get(name) else { return };
  let lean_ci = lean_ci_ref;
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

  // Secondary fields that `get_hash()` considers but `type` and `value`
  // don't: `hints`, `safety`, `all`, `level_params`, and DefnInfo `kind`.
  // When these diverge alone, the Lean-level hash differs even though
  // the structural `type` / `value` match — silently returning here
  // would hide the real cause of `roundtrip_block` failures.
  let aux = const_aux_fields(decompiled);
  let lean_aux = const_aux_fields(lean_ci);
  let aux_match = aux == lean_aux;

  if type_match && val_match && aux_match {
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
  if !aux_match {
    eprintln!("  metadata DIFFER:");
    if aux.level_params != lean_aux.level_params {
      eprintln!(
        "    level_params: decompiled={:?} original={:?}",
        aux.level_params, lean_aux.level_params
      );
    }
    if aux.hints != lean_aux.hints {
      eprintln!(
        "    hints:        decompiled={:?} original={:?}",
        aux.hints, lean_aux.hints
      );
    }
    if aux.safety != lean_aux.safety {
      eprintln!(
        "    safety:       decompiled={:?} original={:?}",
        aux.safety, lean_aux.safety
      );
    }
    if aux.all_names != lean_aux.all_names {
      eprintln!(
        "    all:          decompiled={:?} original={:?}",
        aux.all_names, lean_aux.all_names
      );
    }
    if aux.kind != lean_aux.kind {
      eprintln!(
        "    kind:         decompiled={:?} original={:?}",
        aux.kind, lean_aux.kind
      );
    }
  }
}

/// Secondary fields that contribute to `ConstantInfo::get_hash()` but
/// are NOT captured by `get_type().get_hash()` / `get_value().get_hash()`.
/// Extracting them into a comparable record lets
/// `print_const_comparison` report the exact mismatched field when
/// type + value already agree.
#[derive(Debug, PartialEq, Eq)]
struct ConstAuxFields {
  level_params: Vec<String>,
  hints: Option<ReducibilityHints>,
  safety: Option<DefinitionSafety>,
  all_names: Vec<String>,
  /// Discriminant label for defn-like variants (Definition/Theorem/
  /// Opaque), included so `DefnInfo` vs `ThmInfo` misclassification in
  /// the decompiler shows up here even though both share the same
  /// (cnst, value) shape.
  kind: &'static str,
}

fn const_aux_fields(ci: &LeanConstantInfo) -> ConstAuxFields {
  let level_params_of =
    |lps: &[Name]| -> Vec<String> { lps.iter().map(|n| n.pretty()).collect() };
  let all_of =
    |all: &[Name]| -> Vec<String> { all.iter().map(|n| n.pretty()).collect() };
  match ci {
    LeanConstantInfo::DefnInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: Some(v.hints),
      safety: Some(v.safety),
      all_names: all_of(&v.all),
      kind: "Defn",
    },
    LeanConstantInfo::ThmInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: None,
      all_names: all_of(&v.all),
      kind: "Thm",
    },
    LeanConstantInfo::OpaqueInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: Some(if v.is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      }),
      all_names: all_of(&v.all),
      kind: "Opaq",
    },
    LeanConstantInfo::AxiomInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: Some(if v.is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      }),
      all_names: Vec::new(),
      kind: "Axio",
    },
    LeanConstantInfo::QuotInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: None,
      all_names: Vec::new(),
      kind: "Quot",
    },
    LeanConstantInfo::InductInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: Some(if v.is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      }),
      all_names: all_of(&v.all),
      kind: "Indc",
    },
    LeanConstantInfo::CtorInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: Some(if v.is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      }),
      all_names: Vec::new(),
      kind: "Ctor",
    },
    LeanConstantInfo::RecInfo(v) => ConstAuxFields {
      level_params: level_params_of(&v.cnst.level_params),
      hints: None,
      safety: Some(if v.is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      }),
      all_names: all_of(&v.all),
      kind: "Rec",
    },
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
        stt.env.get_const(addr).map(|c| match &c.info {
          ConstantInfo::RPrj(p) => p.block.clone(),
          ConstantInfo::DPrj(p) => p.block.clone(),
          ConstantInfo::IPrj(p) => p.block.clone(),
          _ => addr.clone(), // bare constant, not a projection
        })
      })
    };
    if let Some(orig) = orig_addr
      && block_addr != orig
    {
      let first_is_aux_gen = is_aux_gen_suffix(&first_name);
      if std::env::var_os("IX_ROUNDTRIP_DEBUG").is_some() {
        // Full dump so we can compare what aux_gen regenerated vs
        // Lean's source for the failing constant. Set
        // IX_ROUNDTRIP_DEBUG=1 to enable.
        eprintln!(
          "[roundtrip DEBUG] {}: regen block_addr={:.12} != orig {:.12}",
          first_name.pretty(),
          block_addr.hex(),
          orig.hex(),
        );
        for cnst in consts {
          let nm = cnst.name();
          eprintln!("  -- regen {} --", nm.pretty());
          match cnst {
            LeanMutConst::Defn(def) => {
              eprintln!("    type: {}", def.typ.pretty());
              eprintln!("    value: {}", def.value.pretty());
            },
            LeanMutConst::Recr(rec) => {
              eprintln!("    type: {}", rec.cnst.typ.pretty());
              for (i, r) in rec.rules.iter().enumerate() {
                eprintln!(
                  "    rule[{i}] {} rhs: {}",
                  r.ctor.pretty(),
                  r.rhs.pretty()
                );
              }
            },
            LeanMutConst::Indc(ind) => {
              eprintln!("    type: {}", ind.ind.cnst.typ.pretty());
            },
          }
          if let Some(orig_env) = orig_env
            && let Some(lean_ci_ref) = orig_env.get(&nm)
          {
            let lean_ci = lean_ci_ref;
            eprintln!("  -- lean  {} --", nm.pretty());
            eprintln!("    type: {}", lean_ci.get_type().pretty());
            if let Some(v) = get_value(lean_ci) {
              eprintln!("    value: {}", v.pretty());
            }
          }
        }
      }
      if !first_is_aux_gen {
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
          if std::env::var_os("IX_ROUNDTRIP_DEBUG").is_some() {
            eprintln!(
              "[orig_meta] {}: using named.original (addr={:.12})",
              name.pretty(),
              named.original.as_ref().unwrap().0.hex(),
            );
          }
          named.original.as_ref().unwrap().1.clone()
        },
        s => {
          if std::env::var_os("IX_ROUNDTRIP_DEBUG").is_some() {
            eprintln!(
              "[orig_meta] {}: no named.original ({}), using all_metas fallback",
              name.pretty(),
              if s.is_some() {
                "has named but original=None"
              } else {
                "no named entry"
              },
            );
          }
          if let Some(meta) = all_metas.get(&name) {
            meta.clone()
          } else {
            continue;
          }
        },
      };

      let mut dec_cache = BlockCache {
        ctx: dec_ctx.clone(),
        sharing: block_constant.sharing.clone(),
        refs: block_constant.refs.clone(),
        univ_table: block_constant.univs.clone(),
        current_const: name.pretty(),
        ..Default::default()
      };
      // Aux_gen constants can carry CallSite metadata after source-order
      // surgery of `.below`/`.brecOn` calls. Load the per-constant metadata
      // extensions so Collapsed entries have their source-order arguments
      // available during binder-name restoration.
      dec_cache.load_meta_extensions(&orig_meta);

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
              && let Some(lean_ci_ref) = orig.get(&n)
              && ci.get_hash() != lean_ci_ref.get_hash()
            {
              let lean_ci = lean_ci_ref;
              if std::env::var_os("IX_ROUNDTRIP_DEBUG").is_some() {
                eprintln!(
                  "[lean hash mismatch] {}: generated_ci_hash={:x?} lean_ci_hash={:x?}",
                  n.pretty(),
                  ci.get_hash(),
                  lean_ci_ref.get_hash(),
                );
                // Dump internal shape
                let gen_type = ci.get_type();
                let orig_type = lean_ci.get_type();
                if gen_type.get_hash() != orig_type.get_hash() {
                  eprintln!("  type DIFFERS");
                  eprintln!("    gen:  {}", gen_type.pretty());
                  eprintln!("    orig: {}", orig_type.pretty());
                }
                if let (Some(gv), Some(ov)) =
                  (get_value(&ci), get_value(lean_ci))
                  && gv.get_hash() != ov.get_hash()
                {
                  eprintln!("  value DIFFERS");
                  eprintln!("    gen:  {}", gv.pretty());
                  eprintln!("    orig: {}", ov.pretty());
                }
                // Check `all` for DefnInfo
                if let (
                  LeanConstantInfo::DefnInfo(g_d),
                  LeanConstantInfo::DefnInfo(o_d),
                ) = (&ci, lean_ci)
                {
                  if g_d.all != o_d.all {
                    eprintln!(
                      "  all DIFFERS: gen={:?} orig={:?}",
                      g_d.all.iter().map(|n| n.pretty()).collect::<Vec<_>>(),
                      o_d.all.iter().map(|n| n.pretty()).collect::<Vec<_>>(),
                    );
                  }
                  if g_d.hints != o_d.hints {
                    eprintln!(
                      "  hints DIFFERS: gen={:?} orig={:?}",
                      g_d.hints, o_d.hints
                    );
                  }
                  if g_d.safety != o_d.safety {
                    eprintln!(
                      "  safety DIFFERS: gen={:?} orig={:?}",
                      g_d.safety, o_d.safety
                    );
                  }
                  if g_d.cnst.level_params != o_d.cnst.level_params {
                    eprintln!(
                      "  lvl_params DIFFERS: gen={:?} orig={:?}",
                      g_d
                        .cnst
                        .level_params
                        .iter()
                        .map(|n| n.pretty())
                        .collect::<Vec<_>>(),
                      o_d
                        .cnst
                        .level_params
                        .iter()
                        .map(|n| n.pretty())
                        .collect::<Vec<_>>(),
                    );
                  }
                }
              }
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
              && !is_aux_gen_suffix(&n)
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
                  // Both addresses reference projections but disagree on
                  // the target — this is a genuine roundtrip failure, not
                  // a wrapping-vs-not discrepancy. Previously logged via
                  // `eprintln!` and swallowed; now propagated so callers
                  // don't silently commit a mismatched constant.
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
                  return Err(DecompileError::BadConstantFormat {
                    msg: format!(
                      "[roundtrip ixon] {} proj mismatch: orig={:.12} [{:?}] \
                       recomp={:.12} [idx={}, block={:.12}]",
                      n.pretty(),
                      orig_addr.hex(),
                      orig_detail,
                      proj_addr.hex(),
                      class_idx,
                      block_addr.hex(),
                    ),
                  });
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
  let orig_ci = orig_env.get(rec_name);
  let Some(LeanConstantInfo::RecInfo(lean_rv)) = orig_ci else {
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

// ===========================================================================
// Per-constant and per-block helpers
// ===========================================================================

/// Decompile a single named constant (non-aux_gen) into the decompile state.
///
/// Dispatches on the constant kind (definition, recursor, axiom, quotient,
/// projection). Constants with `named.original.is_some()` and a recognized
/// aux_gen suffix are skipped — they'll be regenerated by `decompile_block_aux_gen`.
fn decompile_named_const(
  name: &Name,
  named: &Named,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  // Skip aux_gen constants (regenerated separately)
  if named.original.is_some() && is_aux_gen_suffix(name) {
    return Ok(());
  }

  if let Some(cnst) = stt.env.get_const(&named.addr) {
    match &cnst.info {
      // Direct constants - decompile immediately
      ConstantInfo::Defn(_)
      | ConstantInfo::Recr(_)
      | ConstantInfo::Axio(_)
      | ConstantInfo::Quot(_) => decompile_const(name, named, stt, dstt),

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
            name, named, &cnst, &mutuals, sharing, refs, univs, stt, dstt,
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
            name, named, &cnst, &mutuals, sharing, refs, univs, stt, dstt,
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
            name, named, &cnst, &mutuals, sharing, refs, univs, stt, dstt,
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
}

/// Regenerate aux_gen constants for a single mutual inductive block.
///
/// Runs the dependency-ordered phases (.rec -> .casesOn -> .recOn -> .below ->
/// .below.rec -> .brecOn) for one mutual inductive block. Reads parent
/// inductives from `env` (the shared DashMap) and writes generated constants
/// back to `dstt.env`.
///
/// Returns a list of (name, error) pairs for any failures within the block.
/// Rehydrate `stt.aux_perms` from persisted Muts.aux_layout entries.
///
/// Called once at the start of [`decompile_env`] so that aux_gen's
/// in-memory perm lookups see the same permutation compile produced,
/// even when `stt` was reconstructed from a deserialized Ixon env.
///
/// Walk every Muts-tagged Named entry; if it carries a stored
/// `aux_layout`, locate the block's source-order first inductive name
/// via one of its primary members' `Indc.all[0]` and populate
/// `stt.aux_perms[first_name] = layout`.
///
/// Idempotent: if `stt.aux_perms` already has an entry for the name, we
/// leave it alone (compile-in-progress stt wins over rehydrated copy).
fn rehydrate_aux_perms_from_env(stt: &CompileState) {
  use crate::ix::ixon::metadata::ConstantMetaInfo;

  let mut n_muts = 0usize;
  let mut n_muts_with_layout = 0usize;
  let mut n_populated = 0usize;

  // Fast path: every Muts entry is scanned; for non-nested blocks this
  // is a single `None` check and a no-op. The cost scales with the
  // number of mutual blocks in the env, not their sizes.
  for muts_entry in stt.env.named.iter() {
    let muts_named = muts_entry.value();
    let (muts_all, aux_layout) = match &muts_named.meta.info {
      ConstantMetaInfo::Muts { all, aux_layout: Some(layout) } => {
        n_muts += 1;
        n_muts_with_layout += 1;
        (all, layout.clone())
      },
      ConstantMetaInfo::Muts { .. } => {
        n_muts += 1;
        continue;
      },
      _ => continue,
    };
    if muts_all.is_empty() || muts_all[0].is_empty() {
      continue;
    }

    // muts_all[0][0] is the name-hash address of the first canonical
    // class representative. Look up its Named entry to find the Indc
    // metadata, which carries `all` in source order.
    let first_rep_addr = &muts_all[0][0];
    let first_rep_name = match stt.env.get_name(first_rep_addr) {
      Some(n) => n,
      None => continue,
    };
    let rep_named = match stt.env.named.get(&first_rep_name) {
      Some(r) => r,
      None => continue,
    };

    // Source-order `all` lives on any block member's Indc metadata.
    // (For aux-rewritten inductives, `Named.original` holds a pre-aux
    // version whose Indc.all is also source-order; we prefer the
    // canonical-entry `Indc.all` since it's the same source-order list
    // under spec §10.2.)
    let source_all: Option<&[Address]> = match &rep_named.meta.info {
      ConstantMetaInfo::Indc { all, .. } => Some(all.as_slice()),
      _ => None,
    };
    let source_all = match source_all {
      Some(s) if !s.is_empty() => s,
      _ => continue,
    };

    let source_first_name = match stt.env.get_name(&source_all[0]) {
      Some(n) => n,
      None => continue,
    };

    // Only populate if we haven't already — don't clobber an
    // in-progress compile's aux_perms entry.
    if !stt.aux_perms.contains_key(&source_first_name) {
      stt.aux_perms.insert(source_first_name, aux_layout);
      n_populated += 1;
    }
  }

  if std::env::var_os("IX_AUX_LAYOUT_DEBUG").is_some() {
    eprintln!(
      "[rehydrate_aux_perms] scanned {n_muts} Muts entries, \
       {n_muts_with_layout} had stored aux_layout, {n_populated} populated"
    );
  }
}

fn block_mut_consts_from_env(
  all_names: &[Name],
  env: &LeanEnv,
) -> Result<Vec<LeanMutConst>, DecompileError> {
  let mut cs = Vec::with_capacity(all_names.len());
  for name in all_names {
    let Some(LeanConstantInfo::InductInfo(ind)) = env.get(name) else {
      return Err(DecompileError::BadConstantFormat {
        msg: format!(
          "decompile aux plan: block member '{}' is not an inductive",
          name.pretty()
        ),
      });
    };
    let mut ctors = Vec::with_capacity(ind.ctors.len());
    for ctor_name in &ind.ctors {
      match env.get(ctor_name) {
        Some(LeanConstantInfo::CtorInfo(ctor)) => ctors.push(ctor.clone()),
        _ => {
          return Err(DecompileError::BadConstantFormat {
            msg: format!(
              "decompile aux plan: constructor '{}' for '{}' is missing",
              ctor_name.pretty(),
              name.pretty()
            ),
          });
        },
      }
    }
    cs.push(LeanMutConst::Indc(Ind { ind: ind.clone(), ctors }));
  }
  Ok(cs)
}

#[derive(Clone)]
struct StoredPlanBlock {
  class_names: Vec<Vec<Name>>,
  aux_layout: Option<crate::ix::ixon::env::AuxLayout>,
  flat_names: Vec<Name>,
}

fn names_from_addrs(
  addrs: &[Address],
  stt: &CompileState,
) -> Option<Vec<Name>> {
  addrs.iter().map(|addr| stt.env.get_name(addr)).collect()
}

fn indc_source_all(name: &Name, stt: &CompileState) -> Option<Vec<Name>> {
  let named = stt.env.named.get(name)?;
  match &named.meta.info {
    ConstantMetaInfo::Indc { all, .. } => names_from_addrs(all, stt),
    _ => None,
  }
}

fn stored_plan_blocks_for_original_all(
  original_all: &[Name],
  stt: &CompileState,
) -> Vec<StoredPlanBlock> {
  let original_set: FxHashSet<Name> = original_all.iter().cloned().collect();
  let mut candidates = Vec::new();
  let mut seen: FxHashSet<Vec<Name>> = FxHashSet::default();

  for muts_entry in stt.env.named.iter() {
    let ConstantMetaInfo::Muts { all, aux_layout } =
      &muts_entry.value().meta.info
    else {
      continue;
    };

    let mut class_names = Vec::with_capacity(all.len());
    let mut flat_names = Vec::new();
    let mut valid = true;
    for class in all {
      let Some(names) = names_from_addrs(class, stt) else {
        valid = false;
        break;
      };
      if names.is_empty() {
        valid = false;
        break;
      }
      flat_names.extend(names.iter().cloned());
      class_names.push(names);
    }
    if !valid || flat_names.is_empty() {
      continue;
    }
    if !flat_names.iter().all(|name| original_set.contains(name)) {
      continue;
    }

    let same_source_all = flat_names.iter().any(|name| {
      indc_source_all(name, stt)
        .is_some_and(|source_all| source_all.as_slice() == original_all)
    });
    if !same_source_all {
      continue;
    }

    if !seen.insert(flat_names.clone()) {
      continue;
    }
    candidates.push(StoredPlanBlock {
      class_names,
      aux_layout: aux_layout.clone(),
      flat_names,
    });
  }

  // Prefer persisted minimal SCCs. If a stale/full source block is present,
  // it is a strict superset of the minimal candidates and would recreate an
  // over-merged call-site plan after deserialization.
  candidates
    .iter()
    .filter(|candidate| {
      let candidate_set: FxHashSet<Name> =
        candidate.flat_names.iter().cloned().collect();
      !candidates.iter().any(|other| {
        other.flat_names.len() < candidate.flat_names.len()
          && other.flat_names.iter().all(|name| candidate_set.contains(name))
      })
    })
    .cloned()
    .collect()
}

fn fallback_plan_blocks_from_sort(
  all_names: &[Name],
  env: &LeanEnv,
  stt: &CompileState,
) -> Result<Vec<StoredPlanBlock>, DecompileError> {
  use crate::ix::compile::{BlockCache as CompileBlockCache, sort_consts};

  let cs = block_mut_consts_from_env(all_names, env)?;
  if cs.is_empty() {
    return Ok(Vec::new());
  }

  let mut cache = CompileBlockCache::default();
  let refs: Vec<&LeanMutConst> = cs.iter().collect();
  let sorted_classes = sort_consts(&refs, &mut cache, stt).map_err(|e| {
    DecompileError::BadConstantFormat {
      msg: format!("decompile aux plan sort_consts: {e}"),
    }
  })?;
  let class_names: Vec<Vec<Name>> = sorted_classes
    .iter()
    .map(|class| class.iter().map(|c| c.name()).collect())
    .collect();
  let aux_layout = all_names
    .first()
    .and_then(|n| stt.aux_perms.get(n).map(|layout| layout.clone()));
  let flat_names = class_names.iter().flatten().cloned().collect();

  Ok(vec![StoredPlanBlock { class_names, aux_layout, flat_names }])
}

fn install_decompile_call_site_plans(
  all_names: &[Name],
  aux_members: &[(AuxKind, Name)],
  env: &LeanEnv,
  stt: &CompileState,
) -> Result<(), DecompileError> {
  use crate::ix::compile::{aux_gen, surgery};

  if all_names.is_empty() {
    return Ok(());
  }

  let original_all: Vec<Name> = all_names.to_vec();
  let mut plan_blocks = stored_plan_blocks_for_original_all(&original_all, stt);
  if plan_blocks.is_empty() {
    plan_blocks = fallback_plan_blocks_from_sort(all_names, env, stt)?;
  }
  let aux_member_names: FxHashSet<Name> =
    aux_members.iter().map(|(_, n)| n.clone()).collect();

  for block in plan_blocks {
    if block.class_names.is_empty() {
      continue;
    }
    let user_layout_changed = block.class_names.len() < original_all.len()
      || (block.class_names.len() == original_all.len()
        && block
          .class_names
          .iter()
          .zip(original_all.iter())
          .any(|(class, orig)| class[0] != *orig));
    let aux_layout_changed = block.aux_layout.as_ref().is_some_and(|layout| {
      layout.perm.iter().enumerate().any(|(source_j, &canonical_i)| {
        canonical_i != aux_gen::nested::PERM_OUT_OF_SCC
          && canonical_i != source_j
      })
    });

    if !user_layout_changed && !aux_layout_changed {
      continue;
    }

    let plans = surgery::compute_call_site_plans(
      &block.class_names,
      &original_all,
      env,
      block.aux_layout.as_ref(),
    )
    .map_err(|e| DecompileError::BadConstantFormat {
      msg: format!("decompile aux plan compute_call_site_plans: {e}"),
    })?;

    for (name, plan) in plans {
      if let Some(brecon_name) = surgery::rec_name_to_brecon_name(&name)
        && (aux_member_names.contains(&brecon_name)
          || env.contains_key(&brecon_name))
        && !stt.brec_on_call_site_plans.contains_key(&brecon_name)
      {
        stt.brec_on_call_site_plans.insert(
          brecon_name,
          surgery::BRecOnCallSitePlan::from_rec_plan(&plan),
        );
      }
      if let Some(below_name) = surgery::rec_name_to_below_name(&name)
        && (aux_member_names.contains(&below_name)
          || env.contains_key(&below_name))
        && !stt.below_call_site_plans.contains_key(&below_name)
      {
        stt.below_call_site_plans.insert(
          below_name,
          surgery::BRecOnCallSitePlan::from_rec_plan(&plan),
        );
      }
      if !stt.call_site_plans.contains_key(&name) {
        stt.call_site_plans.insert(name, plan);
      }
    }
  }

  Ok(())
}

fn decompile_block_aux_gen(
  all_names: &[Name],
  aux_members: &[(AuxKind, Name)],
  env: &mut LeanEnv,
  kctx: &crate::ix::compile::KernelCtx,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Vec<(Name, DecompileError)> {
  use crate::ix::compile::aux_gen::{
    below::{BelowConstant, generate_below_constants},
    brecon::generate_brecon_constants,
    cases_on::generate_cases_on,
    expr_utils, populate_canon_kenv_with_below,
    recursor::generate_canonical_recursors_with_overlay,
  };

  let orig_env: Option<&LeanEnv> =
    stt.lean_env.as_ref().map(|arc| arc.as_ref());

  let mut aux_gen_errors: Vec<(Name, DecompileError)> = Vec::new();

  // Map from name -> raw generated LeanConstantInfo (before roundtrip).
  // Used for three-way diagnostic: generated vs decompiled vs original.
  let mut generated_consts: FxHashMap<Name, LeanConstantInfo> =
    FxHashMap::default();

  // Build un-collapsed classes: each inductive in its own singleton class.
  // NOTE: This diverges from compile's sort_consts-collapsed classes for
  // alpha-equivalent fixtures (e.g., NestedAlphaCollapse). Resolving the
  // full layout requires (a) passing canonical classes here AND (b)
  // ensuring aux_layout override is compatible with that class count —
  // the naive combination regresses more tests than it fixes. See plan
  // task #8 for the unified refactor.
  let classes: Vec<Vec<Name>> =
    all_names.iter().map(|n| vec![n.clone()]).collect();

  // Ingress parent inductives into the ephemeral kenv.
  for ind_name in all_names {
    expr_utils::ensure_in_kenv_of(ind_name, env, stt, kctx);
  }

  // Ingress transitive dependencies from constructor field types.
  {
    use crate::ix::graph::get_constant_info_references;
    for ind_name in all_names {
      if let Some(ci) = env.get(ind_name) {
        for ref_name in get_constant_info_references(ci) {
          expr_utils::ensure_in_kenv_of(&ref_name, env, stt, kctx);
        }
      }
    }
  }

  // Determine what kinds of aux constants this block needs.
  let needs_rec = aux_members.iter().any(|(k, _)| *k == AuxKind::Rec);
  let needs_below = aux_members.iter().any(|(k, _)| *k == AuxKind::Below);
  let needs_below_rec =
    aux_members.iter().any(|(k, _)| *k == AuxKind::BelowRec);
  let needs_cases_on = aux_members.iter().any(|(k, _)| *k == AuxKind::CasesOn);
  let needs_brecon = aux_members.iter().any(|(k, _)| {
    matches!(k, AuxKind::BRecOn | AuxKind::BRecOnGo | AuxKind::BRecOnEq)
  });
  let needs_rec_on = aux_members.iter().any(|(k, _)| *k == AuxKind::RecOn);

  // Phase 1: Generate canonical recursors.
  //
  // Decompile's `roundtrip_block` verifies that the regenerated Lean,
  // when recompiled, produces byte-equal Ixon at `Named.original.0`
  // (the source-form hash from `compile_const_no_aux`). To satisfy
  // that check, decompile's aux_gen must produce **source-walk order**
  // aux layout (matching Lean's own `.rec_N` naming and motive
  // order), not the canonical hash-sorted order stored in
  // `Named.addr`.
  //
  // Passing `None` for `aux_layout` tells
  // `generate_canonical_recursors_with_layout` to skip the
  // `reorder_flat_by_layout` step and use
  // `build_compile_flat_block_with_overlay`'s discovery order, which
  // mirrors Lean's elaborator source walk. This is the inverse of
  // compile's path — compile feeds aux_gen a hash-sorted `pre_flat`
  // to produce canonical bytes at `Named.addr`; decompile feeds
  // discovery order to produce source-form bytes matching
  // `Named.original.0`.
  //
  // (The stored `AuxLayout` is still rehydrated into `stt.aux_perms`
  // at `rehydrate_aux_perms_from_env` — surgery still needs it.)
  //
  // See `docs/ix_canonicity.md` §9.3 / §17.2 for the canonicity
  // commitment this upholds.
  let aux_layout_for_block: Option<crate::ix::ixon::env::AuxLayout> = None;

  let (canonical_recs, is_prop) = if needs_rec
    || needs_rec_on
    || needs_cases_on
    || needs_below
    || needs_below_rec
    || needs_brecon
  {
    match crate::ix::compile::aux_gen::recursor::generate_canonical_recursors_with_layout(
      &classes, env, None, None, stt, kctx,
      aux_layout_for_block.as_ref(),
      None, // source_of_canonical derived from aux_layout inside _with_layout
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
        return aux_gen_errors;
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
          if rec_members.contains(&&n) || env.contains_key(&n) {
            dstt.env.insert(n, ci);
          }
        }
      },
      Err(e) => {
        eprintln!("[decompile] roundtrip_block .rec failed: {e}");
        for (n, rv) in &canonical_recs {
          if rec_members.contains(&n) {
            dstt.env.insert(n.clone(), LeanConstantInfo::RecInfo(rv.clone()));
          }
        }
      },
    }
  }

  // Sync generated .rec constants into env and dstt.env so later phases can find them.
  for (n, rv) in &canonical_recs {
    env
      .entry(n.clone())
      .or_insert_with(|| LeanConstantInfo::RecInfo(rv.clone()));
    dstt
      .env
      .entry(n.clone())
      .or_insert_with(|| LeanConstantInfo::RecInfo(rv.clone()));
  }
  for (n, ci) in &generated_consts {
    env.entry(n.clone()).or_insert_with(|| ci.clone());
    dstt.env.entry(n.clone()).or_insert_with(|| ci.clone());
  }

  if let Err(e) =
    install_decompile_call_site_plans(all_names, aux_members, env, stt)
  {
    aux_gen_errors.push((all_names[0].clone(), e));
  }

  // Phase 1b: Generate .casesOn definitions.
  if needs_cases_on {
    let cases_on_members: Vec<&Name> = aux_members
      .iter()
      .filter(|(k, _)| *k == AuxKind::CasesOn)
      .map(|(_, n)| n)
      .collect();

    for co_name in &cases_on_members {
      let ind_name = match co_name.as_data() {
        crate::ix::env::NameData::Str(parent, _, _) => parent.clone(),
        _ => continue,
      };
      let rec_name = Name::str(ind_name.clone(), "rec".to_string());
      let rec_val = match env.get(&rec_name) {
        Some(LeanConstantInfo::RecInfo(rv)) => rv.clone(),
        _ => {
          // Try dstt.env (may have been inserted above)
          match dstt.env.get(&rec_name).as_deref() {
            Some(LeanConstantInfo::RecInfo(rv)) => rv.clone(),
            _ => continue,
          }
        },
      };
      if let Some(aux_def) = generate_cases_on(co_name, &rec_val, env) {
        // Lean marks `.casesOn` unsafe iff the parent `.rec` is unsafe
        // (an unsafe recursor transitively forces every wrapper around it).
        let safety = if rec_val.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        };
        let as_defn = LeanConstantInfo::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: aux_def.name.clone(),
            level_params: aux_def.level_params.clone(),
            typ: aux_def.typ.clone(),
          },
          value: aux_def.value.clone(),
          hints: ReducibilityHints::Abbrev,
          safety,
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
          safety,
          // Lean emits `.casesOn` / `.recOn` as standalone `defnDecl`s
          // (`refs/lean4/src/Lean/Elab/Inductive.lean:mkCasesOn` et al.),
          // each with `all = [self]`. `Named.original.0` captured that
          // exact shape; regenerating with `all = []` here makes the
          // Phase-A block hash match but leaves the Lean-level `all`
          // blank, so Phase B's `ConstantInfo::get_hash()` diverges
          // (type + value match but `all` differs). See
          // `docs/ix_canonicity.md` §9.2.
          all: vec![aux_def.name.clone()],
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
      let rec_val = match env.get(&rec_name) {
        Some(LeanConstantInfo::RecInfo(rv)) => rv.clone(),
        _ => match dstt.env.get(&rec_name).as_deref() {
          Some(LeanConstantInfo::RecInfo(rv)) => rv.clone(),
          _ => continue,
        },
      };
      if let Some(aux_def) = generate_rec_on(ro_name, &rec_val) {
        // Same safety propagation rule as `.casesOn`: if `.rec` is unsafe,
        // `.recOn` (which just reorders the rec's arguments) must be too.
        let safety = if rec_val.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        };
        let as_defn = LeanConstantInfo::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: aux_def.name.clone(),
            level_params: aux_def.level_params.clone(),
            typ: aux_def.typ.clone(),
          },
          value: aux_def.value.clone(),
          hints: ReducibilityHints::Abbrev,
          safety,
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
          safety,
          // Lean emits `.casesOn` / `.recOn` as standalone `defnDecl`s
          // (`refs/lean4/src/Lean/Elab/Inductive.lean:mkCasesOn` et al.),
          // each with `all = [self]`. `Named.original.0` captured that
          // exact shape; regenerating with `all = []` here makes the
          // Phase-A block hash match but leaves the Lean-level `all`
          // blank, so Phase B's `ConstantInfo::get_hash()` diverges
          // (type + value match but `all` differs). See
          // `docs/ix_canonicity.md` §9.2.
          all: vec![aux_def.name.clone()],
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
      env,
      is_prop,
      stt,
      kctx,
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
            generated_consts
              .insert(ctor.cnst.name.clone(), LeanConstantInfo::CtorInfo(ctor));
          }
        },
      }
    }
  }

  // Sync generated constants into env and dstt.env for subsequent phases.
  for (n, ci) in &generated_consts {
    env.entry(n.clone()).or_insert_with(|| ci.clone());
    dstt.env.entry(n.clone()).or_insert_with(|| ci.clone());
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

    // BelowIndc: bundle ALL generated below inductives into one roundtrip_block.
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

    // BelowDef: roundtrip through compile(regen, orig_metadata) -> decompile.
    //
    // Lean emits each `.below` / `.below_N` as a standalone `.defnDecl`
    // via `mkBelowFromRec` (`refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean`)
    // — each has `all = [self]` and compiles through `compile_single_def`
    // (bare constant, no `Muts` wrapper). Batching them into a single
    // `roundtrip_block` would wrap the whole list in a `Muts` block,
    // producing bytes that don't match Lean's source-form hash at
    // `Named.original.0`. Process each below def individually to mirror
    // Lean's declaration shape.
    for bc in &below_consts {
      let BelowConstant::Def(d) = bc else {
        continue;
      };
      // DEBUG: report Lean's `.all` and the Ixon addr/kind stored at
      // `Named.original.0`, so we can tell whether Lean emitted this
      // below as a bare def or whether compile_const_no_aux grouped
      // it into a shared `Muts` block (in which case Phase A's
      // singleton-addressed recompile won't match).
      if std::env::var_os("IX_ROUNDTRIP_DEBUG").is_some()
        && let Some(ref lean_env) = stt.lean_env
      {
        let lean_all = match lean_env.get(&d.name) {
          Some(LeanConstantInfo::DefnInfo(v)) => Some(v.all.clone()),
          Some(LeanConstantInfo::ThmInfo(v)) => Some(v.all.clone()),
          Some(LeanConstantInfo::OpaqueInfo(v)) => Some(v.all.clone()),
          _ => None,
        };
        let orig_info: Option<(String, String)> =
          stt.env.named.get(&d.name).and_then(|named| {
            let (addr, _) = named.original.as_ref()?.clone();
            let kind = stt
              .env
              .get_const(&addr)
              .map_or("missing", |c| match &c.info {
                ConstantInfo::Defn(_) => "Defn",
                ConstantInfo::DPrj(_) => "DPrj",
                ConstantInfo::Muts(_) => "Muts",
                _ => "?",
              })
              .to_string();
            Some((addr.hex(), kind))
          });
        if let Some(all) = lean_all {
          eprintln!(
            "[below .all] {} lean.all={:?} orig_addr={} orig_kind={}",
            d.name.pretty(),
            all.iter().map(|n| n.pretty()).collect::<Vec<_>>(),
            orig_info.as_ref().map_or("<none>", |(a, _)| a.as_str()),
            orig_info.as_ref().map_or("<none>", |(_, k)| k.as_str()),
          );
        }
      }
      let mc = LeanMutConst::Defn(Def {
        name: d.name.clone(),
        level_params: d.level_params.clone(),
        typ: d.typ.clone(),
        kind: DefKind::Definition,
        value: d.value.clone(),
        hints: ReducibilityHints::Abbrev,
        // Propagate the parent inductive's `is_unsafe` so the recompiled
        // Ixon address matches Lean's (see `brecon_to_mut_const` for the
        // full decision matrix).
        safety: def_safety(d.is_unsafe),
        // Each `.below` / `.below_N` is a standalone `defnDecl` with
        // `all = [self]` (`mkBelowFromRec`, see the comment on this
        // loop). Must mirror that or `ConstantInfo::get_hash()` differs
        // from `Named.original.0`'s source-form hash.
        all: vec![d.name.clone()],
      });
      match roundtrip_block(&[mc], &generated_consts, orig_env, stt, dstt) {
        Ok(roundtripped) => {
          for (n, ci) in roundtripped {
            dstt.env.insert(n, ci);
          }
        },
        Err(e) => {
          aux_gen_errors.push((d.name.clone(), e));
        },
      }
    }
  }

  // Phase 3: Generate .below.rec (Prop-level .below inductives only).
  if needs_below_rec && is_prop {
    let mut below_env = build_block_env(all_names, env);
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
        below_env.insert(i.name.clone(), LeanConstantInfo::InductInfo(ind_val));
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
        None,
        stt,
        kctx,
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

  // Sync generated constants (below, below.rec) into env and dstt.env for brecOn.
  for (n, ci) in &generated_consts {
    env.entry(n.clone()).or_insert_with(|| ci.clone());
    dstt.env.entry(n.clone()).or_insert_with(|| ci.clone());
  }

  // Populate the ephemeral kenv with .below types so brecOn's TcScope
  // can infer PProd(motive, I.below ...) during sort level inference.
  if !below_consts.is_empty() {
    populate_canon_kenv_with_below(&below_consts, &classes, env, stt, kctx);
  }

  // Phase 4: Generate .brecOn / .brecOn.go / .brecOn.eq.
  if needs_brecon {
    match generate_brecon_constants(
      &classes,
      &canonical_recs,
      &below_consts,
      env,
      is_prop,
      stt,
      kctx,
    ) {
      Ok(brecon_defs) => {
        for d in &brecon_defs {
          generated_consts.insert(d.name.clone(), brecon_def_to_lean(d));
        }

        let brecon_members: Vec<&Name> = aux_members
          .iter()
          .filter(|(k, _)| {
            matches!(k, AuxKind::BRecOn | AuxKind::BRecOnGo | AuxKind::BRecOnEq)
          })
          .map(|(_, n)| n)
          .collect();

        for d in
          brecon_defs.iter().filter(|d| brecon_members.contains(&&d.name))
        {
          // Mirror the `brecon_def_to_lean` / `brecon_to_mut_const`
          // decision matrix so the roundtrip compile step emits the same
          // Ixon bytes Lean does. Unsafe `.brecOn.eq` / unsafe Prop
          // `.brecOn` flip from `Thm` to unsafe `Defn` with opaque hints.
          let is_eq =
            matches!(classify_aux_gen(&d.name), Some((AuxKind::BRecOnEq, _)));
          let wants_thm = (d.is_prop || is_eq) && !d.is_unsafe;
          let kind =
            if wants_thm { DefKind::Theorem } else { DefKind::Definition };
          let hints = if (d.is_unsafe && (d.is_prop || is_eq))
            || matches!(kind, DefKind::Theorem)
          {
            ReducibilityHints::Opaque
          } else {
            ReducibilityHints::Abbrev
          };
          let mc = LeanMutConst::Defn(Def {
            name: d.name.clone(),
            level_params: d.level_params.clone(),
            typ: d.typ.clone(),
            kind,
            value: d.value.clone(),
            hints,
            safety: def_safety(d.is_unsafe),
            // `.brecOn`, `.brecOn.go`, `.brecOn.eq` are each emitted as
            // standalone defs/theorems by Lean with `all = [self]`.
            all: vec![d.name.clone()],
          });
          match roundtrip_block(&[mc], &generated_consts, orig_env, stt, dstt) {
            Ok(roundtripped) if !roundtripped.is_empty() => {
              for (n, ci) in roundtripped {
                dstt.env.insert(n, ci);
              }
            },
            Ok(_) | Err(_) => {
              // Fallback when the roundtrip_block compile step fails:
              // still surface a best-effort LeanConstantInfo so the
              // decompiled env is populated. `brecon_def_to_lean` applies
              // the same kind/safety/hints matrix that the compile path
              // used, so the kind recorded here mirrors what Lean's
              // original has (even if the recompile couldn't prove byte
              // equivalence).
              dstt.env.insert(d.name.clone(), brecon_def_to_lean(d));
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
  if let Some(orig) = orig_env {
    for (name, generated_ci) in &generated_consts {
      if let Some(orig_ci) = orig.get(name)
        && let Err(e) =
          crate::ix::congruence::const_alpha_eq(generated_ci, orig_ci)
      {
        aux_gen_errors.push((
          name.clone(),
          DecompileError::BadConstantFormat { msg: format!("congruence: {e}") },
        ));
      }
    }
  }

  aux_gen_errors
}

// ===========================================================================
// Main entry point
// ===========================================================================

/// Decompile an Ixon environment back to Lean format.
///
/// Single-pass parallel work-stealing scheduler. Computes SCCs over the
/// name-level reference graph, then processes SCC blocks in topological order.
/// For each block:
///   - Phase A: decompile all non-aux_gen constants (`decompile_named_const`)
///   - Phase B: regenerate aux_gen constants if the block has any (`decompile_block_aux_gen`)
///   - Phase C: resolve deps to unlock downstream blocks
pub fn decompile_env(
  stt: &CompileState,
) -> Result<DecompileState, DecompileError> {
  use crate::ix::compile::KernelCtx;
  use crate::ix::compile::aux_gen::expr_utils;
  use crate::ix::condense::compute_sccs;
  use crate::ix::graph::{NameSet, RefMap, get_constant_info_references};

  let dstt = DecompileState::default();

  // Pre-pass: Rehydrate `stt.aux_perms` from persisted Muts metadata.
  //
  // When `stt` was freshly constructed from a deserialized Ixon env,
  // `stt.aux_perms` starts empty — compile wrote it in-memory only. The
  // aux_layout payload survives serialize via
  // `ConstantMetaInfo::Muts.aux_layout`, so we reconstitute it here
  // before Pass 2 runs aux_gen against the decompiled blocks.
  //
  // See `docs/ix_canonicity.md` §10.2 / §17.3.
  rehydrate_aux_perms_from_env(stt);

  // Pass 1: Decompile all non-aux_gen constants (parallel).
  // Aux_gen constants (named.original.is_some() && is_aux_gen_suffix) are
  // skipped — they'll be regenerated in Pass 2 from parent inductives.
  let t_p1 = std::time::Instant::now();
  eprintln!(
    "[decompile] Pass 1: decompiling {} non-aux_gen constants in parallel...",
    stt.env.named.len(),
  );
  stt.env.named.par_iter().try_for_each(|entry| {
    let (name, named) = (entry.key(), entry.value());
    decompile_named_const(name, named, stt, &dstt)
  })?;
  eprintln!(
    "[decompile] Pass 1 done in {:.2}s ({} constants in dstt.env)",
    t_p1.elapsed().as_secs_f32(),
    dstt.env.len(),
  );

  // Pass 2: Regenerate aux_gen constants for mutual inductive blocks.
  // Process blocks in topological order so that when block B's constructor
  // fields reference inductives from block A, A's generated auxiliaries
  // (.rec, .below, .brecOn) are already in dstt.env.

  // Collect aux_gen constants grouped by mutual block.
  // Key: first name in the `all` field (canonical block identifier).
  // Value: (all_names, list of (AuxKind, constant_name)).
  type AuxBlockMap = FxHashMap<Name, (Vec<Name>, Vec<(AuxKind, Name)>)>;
  let mut blocks: AuxBlockMap = FxHashMap::default();
  let t_p2_prep = std::time::Instant::now();

  for entry in stt.env.named.iter() {
    let (name, named) = (entry.key(), entry.value());
    if named.original.is_none() {
      continue;
    }
    let Some((kind, root)) = classify_aux_gen(name) else {
      continue;
    };
    let all_names = match dstt.env.get(&root).as_deref() {
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

  // Topologically sort blocks by cross-block dependencies derived from
  // the parent inductives' constructor types.
  let sorted_block_keys = {
    let mut name_to_block: FxHashMap<Name, Name> = FxHashMap::default();
    for (block_key, (all_names, _)) in &blocks {
      for ind_name in all_names {
        name_to_block.insert(ind_name.clone(), block_key.clone());
        if let Some(LeanConstantInfo::InductInfo(v)) =
          dstt.env.get(ind_name).as_deref()
        {
          for ctor in &v.ctors {
            name_to_block.insert(ctor.clone(), block_key.clone());
          }
        }
      }
    }

    let mut block_deps: RefMap = RefMap::default();
    for (block_key, (all_names, _)) in &blocks {
      let mut deps = NameSet::default();
      for ind_name in all_names {
        if let Some(ci) = dstt.env.get(ind_name) {
          for ref_name in get_constant_info_references(&ci) {
            if let Some(dep_block) = name_to_block.get(&ref_name)
              && dep_block != block_key
            {
              deps.insert(dep_block.clone());
            }
          }
        }
      }
      block_deps.insert(block_key.clone(), deps);
    }

    let condensed = compute_sccs(&block_deps);
    let mut sorted: Vec<Name> = condensed.blocks.keys().cloned().collect();
    sorted.reverse(); // Tarjan produces reverse topo order
    sorted.retain(|k| blocks.contains_key(k));
    sorted
  };
  eprintln!(
    "[decompile] Pass 2 prep done in {:.2}s: {} aux_gen blocks to regenerate",
    t_p2_prep.elapsed().as_secs_f32(),
    sorted_block_keys.len(),
  );

  // Shared kernel context for aux_gen (accumulates across blocks).
  // Decompile must start from a cold kernel env (the whole point of Phase 2
  // is to verify we can regenerate auxiliaries from the Ixon env alone,
  // independent of the compile phase's state).
  let kctx = KernelCtx::new();
  expr_utils::ensure_prelude_in_kenv_of(stt, &kctx);

  // Snapshot dstt.env (DashMap) into work_env (FxHashMap) for aux_gen lookups.
  // This grows incrementally as each block's aux_gen generates new constants.
  let mut work_env: LeanEnv =
    dstt.env.iter().map(|e| (e.key().clone(), e.value().clone())).collect();

  let mut aux_gen_errors: Vec<(Name, DecompileError)> = Vec::new();

  // Tracks constants already ingressed into `kctx.kenv` across all blocks,
  // so the BFS below doesn't redundantly walk the same dependency subgraph
  // for every block (still O(n) across all blocks combined).
  let mut ingressed: FxHashSet<Name> = FxHashSet::default();

  // Progress tracking. Per-block progress logs (every `log_stride` blocks or
  // every 5 s) are opt-in via `IX_DECOMPILE_PROGRESS`; slow-block warnings
  // (any single block exceeding `slow_threshold`) are always emitted.
  let progress_enabled = std::env::var_os("IX_DECOMPILE_PROGRESS").is_some();
  let total_blocks = sorted_block_keys.len();
  let log_stride = (total_blocks / 50).max(1);
  let slow_threshold = std::time::Duration::from_secs(10);
  let t_p2 = std::time::Instant::now();
  let mut t_last_log = t_p2;

  for (block_idx, block_key) in sorted_block_keys.iter().enumerate() {
    let Some((all_names, aux_members)) = blocks.get(block_key) else {
      continue;
    };

    let t_block = std::time::Instant::now();

    // Ingress the transitive closure of the parent inductives' dependencies
    // into KEnv. A simple one- or two-level walk is not enough:
    // `get_constant_info_references` for an `InductInfo` returns refs from
    // the inductive's type signature plus the constructor *names*, but not
    // the references inside each *constructor's type*. So a field of type
    // `PersistentArrayNode InfoTree` inside some `State.mk` is only
    // discovered when we process the ctor and recurse into *its* type refs.
    // Without the transitive walk, TypeChecker::infer during brecOn's
    // universe-level inference fails with "unknown constant" on names that
    // are two or more edges away from the block's parent inductives.
    let mut stack: Vec<Name> = all_names.clone();
    while let Some(name) = stack.pop() {
      if !ingressed.insert(name.clone()) {
        continue;
      }
      expr_utils::ensure_in_kenv_of(&name, &work_env, stt, &kctx);
      if let Some(ci) = work_env.get(&name) {
        for ref_name in get_constant_info_references(ci) {
          if !ingressed.contains(&ref_name) {
            stack.push(ref_name);
          }
        }
      }
    }
    let t_after_ingress = std::time::Instant::now();

    let errors = decompile_block_aux_gen(
      all_names,
      aux_members,
      &mut work_env,
      &kctx,
      stt,
      &dstt,
    );
    aux_gen_errors.extend(errors);

    // Per-block slow-block warning.
    let block_elapsed = t_block.elapsed();
    if block_elapsed > slow_threshold {
      let ingress_ms = (t_after_ingress - t_block).as_millis();
      let gen_ms =
        (t_block.elapsed() - (t_after_ingress - t_block)).as_millis();
      eprintln!(
        "[decompile] slow block [{block_idx}/{total_blocks}] {} \
         took {:.2}s (ingress={ingress_ms}ms, gen={gen_ms}ms, \
         {} members, kenv={})",
        block_key.pretty(),
        block_elapsed.as_secs_f32(),
        aux_members.len(),
        ingressed.len(),
      );
    }

    // Periodic progress log (opt-in via IX_DECOMPILE_PROGRESS).
    if progress_enabled {
      let now = std::time::Instant::now();
      let done = block_idx + 1;
      let should_log = done == total_blocks
        || done % log_stride == 0
        || now.duration_since(t_last_log) > std::time::Duration::from_secs(5);
      if should_log {
        let elapsed = t_p2.elapsed().as_secs_f32();
        // Progress logging is approximate; precision/sign losses below are
        // acceptable for human-readable percentages and ETA seconds.
        #[allow(clippy::cast_precision_loss)]
        let rate = done as f32 / elapsed.max(0.001);
        #[allow(
          clippy::cast_precision_loss,
          clippy::cast_possible_truncation,
          clippy::cast_sign_loss
        )]
        let remaining = ((total_blocks - done) as f32 / rate.max(0.001)) as u64;
        #[allow(clippy::cast_precision_loss)]
        let pct = 100.0 * done as f32 / total_blocks as f32;
        eprintln!(
          "[decompile] Pass 2 progress: {done}/{total_blocks} blocks \
           ({pct:.1}%), elapsed {elapsed:.1}s, eta {remaining}s, kenv={}",
          ingressed.len(),
        );
        t_last_log = now;
      }
    }
  }
  eprintln!(
    "[decompile] Pass 2 done in {:.2}s ({} aux_gen errors, kenv={})",
    t_p2.elapsed().as_secs_f32(),
    aux_gen_errors.len(),
    ingressed.len(),
  );

  if !aux_gen_errors.is_empty() {
    eprintln!(
      "[decompile] aux_gen roundtrip errors ({}):",
      aux_gen_errors.len(),
    );
    for (name, e) in &aux_gen_errors {
      eprintln!("  {}: {e}", name.pretty());
    }
  }

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
    if is_aux_gen_suffix(name) {
      return Ok::<(), DecompileError>(());
    }
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
      .filter(|(name, _)| !dstt.env.contains_key(*name))
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

// ===========================================================================
// Regression tests for call-site surgery decompile
//
// These pin three bugs fixed together in the `_sizeOf_N` / surgered-mutual
// family of failures. Each test constructs an `ExprMeta` arena and matching
// Ixon `Expr` directly (no Lean env / compile_env), then invokes
// `decompile_expr` through the public surface the production code uses.
//
// The goal isn't full compile-pipeline coverage (the `validate-aux` harness
// does that end-to-end on 109k+ constants); it's to anchor the individual
// decompile-side invariants so a future change that breaks one of them
// trips immediately in `cargo test`.
// ===========================================================================

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::compile::compile_name;
  use crate::ix::env::Level;

  /// Register a Name in `stt.env.names` so `decompile_name` can resolve it.
  /// Mirrors `compile_name` (content-address the name, insert into names map).
  fn register_name(stt: &CompileState, name: &Name) -> Address {
    compile_name(name, stt)
  }

  /// Extract the source-order `(head, args)` telescope from a Lean App spine.
  /// Used by tests to assert the reconstructed spine matches expectations.
  fn lean_telescope(e: &LeanExpr) -> (LeanExpr, Vec<LeanExpr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let crate::ix::env::ExprData::App(f, a, _) = cur.as_data() {
      args.push(a.clone());
      cur = f.clone();
    }
    args.reverse();
    (cur, args)
  }

  /// Pull the bvar index out of a Lean expr, or None if it isn't a bvar.
  fn bvar_idx(e: &LeanExpr) -> Option<u64> {
    match e.as_data() {
      crate::ix::env::ExprData::Bvar(n, _) => n.to_u64(),
      _ => None,
    }
  }

  // -------------------------------------------------------------------------
  // Test 1 — BuildTelescope must reconstruct the *source-order* spine.
  //
  // This pins the `args.reverse()` fix in `Frame::BuildTelescope`. Before
  // the fix, entries pushed to the stack in reverse source order landed
  // on `results` in source order, then the LIFO pop + foldl produced
  // `App(… App(head, arg[N-1]), arg[0])` — a literal reversal of the
  // spine.
  //
  // Fixture: three `Kept` entries with `canon_idx = [2, 0, 1]`, meaning
  //   source[0] (Var 10) lives at canonical position 2
  //   source[1] (Var 11) lives at canonical position 0
  //   source[2] (Var 12) lives at canonical position 1
  // The canonical Ixon App spine is therefore
  //   App(App(App(head, Var 11), Var 12), Var 10)
  // and the expected decompiled source-order telescope is
  //   [Var 10, Var 11, Var 12].
  // -------------------------------------------------------------------------
  #[test]
  fn test_callsite_reconstructs_source_order_spine() {
    let stt = CompileState::default();

    // Register the callee name so CallSite.name resolves to something the
    // decompiler can name-lookup.
    let head_name = Name::str(Name::anon(), "head".to_string());
    let head_addr = register_name(&stt, &head_name);

    // Build the arena: three leaf entries (one per arg, all Var/Leaf) plus
    // a CallSite root. The canonical-order args are Var(11), Var(12),
    // Var(10). We allocate their leaf metadata in canonical order so
    // `canonical_roots[i]` = leaf i (matches how compile-side
    // `Frame::BuildCallSite` populates it).
    let mut arena = ExprMeta::default();
    let leaf0 = arena.alloc(ExprMetaData::Leaf); // metadata for canonical arg 0 = Var(11)
    let leaf1 = arena.alloc(ExprMetaData::Leaf); // metadata for canonical arg 1 = Var(12)
    let leaf2 = arena.alloc(ExprMetaData::Leaf); // metadata for canonical arg 2 = Var(10)

    // Build CallSite entries in source order. `canon_idx` records which
    // canonical slot each source-order arg lives in; `meta` is the arena
    // index of that canonical arg's metadata subtree.
    let entries = vec![
      CallSiteEntry::Kept { canon_idx: 2, meta: leaf2 }, // source[0] = Var(10) -> canon 2
      CallSiteEntry::Kept { canon_idx: 0, meta: leaf0 }, // source[1] = Var(11) -> canon 0
      CallSiteEntry::Kept { canon_idx: 1, meta: leaf1 }, // source[2] = Var(12) -> canon 1
    ];
    let callsite_root = arena.alloc(ExprMetaData::CallSite {
      name: head_addr.clone(),
      entries,
      canon_meta: vec![leaf0, leaf1, leaf2],
    });

    // Canonical Ixon App spine: head applied to canonical-order args
    // (Var 11 first, Var 12 second, Var 10 third).
    let head = Expr::reference(0, vec![]);
    let canon_arg0 = Expr::var(11);
    let canon_arg1 = Expr::var(12);
    let canon_arg2 = Expr::var(10);
    let ixon =
      Expr::app(Expr::app(Expr::app(head, canon_arg0), canon_arg1), canon_arg2);

    // Cache: refs[0] points at head_addr so the CallSite head name
    // resolves.
    let mut cache = BlockCache {
      refs: vec![head_addr],
      current_const: "test_source_order".into(),
      ..Default::default()
    };

    let dstt = DecompileState::default();
    let decompiled = decompile_expr(
      &ixon,
      &arena,
      callsite_root,
      &[],
      &mut cache,
      &stt,
      &dstt,
    )
    .expect("decompile_expr succeeded");

    // The reconstructed spine should be in *source* order: Var 10, 11, 12.
    let (head_lean, args) = lean_telescope(&decompiled);
    match head_lean.as_data() {
      crate::ix::env::ExprData::Const(name, _, _) => {
        assert_eq!(*name, head_name, "head const name mismatch");
      },
      other => panic!("expected Const head, got {other:?}"),
    }
    let arg_idxs: Vec<u64> =
      args.iter().map(|a| bvar_idx(a).unwrap()).collect();
    assert_eq!(
      arg_idxs,
      vec![10, 11, 12],
      "args must be in source order (10, 11, 12); \
       the pre-fix BuildTelescope reversed them to (12, 11, 10) or similar"
    );
  }

  // -------------------------------------------------------------------------
  // Test 2 — CallSite::Collapsed.sharing_idx must index `meta_sharing`,
  // NOT the concatenated block+meta `sharing` table.
  //
  // This pins the split-index-space fix. Before the fix, `load_meta_extensions`
  // appended `meta_sharing` onto `cache.sharing` and the Collapsed lookup
  // read `cache.sharing[sharing_idx]`. If the block's primary sharing had
  // any entries, `sharing_idx = 0` would silently return a block-shared
  // subtree (a lambda from body sharing) where the CallSite meta expected
  // a Ref/motive — reproducing the "Binder arena vs Expr::Ref" error on
  // surgered `_sizeOf_N` constants.
  //
  // Fixture: source order is [Collapsed(motive), Kept(major)] — matching
  // Lean's `.rec` telescope shape where the major premise is always Kept.
  // Block `sharing[0]` is a DECOY lambda expression; the Collapsed entry
  // `sharing_idx = 0` must read the Ref from `meta_sharing[0]`.
  // -------------------------------------------------------------------------
  #[test]
  fn test_callsite_collapsed_reads_meta_sharing_not_sharing() {
    let stt = CompileState::default();

    // Register names for the CallSite head and the Collapsed-arg target.
    let head_name = Name::str(Name::anon(), "head".to_string());
    let head_addr = register_name(&stt, &head_name);
    let target_name = Name::str(Name::anon(), "target".to_string());
    let target_addr = register_name(&stt, &target_name);

    // Arena: leaf for the Kept major, Ref-leaf for the Collapsed motive's
    // metadata (tells the walker "this collapsed arg is a const ref"),
    // CallSite root.
    let mut arena = ExprMeta::default();
    let major_leaf = arena.alloc(ExprMetaData::Leaf);
    let motive_ref_leaf =
      arena.alloc(ExprMetaData::Ref { name: target_addr.clone() });
    // Source order: [Collapsed(motive), Kept(major)]. Kept major lives
    // at canon position 0 (the only canonical slot).
    let entries = vec![
      CallSiteEntry::Collapsed { sharing_idx: 0, meta: motive_ref_leaf },
      CallSiteEntry::Kept { canon_idx: 0, meta: major_leaf },
    ];
    let callsite_root = arena.alloc(ExprMetaData::CallSite {
      name: head_addr.clone(),
      entries,
      canon_meta: vec![major_leaf],
    });

    // Canonical Ixon spine: App(head, major). Major is a distinguishable
    // marker bvar so we can assert it lands in the right position.
    let head = Expr::reference(0, vec![]);
    let major_ixon = Expr::var(99);
    let ixon = Expr::app(head, major_ixon);

    // Block sharing has a decoy: a lambda that, if the Collapsed lookup
    // went to `cache.sharing[0]` instead of `cache.meta_sharing[0]`, would
    // be walked as the collapsed motive — producing a Binder-vs-Ref shape
    // mismatch exactly like the validate-aux failure.
    let decoy = Expr::lam(Expr::var(0), Expr::var(0));
    // The real collapsed motive lives in meta_sharing[0]: a Ref to
    // `target`. Its refs-table index is 1 (target_addr is refs[1]).
    let collapsed_motive = Expr::reference(1, vec![]);

    let mut cache = BlockCache {
      sharing: vec![decoy],
      meta_sharing: vec![collapsed_motive],
      refs: vec![head_addr, target_addr],
      current_const: "test_collapsed".into(),
      ..Default::default()
    };

    let dstt = DecompileState::default();
    let decompiled = decompile_expr(
      &ixon,
      &arena,
      callsite_root,
      &[],
      &mut cache,
      &stt,
      &dstt,
    )
    .expect("decompile_expr succeeded — Collapsed must read meta_sharing");

    // Expected source-order spine: App(App(head, motive_ref), major).
    let (head_lean, args) = lean_telescope(&decompiled);
    match head_lean.as_data() {
      crate::ix::env::ExprData::Const(name, _, _) => {
        assert_eq!(*name, head_name);
      },
      other => panic!("expected head Const, got {other:?}"),
    }
    assert_eq!(
      args.len(),
      2,
      "spine should have 2 args: [collapsed_motive, major]"
    );
    // args[0] is the collapsed motive — must be Const(target), NOT the
    // decoy lambda from sharing[0].
    match args[0].as_data() {
      crate::ix::env::ExprData::Const(name, _, _) => {
        assert_eq!(
          *name, target_name,
          "args[0] is the Collapsed motive and must resolve via \
           meta_sharing[0] = Ref(target), NOT via sharing[0] = decoy lambda",
        );
      },
      other => panic!(
        "expected Const(target) as args[0] — reading sharing[0] would give a \
         Lam/Binder, producing a Binder-vs-Ref arena mismatch. Got {other:?}"
      ),
    }
    // args[1] is the Kept major — must decode to bvar 99.
    assert_eq!(
      bvar_idx(&args[1]).expect("major should be a bvar"),
      99,
      "args[1] is the Kept major, must preserve Var(99)"
    );
  }

  // -------------------------------------------------------------------------
  // Test 3 — `decompile_projection` must call `load_meta_extensions`
  // so the projected Defn's `meta_sharing` is visible during the walk.
  //
  // This pins the `decompile_projection` missing-extension-load fix.
  // Every `_sizeOf_N` is a DPrj into a Muts block, so without this call
  // the per-constant `meta_sharing` (where surgery's collapsed args live)
  // stayed empty and any `Collapsed { sharing_idx: 0, ... }` tripped
  // `InvalidShareIndex`.
  //
  // Fixture: construct a minimal Muts block with one Defn whose value is
  // a CallSite with one Collapsed entry, register the Named entry for the
  // DPrj, and drive `decompile_env`.
  // -------------------------------------------------------------------------
  #[test]
  fn test_projection_decompile_loads_meta_extensions() {
    use crate::ix::address::Address;
    use crate::ix::env::DefinitionSafety;
    use crate::ix::ixon::constant::{
      DefKind, Definition, DefinitionProj, MutConst as IxMutConst,
    };

    let stt = CompileState::default();

    // Names: the projection `f`, the CallSite head `head`, the Collapsed
    // arg target `target`.
    let f_name = Name::str(Name::anon(), "f".to_string());
    let head_name = Name::str(Name::anon(), "head".to_string());
    let target_name = Name::str(Name::anon(), "target".to_string());
    let f_addr_name = register_name(&stt, &f_name);
    let head_addr = register_name(&stt, &head_name);
    let target_addr = register_name(&stt, &target_name);

    // Build the Defn's arena: type is a Leaf (Sort), value is a CallSite
    // with [Collapsed(motive → target), Kept(major)] entries. This mirrors
    // the `.rec` telescope shape — at least one Kept (the major premise)
    // means the canonical spine is a real App, not a bare Ref.
    let mut arena = ExprMeta::default();
    let type_root = arena.alloc(ExprMetaData::Leaf);
    let motive_ref_leaf =
      arena.alloc(ExprMetaData::Ref { name: target_addr.clone() });
    let major_leaf = arena.alloc(ExprMetaData::Leaf);
    let value_root = arena.alloc(ExprMetaData::CallSite {
      name: head_addr.clone(),
      entries: vec![
        CallSiteEntry::Collapsed { sharing_idx: 0, meta: motive_ref_leaf },
        CallSiteEntry::Kept { canon_idx: 0, meta: major_leaf },
      ],
      canon_meta: vec![major_leaf],
    });

    // Ixon expressions: type is Sort 0, value is the canonical App spine
    // with the Kept major at canon position 0 (Var 77).
    let typ = Expr::sort(0);
    let value = Expr::app(Expr::reference(0, vec![]), Expr::var(77));
    let collapsed_arg = Expr::reference(1, vec![]); // Ref(target) via refs[1]

    // Build the Defn payload and wrap it in a Muts block.
    let def = Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ,
      value,
    };
    let block = Constant {
      info: ConstantInfo::Muts(vec![IxMutConst::Defn(def)]),
      sharing: vec![],
      refs: vec![head_addr, target_addr],
      univs: vec![Arc::new(Univ::Zero)],
    };

    // Store the block and register it under a synthetic Muts name so
    // decompile_env's Pass 1 scan classifies it.
    let mut block_bytes = Vec::new();
    block.put(&mut block_bytes);
    let block_addr = Address::hash(&block_bytes);
    stt.env.store_const(block_addr.clone(), block);

    let muts_name = block_addr.muts_name(&f_name);
    register_name(&stt, &muts_name);
    stt.env.register_name(
      muts_name,
      Named::new(
        block_addr.clone(),
        ConstantMeta::new(ConstantMetaInfo::Muts {
          all: vec![vec![f_addr_name.clone()]],
          aux_layout: None,
        }),
      ),
    );

    // Store the DPrj projection.
    let proj = Constant::new(ConstantInfo::DPrj(DefinitionProj {
      idx: 0,
      block: block_addr,
    }));
    let mut proj_bytes = Vec::new();
    proj.put(&mut proj_bytes);
    let proj_addr = Address::hash(&proj_bytes);
    stt.env.store_const(proj_addr.clone(), proj);

    // Register the projection's Named entry. Its meta carries the Defn's
    // arena + roots, PLUS the critical `meta_sharing` extension that the
    // bug makes invisible to decompile_projection.
    let mut meta = ConstantMeta::new(ConstantMetaInfo::Def {
      name: f_addr_name.clone(),
      lvls: vec![],
      hints: ReducibilityHints::Opaque,
      all: vec![f_addr_name.clone()],
      ctx: vec![f_addr_name.clone()],
      arena,
      type_root,
      value_root,
    });
    meta.meta_sharing = vec![collapsed_arg];
    stt.env.register_name(f_name.clone(), Named::new(proj_addr, meta));

    // Drive the full decompile_env path — this is what Pass 1 does in
    // production. Before the fix, decompile_projection omitted
    // load_meta_extensions, so cache.meta_sharing stayed empty and the
    // Collapsed lookup returned InvalidShareIndex.
    let dstt = decompile_env(&stt).expect(
      "decompile_env must succeed — pre-fix, the projection's meta_sharing \
       was never loaded and the Collapsed lookup failed with InvalidShareIndex",
    );

    // The decompiled `f` should exist and its value should be
    // `App(App(head, target_ref), bvar(77))` — source-order App with the
    // collapsed motive materialized from meta_sharing, then the Kept
    // major preserved.
    let entry = dstt.env.get(&f_name).expect("f not in decompiled env");
    match &*entry {
      LeanConstantInfo::DefnInfo(dv) => {
        let (head_lean, args) = lean_telescope(&dv.value);
        match head_lean.as_data() {
          crate::ix::env::ExprData::Const(name, _, _) => {
            assert_eq!(
              *name, head_name,
              "CallSite head should decode as `head`"
            );
          },
          other => panic!("expected head Const, got {other:?}"),
        }
        assert_eq!(args.len(), 2, "CallSite had 2 entries -> 2 app args");
        match args[0].as_data() {
          crate::ix::env::ExprData::Const(name, _, _) => {
            assert_eq!(
              *name, target_name,
              "Collapsed arg must resolve via loaded meta_sharing[0]"
            );
          },
          other => {
            panic!("expected Collapsed arg Const(target), got {other:?}")
          },
        }
        assert_eq!(
          bvar_idx(&args[1]).expect("major should be a bvar"),
          77,
          "Kept major must preserve Var(77)"
        );
      },
      other => panic!(
        "expected DefnInfo for f, got {:?}",
        std::mem::discriminant(other)
      ),
    }

    // Silence unused-field warning for Level: the CompileState/Univ
    // machinery pulls univs via the cache, not via `Level`, but we
    // imported it for symmetry with the production callers.
    let _ = Level::zero();
  }
}
