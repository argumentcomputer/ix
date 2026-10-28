//! Decompilation from Ixon format back to Lean environment.
//!
//! This module decompiles alpha-invariant Ixon representations back to
//! Lean constants, expanding Share references and reattaching metadata.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::map_err_ignore)]
#![allow(clippy::match_same_arms)]

use bignat::Nat;

use ix_common::address::Address;
use ix_common::env::{
  AxiomVal, BinderInfo, ConstantInfo as LeanConstantInfo, ConstantVal,
  ConstructorVal, DataValue as LeanDataValue, DefinitionSafety, DefinitionVal,
  Env as LeanEnv, Expr as LeanExpr, InductiveVal, Int, Level, Literal, Name,
  OpaqueVal, QuotVal, RecursorRule as LeanRecursorRule, RecursorVal,
  ReducibilityHints, SourceInfo, Substring, Syntax, SyntaxPreresolved,
  TheoremVal,
};

use ixon::{
  DecompileError, TagN,
  constant::{
    Axiom, Constant, ConstantInfo, Constructor, DefKind, Definition, Inductive,
    MutConst, Quotient, Recursor,
  },
  env::Named,
  expr::Expr,
  metadata::{
    ConstantMeta, ConstantMetaInfo, DataValue, ExprMeta, ExprMetaData, KVMap,
  },
  univ::Univ,
};

use crate::{
  compile::CompileState,
  compile::ind_flags::compute_lean_ind_flags,
  diag::rss_log_suffix,
  mutual::{MutCtx, all_to_ctx},
};
use dashmap::DashMap;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

#[derive(Default, Debug)]
pub struct DecompileState {
  /// Decompiled environment
  pub env: DashMap<Name, LeanConstantInfo>,
  /// Canonical expression nodes keyed by content hash. Decompilation
  /// rebuilds every constant's expressions with sharing local to that
  /// constant, so structurally equal subterms (common types, applied
  /// prefixes) would otherwise each hold a private copy per referencing
  /// constant — a multiple of the whole env's footprint. Constants
  /// entering `env` are canonicalized through this table
  /// ([`Self::insert_interned`]); `decompile_env` drops the table
  /// before returning, since `env` keeps the canonical `Arc`s alive.
  expr_intern: DashMap<[u8; 32], LeanExpr>,
}

#[derive(Debug)]
pub struct DecompileStateStats {
  pub env: usize,
}

impl DecompileState {
  pub fn stats(&self) -> DecompileStateStats {
    DecompileStateStats { env: self.env.len() }
  }

  /// Insert a decompiled constant, canonicalizing its expressions
  /// through [`Self::expr_intern`].
  fn insert_interned(&self, name: Name, ci: LeanConstantInfo) {
    self.env.insert(name, self.intern_ci(ci));
  }

  /// Canonicalize every expression field of `ci` — see
  /// [`Self::expr_intern`].
  fn intern_ci(&self, mut ci: LeanConstantInfo) -> LeanConstantInfo {
    match &mut ci {
      LeanConstantInfo::AxiomInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
      },
      LeanConstantInfo::DefnInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
        v.value = self.intern_expr(&v.value);
      },
      LeanConstantInfo::ThmInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
        v.value = self.intern_expr(&v.value);
      },
      LeanConstantInfo::OpaqueInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
        v.value = self.intern_expr(&v.value);
      },
      LeanConstantInfo::QuotInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
      },
      LeanConstantInfo::InductInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
      },
      LeanConstantInfo::CtorInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
      },
      LeanConstantInfo::RecInfo(v) => {
        v.cnst.typ = self.intern_expr(&v.cnst.typ);
        for rule in &mut v.rules {
          rule.rhs = self.intern_expr(&rule.rhs);
        }
      },
    }
    ci
  }

  /// Canonicalize one expression DAG bottom-up through
  /// [`Self::expr_intern`]. Iterative — proof terms nest far deeper
  /// than the stack allows for recursion. Nodes are rebuilt only when
  /// a child changed; hashes are content-derived from child hashes, so
  /// a rebuild with content-equal children reuses the stored hash.
  fn intern_expr(&self, root: &LeanExpr) -> LeanExpr {
    use ix_common::env::ExprData as ED;

    if let Some(hit) = self.expr_intern.get(root.get_hash().as_bytes()) {
      return hit.clone();
    }

    // Per-walk memo keyed by node pointer: within-constant sharing
    // makes the same `Arc` reachable from several parents.
    let mut memo: FxHashMap<*const ED, LeanExpr> = FxHashMap::default();
    // (node, children_done)
    let mut stack: Vec<(LeanExpr, bool)> = vec![(root.clone(), false)];

    while let Some((e, children_done)) = stack.pop() {
      let key: *const ED = Arc::as_ptr(&e.0);
      if memo.contains_key(&key) {
        continue;
      }
      if !children_done {
        if let Some(hit) = self.expr_intern.get(e.get_hash().as_bytes()) {
          memo.insert(key, hit.clone());
          continue;
        }
        stack.push((e.clone(), true));
        match e.as_data() {
          ED::App(f, a, _) => {
            stack.push((f.clone(), false));
            stack.push((a.clone(), false));
          },
          ED::Lam(_, t, b, _, _) | ED::ForallE(_, t, b, _, _) => {
            stack.push((t.clone(), false));
            stack.push((b.clone(), false));
          },
          ED::LetE(_, t, v, b, _, _) => {
            stack.push((t.clone(), false));
            stack.push((v.clone(), false));
            stack.push((b.clone(), false));
          },
          ED::Mdata(_, inner, _) => stack.push((inner.clone(), false)),
          ED::Proj(_, _, s, _) => stack.push((s.clone(), false)),
          ED::Bvar(..)
          | ED::Fvar(..)
          | ED::Mvar(..)
          | ED::Sort(..)
          | ED::Const(..)
          | ED::Lit(..) => {},
        }
        continue;
      }

      // Children are canonicalized (they were pushed after this node's
      // revisit frame, so they popped first).
      let child = |c: &LeanExpr| -> LeanExpr {
        memo
          .get(&Arc::as_ptr(&c.0))
          .expect("intern walk: child not canonicalized before parent")
          .clone()
      };
      let same =
        |c: &LeanExpr, i: &LeanExpr| -> bool { Arc::ptr_eq(&c.0, &i.0) };
      let rebuilt = match e.as_data() {
        ED::App(f, a, h) => {
          let (fi, ai) = (child(f), child(a));
          if same(f, &fi) && same(a, &ai) {
            e.clone()
          } else {
            LeanExpr(Arc::new(ED::App(fi, ai, *h)))
          }
        },
        ED::Lam(n, t, b, bi, h) => {
          let (ti, bdi) = (child(t), child(b));
          if same(t, &ti) && same(b, &bdi) {
            e.clone()
          } else {
            LeanExpr(Arc::new(ED::Lam(n.clone(), ti, bdi, bi.clone(), *h)))
          }
        },
        ED::ForallE(n, t, b, bi, h) => {
          let (ti, bdi) = (child(t), child(b));
          if same(t, &ti) && same(b, &bdi) {
            e.clone()
          } else {
            LeanExpr(Arc::new(ED::ForallE(n.clone(), ti, bdi, bi.clone(), *h)))
          }
        },
        ED::LetE(n, t, v, b, nd, h) => {
          let (ti, vi, bdi) = (child(t), child(v), child(b));
          if same(t, &ti) && same(v, &vi) && same(b, &bdi) {
            e.clone()
          } else {
            LeanExpr(Arc::new(ED::LetE(n.clone(), ti, vi, bdi, *nd, *h)))
          }
        },
        ED::Mdata(kv, inner, h) => {
          let ii = child(inner);
          if same(inner, &ii) {
            e.clone()
          } else {
            LeanExpr(Arc::new(ED::Mdata(kv.clone(), ii, *h)))
          }
        },
        ED::Proj(n, i, s, h) => {
          let si = child(s);
          if same(s, &si) {
            e.clone()
          } else {
            LeanExpr(Arc::new(ED::Proj(n.clone(), i.clone(), si, *h)))
          }
        },
        ED::Bvar(..)
        | ED::Fvar(..)
        | ED::Mvar(..)
        | ED::Sort(..)
        | ED::Const(..)
        | ED::Lit(..) => e.clone(),
      };
      let canonical = self
        .expr_intern
        .entry(*e.get_hash().as_bytes())
        .or_insert(rebuilt)
        .clone();
      memo.insert(key, canonical);
    }

    memo
      .remove(&Arc::as_ptr(&root.0))
      .expect("intern walk: root not canonicalized")
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
///   table. Its indices also start at 0 but live in a SEPARATE namespace
///   from the block sharing, reset per constant (see [`ShareScope`]).
#[derive(Default, Debug)]
pub struct BlockCache {
  /// Mutual context for resolving Rec references
  pub ctx: MutCtx,
  /// Block-level sharing table: target of `Expr::Share(idx)` in
  /// the block body exprs. Initialized from
  /// `Constant.sharing`.
  pub sharing: Vec<Arc<Expr>>,
  /// Per-constant metadata sharing table. Populated by
  /// `load_meta_extensions` from `ConstantMeta.meta_sharing`. `Share` nodes
  /// inside these expressions are read in the extended index space
  /// (`ShareScope::Meta`).
  pub meta_sharing: Vec<Arc<Expr>>,
  /// Reference table for resolving Ref indices to addresses
  pub refs: Vec<Address>,
  /// Universe table for resolving universe indices
  pub univ_table: Vec<Arc<Univ>>,
  /// Level-spelling patches of the current constant, keyed by metadata
  /// arena index (canonicity §10.6). A patched `sort`/`const`/`rec`
  /// occurrence resolves the patch's
  /// virtual univ indices — through `univ_table`, which
  /// `load_meta_extensions` extends with `meta_univs` — instead of the
  /// node's own canonical indices. Absent patch → the canonical
  /// spelling from the primary table (the D4 foreign-artifact
  /// semantics). Populated by `load_meta_extensions` from
  /// `ConstantMeta.univ_patches`.
  pub univ_patches: FxHashMap<u64, Vec<u64>>,
  /// Length of the PRIMARY univ table before `load_meta_extensions`
  /// appended the constant's `meta_univs`. Virtual indices are minted
  /// against the primary length, so nested per-constant extensions (the
  /// constructor window inside an inductive) must reinstall at this
  /// offset — not at the currently-extended length. `None` until
  /// extensions are loaded (then the full table IS primary).
  pub primary_univ_len: Option<usize>,
  /// Cache for decompiled universes
  pub univ_cache: FxHashMap<*const Univ, Level>,
  /// Cache for decompiled expressions keyed by (Ixon pointer, arena index,
  /// share scope).
  /// Same Ixon expression at same arena index → same metadata → same result.
  /// Same Ixon expression at different arena index → different metadata → different cache key.
  /// The scope is part of the key because an expression valid in a
  /// metadata scope may be invalid in the primary scope.
  pub expr_cache: FxHashMap<(*const Expr, u64, ShareScope), LeanExpr>,
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
  /// - `meta_refs` extends the primary refs table when present (the
  ///   documented virtual-address contract).
  /// - `meta_univs` extends the primary univ table: the stage-2 compiler
  ///   stores original (non-canonical) level spellings here, referenced
  ///   by `univ_patches` in the virtual index space `univs ++
  ///   meta_univs` (canonicity §10.6).
  /// - `univ_patches` → per-constant arena-index → original-spelling-
  ///   indices map (overwrite semantics, like `meta_sharing`).
  ///
  /// Call at most once per cache, immediately after the primary tables
  /// are installed — `primary_univ_len` is captured here, and
  /// `meta_sharing` is checked against the primary `sharing` length
  /// (`validate_meta_sharing`): a malformed table is rejected here even
  /// where decompilation never reads it.
  pub fn load_meta_extensions(
    &mut self,
    meta: &ConstantMeta,
  ) -> Result<(), DecompileError> {
    validate_meta_sharing(
      self.sharing.len(),
      &meta.meta_sharing,
      &self.current_const,
    )?;
    self.meta_sharing = meta.meta_sharing.clone();
    self.refs.extend(meta.meta_refs.iter().cloned());
    self.primary_univ_len = Some(self.univ_table.len());
    self.univ_table.extend(meta.meta_univs.iter().cloned());
    self.univ_patches = meta
      .univ_patches
      .iter()
      .map(|p| (p.arena_idx, p.univ_idxs.clone()))
      .collect();
    Ok(())
  }

  /// Resolve `Share(idx)` read in `scope` (see [`ShareScope`]): the target
  /// expression and the scope its own `Share` nodes are read in. Mirrors
  /// Lean `Ix.DecompileM.resolveShareIn`.
  pub fn resolve_share(
    &self,
    scope: ShareScope,
    idx: u64,
  ) -> Result<(Arc<Expr>, ShareScope), DecompileError> {
    let p = self.sharing.len();
    let i = usize::try_from(idx).ok();
    if let Some(e) = i.and_then(|i| self.sharing.get(i)) {
      // `i < p`: a primary entry in either scope; its own shares are
      // primary again.
      return Ok((e.clone(), ShareScope::Primary));
    }
    match scope {
      ShareScope::Primary => Err(DecompileError::InvalidShareIndex {
        idx,
        max: p,
        constant: self.current_const.clone(),
      }),
      ShareScope::Meta { entry } => {
        // `i >= p` here; only `p <= i < p + entry` (an EARLIER metadata
        // entry) is valid.
        let target = i
          .map(|i| i - p)
          .filter(|m| *m < entry)
          .and_then(|m| self.meta_sharing.get(m).map(|e| (m, e)));
        match target {
          Some((m, e)) => Ok((e.clone(), ShareScope::Meta { entry: m })),
          None => Err(DecompileError::InvalidMetaShareIndex {
            idx,
            entry: entry as u64,
            primary_len: p,
            meta_len: self.meta_sharing.len(),
            constant: self.current_const.clone(),
          }),
        }
      },
    }
  }
}

/// The index space a `Share(i)` node is read in: the extended index space
/// of `ConstantMeta::meta_sharing`. With `p = sharing.len()` primary and
/// `q = meta_sharing.len()` metadata entries:
///
/// - `Primary`: a primary expression (a root or a primary table entry).
///   `Share(i)` is `sharing[i]`; `i >= p` is `InvalidShareIndex`. Metadata
///   never changes how a primary expression decodes.
/// - `Meta { entry: j }`: an expression of `meta_sharing[j]`. `Share(i)` is
///   primary entry `i` when `i < p` (read in `Primary`: shares nested in a
///   primary entry stay primary) and `meta_sharing[i - p]` when
///   `p <= i < p + j` (read in `Meta { entry: i - p }`). Any other index is
///   `InvalidMetaShareIndex`: `i >= p + q` is out of range,
///   `p + j <= i < p + q` a forward or self reference. The entry strictly
///   decreases along metadata-to-metadata resolution, so expansion is well
///   founded.
///
/// Mirrors Lean `Ix.DecompileM.ShareScope`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShareScope {
  Primary,
  Meta { entry: usize },
}

/// Well-foundedness of a `meta_sharing` table against `primary_len`
/// primary entries: every `Share(i)` occurring in `meta_sharing[j]` must
/// have `i < primary_len + j` (a primary entry, or a metadata entry BEFORE
/// `j`). Reports the first violation in entry order, then in left-to-right
/// pre-order, as `InvalidMetaShareIndex` (Lean `validateMetaSharing` walks
/// in the same order). Iterative; `Share` nodes are not expanded.
///
/// Each shared node (`Arc`) is visited once across the whole table, so the
/// walk is linear in the DAG size: in-memory tables share subterms through
/// the compiler's expression memo, and a tree walk is exponential in the
/// depth of such sharing. Skipping a node seen before keeps the first
/// violation: its whole subterm passed then, under a bound no larger than
/// the current one (the bound grows with the entry).
pub fn validate_meta_sharing(
  primary_len: usize,
  meta_sharing: &[Arc<Expr>],
  constant: &str,
) -> Result<(), DecompileError> {
  let mut stack: Vec<&Arc<Expr>> = Vec::new();
  let mut seen: FxHashSet<*const Expr> = FxHashSet::default();
  for (j, root) in meta_sharing.iter().enumerate() {
    let bound = primary_len.saturating_add(j);
    stack.push(root);
    while let Some(e) = stack.pop() {
      if !seen.insert(Arc::as_ptr(e)) {
        continue;
      }
      if let Expr::Share(i) = e.as_ref() {
        if !matches!(usize::try_from(*i), Ok(i) if i < bound) {
          return Err(DecompileError::InvalidMetaShareIndex {
            idx: *i,
            entry: j as u64,
            primary_len,
            meta_len: meta_sharing.len(),
            constant: constant.to_string(),
          });
        }
      } else {
        stack.extend(e.children().into_iter().rev());
      }
    }
  }
  Ok(())
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

/// Read a Constant from the const store, materializing the lazy entry.
fn read_const(
  addr: &Address,
  stt: &CompileState,
) -> Result<Arc<Constant>, DecompileError> {
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

/// Read a TagN (f = 0) u64 from a byte slice, advancing the cursor.
fn read_tagn0(buf: &mut &[u8]) -> Result<u64, DecompileError> {
  TagN::get(0, buf).map(|t| t.value).map_err(|e| {
    DecompileError::BadConstantFormat { msg: format!("read_tagn0: {e}") }
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
  let start_pos = Nat::from(read_tagn0(buf)?);
  let stop_pos = Nat::from(read_tagn0(buf)?);
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
      let leading_pos = Nat::from(read_tagn0(buf)?);
      let trailing = deserialize_substring(buf, stt)?;
      let trailing_pos = Nat::from(read_tagn0(buf)?);
      Ok(SourceInfo::Original(leading, leading_pos, trailing, trailing_pos))
    },
    1 => {
      let start = Nat::from(read_tagn0(buf)?);
      let end = Nat::from(read_tagn0(buf)?);
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
      let count = read_tagn0(buf)? as usize;
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
      let arg_count = read_tagn0(buf)? as usize;
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
      let pr_count = read_tagn0(buf)? as usize;
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

  enum Frame {
    /// Decompile an Ixon expression read in a share scope at an arena index.
    Decompile(Arc<Expr>, u64, ShareScope),
    BuildApp(LeanMdata),
    BuildLam(Name, BinderInfo, LeanMdata),
    BuildAll(Name, BinderInfo, LeanMdata),
    BuildLet(Name, bool, LeanMdata),
    BuildProj(Name, Nat, LeanMdata),
    CacheResult(*const Expr, u64, ShareScope),
  }

  // The root is a primary expression.
  let mut stack: Vec<Frame> =
    vec![Frame::Decompile(expr.clone(), arena_idx, ShareScope::Primary)];
  let mut results: Vec<LeanExpr> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Decompile(e, idx, scope) => {
        // Expand Share transparently with the SAME arena_idx, in the
        // target's scope.
        if let Expr::Share(share_idx) = e.as_ref() {
          let (shared_expr, shared_scope) =
            cache.resolve_share(scope, *share_idx)?;
          stack.push(Frame::Decompile(shared_expr, idx, shared_scope));
          continue;
        }

        // Cache check: (Ixon pointer, arena index, share scope)
        let cache_key = (Arc::as_ptr(&e), idx, scope);
        if let Some(cached) = cache.expr_cache.get(&cache_key) {
          results.push(cached.clone());
          continue;
        }

        // Follow Mdata chain in arena, collecting mdata layers.
        let mut current_idx = idx;
        let mut mdata_layers: LeanMdata = Vec::new();
        while let ExprMetaData::Mdata { mdata, child } =
          arena_lookup(arena, current_idx, &cache.current_const)?
        {
          for kvm in mdata {
            let data = decompile_kvmap(kvm, stt)?;
            if crate::semantic_contract::has_metadata(&data) {
              return Err(DecompileError::BadConstantFormat {
                msg: "semantic contracts cannot come from optional metadata"
                  .into(),
              });
            }
            mdata_layers.push(data);
          }
          current_idx = *child;
        }

        let node = arena_lookup(arena, current_idx, &cache.current_const)?;

        // Push CacheResult frame
        stack.push(Frame::CacheResult(Arc::as_ptr(&e), idx, scope));

        if let Some(contract) = crate::semantic_contract::of_ixon(&e) {
          mdata_layers.push(contract.metadata());
        }
        match (node, e.as_ref()) {
          // Leaf nodes: Var, Sort, Nat, Str
          (_, Expr::Var(v)) => {
            let expr = apply_mdata(LeanExpr::bvar(Nat::from(*v)), mdata_layers);
            results.push(expr);
          },

          (_, Expr::Sort(univ_idx)) => {
            // Level-spelling patch replay (canonicity §10.6): a patch
            // keyed by this occurrence's arena index restores the
            // original spelling via its virtual univ index.
            let eff_idx = cache
              .univ_patches
              .get(&current_idx)
              .and_then(|idxs| idxs.first())
              .copied()
              .unwrap_or(*univ_idx);
            let univ = cache
              .univ_table
              .get(eff_idx as usize)
              .ok_or_else(|| DecompileError::InvalidUnivIndex {
                idx: eff_idx,
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
            // Level-spelling patch replay (canonicity §10.6): the patch
            // carries the FULL level-arg list in the virtual index space.
            let patch = cache.univ_patches.get(&current_idx).cloned();
            let levels = match &patch {
              Some(idxs) => decompile_univ_indices(idxs, lvl_names, cache)?,
              None => decompile_univ_indices(univ_indices, lvl_names, cache)?,
            };
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
            // Level-spelling patch replay (canonicity §10.6).
            let patch = cache.univ_patches.get(&current_idx).cloned();
            let levels = match &patch {
              Some(idxs) => decompile_univ_indices(idxs, lvl_names, cache)?,
              None => decompile_univ_indices(univ_indices, lvl_names, cache)?,
            };
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
            // Level-spelling patch replay (canonicity §10.6).
            let patch = cache.univ_patches.get(&current_idx).cloned();
            let levels = match &patch {
              Some(idxs) => decompile_univ_indices(idxs, lvl_names, cache)?,
              None => decompile_univ_indices(univ_indices, lvl_names, cache)?,
            };
            let expr = apply_mdata(LeanExpr::cnst(name, levels), mdata_layers);
            results.push(expr);
          },

          // App: follow arena children
          (ExprMetaData::App { children }, Expr::App(f, a)) => {
            stack.push(Frame::BuildApp(mdata_layers));
            stack.push(Frame::Decompile(a.clone(), children[1], scope));
            stack.push(Frame::Decompile(f.clone(), children[0], scope));
          },

          (_, Expr::App(f, a)) => {
            // No App metadata — use dummy indices (Leaf fallback)
            stack.push(Frame::BuildApp(mdata_layers));
            stack.push(Frame::Decompile(a.clone(), u64::MAX, scope));
            stack.push(Frame::Decompile(f.clone(), u64::MAX, scope));
          },

          // Lam: extract binder name/info from arena
          (
            ExprMetaData::Binder { name: name_addr, info, children },
            Expr::Lam(_, ty, body),
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
            stack.push(Frame::Decompile(body.clone(), children[1], scope));
            stack.push(Frame::Decompile(ty.clone(), children[0], scope));
          },

          (_, Expr::Lam(_, ty, body)) => {
            stack.push(Frame::BuildLam(
              Name::anon(),
              BinderInfo::Default,
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), u64::MAX, scope));
            stack.push(Frame::Decompile(ty.clone(), u64::MAX, scope));
          },

          // All: extract binder name/info from arena
          (
            ExprMetaData::Binder { name: name_addr, info, children },
            Expr::All(_, _, ty, body),
          ) => {
            // See Lam arm above: binder address must resolve.
            let binder_name = decompile_name(name_addr, stt)?;
            stack.push(Frame::BuildAll(
              binder_name,
              info.clone(),
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), children[1], scope));
            stack.push(Frame::Decompile(ty.clone(), children[0], scope));
          },

          (_, Expr::All(_, _, ty, body)) => {
            stack.push(Frame::BuildAll(
              Name::anon(),
              BinderInfo::Default,
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), u64::MAX, scope));
            stack.push(Frame::Decompile(ty.clone(), u64::MAX, scope));
          },

          // Let: extract name from arena
          (
            ExprMetaData::LetBinder { name: name_addr, children },
            Expr::Let(non_dep, ty, val, body),
          ) => {
            // See Lam arm above: binder address must resolve.
            let let_name = decompile_name(name_addr, stt)?;
            stack.push(Frame::BuildLet(
              let_name,
              non_dep.non_dep,
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), children[2], scope));
            stack.push(Frame::Decompile(val.clone(), children[1], scope));
            stack.push(Frame::Decompile(ty.clone(), children[0], scope));
          },

          (_, Expr::Let(non_dep, ty, val, body)) => {
            stack.push(Frame::BuildLet(
              Name::anon(),
              non_dep.non_dep,
              mdata_layers,
            ));
            stack.push(Frame::Decompile(body.clone(), u64::MAX, scope));
            stack.push(Frame::Decompile(val.clone(), u64::MAX, scope));
            stack.push(Frame::Decompile(ty.clone(), u64::MAX, scope));
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
            stack.push(Frame::Decompile(struct_val.clone(), *child, scope));
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

      Frame::CacheResult(e_ptr, arena_idx, scope) => {
        if let Some(result) = results.last() {
          cache.expr_cache.insert((e_ptr, arena_idx, scope), result.clone());
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

  let all = match &meta.info {
    ConstantMetaInfo::Def { all, .. } => {
      let all_names: Result<Vec<Name>, _> =
        all.iter().map(|a| decompile_name(a, stt)).collect();
      all_names?
    },
    _ => vec![],
  };
  // Hints come from the per-name `Named.hints` channel — the exact
  // value `finalize_hints` recorded for this name. The per-address
  // `env.anon_hints` channel is unusable here: alpha-identical
  // definitions under different names share one constant address, so
  // it only holds a merged winner. Absent → `Opaque`, matching the
  // compiler's treatment of theorems and opaques.
  let hints = stt
    .env
    .named
    .get(&name)
    .and_then(|n| n.value().hints())
    .unwrap_or(ReducibilityHints::Opaque);

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
    // Clear the pointer-keyed univ memo too (canonicity §10.6): the
    // constructor window below swaps per-ctor `meta_univs` extensions in
    // and out of `univ_table`, so `*const Univ` keys minted under one
    // ctor's extension can be REUSED by a fresh allocation in a later
    // iteration — a stale hit then substitutes an arbitrary earlier
    // level for the patched spelling. (Pre-stage-2 `meta_univs` was
    // always empty, so the memo never saw ephemeral pointers.)
    cache.univ_cache.clear();

    // Look up constructor's Named entry for its ConstantMetaInfo::Ctor
    let ctor_meta = if let Some(addr) = ctor_name_addrs.get(i) {
      if let Ok(ctor_name) = decompile_name(addr, stt) {
        stt
          .env
          .named
          .get(&ctor_name)
          .map(|n| (*n.meta()).clone())
          .unwrap_or_default()
      } else {
        ConstantMeta::default()
      }
    } else {
      ConstantMeta::default()
    };

    // Constructor metadata is per-constructor, not inherited from the parent
    // inductive. In particular, a constructor carries its own
    // `meta_sharing` table and its own `univ_patches` (canonicity §10.6).
    // Install those extensions only while
    // walking this constructor so they do not leak across sibling
    // constructor arenas. The constructor's `meta_sharing` is checked
    // against the block's primary table, as `load_meta_extensions` does.
    validate_meta_sharing(
      cache.sharing.len(),
      &ctor_meta.meta_sharing,
      &cache.current_const,
    )?;
    let saved_meta_sharing = std::mem::replace(
      &mut cache.meta_sharing,
      ctor_meta.meta_sharing.clone(),
    );
    let saved_univ_patches = std::mem::replace(
      &mut cache.univ_patches,
      ctor_meta
        .univ_patches
        .iter()
        .map(|p| (p.arena_idx, p.univ_idxs.clone()))
        .collect(),
    );
    let refs_len = cache.refs.len();
    // Virtual univ indices are minted against the PRIMARY table length
    // (canonicity §10.6), so the constructor's `meta_univs` must be
    // installed at that offset — the parent inductive's own extension
    // (appended by `load_meta_extensions`) is displaced for the
    // duration, and the whole table is restored afterwards.
    let primary_univ_len =
      cache.primary_univ_len.unwrap_or(cache.univ_table.len());
    let saved_univ_table = cache.univ_table.clone();
    cache.refs.extend(ctor_meta.meta_refs.iter().cloned());
    cache.univ_table.truncate(primary_univ_len);
    cache.univ_table.extend(ctor_meta.meta_univs.iter().cloned());

    let ctor_result =
      decompile_constructor(ctor, &ctor_meta, name.clone(), cache, stt, dstt);

    cache.meta_sharing = saved_meta_sharing;
    cache.univ_patches = saved_univ_patches;
    cache.refs.truncate(refs_len);
    cache.univ_table = saved_univ_table;

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
    num_nested: Nat::from(0u64),
    is_rec: false,
    is_reflexive: false,
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
  let named_meta = named.meta();
  let ctx_addrs = get_ctx_from_meta(&named_meta);
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
  // Projection metadata can carry the metadata extensions; load them for
  // the projection's own arena.
  cache.load_meta_extensions(&named_meta)?;

  // Each projection variant must land on the matching `MutConst` kind
  // at its block index. A silent fall-through would leave `name`
  // unregistered in `dstt.env`, and downstream references would fail
  // far from the real point of corruption.
  match &cnst.info {
    ConstantInfo::DPrj(proj) => match mutuals.get(proj.idx as usize) {
      Some(MutConst::Defn(def)) => {
        let info =
          decompile_definition(def, &named_meta, &mut cache, stt, dstt)?;
        dstt.insert_interned(name.clone(), info);
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
          decompile_inductive(ind, &named_meta, &mut cache, stt, dstt)?;
        dstt
          .insert_interned(name.clone(), LeanConstantInfo::InductInfo(ind_val));
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
        let info = decompile_recursor(rec, &named_meta, &mut cache, stt, dstt)?;
        dstt.insert_interned(name.clone(), info);
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
  let has_original = stt.env.named.get(name).is_some_and(|n| n.has_original());
  DecompileError::BadConstantFormat {
    msg: format!(
      "{kind} '{}' idx={idx} landed on {:?} (mutuals.len={mutuals_len}, \
       addr={has_addr}, has_original={has_original})",
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
  let named_meta = named.meta();
  let all_addrs = get_all_from_meta(&named_meta);
  let all_names: Vec<Name> = all_addrs
    .iter()
    .map(|a| decompile_name(a, stt))
    .collect::<Result<Vec<_>, _>>()?;
  let ctx = all_to_ctx(&all_names);
  let current_const = name.pretty();

  match cnst.as_ref() {
    Constant { info: ConstantInfo::Defn(def), sharing, refs, univs } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx: ctx.clone(),
        current_const: current_const.clone(),
        ..Default::default()
      };
      cache.load_meta_extensions(&named_meta)?;
      let info = decompile_definition(def, &named_meta, &mut cache, stt, dstt)?;
      dstt.insert_interned(name.clone(), info);
    },

    Constant { info: ConstantInfo::Recr(rec), sharing, refs, univs } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx: ctx.clone(),
        current_const: current_const.clone(),
        ..Default::default()
      };
      // Recursor rule RHSs can carry metadata extensions, as in the Defn
      // branch above.
      cache.load_meta_extensions(&named_meta)?;
      let info = decompile_recursor(rec, &named_meta, &mut cache, stt, dstt)?;
      dstt.insert_interned(name.clone(), info);
    },

    Constant { info: ConstantInfo::Axio(ax), sharing, refs, univs } => {
      let mut cache = BlockCache {
        sharing: sharing.clone(),
        refs: refs.clone(),
        univ_table: univs.clone(),
        ctx: ctx.clone(),
        current_const: current_const.clone(),
        ..Default::default()
      };
      // Load extensions for consistency with the other branches.
      cache.load_meta_extensions(&named_meta)?;
      let info = decompile_axiom(ax, &named_meta, &mut cache, stt, dstt)?;
      dstt.insert_interned(name.clone(), info);
    },

    Constant { info: ConstantInfo::Quot(quot), sharing, refs, univs } => {
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
      cache.load_meta_extensions(&named_meta)?;
      let info = decompile_quotient(quot, &named_meta, &mut cache, stt, dstt)?;
      dstt.insert_interned(name.clone(), info);
    },

    Constant { info: ConstantInfo::DPrj(_), .. }
    | Constant { info: ConstantInfo::IPrj(_), .. }
    | Constant { info: ConstantInfo::RPrj(_), .. }
    | Constant { info: ConstantInfo::CPrj(_), .. } => {
      // Projections are handled by `decompile_projection`
    },

    Constant { info: ConstantInfo::Muts(_), .. } => {
      // Mutual blocks are handled separately
    },
  }

  Ok(())
}

// ===========================================================================
// Per-constant helpers
// ===========================================================================

/// Decompile a single named constant into the decompile state.
///
/// Dispatches on the constant kind (definition, recursor, axiom, quotient,
/// projection).
fn decompile_named_const(
  name: &Name,
  named: &Named,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  if let Some(cnst) = stt.env.get_const(&named.addr) {
    match &cnst.info {
      // Direct constants - decompile immediately
      ConstantInfo::Defn(_)
      | ConstantInfo::Recr(_)
      | ConstantInfo::Axio(_)
      | ConstantInfo::Quot(_) => decompile_const(name, named, stt, dstt),

      // Projections - get the block and decompile
      ConstantInfo::DPrj(proj) => {
        match stt.env.get_const(&proj.block).as_deref() {
          Some(Constant {
            info: ConstantInfo::Muts(mutuals),
            sharing,
            refs,
            univs,
          }) => decompile_projection(
            name, named, &cnst, mutuals, sharing, refs, univs, stt, dstt,
          ),
          _ => Err(DecompileError::MissingAddress(proj.block.clone())),
        }
      },

      ConstantInfo::IPrj(proj) => {
        match stt.env.get_const(&proj.block).as_deref() {
          Some(Constant {
            info: ConstantInfo::Muts(mutuals),
            sharing,
            refs,
            univs,
          }) => decompile_projection(
            name, named, &cnst, mutuals, sharing, refs, univs, stt, dstt,
          ),
          _ => Err(DecompileError::MissingAddress(proj.block.clone())),
        }
      },

      ConstantInfo::RPrj(proj) => {
        match stt.env.get_const(&proj.block).as_deref() {
          Some(Constant {
            info: ConstantInfo::Muts(mutuals),
            sharing,
            refs,
            univs,
          }) => decompile_projection(
            name, named, &cnst, mutuals, sharing, refs, univs, stt, dstt,
          ),
          _ => Err(DecompileError::MissingAddress(proj.block.clone())),
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

// ===========================================================================
// Main entry point
// ===========================================================================

/// Decompile an Ixon environment back to Lean format: every named constant
/// is decompiled in parallel (`decompile_named_const`), then each inductive
/// block's Lean flags are recomputed (`compute_lean_ind_flags`).
pub fn decompile_env(
  stt: &CompileState,
) -> Result<DecompileState, DecompileError> {
  let dstt = DecompileState::default();

  let t_constants = std::time::Instant::now();
  eprintln!(
    "[decompile] decompiling {} named constants in parallel...",
    stt.env.named.len(),
  );
  stt.env.named.par_iter().try_for_each(|entry| {
    let (name, named) = (entry.key(), entry.value());
    decompile_named_const(name, named, stt, &dstt)
  })?;
  eprintln!(
    "[decompile] constants done in {:.2}s ({} constants in dstt.env){}",
    t_constants.elapsed().as_secs_f32(),
    dstt.env.len(),
    rss_log_suffix(),
  );

  // Lean-faithful inductive flags. Scoped so `lean_env` — a full structured
  // copy of the environment used only by `compute_lean_ind_flags` — drops
  // here instead of living to the end of the function.
  let t_flags = std::time::Instant::now();
  let n_ind_groups = {
    let lean_env: ix_common::env::Env =
      dstt.env.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let mut groups: FxHashMap<Name, Vec<Name>> = FxHashMap::default();
    for entry in dstt.env.iter() {
      if let LeanConstantInfo::InductInfo(v) = entry.value()
        && let Some(first) = v.all.first()
      {
        groups.entry(first.clone()).or_insert_with(|| v.all.clone());
      }
    }
    for (key, all) in &groups {
      let flags = compute_lean_ind_flags(all, &lean_env).map_err(|e| {
        DecompileError::BadConstantFormat {
          msg: format!("ind-flags fixup for block '{}': {e}", key.pretty()),
        }
      })?;
      for member in all {
        if let Some(mut entry) = dstt.env.get_mut(member)
          && let LeanConstantInfo::InductInfo(v) = entry.value_mut()
        {
          v.num_nested = Nat::from(flags.num_nested);
          v.is_rec = flags.is_rec;
          v.is_reflexive = flags.is_reflexive;
        }
      }
    }
    groups.len()
  };
  eprintln!(
    "[decompile] inductive flags done in {:.2}s ({} inductive groups){}",
    t_flags.elapsed().as_secs_f32(),
    n_ind_groups,
    rss_log_suffix(),
  );

  // The intern table's job is done — `dstt.env` keeps the canonical
  // `Arc`s alive, and consumers only read `env`.
  let mut dstt = dstt;
  dstt.expr_intern = DashMap::new();

  Ok(dstt)
}

/// Select the source view of a decompiled environment, the one Lean import
/// restores (`rs_decompile_env_consts`, `import_ixe`). `requested` empty
/// selects every name; otherwise the requested names, which must be present
/// in `env`, and their reference closure. The reference closure is checked
/// for a full selection too, so a broken source reconstruction is refused:
/// every reference must be a present name. Sorted.
pub fn materialized_source_names(
  env: &DashMap<Name, LeanConstantInfo>,
  requested: &[Name],
) -> Result<Vec<Name>, String> {
  use crate::graph::{NameSet, get_constant_info_references};

  let roots: Vec<Name> = if requested.is_empty() {
    env.iter().map(|entry| entry.key().clone()).collect()
  } else {
    requested.to_vec()
  };
  let mut seen = NameSet::default();
  let mut worklist = Vec::new();
  for root in roots {
    if !env.contains_key(&root) {
      return Err(format!(
        "requested source constant '{}' not found",
        root.pretty()
      ));
    }
    if seen.insert(root.clone()) {
      worklist.push(root);
    }
  }
  while let Some(name) = worklist.pop() {
    let references = {
      let declaration = env.get(&name).ok_or_else(|| {
        format!(
          "source constant '{}' disappeared during selection",
          name.pretty()
        )
      })?;
      get_constant_info_references(declaration.value())
    };
    for reference in references {
      if seen.contains(&reference) {
        continue;
      }
      if !env.contains_key(&reference) {
        return Err(format!(
          "source constant '{}' references missing source constant '{}' — \
           broken closure",
          name.pretty(),
          reference.pretty()
        ));
      }
      seen.insert(reference.clone());
      worklist.push(reference);
    }
  }
  let mut selected: Vec<Name> = seen.into_iter().collect();
  selected.sort_unstable();
  Ok(selected)
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
  /// Constants of the original absent from the decompiled environment,
  /// sorted by pretty name. Expected only for inputs the compile left
  /// ungrounded; any other is a failure (`failures`).
  pub absent: Vec<Name>,
}

impl CheckResult {
  /// The round trip's failures: mismatches, names not in the original, and
  /// original constants absent from the decompiled environment other than
  /// those `expected_absent` accepts (the compile's ungrounded inputs).
  /// Each absence is printed.
  pub fn failures(&self, expected_absent: impl Fn(&Name) -> bool) -> usize {
    let unexpected: Vec<&Name> =
      self.absent.iter().filter(|n| !expected_absent(n)).collect();
    for n in &unexpected {
      eprintln!("check_decompile: FAIL absent from decompiled: {}", n.pretty());
    }
    self.mismatches + self.missing + unexpected.len()
  }
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
    match original.get(name).as_deref() {
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

  // Report constants in original but missing from decompiled.
  let mut absent: Vec<Name> = original
    .iter()
    .filter(|(name, _)| !dstt.env.contains_key(*name))
    .map(|(name, _)| name.clone())
    .collect();
  absent.sort_by_key(Name::pretty);
  if !absent.is_empty() {
    eprintln!(
      "check_decompile: {} constants missing from decompiled:",
      absent.len()
    );
    for name in &absent {
      eprintln!("  missing: {}", name.pretty());
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
    absent,
  };
  eprintln!(
    "check_decompile: {} matches, {} mismatches, {} not in original, {} \
     absent",
    result.matches,
    result.mismatches,
    result.missing,
    result.absent.len(),
  );

  Ok(result)
}

// ===========================================================================
// Regression tests for the decompiler
//
// These anchor the individual decompile-side invariants so a future change
// that breaks one of them trips immediately in `cargo test`.
// ===========================================================================

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::Level;

  fn import_view_axiom(name: Name, typ: LeanExpr) -> LeanConstantInfo {
    LeanConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal { name, level_params: vec![], typ },
      is_unsafe: false,
    })
  }

  /// A full selection keeps every name, including names that start with an
  /// underscore; a scoped one is the requested source closure.
  #[test]
  fn source_import_keeps_public_names_and_scoped_dependencies() {
    let env = DashMap::new();
    let root = Name::str(Name::anon(), "ImportView".into());
    let source = Name::str(root.clone(), "source".into());
    let dependency = Name::str(root.clone(), "dependency".into());
    let unrelated = Name::str(root, "unrelated_ix_name".into());
    let source_private =
      Name::str(Name::str(Name::anon(), "_private".into()), "original".into());
    for name in [&dependency, &unrelated, &source_private] {
      env.insert(
        name.clone(),
        import_view_axiom(name.clone(), LeanExpr::sort(Level::zero())),
      );
    }
    env.insert(
      source.clone(),
      import_view_axiom(
        source.clone(),
        LeanExpr::cnst(dependency.clone(), vec![]),
      ),
    );
    let mut all =
      vec![source.clone(), dependency.clone(), unrelated, source_private];
    all.sort_unstable();
    assert_eq!(materialized_source_names(&env, &[]).unwrap(), all);
    let mut scoped = vec![source.clone(), dependency];
    scoped.sort_unstable();
    assert_eq!(materialized_source_names(&env, &[source]).unwrap(), scoped);
  }

  /// A missing requested name and a dangling reference are refused, the
  /// latter for a full selection too.
  #[test]
  fn source_import_rejects_missing_roots_and_dependencies() {
    let env = DashMap::new();
    let source = Name::str(Name::anon(), "Source".into());
    let missing = Name::str(Name::anon(), "Missing".into());
    assert!(
      materialized_source_names(&env, std::slice::from_ref(&missing))
        .unwrap_err()
        .contains("not found")
    );
    env.insert(
      source.clone(),
      import_view_axiom(source.clone(), LeanExpr::cnst(missing, vec![])),
    );
    for roots in [vec![], vec![source]] {
      assert!(
        materialized_source_names(&env, &roots)
          .unwrap_err()
          .contains("broken closure")
      );
    }
  }

  /// A decompiled name that is not in the original counts as `missing` and
  /// is listed in `extra_names`.
  #[test]
  fn check_decompile_counts_names_not_in_the_original() {
    let source = Name::str(Name::anon(), "Source".into());
    let extra = Name::str(Name::anon(), "Extra".into());
    let axiom =
      |n: &Name| import_view_axiom(n.clone(), LeanExpr::sort(Level::zero()));
    let mut original = LeanEnv::default();
    original.insert(source.clone(), axiom(&source));
    let dstt = DecompileState::default();
    dstt.env.insert(source.clone(), axiom(&source));
    let stt = CompileState::default();
    let r = check_decompile(&original, &stt, &dstt).unwrap();
    assert_eq!((r.matches, r.missing), (1, 0));
    assert!(r.extra_names.is_empty(), "{:?}", r.extra_names);
    dstt.env.insert(extra.clone(), axiom(&extra));
    let r = check_decompile(&original, &stt, &dstt).unwrap();
    assert_eq!((r.matches, r.missing), (1, 1));
    assert_eq!(r.extra_names, vec![extra.pretty()]);
  }

  /// `CheckResult::failures` counts every absent original the caller does
  /// not expect, besides mismatches and extra names.
  #[test]
  fn check_failures_count_mismatches_and_unexpected_absences() {
    let expected = Name::str(Name::anon(), "Ungrounded".into());
    let unexpected = Name::str(Name::anon(), "Lost".into());
    let result = CheckResult {
      matches: 3,
      mismatches: 1,
      missing: 1,
      extra_names: vec!["Extra".into()],
      absent: vec![expected.clone(), unexpected],
    };
    assert_eq!(result.failures(|n| *n == expected), 3);
    let clean = CheckResult {
      matches: 3,
      mismatches: 0,
      missing: 0,
      extra_names: vec![],
      absent: vec![expected.clone()],
    };
    assert_eq!(clean.failures(|n| *n == expected), 0);
  }
}

// ===========================================================================
// Extended index space for `Share` inside `meta_sharing`
//
// `Share(i)` inside `meta_sharing[j]` denotes primary entry `i` (`i < p`) or
// `meta_sharing[i - p]` (`p <= i < p + j`); anything else is
// `InvalidMetaShareIndex`. No compiler emits such a share today, so these
// hand-built fixtures pin the table check (`validate_meta_sharing`). They
// mirror the Lean `decompile-unit` "metadata share" tests in
// `Tests/Ix/Decompile.lean`.
//
// Every fixture has one primary entry (`p = 1`), `prim0 = (#1 #2)`.
// ===========================================================================

#[cfg(test)]
mod meta_share_tests {
  //! The `meta_sharing` table check (`validate_meta_sharing`), directly and
  //! through `load_meta_extensions` on the whole `decompile_env` path.
  use super::*;
  use crate::compile::{compile_name, store_nat};

  struct Fx {
    stt: CompileState,
    head_addr: Address,
    key_addr: Address,
  }

  fn fx() -> Fx {
    let stt = CompileState::default();
    let head = Name::str(Name::anon(), "MS.head".to_string());
    let head_addr = compile_name(&head, &stt).unwrap();
    let key = Name::str(Name::anon(), "MS.key".to_string());
    let key_addr = compile_name(&key, &stt).unwrap();
    Fx { stt, head_addr, key_addr }
  }

  fn prim0() -> Arc<Expr> {
    Expr::app(Expr::var(1), Expr::var(2))
  }
  /// `meta_sharing[0]`, shared: `Share(0)` is primary entry 0.
  fn shared_m0() -> Arc<Expr> {
    Expr::app(Expr::share(0), Expr::var(3))
  }
  /// `meta_sharing[1]`, shared: `Share(1) = p + 0` is `meta_sharing[0]`.
  fn shared_m1() -> Arc<Expr> {
    Expr::app(Expr::share(1), Expr::share(0))
  }
  fn plain_m0() -> Arc<Expr> {
    Expr::app(prim0(), Expr::var(3))
  }
  fn plain_m1() -> Arc<Expr> {
    Expr::app(plain_m0(), prim0())
  }

  /// The primary root `head #99`.
  fn root() -> Arc<Expr> {
    Expr::app(Expr::reference(0, vec![]), Expr::var(99))
  }

  /// Arena `0` a leaf, `1` an ordinary metadata layer `[(MS.key, 1)]`
  /// over it.
  fn arena(fx: &Fx) -> ExprMeta {
    let nat =
      |n: u64| DataValue::OfNat(store_nat(&Nat::from(n), &fx.stt).unwrap());
    let mut arena = ExprMeta::default();
    let leaf = arena.alloc(ExprMetaData::Leaf);
    arena.alloc(ExprMetaData::Mdata {
      mdata: vec![vec![(fx.key_addr.clone(), nat(1))]],
      child: leaf,
    });
    arena
  }

  fn assert_meta_share_err<T: std::fmt::Debug>(
    r: Result<T, DecompileError>,
    want_idx: u64,
    want_entry: u64,
    want_p: usize,
    want_q: usize,
  ) {
    match r {
      Err(DecompileError::InvalidMetaShareIndex {
        idx,
        entry,
        primary_len,
        meta_len,
        ..
      }) => assert_eq!(
        (idx, entry, primary_len, meta_len),
        (want_idx, want_entry, want_p, want_q)
      ),
      other => panic!("expected InvalidMetaShareIndex, got {other:?}"),
    }
  }

  #[test]
  fn meta_share_forward_reference_rejected() {
    let table = vec![Expr::app(Expr::share(2), Expr::var(3)), Expr::var(4)];
    assert_meta_share_err(validate_meta_sharing(1, &table, "t"), 2, 0, 1, 2);
  }

  #[test]
  fn meta_share_self_reference_rejected() {
    let table = vec![Expr::app(Expr::share(1), Expr::var(3))];
    assert_meta_share_err(validate_meta_sharing(1, &table, "t"), 1, 0, 1, 1);
  }

  #[test]
  fn meta_share_out_of_range_rejected() {
    let table = vec![Expr::var(0), Expr::app(Expr::share(5), Expr::var(3))];
    assert_meta_share_err(validate_meta_sharing(1, &table, "t"), 5, 1, 1, 2);
  }

  /// Register an axiom `MS.ax` whose type carries an ordinary metadata
  /// layer, with the given `meta_sharing`, and run the whole
  /// `decompile_env` path (the table is checked by `load_meta_extensions`).
  fn decompile_axiom_env(
    meta_sharing: Vec<Arc<Expr>>,
  ) -> (Result<DecompileState, DecompileError>, Fx, Name) {
    let fx = fx();
    let ax_name = Name::str(Name::anon(), "MS.ax".to_string());
    let ax_addr_name = compile_name(&ax_name, &fx.stt).unwrap();
    let ax = Constant {
      info: ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: 0,
        typ: root(),
      }),
      sharing: vec![prim0()],
      refs: vec![fx.head_addr.clone()],
      univs: vec![],
    };
    let mut bytes = Vec::new();
    ax.put(&mut bytes);
    let addr = Address::hash(&bytes);
    fx.stt.env.store_const(addr.clone(), ax);
    let mut meta = ConstantMeta::new(ConstantMetaInfo::Axio {
      name: ax_addr_name,
      lvls: vec![],
      arena: arena(&fx),
      type_root: 1,
    });
    meta.meta_sharing = meta_sharing;
    fx.stt.env.register_name(ax_name.clone(), Named::new(addr, meta));
    (decompile_env(&fx.stt), fx, ax_name)
  }

  /// No entry is read, and entry 2 references itself
  /// (`Share(3) = p + 2`): the table check still rejects it.
  #[test]
  fn meta_share_unread_malformed_entry_rejected() {
    let (dstt, _, _) = decompile_axiom_env(vec![
      shared_m0(),
      shared_m1(),
      Expr::app(Expr::share(3), Expr::var(0)),
    ]);
    assert_meta_share_err(dstt.map(|_| ()), 3, 2, 1, 3);
  }

  /// Regression: metadata without shares behaves as before.
  #[test]
  fn meta_share_tables_without_shares_unchanged() {
    validate_meta_sharing(0, &[plain_m0(), plain_m1()], "t")
      .expect("no shares: valid against an empty primary table");
  }

  /// The table check visits each shared node once. In-memory tables share
  /// subterms through `Arc`s (the compiler's expression memo); on the chain
  /// `e(k+1) = App(e(k), e(k))` a tree walk is 2^depth (depth 26 took 1.6 s,
  /// doubling per level), so depth 64 only finishes as a DAG walk. A
  /// violation behind shared subterms is still the one the tree walk
  /// reports first.
  #[test]
  fn validate_meta_sharing_visits_shared_subterms_once() {
    let mut e = Expr::app(Expr::share(0), Expr::var(0));
    for _ in 0..64 {
      e = Expr::app(e.clone(), e);
    }
    validate_meta_sharing(1, &[e.clone(), e.clone()], "t")
      .expect("every share is primary entry 0");
    // Entry 1 reads `e` (seen in entry 0) and then `Share(2)`, a self
    // reference of entry 1 (`p + 1 = 2`).
    let err = validate_meta_sharing(
      1,
      &[e.clone(), Expr::app(e.clone(), Expr::share(2))],
      "t",
    )
    .unwrap_err();
    assert_eq!(
      err,
      DecompileError::InvalidMetaShareIndex {
        idx: 2,
        entry: 1,
        primary_len: 1,
        meta_len: 2,
        constant: "t".into(),
      }
    );
    // Inside the shared chain itself, the first violation in pre-order is
    // the leftmost leaf: `Share(0)` against an empty primary table.
    let err = validate_meta_sharing(0, &[e], "t").unwrap_err();
    assert!(
      matches!(
        err,
        DecompileError::InvalidMetaShareIndex { idx: 0, entry: 0, .. }
      ),
      "{err}"
    );
  }
}
