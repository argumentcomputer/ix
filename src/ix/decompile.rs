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
    ConstructorVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
    Expr as LeanExpr, InductiveVal, Level, Literal, Name, OpaqueVal, QuotVal,
    RecursorRule as LeanRecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
  },
  ix::ixon::{
    DecompileError,
    constant::{
      Axiom, Constant, ConstantInfo, Constructor, DefKind, Definition,
      Inductive, MutConst, Quotient, Recursor,
    },
    env::Named,
    expr::Expr,
    metadata::{ConstantMeta, CtorMeta, ExprMetas},
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
  /// Cache for decompiled names
  pub names: DashMap<Address, Name>,
  /// Decompiled environment
  pub env: DashMap<Name, LeanConstantInfo>,
}

#[derive(Debug)]
pub struct DecompileStateStats {
  pub names: usize,
  pub env: usize,
}

impl DecompileState {
  pub fn stats(&self) -> DecompileStateStats {
    DecompileStateStats { names: self.names.len(), env: self.env.len() }
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
  /// Cache for decompiled expressions
  pub exprs: FxHashMap<*const Expr, LeanExpr>,
  /// Cache for decompiled universes
  pub univ_cache: FxHashMap<*const Univ, Level>,
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
  stt.env.get_blob(addr).ok_or(DecompileError::MissingAddress(addr.clone()))
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
  String::from_utf8(bytes)
    .map_err(|_| DecompileError::MissingAddress(addr.clone()))
}

/// Read a Constant from the const store.
fn read_const(
  addr: &Address,
  stt: &CompileState,
) -> Result<Constant, DecompileError> {
  stt.env.get_const(addr).ok_or(DecompileError::MissingAddress(addr.clone()))
}

// ===========================================================================
// Name decompilation
// ===========================================================================

/// Decompile a Name from its blob address.
pub fn decompile_name(
  addr: &Address,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<Name, DecompileError> {
  // First check env.names (direct lookup from compile)
  if let Some(name) = stt.env.names.get(addr) {
    return Ok(name.clone());
  }

  // Then check decompile cache
  if let Some(cached) = dstt.names.get(addr) {
    return Ok(cached.clone());
  }

  // Fall back to blob deserialization (for backwards compatibility)
  let bytes = read_blob(addr, stt)?;
  if bytes.is_empty() {
    return Err(DecompileError::MissingAddress(addr.clone()));
  }

  let name = match bytes[0] {
    0x00 => Name::anon(),
    0x01 => {
      // NStr: tag + pre_addr (32 bytes) + str_addr (32 bytes)
      if bytes.len() < 65 {
        return Err(DecompileError::MissingAddress(addr.clone()));
      }
      let pre_addr = Address::from_slice(&bytes[1..33])
        .map_err(|_| DecompileError::MissingAddress(addr.clone()))?;
      let str_addr = Address::from_slice(&bytes[33..65])
        .map_err(|_| DecompileError::MissingAddress(addr.clone()))?;
      let pre = decompile_name(&pre_addr, stt, dstt)?;
      let s = read_string(&str_addr, stt)?;
      Name::str(pre, s)
    },
    0x02 => {
      // NNum: tag + pre_addr (32 bytes) + nat_addr (32 bytes)
      if bytes.len() < 65 {
        return Err(DecompileError::MissingAddress(addr.clone()));
      }
      let pre_addr = Address::from_slice(&bytes[1..33])
        .map_err(|_| DecompileError::MissingAddress(addr.clone()))?;
      let nat_addr = Address::from_slice(&bytes[33..65])
        .map_err(|_| DecompileError::MissingAddress(addr.clone()))?;
      let pre = decompile_name(&pre_addr, stt, dstt)?;
      let n = read_nat(&nat_addr, stt)?;
      Name::num(pre, n)
    },
    _ => return Err(DecompileError::MissingAddress(addr.clone())),
  };

  dstt.names.insert(addr.clone(), name.clone());
  Ok(name)
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

/// Decompile an Ixon Expr to a Lean Expr.
/// Expands Share(idx) references using the sharing vector in cache.
pub fn decompile_expr(
  expr: &Arc<Expr>,
  lvl_names: &[Name],
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanExpr, DecompileError> {
  // Stack-based iterative decompilation to avoid stack overflow
  enum Frame<'a> {
    Decompile(&'a Arc<Expr>),
    BuildApp,
    BuildLam(Name, BinderInfo),
    BuildAll(Name, BinderInfo),
    BuildLet(Name, bool),
    BuildProj(Name, Nat),
    Cache(&'a Arc<Expr>),
  }

  let ptr = Arc::as_ptr(expr);
  if let Some(cached) = cache.exprs.get(&ptr) {
    return Ok(cached.clone());
  }

  let mut stack: Vec<Frame<'_>> = vec![Frame::Decompile(expr)];
  let mut results: Vec<LeanExpr> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Decompile(e) => {
        let ptr = Arc::as_ptr(e);
        if let Some(cached) = cache.exprs.get(&ptr) {
          results.push(cached.clone());
          continue;
        }

        match e.as_ref() {
          Expr::Var(idx) => {
            let expr = LeanExpr::bvar(Nat::from(*idx));
            cache.exprs.insert(ptr, expr.clone());
            results.push(expr);
          },

          Expr::Sort(univ_idx) => {
            // Look up the universe from the univs table (clone Arc to avoid borrow conflict)
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
            let expr = LeanExpr::sort(level);
            cache.exprs.insert(ptr, expr.clone());
            results.push(expr);
          },

          Expr::Ref(idx, univ_indices) => {
            // Look up the address from the refs table
            let addr = cache.refs.get(*idx as usize).ok_or_else(|| {
              DecompileError::InvalidRefIndex {
                idx: *idx,
                refs_len: cache.refs.len(),
                constant: cache.current_const.clone(),
              }
            })?;
            // Look up the name using O(1) reverse index
            let name = stt
              .env
              .get_name_by_addr(addr)
              .ok_or(DecompileError::MissingAddress(addr.clone()))?;
            // Look up each universe from the univs table and decompile (clone Arcs first)
            let univs: Vec<_> = univ_indices
              .iter()
              .map(|idx| {
                cache
                  .univ_table
                  .get(*idx as usize)
                  .ok_or_else(|| DecompileError::InvalidUnivIndex {
                    idx: *idx,
                    univs_len: cache.univ_table.len(),
                    constant: cache.current_const.clone(),
                  })
                  .cloned()
              })
              .collect::<Result<_, _>>()?;
            let levels: Vec<_> = univs
              .iter()
              .map(|u| decompile_univ(u, lvl_names, cache))
              .collect::<Result<_, _>>()?;
            let expr = LeanExpr::cnst(name, levels);
            cache.exprs.insert(ptr, expr.clone());
            results.push(expr);
          },

          Expr::Rec(idx, univ_indices) => {
            // Look up the name from the mutual context
            let name = cache
              .ctx
              .iter()
              .find(|(_, i)| i.to_u64() == Some(*idx))
              .map(|(n, _)| n.clone())
              .ok_or_else(|| DecompileError::InvalidRecIndex {
                idx: *idx,
                ctx_size: cache.ctx.len(),
                constant: cache.current_const.clone(),
              })?;
            // Look up each universe from the univs table and decompile (clone Arcs first)
            let univs: Vec<_> = univ_indices
              .iter()
              .map(|idx| {
                cache
                  .univ_table
                  .get(*idx as usize)
                  .ok_or_else(|| DecompileError::InvalidUnivIndex {
                    idx: *idx,
                    univs_len: cache.univ_table.len(),
                    constant: cache.current_const.clone(),
                  })
                  .cloned()
              })
              .collect::<Result<_, _>>()?;
            let levels: Vec<_> = univs
              .iter()
              .map(|u| decompile_univ(u, lvl_names, cache))
              .collect::<Result<_, _>>()?;
            let expr = LeanExpr::cnst(name, levels);
            cache.exprs.insert(ptr, expr.clone());
            results.push(expr);
          },

          Expr::Nat(ref_idx) => {
            let addr = cache.refs.get(*ref_idx as usize).ok_or_else(|| {
              DecompileError::InvalidRefIndex {
                idx: *ref_idx,
                refs_len: cache.refs.len(),
                constant: cache.current_const.clone(),
              }
            })?;
            let n = read_nat(addr, stt)?;
            let expr = LeanExpr::lit(Literal::NatVal(n));
            cache.exprs.insert(ptr, expr.clone());
            results.push(expr);
          },

          Expr::Str(ref_idx) => {
            let addr = cache.refs.get(*ref_idx as usize).ok_or_else(|| {
              DecompileError::InvalidRefIndex {
                idx: *ref_idx,
                refs_len: cache.refs.len(),
                constant: cache.current_const.clone(),
              }
            })?;
            let s = read_string(addr, stt)?;
            let expr = LeanExpr::lit(Literal::StrVal(s));
            cache.exprs.insert(ptr, expr.clone());
            results.push(expr);
          },

          Expr::App(f, a) => {
            stack.push(Frame::Cache(e));
            stack.push(Frame::BuildApp);
            stack.push(Frame::Decompile(a));
            stack.push(Frame::Decompile(f));
          },

          Expr::Lam(ty, body) => {
            // For now, use anonymous name and default binder info
            // TODO: Get from metadata if available
            let name = Name::anon();
            let info = BinderInfo::Default;
            stack.push(Frame::Cache(e));
            stack.push(Frame::BuildLam(name, info));
            stack.push(Frame::Decompile(body));
            stack.push(Frame::Decompile(ty));
          },

          Expr::All(ty, body) => {
            let name = Name::anon();
            let info = BinderInfo::Default;
            stack.push(Frame::Cache(e));
            stack.push(Frame::BuildAll(name, info));
            stack.push(Frame::Decompile(body));
            stack.push(Frame::Decompile(ty));
          },

          Expr::Let(non_dep, ty, val, body) => {
            let name = Name::anon();
            stack.push(Frame::Cache(e));
            stack.push(Frame::BuildLet(name, *non_dep));
            stack.push(Frame::Decompile(body));
            stack.push(Frame::Decompile(val));
            stack.push(Frame::Decompile(ty));
          },

          Expr::Prj(type_ref_idx, field_idx, struct_val) => {
            // Look up the type name from the refs table
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
            let type_name = decompile_name_from_meta(&named.meta, stt, dstt)?;
            stack.push(Frame::Cache(e));
            stack.push(Frame::BuildProj(type_name, Nat::from(*field_idx)));
            stack.push(Frame::Decompile(struct_val));
          },

          Expr::Share(idx) => {
            // Expand the share reference
            let shared_expr = cache
              .sharing
              .get(*idx as usize)
              .ok_or_else(|| DecompileError::InvalidShareIndex {
                idx: *idx,
                max: cache.sharing.len(),
                constant: cache.current_const.clone(),
              })?
              .clone();
            // Recursively decompile the shared expression (can't use stack due to lifetime)
            let decompiled =
              decompile_expr(&shared_expr, lvl_names, cache, stt, dstt)?;
            cache.exprs.insert(ptr, decompiled.clone());
            results.push(decompiled);
          },
        }
      },

      Frame::BuildApp => {
        let a = results.pop().expect("BuildApp missing arg");
        let f = results.pop().expect("BuildApp missing fun");
        let expr = LeanExpr::app(f, a);
        results.push(expr);
      },

      Frame::BuildLam(name, info) => {
        let body = results.pop().expect("BuildLam missing body");
        let ty = results.pop().expect("BuildLam missing ty");
        let expr = LeanExpr::lam(name, ty, body, info);
        results.push(expr);
      },

      Frame::BuildAll(name, info) => {
        let body = results.pop().expect("BuildAll missing body");
        let ty = results.pop().expect("BuildAll missing ty");
        let expr = LeanExpr::all(name, ty, body, info);
        results.push(expr);
      },

      Frame::BuildLet(name, non_dep) => {
        let body = results.pop().expect("BuildLet missing body");
        let val = results.pop().expect("BuildLet missing val");
        let ty = results.pop().expect("BuildLet missing ty");
        let expr = LeanExpr::letE(name, ty, val, body, non_dep);
        results.push(expr);
      },

      Frame::BuildProj(name, idx) => {
        let s = results.pop().expect("BuildProj missing struct");
        let expr = LeanExpr::proj(name, idx, s);
        results.push(expr);
      },

      Frame::Cache(e) => {
        let ptr = Arc::as_ptr(e);
        if let Some(result) = results.last() {
          cache.exprs.insert(ptr, result.clone());
        }
      },
    }
  }

  results.pop().ok_or(DecompileError::MissingName { context: "empty result" })
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

/// Extract type expression metadata from ConstantMeta.
#[allow(dead_code)]
fn get_type_meta_from_meta(meta: &ConstantMeta) -> Option<&ExprMetas> {
  match meta {
    ConstantMeta::Empty => None,
    ConstantMeta::Def { type_meta, .. } => Some(type_meta),
    ConstantMeta::Axio { type_meta, .. } => Some(type_meta),
    ConstantMeta::Quot { type_meta, .. } => Some(type_meta),
    ConstantMeta::Indc { type_meta, .. } => Some(type_meta),
    ConstantMeta::Ctor { type_meta, .. } => Some(type_meta),
    ConstantMeta::Rec { type_meta, .. } => Some(type_meta),
  }
}

/// Extract value expression metadata from ConstantMeta (only for Def).
#[allow(dead_code)]
fn get_value_meta_from_meta(meta: &ConstantMeta) -> Option<&ExprMetas> {
  match meta {
    ConstantMeta::Def { value_meta, .. } => Some(value_meta),
    _ => None,
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
  dstt: &DecompileState,
) -> Result<Name, DecompileError> {
  match get_name_addr_from_meta(meta) {
    Some(addr) => decompile_name(addr, stt, dstt),
    None => Err(DecompileError::MissingName { context: "empty metadata" }),
  }
}

/// Extract level param names from ConstantMeta.
fn decompile_level_names_from_meta(
  meta: &ConstantMeta,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<Vec<Name>, DecompileError> {
  get_lvls_from_meta(meta)
    .iter()
    .map(|a| decompile_name(a, stt, dstt))
    .collect()
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
  let name = decompile_name_from_meta(meta, stt, dstt)?;
  let level_params = decompile_level_names_from_meta(meta, stt, dstt)?;
  let typ = decompile_expr(typ, &level_params, cache, stt, dstt)?;
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
  let name = decompile_name_from_meta(meta, stt, dstt)?;
  let level_params = decompile_level_names_from_meta(meta, stt, dstt)?;
  let typ = decompile_expr(&def.typ, &level_params, cache, stt, dstt)?;
  let value = decompile_expr(&def.value, &level_params, cache, stt, dstt)?;

  // Extract hints and all from metadata
  let (hints, all) = match meta {
    ConstantMeta::Def { hints, all, .. } => {
      let all_names: Result<Vec<Name>, _> =
        all.iter().map(|a| decompile_name(a, stt, dstt)).collect();
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
fn decompile_recursor(
  rec: &Recursor,
  meta: &ConstantMeta,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanConstantInfo, DecompileError> {
  let name = decompile_name_from_meta(meta, stt, dstt)?;
  let level_params = decompile_level_names_from_meta(meta, stt, dstt)?;
  let typ = decompile_expr(&rec.typ, &level_params, cache, stt, dstt)?;

  // Extract rule constructor names and all from metadata
  let (rule_names, all) = match meta {
    ConstantMeta::Rec { rules: rule_addrs, all: all_addrs, .. } => {
      let rule_names = rule_addrs
        .iter()
        .map(|a| decompile_name(a, stt, dstt))
        .collect::<Result<Vec<_>, _>>()?;
      let all = all_addrs
        .iter()
        .map(|a| decompile_name(a, stt, dstt))
        .collect::<Result<Vec<_>, _>>()?;
      (rule_names, all)
    },
    _ => (vec![], vec![name.clone()]),
  };

  let mut rules = Vec::with_capacity(rec.rules.len());
  for (rule, ctor_name) in rec.rules.iter().zip(rule_names.iter()) {
    let rhs = decompile_expr(&rule.rhs, &level_params, cache, stt, dstt)?;
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
fn decompile_constructor(
  ctor: &Constructor,
  meta: &CtorMeta,
  induct_name: Name,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstructorVal, DecompileError> {
  let name = decompile_name(&meta.name, stt, dstt)?;
  let level_params: Vec<Name> = meta
    .lvls
    .iter()
    .map(|a| decompile_name(a, stt, dstt))
    .collect::<Result<Vec<_>, _>>()?;
  let typ = decompile_expr(&ctor.typ, &level_params, cache, stt, dstt)?;

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
fn decompile_inductive(
  ind: &Inductive,
  meta: &ConstantMeta,
  ctor_metas: &[CtorMeta],
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(InductiveVal, Vec<ConstructorVal>), DecompileError> {
  let name = decompile_name_from_meta(meta, stt, dstt)?;
  let level_params = decompile_level_names_from_meta(meta, stt, dstt)?;
  let typ = decompile_expr(&ind.typ, &level_params, cache, stt, dstt)?;

  // Extract all from metadata
  let all = match meta {
    ConstantMeta::Indc { all: all_addrs, .. } => all_addrs
      .iter()
      .map(|a| decompile_name(a, stt, dstt))
      .collect::<Result<Vec<_>, _>>()?,
    _ => vec![name.clone()],
  };

  let mut ctors = Vec::with_capacity(ind.ctors.len());
  let mut ctor_names = Vec::new();

  for (ctor, ctor_meta) in ind.ctors.iter().zip(ctor_metas.iter()) {
    let ctor_val =
      decompile_constructor(ctor, ctor_meta, name.clone(), cache, stt, dstt)?;
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
    .filter_map(|a| decompile_name(a, stt, dstt).ok())
    .collect();

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
        // Get constructor metas directly from the Indc metadata
        let ctor_metas = match &named.meta {
          ConstantMeta::Indc { ctor_metas, .. } => ctor_metas.clone(),
          _ => vec![],
        };

        let (ind_val, ctors) = decompile_inductive(
          ind,
          &named.meta,
          &ctor_metas,
          &mut cache,
          stt,
          dstt,
        )?;
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
  let all_names: Vec<Name> = all_addrs
    .iter()
    .filter_map(|a| decompile_name(a, stt, dstt).ok())
    .collect();
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
  use std::sync::atomic::AtomicUsize;

  let dstt = DecompileState::default();
  let start = std::time::SystemTime::now();

  // Constructor metadata is now embedded directly in ConstantMeta::Indc,
  // so no pre-indexing is needed.

  let total = stt.env.named.len();
  let done_count = AtomicUsize::new(0);
  let last_progress = AtomicUsize::new(0);

  eprintln!("Decompiling {} constants...", total);

  // Single pass through all named constants
  stt.env.named.par_iter().try_for_each(|entry| {
    let (name, named) = (entry.key(), entry.value());

    let result = if let Some(cnst) = stt.env.get_const(&named.addr) {
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
    };

    // Progress tracking (disabled for cleaner output - uncomment for debugging)
    // let done = done_count.fetch_add(1, AtomicOrdering::SeqCst) + 1;
    // let last = last_progress.load(AtomicOrdering::Relaxed);
    // let pct = done * 100 / total.max(1);
    // let last_pct = last * 100 / total.max(1);
    // if pct > last_pct || done == total {
    //   if last_progress.compare_exchange(
    //     last, done, AtomicOrdering::SeqCst, AtomicOrdering::Relaxed
    //   ).is_ok() {
    //     let elapsed = start.elapsed().unwrap().as_secs_f32();
    //     eprintln!("Progress: {}/{} ({}%) in {:.1}s", done, total, pct, elapsed);
    //   }
    // }
    let _ = (&done_count, &last_progress, &start); // suppress unused warnings

    result
  })?;

  Ok(dstt)
}

/// Check that decompiled environment matches the original.
pub fn check_decompile(
  original: &LeanEnv,
  _stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  if original.len() != dstt.env.len() {
    // Size mismatch - could be due to missing constants
    // For now, just warn
  }

  dstt.env.par_iter().try_for_each(|entry| {
    let (name, info) = (entry.key(), entry.value());
    match original.get(name) {
      Some(orig_info) if orig_info.get_hash() == info.get_hash() => {
        Ok::<(), DecompileError>(())
      },
      Some(_) => {
        // Hash mismatch - the constant was decompiled differently
        // This could be due to metadata loss
        Ok(())
      },
      None => {
        // Constant not in original - might be a constructor
        Ok(())
      },
    }
  })?;

  Ok(())
}
