//! Shared expression manipulation utilities for auxiliary generation.
//!
//! Provides FVar-based expression construction: create fresh free variables,
//! open forall telescopes, build expressions using FVar references, then
//! abstract back into de Bruijn binder chains with `mk_forall`/`mk_lambda`.
//!
//! Also includes substitution, shifting, and universe manipulation helpers
//! used across `recursor.rs`, `below.rs`, and `brecon.rs`.

use rustc_hash::FxHashMap;

use crate::ix::address::Address;
use crate::ix::env::{
  BinderInfo, Expr as LeanExpr, ExprData, Level, LevelData, Name,
};
use crate::ix::kernel::ingress::{lean_level_to_kuniv, resolve_lean_name_addr};
use crate::ix::kernel::mode::Meta;
use lean_ffi::nat::Nat;

// =========================================================================
// FVar infrastructure
// =========================================================================

/// A local declaration: FVar name, binder metadata, and domain type.
///
/// Used to accumulate binder information while building expressions in
/// FVar space. The `fvar_name` is a unique identifier; `binder_name` is
/// the cosmetic name that appears in the final forall/lambda chain.
#[derive(Clone)]
pub(super) struct LocalDecl {
  pub fvar_name: Name,
  pub binder_name: Name,
  pub domain: LeanExpr,
  pub info: BinderInfo,
}

/// Create a fresh FVar with a unique name derived from `prefix` and `idx`.
pub(super) fn fresh_fvar(prefix: &str, idx: usize) -> (Name, LeanExpr) {
  let name = Name::str(Name::anon(), format!("_{}_{}", prefix, idx));
  let fvar = LeanExpr::fvar(name.clone());
  (name, fvar)
}

/// Open N leading foralls of `expr`, replacing each BVar(0) with a fresh
/// FVar. Returns the FVars, their declarations, and the remaining body.
///
/// This is the Rust equivalent of Lean's `forallTelescope`: it converts
/// a de Bruijn binder chain into FVar-based form so that expression
/// construction can use named references instead of manual index arithmetic.
///
/// The declarations are returned in outermost-first order, suitable for
/// passing directly to `mk_forall` or `mk_lambda`.
pub(super) fn forall_telescope(
  expr: &LeanExpr,
  n: usize,
  prefix: &str,
  start_idx: usize,
) -> (Vec<LeanExpr>, Vec<LocalDecl>, LeanExpr) {
  let mut fvars = Vec::with_capacity(n);
  let mut decls = Vec::with_capacity(n);
  let mut cur = expr.clone();
  for i in 0..n {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar(prefix, start_idx + i);
        decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: dom.clone(),
          info: bi.clone(),
        });
        fvars.push(fv.clone());
        cur = instantiate1(body, &fv);
      },
      _ => break,
    }
  }
  (fvars, decls, cur)
}

// =========================================================================
// Abstraction: FVar -> BVar
// =========================================================================

/// Abstract a single FVar: replace all occurrences of `Fvar(fvar_name)` with
/// `BVar(depth)`, and increment all existing BVars >= depth.
/// This is the inverse of `instantiate1`.
///
/// Prefer `batch_abstract` or `mk_forall`/`mk_lambda` which abstract all
/// FVars in a single pass. This function is retained for cases that need
/// to abstract a single FVar outside of a binder-chain context.
#[allow(dead_code)]
pub(super) fn abstract_fvar(
  expr: &LeanExpr,
  fvar_name: &Name,
  depth: u64,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Fvar(n, _) if n == fvar_name => LeanExpr::bvar(Nat::from(depth)),
    ExprData::Bvar(idx, _) => {
      let i = idx.to_u64().unwrap_or(0);
      if i >= depth { LeanExpr::bvar(Nat::from(i + 1)) } else { expr.clone() }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      abstract_fvar(f, fvar_name, depth),
      abstract_fvar(a, fvar_name, depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      abstract_fvar(t, fvar_name, depth),
      abstract_fvar(b, fvar_name, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      abstract_fvar(t, fvar_name, depth),
      abstract_fvar(b, fvar_name, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      abstract_fvar(t, fvar_name, depth),
      abstract_fvar(v, fvar_name, depth),
      abstract_fvar(b, fvar_name, depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), abstract_fvar(e, fvar_name, depth))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), abstract_fvar(e, fvar_name, depth))
    },
    _ => expr.clone(),
  }
}

/// Build a forall chain by batch-abstracting all FVars in a single pass
/// per sub-expression.
///
/// `binders` is outermost-first. Each domain and the body are walked
/// exactly once by `batch_abstract`, replacing all FVar references with
/// the correct BVar indices simultaneously.
///
/// Complexity: O(|body| + sum(|D_j|)) — one walk per expression.
/// The previous per-binder approach was O(k * (|body| + sum(|D_j|))).
pub(super) fn mk_forall(body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  mk_binder_chain(body, binders, BinderKind::Forall)
}

/// Build a lambda chain by batch-abstracting all FVars in a single pass.
///
/// Same semantics as `mk_forall` but produces `λ (x : T), body`.
pub(super) fn mk_lambda(body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  mk_binder_chain(body, binders, BinderKind::Lambda)
}

/// Whether to build forall or lambda binders.
enum BinderKind {
  Forall,
  Lambda,
}

/// Shared implementation for `mk_forall` and `mk_lambda`.
fn mk_binder_chain(
  body: LeanExpr,
  binders: &[LocalDecl],
  kind: BinderKind,
) -> LeanExpr {
  let k = binders.len();
  if k == 0 {
    return body;
  }

  // Build FVar name → binder position map (0 = outermost).
  let fvar_map: FxHashMap<Name, usize> =
    binders.iter().enumerate().map(|(i, d)| (d.fvar_name.clone(), i)).collect();

  // Abstract body: all k binders in scope.
  let mut result = batch_abstract(&body, &fvar_map, k, 0);

  // Build binder chain from innermost to outermost.
  for j in (0..k).rev() {
    let decl = &binders[j];
    // Domain D_j: only binders 0..j-1 are in scope (scope_depth = j).
    // Binder j's domain is NOT under binder j itself — only the body is.
    let domain = batch_abstract(&decl.domain, &fvar_map, j, 0);
    result = match kind {
      BinderKind::Forall => LeanExpr::all(
        decl.binder_name.clone(),
        domain,
        result,
        decl.info.clone(),
      ),
      BinderKind::Lambda => LeanExpr::lam(
        decl.binder_name.clone(),
        domain,
        result,
        decl.info.clone(),
      ),
    };
  }
  result
}

/// Single-pass FVar→BVar abstraction for an entire binder telescope.
///
/// Replaces all FVars (identified by `fvar_map`) with the correct BVar
/// indices in one expression walk, and shifts existing free BVars to
/// account for the new binders.
///
/// # Parameters
/// - `fvar_map`: FVar name → binder position (0 = outermost binder)
/// - `scope_depth`: how many of our binders are in scope at this point.
///   For the body, this is `k` (all binders). For domain `D_j`, this is `j`.
/// - `internal_depth`: expression-internal binder depth (forall/lambda/let
///   bodies entered during the walk). Starts at 0.
///
/// # BVar index computation
/// - FVar at binder position `i`, scope depth `s`, internal depth `d`:
///   `BVar((s - 1 - i) + d)`
/// - Free BVar(n) where `n >= d`: shifted to `BVar(n + s)`
/// - Bound BVar(n) where `n < d`: unchanged
pub(super) fn batch_abstract(
  expr: &LeanExpr,
  fvar_map: &FxHashMap<Name, usize>,
  scope_depth: usize,
  internal_depth: u64,
) -> LeanExpr {
  // Fast path: no binders to abstract.
  if scope_depth == 0 {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Fvar(name, _) => {
      if let Some(&pos) = fvar_map.get(name) {
        if pos < scope_depth {
          let idx = (scope_depth - 1 - pos) as u64 + internal_depth;
          LeanExpr::bvar(Nat::from(idx))
        } else {
          // FVar not yet in scope (e.g., a forward reference in a domain
          // to a binder declared later). Leave as-is.
          expr.clone()
        }
      } else {
        // FVar not in our telescope — leave as-is.
        expr.clone()
      }
    },
    ExprData::Bvar(idx, _) => {
      let i = idx.to_u64().unwrap_or(0);
      if i >= internal_depth {
        // Free BVar: shift up by scope_depth to make room for our binders.
        LeanExpr::bvar(Nat::from(i + scope_depth as u64))
      } else {
        // Bound by an expression-internal binder — unchanged.
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      batch_abstract(f, fvar_map, scope_depth, internal_depth),
      batch_abstract(a, fvar_map, scope_depth, internal_depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      batch_abstract(t, fvar_map, scope_depth, internal_depth),
      batch_abstract(b, fvar_map, scope_depth, internal_depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      batch_abstract(t, fvar_map, scope_depth, internal_depth),
      batch_abstract(b, fvar_map, scope_depth, internal_depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      batch_abstract(t, fvar_map, scope_depth, internal_depth),
      batch_abstract(v, fvar_map, scope_depth, internal_depth),
      batch_abstract(b, fvar_map, scope_depth, internal_depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      batch_abstract(e, fvar_map, scope_depth, internal_depth),
    ),
    ExprData::Mdata(kvs, e, _) => LeanExpr::mdata(
      kvs.clone(),
      batch_abstract(e, fvar_map, scope_depth, internal_depth),
    ),
    // Sort, Const, MVar, Lit — no FVars or BVars to process.
    _ => expr.clone(),
  }
}

// =========================================================================
// Instantiation: BVar -> replacement
// =========================================================================

/// Lean's `instantiate1`: replace BVar(0) with `replacement`, decrement
/// BVar(i>0) by 1 (removing a binder level). The replacement is NOT
/// shifted — it's inserted as-is at the substitution depth.
///
/// This differs from `subst_bvar0` which shifts the replacement by the
/// current depth. `instantiate1` is used when peeling forall binders
/// during recursor construction (matching Lean C++ and lean4lean).
pub(super) fn instantiate1(
  body: &LeanExpr,
  replacement: &LeanExpr,
) -> LeanExpr {
  instantiate1_at(body, replacement, 0)
}

pub(super) fn instantiate1_at(
  body: &LeanExpr,
  replacement: &LeanExpr,
  depth: u64,
) -> LeanExpr {
  match body.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = idx.to_u64().unwrap_or(0);
      if i == depth {
        replacement.clone()
      } else if i > depth {
        LeanExpr::bvar(Nat::from(i - 1))
      } else {
        body.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      instantiate1_at(f, replacement, depth),
      instantiate1_at(a, replacement, depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      instantiate1_at(t, replacement, depth),
      instantiate1_at(b, replacement, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      instantiate1_at(t, replacement, depth),
      instantiate1_at(b, replacement, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      instantiate1_at(t, replacement, depth),
      instantiate1_at(v, replacement, depth),
      instantiate1_at(b, replacement, depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      instantiate1_at(e, replacement, depth),
    ),
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), instantiate1_at(e, replacement, depth))
    },
    _ => body.clone(),
  }
}

/// Substitute BVar(depth) with `replacement`, shifting the replacement
/// by the current depth. Decrements BVar(i > depth) by 1.
#[allow(dead_code)]
pub(super) fn subst_at(
  body: &LeanExpr,
  replacement: &LeanExpr,
  depth: u64,
) -> LeanExpr {
  match body.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = idx.to_u64().unwrap_or(0);
      if i == depth {
        shift_vars(replacement, depth as usize, 0)
      } else if i > depth {
        LeanExpr::bvar(Nat::from(i - 1))
      } else {
        body.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      subst_at(f, replacement, depth),
      subst_at(a, replacement, depth),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      subst_at(t, replacement, depth),
      subst_at(b, replacement, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      subst_at(t, replacement, depth),
      subst_at(b, replacement, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      subst_at(t, replacement, depth),
      subst_at(v, replacement, depth),
      subst_at(b, replacement, depth + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), subst_at(e, replacement, depth))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), subst_at(e, replacement, depth))
    },
    _ => body.clone(),
  }
}

#[allow(dead_code)]
pub(super) fn subst_bvar0(body: &LeanExpr, replacement: &LeanExpr) -> LeanExpr {
  subst_at(body, replacement, 0)
}

/// Convert spec_params from BVar form to FVar form.
///
/// Spec_params use BVars relative to the param context: BVar(0) is the
/// last (innermost) param, BVar(n_params-1) is the first. We convert
/// each BVar(i) to the corresponding param FVar by iterating
/// `instantiate1` from innermost to outermost.
pub(super) fn instantiate_spec_with_fvars(
  spec_params: &[LeanExpr],
  param_fvars: &[LeanExpr],
) -> Vec<LeanExpr> {
  spec_params
    .iter()
    .map(|sp| {
      let mut result = sp.clone();
      for j in (0..param_fvars.len()).rev() {
        result = instantiate1(&result, &param_fvars[j]);
      }
      result
    })
    .collect()
}

// =========================================================================
// BVar shifting
// =========================================================================

/// Shift BVars UP by `amount` for BVars >= cutoff.
///
/// Used in substitution helpers and during manual BVar adjustments.
/// After full FVar conversion, this is primarily used internally by
/// `subst_at`.
pub(super) fn shift_vars(
  expr: &LeanExpr,
  amount: usize,
  cutoff: usize,
) -> LeanExpr {
  if amount == 0 {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = idx.to_u64().unwrap_or(0) as usize;
      if i >= cutoff {
        LeanExpr::bvar(Nat::from((i + amount) as u64))
      } else {
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      shift_vars(f, amount, cutoff),
      shift_vars(a, amount, cutoff),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      shift_vars(t, amount, cutoff),
      shift_vars(b, amount, cutoff + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      shift_vars(t, amount, cutoff),
      shift_vars(b, amount, cutoff + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      shift_vars(t, amount, cutoff),
      shift_vars(v, amount, cutoff),
      shift_vars(b, amount, cutoff + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), shift_vars(e, amount, cutoff))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), shift_vars(e, amount, cutoff))
    },
    _ => expr.clone(),
  }
}

// =========================================================================
// Universe substitution
// =========================================================================

/// Substitute universe parameters in expressions.
pub(super) fn subst_levels(
  expr: &LeanExpr,
  params: &[Name],
  univs: &[Level],
) -> LeanExpr {
  if params.is_empty() || univs.is_empty() {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Sort(lvl, _) => LeanExpr::sort(subst_level(lvl, params, univs)),
    ExprData::Const(name, us, _) => LeanExpr::cnst(
      name.clone(),
      us.iter().map(|u| subst_level(u, params, univs)).collect(),
    ),
    ExprData::App(f, a, _) => LeanExpr::app(
      subst_levels(f, params, univs),
      subst_levels(a, params, univs),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      subst_levels(t, params, univs),
      subst_levels(b, params, univs),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      subst_levels(t, params, univs),
      subst_levels(b, params, univs),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      subst_levels(t, params, univs),
      subst_levels(v, params, univs),
      subst_levels(b, params, univs),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), subst_levels(e, params, univs))
    },
    ExprData::Mdata(md, e, _) => {
      LeanExpr::mdata(md.clone(), subst_levels(e, params, univs))
    },
    _ => expr.clone(),
  }
}

/// Substitute universe parameters in a level.
pub(super) fn subst_level(
  lvl: &Level,
  params: &[Name],
  univs: &[Level],
) -> Level {
  match lvl.as_data() {
    LevelData::Zero(_) | LevelData::Mvar(_, _) => lvl.clone(),
    LevelData::Succ(l, _) => {
      super::below::mk_level_succ(&subst_level(l, params, univs))
    },
    LevelData::Max(a, b, _) => {
      Level::max(subst_level(a, params, univs), subst_level(b, params, univs))
    },
    LevelData::Imax(a, b, _) => {
      Level::imax(subst_level(a, params, univs), subst_level(b, params, univs))
    },
    LevelData::Param(name, _) => {
      for (i, p) in params.iter().enumerate() {
        if p == name && i < univs.len() {
          return univs[i].clone();
        }
      }
      lvl.clone()
    },
  }
}

// =========================================================================
// Expression utilities
// =========================================================================

/// Create a `Const` expression with the given name and universe levels.
pub(super) fn mk_const(name: &Name, univs: &[Level]) -> LeanExpr {
  LeanExpr::cnst(name.clone(), univs.to_vec())
}

/// Strip type annotation wrappers from a type expression.
///
/// Matches Lean's `Expr.consumeTypeAnnotations` (Expr.lean:1721-1727):
/// - `outParam α` → recurse on `α`
/// - `semiOutParam α` → recurse on `α`
/// - `optParam α default` → recurse on `α`
/// - `autoParam α tactic` → recurse on `α`
///
/// Called by the kernel's `mk_local_decl` during inductive processing
/// to ensure parameter/field types are clean before entering the local context.
pub(super) fn consume_type_annotations(e: &LeanExpr) -> LeanExpr {
  let (head, args) = decompose_apps(e);
  if let ExprData::Const(name, _, _) = head.as_data() {
    let n = name.pretty();
    if (n == "outParam" || n == "semiOutParam") && args.len() == 1 {
      // outParam.{u} (α : Sort u) := α — strip and recurse
      return consume_type_annotations(&args[0]);
    }
    if (n == "optParam" || n == "autoParam") && args.len() == 2 {
      // optParam.{u} (α : Sort u) (default : α) := α — strip to first arg
      return consume_type_annotations(&args[0]);
    }
  }
  e.clone()
}

/// Decompose an application spine: `f a1 a2 ... an` -> `(f, [a1, ..., an])`.
pub(super) fn decompose_apps(expr: &LeanExpr) -> (LeanExpr, Vec<LeanExpr>) {
  let mut args = Vec::new();
  let mut cur = expr.clone();
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

/// Count the number of leading forall binders in an expression.
pub(super) fn count_foralls(expr: &LeanExpr) -> usize {
  let mut n = 0;
  let mut cur = expr.clone();
  loop {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        n += 1;
        cur = body.clone();
      },
      _ => return n,
    }
  }
}

/// Apply an expression to a sequence of arguments: `f a1 a2 ... an`.
pub(super) fn mk_app_n(f: LeanExpr, args: &[LeanExpr]) -> LeanExpr {
  let mut result = f;
  for a in args {
    result = LeanExpr::app(result, a.clone());
  }
  result
}

/// Check if the head of `dom` (after peeling foralls) is one of the
/// given `motive_fvars`. Returns `Some(class_index)` if matched.
///
/// Substitute all occurrences of `Fvar(fvar_name)` with `replacement`.
///
/// Unlike `abstract_fvar` (which replaces FVar with BVar), this replaces
/// FVar with an arbitrary expression. Used when eliminating free FVars
/// that shouldn't appear in the final output.
pub(super) fn subst_fvar(
  expr: &LeanExpr,
  fvar_name: &Name,
  replacement: &LeanExpr,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Fvar(n, _) if n == fvar_name => replacement.clone(),
    ExprData::App(f, a, _) => LeanExpr::app(
      subst_fvar(f, fvar_name, replacement),
      subst_fvar(a, fvar_name, replacement),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      subst_fvar(t, fvar_name, replacement),
      subst_fvar(b, fvar_name, replacement),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      subst_fvar(t, fvar_name, replacement),
      subst_fvar(b, fvar_name, replacement),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      subst_fvar(t, fvar_name, replacement),
      subst_fvar(v, fvar_name, replacement),
      subst_fvar(b, fvar_name, replacement),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      subst_fvar(e, fvar_name, replacement),
    ),
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), subst_fvar(e, fvar_name, replacement))
    },
    _ => expr.clone(),
  }
}

/// Replace constant names throughout an expression according to a name map.
///
/// Recursively traverses the expression tree, substituting `Const` names
/// and `Proj` type names that appear as keys in `map` with their
/// corresponding values. All other expression structure is preserved.
///
/// Used by `rename_below_indc` to fix up constructor types when creating
/// alpha-collapsed aliases: the canonical `.below` constructor types
/// reference the canonical parent inductive and its constructors, which
/// must be rewritten to reference the alias target.
pub(super) fn replace_const_names(
  expr: &LeanExpr,
  map: &std::collections::HashMap<Name, Name>,
) -> LeanExpr {
  if map.is_empty() {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Const(name, lvls, _) => {
      let new_name = map.get(name).cloned().unwrap_or_else(|| name.clone());
      LeanExpr::cnst(new_name, lvls.clone())
    },
    ExprData::App(f, a, _) => {
      LeanExpr::app(replace_const_names(f, map), replace_const_names(a, map))
    },
    ExprData::ForallE(n, d, b, bi, _) => LeanExpr::all(
      n.clone(),
      replace_const_names(d, map),
      replace_const_names(b, map),
      bi.clone(),
    ),
    ExprData::Lam(n, d, b, bi, _) => LeanExpr::lam(
      n.clone(),
      replace_const_names(d, map),
      replace_const_names(b, map),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      replace_const_names(t, map),
      replace_const_names(v, map),
      replace_const_names(b, map),
      *nd,
    ),
    ExprData::Proj(type_name, idx, e, _) => {
      let new_type_name =
        map.get(type_name).cloned().unwrap_or_else(|| type_name.clone());
      LeanExpr::proj(new_type_name, idx.clone(), replace_const_names(e, map))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), replace_const_names(e, map))
    },
    // BVar, FVar, MVar, Sort, Lit — no constant names to replace.
    _ => expr.clone(),
  }
}

/// This replaces the BVar-range-based `is_motive_application` and
/// `find_motive_class` with a simple structural FVar comparison.
pub(super) fn find_motive_fvar(
  dom: &LeanExpr,
  motive_fvars: &[LeanExpr],
) -> Option<usize> {
  let mut ty = dom.clone();
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => ty = body.clone(),
      _ => {
        let (head, _) = decompose_apps(&ty);
        if let ExprData::Fvar(name, _) = head.as_data() {
          for (j, mfv) in motive_fvars.iter().enumerate() {
            if let ExprData::Fvar(mn, _) = mfv.as_data()
              && name == mn
            {
              return Some(j);
            }
          }
        }
        return None;
      },
    }
  }
}

// =========================================================================
// Kernel-backed sort level inference
// =========================================================================

/// Ensure PUnit and PProd are in `stt.kenv` for kernel type inference.
///
/// These are prelude constants with fixed definitions that brecOn's
/// `get_level` needs to resolve. Hardcoded so they're available even
/// without a Lean environment (e.g. during decompile roundtrip).
///
/// ```text
/// inductive PUnit : Sort u where | unit : PUnit
/// structure PProd (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
///   mk :: (fst : α) (snd : β)
/// ```
/// Ensure PUnit and PProd are in the given kenv for kernel type inference.
/// Accepts `kctx` so callers can choose which KernelCtx to populate.
pub(crate) fn ensure_prelude_in_kenv_of(
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::expr::KExpr;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::level::KUniv;

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);

  // --- PUnit.{u} : Sort u ---
  // Always insert (unconditional) so the hardcoded Indc definitions are
  // authoritative. ingress_field_deps may have already inserted PUnit/PProd
  // as bare Axio stubs with potentially wrong types; overwriting is safe.
  let punit_name = Name::str(Name::anon(), "PUnit".to_string());
  let punit_addr = resolve_lean_name_addr(&punit_name, n2a, aux_n2a);
  let punit_id = KId::new(punit_addr, punit_name.clone());
  let u_name = Name::str(Name::anon(), "u".to_string());
  {
    // PUnit.{u} : Sort u
    let u0 = KUniv::param(0, u_name.clone());
    let punit_ty = KExpr::sort(u0);
    // PUnit.unit.{u} : PUnit.{u}
    let unit_name = Name::str(punit_name.clone(), "unit".to_string());
    let unit_addr = resolve_lean_name_addr(&unit_name, n2a, aux_n2a);
    let unit_id = KId::new(unit_addr, unit_name.clone());
    let unit_ty = KExpr::cnst(
      punit_id.clone(),
      vec![KUniv::param(0, u_name.clone())].into_boxed_slice(),
    );
    kctx.kenv.insert(
      unit_id.clone(),
      KConst::Ctor {
        name: unit_name,
        level_params: vec![u_name.clone()],
        is_unsafe: false,
        lvls: 1,
        induct: punit_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: unit_ty,
      },
    );
    kctx.kenv.insert(
      punit_id.clone(),
      KConst::Indc {
        name: punit_name.clone(),
        level_params: vec![u_name.clone()],
        lvls: 1,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        ctors: vec![unit_id],
        ty: punit_ty,
        block: punit_id,
        nested: 0,
        member_idx: 0,
        lean_all: vec![],
      },
    );
  }

  // --- PProd.{u, v} (α : Sort u) (β : Sort v) : Sort (max 1 u v) ---
  let pprod_name = Name::str(Name::anon(), "PProd".to_string());
  let pprod_addr = resolve_lean_name_addr(&pprod_name, n2a, aux_n2a);
  let pprod_id = KId::new(pprod_addr, pprod_name.clone());
  let v_name = Name::str(Name::anon(), "v".to_string());
  let alpha_name = Name::str(Name::anon(), "\u{03B1}".to_string());
  let beta_name = Name::str(Name::anon(), "\u{03B2}".to_string());
  let fst_name = Name::str(Name::anon(), "fst".to_string());
  let snd_name = Name::str(Name::anon(), "snd".to_string());
  {
    let u0 = KUniv::param(0, u_name.clone());
    let u1 = KUniv::param(1, v_name.clone());
    let sort_u = KExpr::sort(u0.clone());
    let sort_v = KExpr::sort(u1.clone());
    let max_1_u_v = KUniv::max(
      KUniv::succ(KUniv::zero()),
      KUniv::max(u0.clone(), u1.clone()),
    );

    // PProd.{u,v} : Sort u → Sort v → Sort (max 1 u v)
    let pprod_ty = KExpr::all(
      alpha_name.clone(),
      BinderInfo::Default,
      sort_u.clone(),
      KExpr::all(
        beta_name.clone(),
        BinderInfo::Default,
        sort_v.clone(),
        KExpr::sort(max_1_u_v),
      ),
    );

    // PProd.mk.{u,v} : {α : Sort u} → {β : Sort v} → α → β → PProd α β
    let mk_name = Name::str(pprod_name.clone(), "mk".to_string());
    let mk_addr = resolve_lean_name_addr(&mk_name, n2a, aux_n2a);
    let mk_id = KId::new(mk_addr, mk_name.clone());
    // Body: ∀ {α : Sort u} {β : Sort v} (fst : α) (snd : β), PProd.{u,v} α β
    // In de Bruijn: ∀ Sort(u) . ∀ Sort(v) . ∀ Var(1) . ∀ Var(1) . PProd Var(3) Var(2)
    let pprod_app = KExpr::app(
      KExpr::app(
        KExpr::cnst(
          pprod_id.clone(),
          vec![u0.clone(), u1.clone()].into_boxed_slice(),
        ),
        KExpr::var(3, Name::anon()),
      ),
      KExpr::var(2, Name::anon()),
    );
    let mk_ty = KExpr::all(
      alpha_name.clone(),
      BinderInfo::Implicit,
      sort_u, // {α : Sort u}
      KExpr::all(
        beta_name.clone(),
        BinderInfo::Implicit,
        sort_v, // {β : Sort v}
        KExpr::all(
          fst_name,
          BinderInfo::Default,
          KExpr::var(1, Name::anon()), // (fst : α)
          KExpr::all(
            snd_name,
            BinderInfo::Default,
            KExpr::var(1, Name::anon()), // (snd : β)
            pprod_app,
          ),
        ),
      ),
    );
    kctx.kenv.insert(
      mk_id.clone(),
      KConst::Ctor {
        name: mk_name,
        level_params: vec![u_name.clone(), v_name.clone()],
        is_unsafe: false,
        lvls: 2,
        induct: pprod_id.clone(),
        cidx: 0,
        params: 2,
        fields: 2,
        ty: mk_ty,
      },
    );
    kctx.kenv.insert(
      pprod_id.clone(),
      KConst::Indc {
        name: pprod_name,
        level_params: vec![u_name, v_name],
        lvls: 2,
        params: 2,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        ctors: vec![mk_id],
        ty: pprod_ty,
        block: pprod_id,
        nested: 0,
        member_idx: 0,
        lean_all: vec![],
      },
    );
  }
}

/// Ingress a Lean constant into the given kenv so the kernel type checker
/// can resolve it during inference. Handles all constant types: inductives
/// (with constructors), definitions, theorems, axioms, quotients, and
/// recursors.
///
/// Idempotent: skips if the constant is already loaded in `kctx.kenv`.
pub(crate) fn ensure_in_kenv_of(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) {
  use crate::ix::env::{ConstantInfo as LCI, DefinitionSafety};
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr_cached, param_names_hash,
  };

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);

  let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
  let zid: KId<Meta> = KId::new(addr, name.clone());

  if kctx.kenv.get(&zid).is_some() {
    return; // Already loaded.
  }

  let Some(ci) = lean_env.get(name) else { return };
  let cache = Some(&kctx.kenv.ingress_cache);

  // Helper: convert a LeanExpr to KExpr with the given level param names,
  // using the KEnv's persistent ingress cache.
  let to_z = |expr: &crate::ix::env::Expr,
              lp: &[Name]|
   -> crate::ix::kernel::expr::KExpr<Meta> {
    let pn_h = param_names_hash(lp);
    lean_expr_to_zexpr_cached(
      expr,
      lp,
      &kctx.kenv.intern,
      n2a,
      aux_n2a,
      cache,
      Some(&pn_h),
    )
  };

  match ci {
    LCI::InductInfo(ind) => {
      let lp = &ind.cnst.level_params;
      let n_lvls = lp.len() as u64;
      let ty_z = to_z(&ind.cnst.typ, lp);
      let mut ctor_zids = Vec::new();
      for ctor_name in &ind.ctors {
        if let Some(LCI::CtorInfo(ctor)) = lean_env.get(ctor_name) {
          let ctor_zid = KId::new(
            resolve_lean_name_addr(ctor_name, n2a, aux_n2a),
            ctor_name.clone(),
          );
          kctx.kenv.insert(
            ctor_zid.clone(),
            KConst::Ctor {
              name: ctor_name.clone(),
              level_params: lp.clone(),
              is_unsafe: ctor.is_unsafe,
              lvls: n_lvls,
              induct: zid.clone(),
              cidx: ctor_zids.len() as u64,
              params: ctor.num_params.to_u64().unwrap_or(0),
              fields: ctor.num_fields.to_u64().unwrap_or(0),
              ty: to_z(&ctor.cnst.typ, lp),
            },
          );
          ctor_zids.push(ctor_zid);
        }
      }
      kctx.kenv.insert(
        zid.clone(),
        KConst::Indc {
          name: name.clone(),
          level_params: lp.clone(),
          lvls: n_lvls,
          params: ind.num_params.to_u64().unwrap_or(0),
          indices: ind.num_indices.to_u64().unwrap_or(0),
          is_rec: ind.is_rec,
          is_refl: ind.is_reflexive,
          is_unsafe: ind.is_unsafe,
          ctors: ctor_zids,
          ty: ty_z,
          block: zid,
          nested: ind.num_nested.to_u64().unwrap_or(0),
          member_idx: 0,
          lean_all: vec![],
        },
      );
    },
    LCI::DefnInfo(d) => {
      let lp = &d.cnst.level_params;
      kctx.kenv.insert(
        zid.clone(),
        KConst::Defn {
          name: name.clone(),
          level_params: lp.clone(),
          kind: crate::ix::ixon::constant::DefKind::Definition,
          safety: d.safety.clone(),
          hints: d.hints.clone(),
          lvls: lp.len() as u64,
          ty: to_z(&d.cnst.typ, lp),
          val: to_z(&d.value, lp),
          lean_all: vec![],
          block: zid,
        },
      );
    },
    LCI::ThmInfo(d) => {
      let lp = &d.cnst.level_params;
      kctx.kenv.insert(
        zid.clone(),
        KConst::Defn {
          name: name.clone(),
          level_params: lp.clone(),
          kind: crate::ix::ixon::constant::DefKind::Theorem,
          safety: DefinitionSafety::Safe,
          hints: crate::ix::env::ReducibilityHints::Opaque,
          lvls: lp.len() as u64,
          ty: to_z(&d.cnst.typ, lp),
          val: to_z(&d.value, lp),
          lean_all: vec![],
          block: zid,
        },
      );
    },
    LCI::OpaqueInfo(d) => {
      let lp = &d.cnst.level_params;
      kctx.kenv.insert(
        zid.clone(),
        KConst::Defn {
          name: name.clone(),
          level_params: lp.clone(),
          kind: crate::ix::ixon::constant::DefKind::Opaque,
          safety: DefinitionSafety::Safe,
          hints: crate::ix::env::ReducibilityHints::Opaque,
          lvls: lp.len() as u64,
          ty: to_z(&d.cnst.typ, lp),
          val: to_z(&d.value, lp),
          lean_all: vec![],
          block: zid,
        },
      );
    },
    LCI::AxiomInfo(a) => {
      let lp = &a.cnst.level_params;
      kctx.kenv.insert(
        zid.clone(),
        KConst::Axio {
          name: name.clone(),
          level_params: lp.clone(),
          is_unsafe: a.is_unsafe,
          lvls: lp.len() as u64,
          ty: to_z(&a.cnst.typ, lp),
        },
      );
    },
    LCI::QuotInfo(q) => {
      let lp = &q.cnst.level_params;
      kctx.kenv.insert(
        zid.clone(),
        KConst::Quot {
          name: name.clone(),
          level_params: lp.clone(),
          kind: q.kind.clone(),
          lvls: lp.len() as u64,
          ty: to_z(&q.cnst.typ, lp),
        },
      );
    },
    LCI::CtorInfo(ctor) => {
      // Constructors are ingressed as part of their parent inductive.
      ensure_in_kenv_of(&ctor.induct, lean_env, stt, kctx);
    },
    LCI::RecInfo(_) => {
      // Recursors are generated by the kernel, not ingressed from Lean.
      // They'll be created when check_inductive runs on the parent.
    },
  }
}

/// Convenience wrapper: ingress into the **original** kenv (`stt.kctx`).
pub(crate) fn ensure_in_kenv(
  name: &Name,
  lean_env: &crate::ix::env::Env,
  stt: &crate::ix::compile::CompileState,
) {
  ensure_in_kenv_of(name, lean_env, stt, &stt.kctx);
}

// =========================================================================
// Scoped access to the global TypeChecker
// =========================================================================

/// RAII scope for using a TypeChecker with an FVar context.
///
/// Locks `kctx.tc` for its lifetime. Callers push/pop locals via
/// `push_locals` / `pop_locals` and infer sort levels via `get_level`.
/// All locals pushed must be popped before the scope is dropped.
pub(super) struct TcScope<'a> {
  fvar_levels: FxHashMap<Name, usize>,
  base_depth: usize,
  param_names: &'a [Name],
  stt: &'a crate::ix::compile::CompileState,
  tc: crate::ix::kernel::tc::TypeChecker<Meta>,
  /// How many extra locals are currently pushed above base_depth.
  extra_locals: usize,
}

impl<'a> TcScope<'a> {
  /// Lock the TC (`kctx.tc`) and push the outer FVar context.
  pub(super) fn new(
    outer_fvar_ctx: &[LocalDecl],
    param_names: &'a [Name],
    stt: &'a crate::ix::compile::CompileState,
    kctx: &'a crate::ix::compile::KernelCtx,
  ) -> Self {
    let fvar_levels: FxHashMap<Name, usize> = outer_fvar_ctx
      .iter()
      .enumerate()
      .map(|(i, decl)| (decl.fvar_name.clone(), i))
      .collect();

    let mut tc = crate::ix::kernel::tc::TypeChecker::new(kctx.kenv.clone());
    tc.infer_only = true;

    // Push outer FVar types once.
    for (i, decl) in outer_fvar_ctx.iter().enumerate() {
      let kty =
        to_kexpr_static(&decl.domain, &fvar_levels, i, param_names, stt);
      tc.push_local(kty);
    }

    TcScope {
      fvar_levels,
      base_depth: outer_fvar_ctx.len(),
      param_names,
      stt,
      tc,
      extra_locals: 0,
    }
  }

  /// Push additional locals (e.g. minor premise lambda binders).
  /// Must be balanced by a later `pop_locals` call.
  pub(super) fn push_locals(&mut self, decls: &[LocalDecl]) {
    let depth = self.base_depth + self.extra_locals;
    for (i, decl) in decls.iter().enumerate() {
      self.fvar_levels.insert(decl.fvar_name.clone(), depth + i);
      let kty = to_kexpr_static(
        &decl.domain,
        &self.fvar_levels,
        depth + i,
        self.param_names,
        self.stt,
      );
      self.tc.push_local(kty);
    }
    self.extra_locals += decls.len();
  }

  /// Pop locals pushed by `push_locals`.
  pub(super) fn pop_locals(&mut self, decls: &[LocalDecl]) {
    for decl in decls.iter().rev() {
      self.tc.pop_local();
      self.fvar_levels.remove(&decl.fvar_name);
    }
    self.extra_locals -= decls.len();
  }

  /// Infer the sort level of a type expression in the current context.
  pub(super) fn get_level(
    &mut self,
    ty: &LeanExpr,
  ) -> Result<Level, crate::ix::ixon::CompileError> {
    let depth = self.base_depth + self.extra_locals;
    let kexpr =
      to_kexpr_static(ty, &self.fvar_levels, depth, self.param_names, self.stt);

    let inferred = self.tc.infer(&kexpr).map_err(|e| {
      eprintln!("[TcScope::get_level] FAILED");
      eprintln!("  lean_expr: {}", ty.pretty());
      eprintln!("  kexpr:     {kexpr}");
      eprintln!("  error:     {e}");
      eprintln!(
        "  ctx depth: {} (base={}, extra={})",
        self.tc.ctx.len(),
        self.base_depth,
        self.extra_locals
      );
      // Dump kenv entries for constants referenced in the expression
      let mut stack: Vec<&crate::ix::kernel::expr::KExpr<Meta>> = vec![&kexpr];
      let mut seen_ids = std::collections::HashSet::new();
      while let Some(expr) = stack.pop() {
        use crate::ix::kernel::expr::ExprData as ZED;
        match expr.data() {
          ZED::Const(id, us, _) => {
            if seen_ids.insert(id.clone()) {
              match self.tc.env.get(id) {
                Some(c) => {
                  eprintln!("  kenv[{}]: lvls={}, ty={}", id, c.lvls(), c.ty())
                },
                None => eprintln!("  kenv[{}]: NOT FOUND", id),
              }
              eprintln!(
                "    level_args: [{}]",
                us.iter()
                  .map(|u| format!("{u}"))
                  .collect::<Vec<_>>()
                  .join(", ")
              );
            }
          },
          ZED::App(f, a, _) => {
            stack.push(f);
            stack.push(a);
          },
          ZED::All(_, _, d, b, _) | ZED::Lam(_, _, d, b, _) => {
            stack.push(d);
            stack.push(b);
          },
          _ => {},
        }
      }
      crate::ix::ixon::CompileError::UnsupportedExpr {
        desc: format!(
          "TcScope::get_level({}): tc.infer failed: {e}",
          ty.pretty()
        ),
      }
    })?;
    let ku = self.tc.ensure_sort(&inferred).map_err(|e| {
      crate::ix::ixon::CompileError::UnsupportedExpr {
        desc: format!("TcScope::get_level: ensure_sort failed: {e}"),
      }
    })?;
    Ok(super::below::kuniv_to_level(&ku, self.param_names))
  }
}

// No Drop impl needed — the TC is owned and discarded with the scope.
// Context cleanup (pop_local) is unnecessary since the TC dies here.

/// Static version of `to_kexpr` that takes borrowed references.
///
/// Identical to the closure-based `to_kexpr` in `get_level`, but as a
/// standalone function so it can be called from both `PreparedTC::new`
/// and `get_level_with_tc`.
fn to_kexpr_static(
  expr: &LeanExpr,
  fvar_levels: &FxHashMap<Name, usize>,
  ctx_depth: usize,
  param_names: &[Name],
  stt: &crate::ix::compile::CompileState,
) -> crate::ix::kernel::expr::KExpr<Meta> {
  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
  use crate::ix::kernel::expr::KExpr;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::level::KUniv;

  match expr.as_data() {
    ExprData::Fvar(fname, _) => {
      if let Some(&level) = fvar_levels.get(fname) {
        KExpr::var((ctx_depth - level - 1) as u64, Name::anon())
      } else {
        KExpr::sort(KUniv::zero())
      }
    },
    ExprData::Bvar(idx, _) => {
      KExpr::var(idx.to_u64().unwrap_or(0), Name::anon())
    },
    ExprData::Sort(lvl, _) => {
      KExpr::sort(lean_level_to_kuniv(lvl, param_names))
    },
    ExprData::Const(cname, us, _) => {
      let addr = resolve_lean_name_addr(cname, n2a, aux_n2a);
      let zid = KId::new(addr, cname.clone());
      let zus: Box<[KUniv<Meta>]> =
        us.iter().map(|u| lean_level_to_kuniv(u, param_names)).collect();
      KExpr::cnst(zid, zus)
    },
    ExprData::App(f, a, _) => {
      let kf = to_kexpr_static(f, fvar_levels, ctx_depth, param_names, stt);
      let ka = to_kexpr_static(a, fvar_levels, ctx_depth, param_names, stt);
      KExpr::app(kf, ka)
    },
    ExprData::ForallE(binder_name, dom, body, bi, _) => {
      let kd = to_kexpr_static(dom, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::all(binder_name.clone(), bi.clone(), kd, kb)
    },
    ExprData::Lam(binder_name, dom, body, bi, _) => {
      let kd = to_kexpr_static(dom, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::lam(binder_name.clone(), bi.clone(), kd, kb)
    },
    ExprData::LetE(binder_name, ty, val, body, nd, _) => {
      let kt = to_kexpr_static(ty, fvar_levels, ctx_depth, param_names, stt);
      let kv = to_kexpr_static(val, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::let_(binder_name.clone(), kt, kv, kb, *nd)
    },
    ExprData::Proj(pname, idx, e, _) => {
      let addr = resolve_lean_name_addr(pname, n2a, aux_n2a);
      let zid = KId::new(addr, pname.clone());
      let ke = to_kexpr_static(e, fvar_levels, ctx_depth, param_names, stt);
      KExpr::prj(zid, idx.to_u64().unwrap_or(0), ke)
    },
    ExprData::Lit(lit, _) => {
      use crate::ix::env::Literal;
      match lit {
        Literal::NatVal(n) => {
          let addr = Address::hash(&n.to_u64().unwrap_or(0).to_le_bytes());
          KExpr::nat(n.clone(), addr)
        },
        Literal::StrVal(s) => {
          let addr = Address::hash(s.as_bytes());
          KExpr::str(s.clone(), addr)
        },
      }
    },
    ExprData::Mdata(_, inner, _) => {
      to_kexpr_static(inner, fvar_levels, ctx_depth, param_names, stt)
    },
    _ => crate::ix::kernel::expr::KExpr::sort(
      crate::ix::kernel::level::KUniv::zero(),
    ),
  }
}
