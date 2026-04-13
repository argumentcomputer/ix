//! Shared expression manipulation utilities for auxiliary generation.
//!
//! Provides FVar-based expression construction: create fresh free variables,
//! open forall telescopes, build expressions using FVar references, then
//! abstract back into de Bruijn binder chains with `mk_forall`/`mk_lambda`.
//!
//! Also includes substitution, shifting, and universe manipulation helpers
//! used across `recursor.rs`, `below.rs`, and `brecon.rs`.

use crate::ix::env::{
  BinderInfo, Expr as LeanExpr, ExprData, Level, LevelData, Name,
};
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

/// Abstract an FVar: replace all occurrences of `Fvar(fvar_name)` with
/// `BVar(depth)`, and increment all existing BVars >= depth.
/// This is the inverse of `instantiate1`.
///
/// Used when folding expressions with FVars back into forall/lambda chains.
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

/// Build a forall chain by abstracting FVars.
///
/// `binders` is outermost-first. Abstracts from innermost to outermost,
/// building the `∀ (x : T), body` chain. Each FVar in the body and in
/// subsequent domains is replaced with the correct BVar index.
pub(super) fn mk_forall(mut body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  for decl in binders.iter().rev() {
    body = abstract_fvar(&body, &decl.fvar_name, 0);
    let domain = abstract_fvar(&decl.domain, &decl.fvar_name, 0);
    body =
      LeanExpr::all(decl.binder_name.clone(), domain, body, decl.info.clone());
  }
  body
}

/// Build a lambda chain by abstracting FVars.
///
/// Same semantics as `mk_forall` but produces `λ (x : T), body`.
pub(super) fn mk_lambda(mut body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  for decl in binders.iter().rev() {
    body = abstract_fvar(&body, &decl.fvar_name, 0);
    let domain = abstract_fvar(&decl.domain, &decl.fvar_name, 0);
    body =
      LeanExpr::lam(decl.binder_name.clone(), domain, body, decl.info.clone());
  }
  body
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
    LevelData::Succ(l, _) => Level::succ(subst_level(l, params, univs)),
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
