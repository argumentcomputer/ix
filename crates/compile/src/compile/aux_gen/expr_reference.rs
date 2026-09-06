//! Frozen pre-memoization implementations for differential tests only.
#![allow(dead_code)]

use super::expr_utils::{LocalDecl, fresh_fvar};
use crate::compile::nat_conv::{nat_to_u64, nat_to_usize};
use bignat::Nat;
use ix_common::env::{Expr as LeanExpr, ExprData, Level, LevelData, Name};
use rustc_hash::FxHashMap;

#[derive(Clone, Copy)]
enum BinderKind {
  Forall,
  Lambda,
}

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
    // Peel any Mdata wrappers before matching — they're structural no-ops.
    while let ExprData::Mdata(_, inner, _) = cur.as_data() {
      cur = inner.clone();
    }
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

pub(super) fn mk_forall(body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  mk_binder_chain(body, binders, BinderKind::Forall)
}

pub(super) fn mk_lambda(body: LeanExpr, binders: &[LocalDecl]) -> LeanExpr {
  mk_binder_chain(body, binders, BinderKind::Lambda)
}

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
      let i = nat_to_u64(idx);
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
      let i = nat_to_u64(idx);
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

pub(super) fn instantiate_rev(body: &LeanExpr, args: &[LeanExpr]) -> LeanExpr {
  if args.is_empty() {
    return body.clone();
  }
  instantiate_rev_at(body, args, 0)
}

fn instantiate_rev_at(
  body: &LeanExpr,
  args: &[LeanExpr],
  depth: u64,
) -> LeanExpr {
  let n = args.len() as u64;
  match body.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_u64(idx);
      if i >= depth {
        let ridx = i - depth;
        if ridx < n {
          // Replace with args[ridx], shifted up by depth for the binders we're under.
          shift_vars(&args[ridx as usize], depth as usize, 0)
        } else {
          // Free BVar past our substitution range: decrement by n.
          LeanExpr::bvar(Nat::from(i - n))
        }
      } else {
        // Bound by an expression-internal binder — unchanged.
        body.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      instantiate_rev_at(f, args, depth),
      instantiate_rev_at(a, args, depth),
    ),
    ExprData::Lam(name, t, b, bi, _) => LeanExpr::lam(
      name.clone(),
      instantiate_rev_at(t, args, depth),
      instantiate_rev_at(b, args, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(name, t, b, bi, _) => LeanExpr::all(
      name.clone(),
      instantiate_rev_at(t, args, depth),
      instantiate_rev_at(b, args, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(name, t, v, b, nd, _) => LeanExpr::letE(
      name.clone(),
      instantiate_rev_at(t, args, depth),
      instantiate_rev_at(v, args, depth),
      instantiate_rev_at(b, args, depth + 1),
      *nd,
    ),
    ExprData::Proj(name, i, e, _) => LeanExpr::proj(
      name.clone(),
      i.clone(),
      instantiate_rev_at(e, args, depth),
    ),
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), instantiate_rev_at(e, args, depth))
    },
    // Sort, Const, Lit, FVar, MVar — no BVars to substitute.
    _ => body.clone(),
  }
}

pub(crate) fn instantiate_pi_params(
  typ: &LeanExpr,
  n: usize,
  args: &[LeanExpr],
) -> LeanExpr {
  debug_assert!(
    args.len() >= n,
    "instantiate_pi_params: args.len()={} < n={}",
    args.len(),
    n
  );
  let mut cur = typ.clone();
  for arg in args.iter().take(n) {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        cur = instantiate_rev(body, std::slice::from_ref(arg));
      },
      _ => break,
    }
  }
  cur
}

pub(crate) fn shift_vars(
  expr: &LeanExpr,
  amount: usize,
  cutoff: usize,
) -> LeanExpr {
  if amount == 0 {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_usize(idx);
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

pub(crate) fn lower_vars(
  expr: &LeanExpr,
  amount: usize,
  cutoff: usize,
) -> LeanExpr {
  if amount == 0 {
    return expr.clone();
  }
  match expr.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_usize(idx);
      if i >= cutoff + amount {
        LeanExpr::bvar(Nat::from((i - amount) as u64))
      } else {
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      lower_vars(f, amount, cutoff),
      lower_vars(a, amount, cutoff),
    ),
    ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
      n.clone(),
      lower_vars(t, amount, cutoff),
      lower_vars(b, amount, cutoff + 1),
      bi.clone(),
    ),
    ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
      n.clone(),
      lower_vars(t, amount, cutoff),
      lower_vars(b, amount, cutoff + 1),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      lower_vars(t, amount, cutoff),
      lower_vars(v, amount, cutoff),
      lower_vars(b, amount, cutoff + 1),
      *nd,
    ),
    ExprData::Proj(n, i, e, _) => {
      LeanExpr::proj(n.clone(), i.clone(), lower_vars(e, amount, cutoff))
    },
    ExprData::Mdata(kvs, e, _) => {
      LeanExpr::mdata(kvs.clone(), lower_vars(e, amount, cutoff))
    },
    _ => expr.clone(),
  }
}

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

pub(super) fn subst_level(
  lvl: &Level,
  params: &[Name],
  univs: &[Level],
) -> Level {
  match lvl.as_data() {
    LevelData::Zero(_) | LevelData::Mvar(_, _) => lvl.clone(),
    LevelData::Succ(l, _) => Level::succ(subst_level(l, params, univs)),
    LevelData::Max(a, b, _) => Level::max_smart(
      subst_level(a, params, univs),
      subst_level(b, params, univs),
    ),
    LevelData::Imax(a, b, _) => Level::imax_smart(
      subst_level(a, params, univs),
      subst_level(b, params, univs),
    ),
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
