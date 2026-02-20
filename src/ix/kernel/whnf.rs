use core::ptr::NonNull;

use crate::ix::env::*;
use crate::lean::nat::Nat;
use num_bigint::BigUint;

use super::convert::{from_expr, to_expr};
use super::dag::*;
use super::level::{simplify, subst_level};
use super::upcopy::{reduce_lam, reduce_let};
use crate::ix::env::Literal;

// ============================================================================
// Expression helpers (inst, unfold_apps, foldl_apps, subst_expr_levels)
// ============================================================================

/// Instantiate bound variables: `body[0 := substs[n-1], 1 := substs[n-2], ...]`.
/// Follows Lean 4's `instantiate` convention: `substs[0]` is the outermost
/// variable and replaces `Bvar(n-1)`, while `substs[n-1]` is the innermost
/// and replaces `Bvar(0)`.
pub fn inst(body: &Expr, substs: &[Expr]) -> Expr {
  if substs.is_empty() {
    return body.clone();
  }
  inst_aux(body, substs, 0)
}

fn inst_aux(e: &Expr, substs: &[Expr], offset: u64) -> Expr {
  enum Frame<'a> {
    Visit(&'a Expr, u64),
    App,
    Lam(Name, BinderInfo),
    All(Name, BinderInfo),
    LetE(Name, bool),
    Proj(Name, Nat),
    Mdata(Vec<(Name, DataValue)>),
  }

  let mut work: Vec<Frame<'_>> = vec![Frame::Visit(e, offset)];
  let mut results: Vec<Expr> = Vec::new();

  while let Some(frame) = work.pop() {
    match frame {
      Frame::Visit(e, offset) => match e.as_data() {
        ExprData::Bvar(idx, _) => {
          let idx_u64 = idx.to_u64().unwrap_or(u64::MAX);
          if idx_u64 >= offset {
            let adjusted = (idx_u64 - offset) as usize;
            if adjusted < substs.len() {
              // Lean 4 convention: substs[0] = outermost, substs[n-1] = innermost
              // bvar(0) = innermost → substs[n-1], bvar(n-1) = outermost → substs[0]
              results.push(substs[substs.len() - 1 - adjusted].clone());
              continue;
            }
          }
          results.push(e.clone());
        },
        ExprData::App(f, a, _) => {
          work.push(Frame::App);
          work.push(Frame::Visit(a, offset));
          work.push(Frame::Visit(f, offset));
        },
        ExprData::Lam(n, t, b, bi, _) => {
          work.push(Frame::Lam(n.clone(), bi.clone()));
          work.push(Frame::Visit(b, offset + 1));
          work.push(Frame::Visit(t, offset));
        },
        ExprData::ForallE(n, t, b, bi, _) => {
          work.push(Frame::All(n.clone(), bi.clone()));
          work.push(Frame::Visit(b, offset + 1));
          work.push(Frame::Visit(t, offset));
        },
        ExprData::LetE(n, t, v, b, nd, _) => {
          work.push(Frame::LetE(n.clone(), *nd));
          work.push(Frame::Visit(b, offset + 1));
          work.push(Frame::Visit(v, offset));
          work.push(Frame::Visit(t, offset));
        },
        ExprData::Proj(n, i, s, _) => {
          work.push(Frame::Proj(n.clone(), i.clone()));
          work.push(Frame::Visit(s, offset));
        },
        ExprData::Mdata(kvs, inner, _) => {
          work.push(Frame::Mdata(kvs.clone()));
          work.push(Frame::Visit(inner, offset));
        },
        ExprData::Sort(..)
        | ExprData::Const(..)
        | ExprData::Fvar(..)
        | ExprData::Mvar(..)
        | ExprData::Lit(..) => results.push(e.clone()),
      },
      Frame::App => {
        let a = results.pop().unwrap();
        let f = results.pop().unwrap();
        results.push(Expr::app(f, a));
      },
      Frame::Lam(n, bi) => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::lam(n, t, b, bi));
      },
      Frame::All(n, bi) => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::all(n, t, b, bi));
      },
      Frame::LetE(n, nd) => {
        let b = results.pop().unwrap();
        let v = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::letE(n, t, v, b, nd));
      },
      Frame::Proj(n, i) => {
        let s = results.pop().unwrap();
        results.push(Expr::proj(n, i, s));
      },
      Frame::Mdata(kvs) => {
        let inner = results.pop().unwrap();
        results.push(Expr::mdata(kvs, inner));
      },
    }
  }

  results.pop().unwrap()
}

/// Abstract: replace free variables with bound variables.
/// Follows Lean 4 convention: `fvars[0]` (outermost) maps to `Bvar(n-1+offset)`,
/// `fvars[n-1]` (innermost) maps to `Bvar(0+offset)`.
pub fn abstr(e: &Expr, fvars: &[Expr]) -> Expr {
  if fvars.is_empty() {
    return e.clone();
  }
  abstr_aux(e, fvars, 0)
}

fn abstr_aux(e: &Expr, fvars: &[Expr], offset: u64) -> Expr {
  enum Frame<'a> {
    Visit(&'a Expr, u64),
    App,
    Lam(Name, BinderInfo),
    All(Name, BinderInfo),
    LetE(Name, bool),
    Proj(Name, Nat),
    Mdata(Vec<(Name, DataValue)>),
  }

  let mut work: Vec<Frame<'_>> = vec![Frame::Visit(e, offset)];
  let mut results: Vec<Expr> = Vec::new();

  while let Some(frame) = work.pop() {
    match frame {
      Frame::Visit(e, offset) => match e.as_data() {
        ExprData::Fvar(..) => {
          let n = fvars.len();
          let mut found = false;
          for (i, fv) in fvars.iter().enumerate() {
            if e == fv {
              // fvars[0] (outermost) → Bvar(n-1+offset)
              // fvars[n-1] (innermost) → Bvar(0+offset)
              let bvar_idx = (n - 1 - i) as u64 + offset;
              results.push(Expr::bvar(Nat::from(bvar_idx)));
              found = true;
              break;
            }
          }
          if !found {
            results.push(e.clone());
          }
        },
        ExprData::App(f, a, _) => {
          work.push(Frame::App);
          work.push(Frame::Visit(a, offset));
          work.push(Frame::Visit(f, offset));
        },
        ExprData::Lam(n, t, b, bi, _) => {
          work.push(Frame::Lam(n.clone(), bi.clone()));
          work.push(Frame::Visit(b, offset + 1));
          work.push(Frame::Visit(t, offset));
        },
        ExprData::ForallE(n, t, b, bi, _) => {
          work.push(Frame::All(n.clone(), bi.clone()));
          work.push(Frame::Visit(b, offset + 1));
          work.push(Frame::Visit(t, offset));
        },
        ExprData::LetE(n, t, v, b, nd, _) => {
          work.push(Frame::LetE(n.clone(), *nd));
          work.push(Frame::Visit(b, offset + 1));
          work.push(Frame::Visit(v, offset));
          work.push(Frame::Visit(t, offset));
        },
        ExprData::Proj(n, i, s, _) => {
          work.push(Frame::Proj(n.clone(), i.clone()));
          work.push(Frame::Visit(s, offset));
        },
        ExprData::Mdata(kvs, inner, _) => {
          work.push(Frame::Mdata(kvs.clone()));
          work.push(Frame::Visit(inner, offset));
        },
        ExprData::Bvar(..)
        | ExprData::Sort(..)
        | ExprData::Const(..)
        | ExprData::Mvar(..)
        | ExprData::Lit(..) => results.push(e.clone()),
      },
      Frame::App => {
        let a = results.pop().unwrap();
        let f = results.pop().unwrap();
        results.push(Expr::app(f, a));
      },
      Frame::Lam(n, bi) => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::lam(n, t, b, bi));
      },
      Frame::All(n, bi) => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::all(n, t, b, bi));
      },
      Frame::LetE(n, nd) => {
        let b = results.pop().unwrap();
        let v = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::letE(n, t, v, b, nd));
      },
      Frame::Proj(n, i) => {
        let s = results.pop().unwrap();
        results.push(Expr::proj(n, i, s));
      },
      Frame::Mdata(kvs) => {
        let inner = results.pop().unwrap();
        results.push(Expr::mdata(kvs, inner));
      },
    }
  }

  results.pop().unwrap()
}

/// Decompose `f a1 a2 ... an` into `(f, [a1, a2, ..., an])`.
pub fn unfold_apps(e: &Expr) -> (Expr, Vec<Expr>) {
  let mut args = Vec::new();
  let mut cursor = e.clone();
  loop {
    match cursor.as_data() {
      ExprData::App(f, a, _) => {
        args.push(a.clone());
        cursor = f.clone();
      },
      _ => break,
    }
  }
  args.reverse();
  (cursor, args)
}

/// Reconstruct `f a1 a2 ... an`.
pub fn foldl_apps(mut fun: Expr, args: impl Iterator<Item = Expr>) -> Expr {
  for arg in args {
    fun = Expr::app(fun, arg);
  }
  fun
}

/// Substitute universe level parameters in an expression.
pub fn subst_expr_levels(e: &Expr, params: &[Name], values: &[Level]) -> Expr {
  if params.is_empty() {
    return e.clone();
  }
  subst_expr_levels_aux(e, params, values)
}

fn subst_expr_levels_aux(e: &Expr, params: &[Name], values: &[Level]) -> Expr {
  use rustc_hash::FxHashMap;
  use std::sync::Arc;

  enum Frame<'a> {
    Visit(&'a Expr),
    CacheResult(*const ExprData),
    App,
    Lam(Name, BinderInfo),
    All(Name, BinderInfo),
    LetE(Name, bool),
    Proj(Name, Nat),
    Mdata(Vec<(Name, DataValue)>),
  }

  let mut cache: FxHashMap<*const ExprData, Expr> = FxHashMap::default();
  let mut work: Vec<Frame<'_>> = vec![Frame::Visit(e)];
  let mut results: Vec<Expr> = Vec::new();

  while let Some(frame) = work.pop() {
    match frame {
      Frame::Visit(e) => {
        let key = Arc::as_ptr(&e.0);
        if let Some(cached) = cache.get(&key) {
          results.push(cached.clone());
          continue;
        }
        match e.as_data() {
          ExprData::Sort(level, _) => {
            let r = Expr::sort(subst_level(level, params, values));
            cache.insert(key, r.clone());
            results.push(r);
          },
          ExprData::Const(name, levels, _) => {
            let new_levels: Vec<Level> =
              levels.iter().map(|l| subst_level(l, params, values)).collect();
            let r = Expr::cnst(name.clone(), new_levels);
            cache.insert(key, r.clone());
            results.push(r);
          },
          ExprData::App(f, a, _) => {
            work.push(Frame::CacheResult(key));
            work.push(Frame::App);
            work.push(Frame::Visit(a));
            work.push(Frame::Visit(f));
          },
          ExprData::Lam(n, t, b, bi, _) => {
            work.push(Frame::CacheResult(key));
            work.push(Frame::Lam(n.clone(), bi.clone()));
            work.push(Frame::Visit(b));
            work.push(Frame::Visit(t));
          },
          ExprData::ForallE(n, t, b, bi, _) => {
            work.push(Frame::CacheResult(key));
            work.push(Frame::All(n.clone(), bi.clone()));
            work.push(Frame::Visit(b));
            work.push(Frame::Visit(t));
          },
          ExprData::LetE(n, t, v, b, nd, _) => {
            work.push(Frame::CacheResult(key));
            work.push(Frame::LetE(n.clone(), *nd));
            work.push(Frame::Visit(b));
            work.push(Frame::Visit(v));
            work.push(Frame::Visit(t));
          },
          ExprData::Proj(n, i, s, _) => {
            work.push(Frame::CacheResult(key));
            work.push(Frame::Proj(n.clone(), i.clone()));
            work.push(Frame::Visit(s));
          },
          ExprData::Mdata(kvs, inner, _) => {
            work.push(Frame::CacheResult(key));
            work.push(Frame::Mdata(kvs.clone()));
            work.push(Frame::Visit(inner));
          },
          ExprData::Bvar(..)
          | ExprData::Fvar(..)
          | ExprData::Mvar(..)
          | ExprData::Lit(..) => {
            cache.insert(key, e.clone());
            results.push(e.clone());
          },
        }
      },
      Frame::CacheResult(key) => {
        let result = results.last().unwrap().clone();
        cache.insert(key, result);
      },
      Frame::App => {
        let a = results.pop().unwrap();
        let f = results.pop().unwrap();
        results.push(Expr::app(f, a));
      },
      Frame::Lam(n, bi) => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::lam(n, t, b, bi));
      },
      Frame::All(n, bi) => {
        let b = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::all(n, t, b, bi));
      },
      Frame::LetE(n, nd) => {
        let b = results.pop().unwrap();
        let v = results.pop().unwrap();
        let t = results.pop().unwrap();
        results.push(Expr::letE(n, t, v, b, nd));
      },
      Frame::Proj(n, i) => {
        let s = results.pop().unwrap();
        results.push(Expr::proj(n, i, s));
      },
      Frame::Mdata(kvs) => {
        let inner = results.pop().unwrap();
        results.push(Expr::mdata(kvs, inner));
      },
    }
  }

  results.pop().unwrap()
}

/// Check if an expression has any loose bound variables above `offset`.
pub fn has_loose_bvars(e: &Expr) -> bool {
  has_loose_bvars_aux(e, 0)
}

fn has_loose_bvars_aux(e: &Expr, depth: u64) -> bool {
  let mut stack: Vec<(&Expr, u64)> = vec![(e, depth)];
  while let Some((e, depth)) = stack.pop() {
    match e.as_data() {
      ExprData::Bvar(idx, _) => {
        if idx.to_u64().unwrap_or(u64::MAX) >= depth {
          return true;
        }
      },
      ExprData::App(f, a, _) => {
        stack.push((f, depth));
        stack.push((a, depth));
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push((t, depth));
        stack.push((b, depth + 1));
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push((t, depth));
        stack.push((v, depth));
        stack.push((b, depth + 1));
      },
      ExprData::Proj(_, _, s, _) => stack.push((s, depth)),
      ExprData::Mdata(_, inner, _) => stack.push((inner, depth)),
      _ => {},
    }
  }
  false
}

/// Check if expression contains any free variables (Fvar).
pub fn has_fvars(e: &Expr) -> bool {
  let mut stack: Vec<&Expr> = vec![e];
  while let Some(e) = stack.pop() {
    match e.as_data() {
      ExprData::Fvar(..) => return true,
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(t);
        stack.push(b);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(t);
        stack.push(v);
        stack.push(b);
      },
      ExprData::Proj(_, _, s, _) => stack.push(s),
      ExprData::Mdata(_, inner, _) => stack.push(inner),
      _ => {},
    }
  }
  false
}

// ============================================================================
// Name helpers
// ============================================================================

pub(crate) fn mk_name2(a: &str, b: &str) -> Name {
  Name::str(Name::str(Name::anon(), a.into()), b.into())
}

// ============================================================================
// WHNF
// ============================================================================

/// Weak head normal form reduction.
///
/// Uses DAG-based reduction internally: converts Expr to DAG, reduces using
/// BUBS (reduce_lam/reduce_let) for beta/zeta, falls back to Expr level for
/// iota/quot/nat/projection, and uses DAG-level splicing for delta.
pub fn whnf(e: &Expr, env: &Env) -> Expr {
  let mut dag = from_expr(e);
  whnf_dag(&mut dag, env, false);
  let result = to_expr(&dag);
  free_dag(dag);
  result
}



/// WHNF without delta reduction (beta/zeta/iota/quot/nat/proj only).
/// Matches Lean 4's `whnf_core` used in `is_def_eq_core`.
pub fn whnf_no_delta(e: &Expr, env: &Env) -> Expr {
  let mut dag = from_expr(e);
  whnf_dag(&mut dag, env, true);
  let result = to_expr(&dag);
  free_dag(dag);
  result
}


/// Trail-based WHNF on DAG. Walks down the App spine collecting a trail,
/// then dispatches on the head node.
/// When `no_delta` is true, skips delta (definition) unfolding.
pub(crate) fn whnf_dag(dag: &mut DAG, env: &Env, no_delta: bool) {
  use std::sync::atomic::{AtomicU64, Ordering};
  static WHNF_DEPTH: AtomicU64 = AtomicU64::new(0);
  static WHNF_TOTAL: AtomicU64 = AtomicU64::new(0);

  let depth = WHNF_DEPTH.fetch_add(1, Ordering::Relaxed);
  let total = WHNF_TOTAL.fetch_add(1, Ordering::Relaxed);
  if depth > 50 || total % 10_000 == 0 {
    eprintln!("[whnf_dag] depth={depth} total={total} no_delta={no_delta}");
  }
  if depth > 200 {
    eprintln!("[whnf_dag] DEPTH LIMIT depth={depth}, bailing");
    WHNF_DEPTH.fetch_sub(1, Ordering::Relaxed);
    return;
  }

  const WHNF_STEP_LIMIT: u64 = 100_000;
  let mut steps: u64 = 0;
  let whnf_done = |depth| { WHNF_DEPTH.fetch_sub(1, Ordering::Relaxed); };
  loop {
    steps += 1;
    if steps > WHNF_STEP_LIMIT {
      eprintln!("[whnf_dag] step limit exceeded ({steps}) depth={depth}");
      whnf_done(depth);
      return;
    }
    if steps <= 5 || steps % 10_000 == 0 {
      let head_variant = match dag.head {
        DAGPtr::Var(_) => "Var", DAGPtr::Sort(_) => "Sort", DAGPtr::Cnst(_) => "Cnst",
        DAGPtr::App(_) => "App", DAGPtr::Fun(_) => "Fun", DAGPtr::Pi(_) => "Pi",
        DAGPtr::Let(_) => "Let", DAGPtr::Lit(_) => "Lit", DAGPtr::Proj(_) => "Proj",
        DAGPtr::Lam(_) => "Lam",
      };
      eprintln!("[whnf_dag] step={steps} head={head_variant} trail_build_start");
    }
    // Build trail of App nodes by walking down the fun chain
    let mut trail: Vec<NonNull<App>> = Vec::new();
    let mut cursor = dag.head;

    loop {
      match cursor {
        DAGPtr::App(app) => {
          trail.push(app);
          if trail.len() > 100_000 {
            eprintln!("[whnf_dag] TRAIL OVERFLOW: trail.len()={} — possible App cycle!", trail.len());
            whnf_done(depth); return;
          }
          cursor = unsafe { (*app.as_ptr()).fun };
        },
        _ => break,
      }
    }

    if steps <= 5 || steps % 10_000 == 0 {
      let cursor_variant = match cursor {
        DAGPtr::Var(_) => "Var", DAGPtr::Sort(_) => "Sort", DAGPtr::Cnst(_) => "Cnst",
        DAGPtr::App(_) => "App", DAGPtr::Fun(_) => "Fun", DAGPtr::Pi(_) => "Pi",
        DAGPtr::Let(_) => "Let", DAGPtr::Lit(_) => "Lit", DAGPtr::Proj(_) => "Proj",
        DAGPtr::Lam(_) => "Lam",
      };
      eprintln!("[whnf_dag] step={steps} trail_len={} cursor={cursor_variant}", trail.len());
    }

    match cursor {
      // Beta: Fun at head with args on trail
      DAGPtr::Fun(fun_ptr) if !trail.is_empty() => {
        let app = trail.pop().unwrap();
        let lam = unsafe { (*fun_ptr.as_ptr()).img };
        let result = reduce_lam(app, lam);
        set_dag_head(dag, result, &trail);
        continue;
      },

      // Zeta: Let at head
      DAGPtr::Let(let_ptr) => {
        let result = reduce_let(let_ptr);
        set_dag_head(dag, result, &trail);
        continue;
      },

      // Const: try iota, quot, nat, then delta
      DAGPtr::Cnst(_) => {
        // Try iota, quot, nat
        if try_dag_reductions(dag, env) {
          continue;
        }
        // Try delta (definition unfolding) on DAG, unless no_delta
        if !no_delta && try_dag_delta(dag, &trail, env) {
          continue;
        }
        whnf_done(depth); return; // stuck
      },

      // Proj: try projection reduction (Expr-level fallback)
      DAGPtr::Proj(_) => {
        if try_dag_reductions(dag, env) {
          continue;
        }
        whnf_done(depth); return; // stuck
      },

      // Sort: simplify level in place
      DAGPtr::Sort(sort_ptr) => {
        unsafe {
          let sort = &mut *sort_ptr.as_ptr();
          sort.level = simplify(&sort.level);
        }
        whnf_done(depth); return;
      },

      // Mdata: strip metadata (Expr-level fallback)
      DAGPtr::Lit(_) => {
        // Check if this is a Nat literal that could be a Nat.succ application
        // by trying Expr-level reductions (which handles nat ops)
        if !trail.is_empty() {
          if try_dag_reductions(dag, env) {
            continue;
          }
        }
        whnf_done(depth); return;
      },

      // Everything else (Var, Pi, Lam without args, etc.): already WHNF
      _ => { whnf_done(depth); return; },
    }
  }
}

/// Set the DAG head after a reduction step.
/// If trail is empty, the result becomes the new head.
/// If trail is non-empty, splice result into the innermost remaining App.
fn set_dag_head(dag: &mut DAG, result: DAGPtr, trail: &[NonNull<App>]) {
  if trail.is_empty() {
    dag.head = result;
  } else {
    unsafe {
      (*trail.last().unwrap().as_ptr()).fun = result;
    }
    dag.head = DAGPtr::App(trail[0]);
  }
}

/// Try iota/quot/nat/projection reductions directly on DAG.
fn try_dag_reductions(dag: &mut DAG, env: &Env) -> bool {
  let (head, args) = dag_unfold_apps(dag.head);

  let reduced = match head {
    DAGPtr::Cnst(cnst) => unsafe {
      let cnst_ref = &*cnst.as_ptr();
      if let Some(result) =
        try_reduce_rec_dag(&cnst_ref.name, &cnst_ref.levels, &args, env)
      {
        Some(result)
      } else if let Some(result) =
        try_reduce_quot_dag(&cnst_ref.name, &args, env)
      {
        Some(result)
      } else if let Some(result) =
        try_reduce_native_dag(&cnst_ref.name, &args)
      {
        Some(result)
      } else if let Some(result) =
        try_reduce_nat_dag(&cnst_ref.name, &args, env)
      {
        Some(result)
      } else {
        None
      }
    },
    DAGPtr::Proj(proj) => unsafe {
      let proj_ref = &*proj.as_ptr();
      reduce_proj_dag(&proj_ref.type_name, &proj_ref.idx, proj_ref.expr, env)
        .map(|result| dag_foldl_apps(result, &args))
    },
    _ => None,
  };

  if let Some(result) = reduced {
    dag.head = result;
    true
  } else {
    false
  }
}

/// Try to reduce a recursor application (iota reduction) on DAG.
fn try_reduce_rec_dag(
  name: &Name,
  levels: &[Level],
  args: &[DAGPtr],
  env: &Env,
) -> Option<DAGPtr> {
  let ci = env.get(name)?;
  let rec = match ci {
    ConstantInfo::RecInfo(r) => r,
    _ => return None,
  };

  let major_idx = rec.num_params.to_u64().unwrap() as usize
    + rec.num_motives.to_u64().unwrap() as usize
    + rec.num_minors.to_u64().unwrap() as usize
    + rec.num_indices.to_u64().unwrap() as usize;

  let major = args.get(major_idx)?;

  // WHNF the major premise directly on the DAG
  let mut major_dag = DAG { head: *major };
  whnf_dag(&mut major_dag, env, false);

  // Decompose the major premise into (ctor_head, ctor_args) at DAG level.
  // Handle nat literal → constructor form as DAG nodes directly.
  let (ctor_head, ctor_args) = match major_dag.head {
    DAGPtr::Lit(lit) => unsafe {
      match &(*lit.as_ptr()).val {
        Literal::NatVal(n) => {
          if n.0 == BigUint::ZERO {
            let zero = DAGPtr::Cnst(alloc_val(Cnst {
              name: mk_name2("Nat", "zero"),
              levels: vec![],
              parents: None,
            }));
            (zero, vec![])
          } else {
            let pred = Nat(n.0.clone() - BigUint::from(1u64));
            let succ = DAGPtr::Cnst(alloc_val(Cnst {
              name: mk_name2("Nat", "succ"),
              levels: vec![],
              parents: None,
            }));
            let pred_lit = nat_lit_dag(pred);
            (succ, vec![pred_lit])
          }
        },
        _ => return None,
      }
    },
    _ => dag_unfold_apps(major_dag.head),
  };

  // Find the matching rec rule by reading ctor name from DAG head
  let ctor_name = match ctor_head {
    DAGPtr::Cnst(cnst) => unsafe { &(*cnst.as_ptr()).name },
    _ => return None,
  };

  let rule = rec.rules.iter().find(|r| r.ctor == *ctor_name)?;

  let n_fields = rule.n_fields.to_u64().unwrap() as usize;
  let num_params = rec.num_params.to_u64().unwrap() as usize;
  let num_motives = rec.num_motives.to_u64().unwrap() as usize;
  let num_minors = rec.num_minors.to_u64().unwrap() as usize;

  if ctor_args.len() < n_fields {
    return None;
  }
  let ctor_fields = &ctor_args[ctor_args.len() - n_fields..];

  // Build RHS as DAG: from_expr(subst_expr_levels(rule.rhs, ...)) once
  // (unavoidable — rule RHS is stored as Expr in Env)
  let rhs_expr = subst_expr_levels(&rule.rhs, &rec.cnst.level_params, levels);
  let rhs_dag = from_expr(&rhs_expr);

  // Collect all args at DAG level: params+motives+minors, ctor_fields, rest
  let prefix_count = num_params + num_motives + num_minors;
  let mut all_args: Vec<DAGPtr> =
    Vec::with_capacity(prefix_count + n_fields + args.len() - major_idx - 1);
  all_args.extend_from_slice(&args[..prefix_count]);
  all_args.extend_from_slice(ctor_fields);
  all_args.extend_from_slice(&args[major_idx + 1..]);

  Some(dag_foldl_apps(rhs_dag.head, &all_args))
}

/// Try to reduce a projection on DAG.
fn reduce_proj_dag(
  _type_name: &Name,
  idx: &Nat,
  structure: DAGPtr,
  env: &Env,
) -> Option<DAGPtr> {
  // WHNF the structure directly on the DAG
  let mut struct_dag = DAG { head: structure };
  whnf_dag(&mut struct_dag, env, false);

  // Handle string literal → constructor form at DAG level
  let struct_whnf = match struct_dag.head {
    DAGPtr::Lit(lit) => unsafe {
      match &(*lit.as_ptr()).val {
        Literal::StrVal(s) => string_lit_to_dag_ctor(s),
        _ => struct_dag.head,
      }
    },
    _ => struct_dag.head,
  };

  // Decompose at DAG level
  let (ctor_head, ctor_args) = dag_unfold_apps(struct_whnf);

  let ctor_name = match ctor_head {
    DAGPtr::Cnst(cnst) => unsafe { &(*cnst.as_ptr()).name },
    _ => return None,
  };

  let ci = env.get(ctor_name)?;
  let num_params = match ci {
    ConstantInfo::CtorInfo(c) => c.num_params.to_u64().unwrap() as usize,
    _ => return None,
  };

  let field_idx = num_params + idx.to_u64().unwrap() as usize;
  ctor_args.get(field_idx).copied()
}

/// Try to reduce a quotient operation on DAG.
fn try_reduce_quot_dag(
  name: &Name,
  args: &[DAGPtr],
  env: &Env,
) -> Option<DAGPtr> {
  let ci = env.get(name)?;
  let kind = match ci {
    ConstantInfo::QuotInfo(q) => &q.kind,
    _ => return None,
  };

  let (qmk_idx, rest_idx) = match kind {
    QuotKind::Lift => (5, 6),
    QuotKind::Ind => (4, 5),
    _ => return None,
  };

  let qmk = args.get(qmk_idx)?;

  // WHNF the Quot.mk arg directly on the DAG
  let mut qmk_dag = DAG { head: *qmk };
  whnf_dag(&mut qmk_dag, env, false);

  // Check that the head is Quot.mk at DAG level
  let (qmk_head, _) = dag_unfold_apps(qmk_dag.head);
  match qmk_head {
    DAGPtr::Cnst(cnst) => unsafe {
      if (*cnst.as_ptr()).name != mk_name2("Quot", "mk") {
        return None;
      }
    },
    _ => return None,
  }

  let f = args.get(3)?;

  // Extract the argument of Quot.mk (the outermost App's arg)
  let qmk_arg = match qmk_dag.head {
    DAGPtr::App(app) => unsafe { (*app.as_ptr()).arg },
    _ => return None,
  };

  // Build result directly at DAG level: f qmk_arg rest_args...
  let mut result_args = Vec::with_capacity(1 + args.len() - rest_idx);
  result_args.push(qmk_arg);
  result_args.extend_from_slice(&args[rest_idx..]);
  Some(dag_foldl_apps(*f, &result_args))
}

/// Try to reduce `Lean.reduceBool` / `Lean.reduceNat` on DAG.
pub(crate) fn try_reduce_native_dag(name: &Name, args: &[DAGPtr]) -> Option<DAGPtr> {
  if args.len() != 1 {
    return None;
  }
  let reduce_bool = mk_name2("Lean", "reduceBool");
  let reduce_nat = mk_name2("Lean", "reduceNat");
  if *name == reduce_bool || *name == reduce_nat {
    Some(args[0])
  } else {
    None
  }
}

/// Try to reduce nat operations on DAG.
pub(crate) fn try_reduce_nat_dag(
  name: &Name,
  args: &[DAGPtr],
  env: &Env,
) -> Option<DAGPtr> {
  match args.len() {
    1 => {
      if *name == mk_name2("Nat", "succ") {
        // WHNF the arg directly on the DAG
        let mut arg_dag = DAG { head: args[0] };
        whnf_dag(&mut arg_dag, env, false);
        let n = get_nat_value_dag(arg_dag.head)?;
        let result = alloc_val(LitNode {
          val: Literal::NatVal(Nat(n + BigUint::from(1u64))),
          parents: None,
        });
        Some(DAGPtr::Lit(result))
      } else {
        None
      }
    },
    2 => {
      // WHNF both args directly on the DAG
      let mut a_dag = DAG { head: args[0] };
      whnf_dag(&mut a_dag, env, false);
      let mut b_dag = DAG { head: args[1] };
      whnf_dag(&mut b_dag, env, false);
      let a = get_nat_value_dag(a_dag.head)?;
      let b = get_nat_value_dag(b_dag.head)?;

      if *name == mk_name2("Nat", "add") {
        Some(nat_lit_dag(Nat(a + b)))
      } else if *name == mk_name2("Nat", "sub") {
        Some(nat_lit_dag(Nat(if a >= b { a - b } else { BigUint::ZERO })))
      } else if *name == mk_name2("Nat", "mul") {
        Some(nat_lit_dag(Nat(a * b)))
      } else if *name == mk_name2("Nat", "div") {
        Some(nat_lit_dag(Nat(if b == BigUint::ZERO {
          BigUint::ZERO
        } else {
          a / b
        })))
      } else if *name == mk_name2("Nat", "mod") {
        Some(nat_lit_dag(Nat(if b == BigUint::ZERO { a } else { a % b })))
      } else if *name == mk_name2("Nat", "beq") {
        Some(bool_to_dag(a == b))
      } else if *name == mk_name2("Nat", "ble") {
        Some(bool_to_dag(a <= b))
      } else if *name == mk_name2("Nat", "pow") {
        let exp = u32::try_from(&b).unwrap_or(u32::MAX);
        Some(nat_lit_dag(Nat(a.pow(exp))))
      } else if *name == mk_name2("Nat", "land") {
        Some(nat_lit_dag(Nat(a & b)))
      } else if *name == mk_name2("Nat", "lor") {
        Some(nat_lit_dag(Nat(a | b)))
      } else if *name == mk_name2("Nat", "xor") {
        Some(nat_lit_dag(Nat(a ^ b)))
      } else if *name == mk_name2("Nat", "shiftLeft") {
        let shift = u64::try_from(&b).unwrap_or(u64::MAX);
        Some(nat_lit_dag(Nat(a << shift)))
      } else if *name == mk_name2("Nat", "shiftRight") {
        let shift = u64::try_from(&b).unwrap_or(u64::MAX);
        Some(nat_lit_dag(Nat(a >> shift)))
      } else if *name == mk_name2("Nat", "blt") {
        Some(bool_to_dag(a < b))
      } else {
        None
      }
    },
    _ => None,
  }
}

/// Extract a nat value from a DAGPtr (analog of get_nat_value_expr).
fn get_nat_value_dag(ptr: DAGPtr) -> Option<BigUint> {
  unsafe {
    match ptr {
      DAGPtr::Lit(lit) => match &(*lit.as_ptr()).val {
        Literal::NatVal(n) => Some(n.0.clone()),
        _ => None,
      },
      DAGPtr::Cnst(cnst) => {
        if (*cnst.as_ptr()).name == mk_name2("Nat", "zero") {
          Some(BigUint::ZERO)
        } else {
          None
        }
      },
      _ => None,
    }
  }
}

/// Allocate a Nat literal DAG node.
pub(crate) fn nat_lit_dag(n: Nat) -> DAGPtr {
  DAGPtr::Lit(alloc_val(LitNode { val: Literal::NatVal(n), parents: None }))
}

/// Convert a bool to a DAG constant (Bool.true / Bool.false).
fn bool_to_dag(b: bool) -> DAGPtr {
  let name =
    if b { mk_name2("Bool", "true") } else { mk_name2("Bool", "false") };
  DAGPtr::Cnst(alloc_val(Cnst { name, levels: vec![], parents: None }))
}

/// Build `String.mk (List.cons (Char.ofNat n1) (List.cons ... List.nil))`
/// entirely at the DAG level (no Expr round-trip).
fn string_lit_to_dag_ctor(s: &str) -> DAGPtr {
  let list_name = Name::str(Name::anon(), "List".into());
  let char_name = Name::str(Name::anon(), "Char".into());
  let char_type = DAGPtr::Cnst(alloc_val(Cnst {
    name: char_name.clone(),
    levels: vec![],
    parents: None,
  }));
  let nil = DAGPtr::App(alloc_app(
    DAGPtr::Cnst(alloc_val(Cnst {
      name: Name::str(list_name.clone(), "nil".into()),
      levels: vec![Level::succ(Level::zero())],
      parents: None,
    })),
    char_type,
    None,
  ));
  let list = s.chars().rev().fold(nil, |acc, c| {
    let of_nat = DAGPtr::Cnst(alloc_val(Cnst {
      name: Name::str(char_name.clone(), "ofNat".into()),
      levels: vec![],
      parents: None,
    }));
    let char_val =
      DAGPtr::App(alloc_app(of_nat, nat_lit_dag(Nat::from(c as u64)), None));
    let char_type_copy = DAGPtr::Cnst(alloc_val(Cnst {
      name: char_name.clone(),
      levels: vec![],
      parents: None,
    }));
    let cons = DAGPtr::Cnst(alloc_val(Cnst {
      name: Name::str(list_name.clone(), "cons".into()),
      levels: vec![Level::succ(Level::zero())],
      parents: None,
    }));
    let c1 = DAGPtr::App(alloc_app(cons, char_type_copy, None));
    let c2 = DAGPtr::App(alloc_app(c1, char_val, None));
    DAGPtr::App(alloc_app(c2, acc, None))
  });
  let string_mk = DAGPtr::Cnst(alloc_val(Cnst {
    name: Name::str(Name::str(Name::anon(), "String".into()), "mk".into()),
    levels: vec![],
    parents: None,
  }));
  DAGPtr::App(alloc_app(string_mk, list, None))
}

/// Try delta (definition) unfolding on DAG.
/// Looks up the constant, substitutes universe levels in the definition body,
/// converts it to a DAG, and splices it into the current DAG.
fn try_dag_delta(dag: &mut DAG, trail: &[NonNull<App>], env: &Env) -> bool {
  // Extract constant info from head
  let cnst_ref = match dag_head_past_trail(dag, trail) {
    DAGPtr::Cnst(cnst) => unsafe { &*cnst.as_ptr() },
    _ => return false,
  };

  let ci = match env.get(&cnst_ref.name) {
    Some(c) => c,
    None => return false,
  };
  let (def_params, def_value) = match ci {
    ConstantInfo::DefnInfo(d) if d.hints != ReducibilityHints::Opaque => {
      (&d.cnst.level_params, &d.value)
    },
    _ => return false,
  };

  if cnst_ref.levels.len() != def_params.len() {
    return false;
  }

  eprintln!("[try_dag_delta] unfolding: {}", cnst_ref.name.pretty());

  // Substitute levels at Expr level, then convert to DAG
  let val = subst_expr_levels(def_value, def_params, &cnst_ref.levels);
  eprintln!("[try_dag_delta] subst done, calling from_expr");
  let body_dag = from_expr(&val);
  eprintln!("[try_dag_delta] from_expr done, calling set_dag_head");

  // Splice body into the working DAG
  set_dag_head(dag, body_dag.head, trail);
  eprintln!("[try_dag_delta] set_dag_head done");
  true
}

/// Get the head node past the trail (the non-App node at the bottom).
fn dag_head_past_trail(dag: &DAG, trail: &[NonNull<App>]) -> DAGPtr {
  if trail.is_empty() {
    dag.head
  } else {
    unsafe { (*trail.last().unwrap().as_ptr()).fun }
  }
}

/// Try to unfold a definition at the head.
pub fn try_unfold_def(e: &Expr, env: &Env) -> Option<Expr> {
  let (head, args) = unfold_apps(e);
  let (name, levels) = match head.as_data() {
    ExprData::Const(name, levels, _) => (name, levels),
    _ => return None,
  };

  let ci = env.get(name)?;
  let (def_params, def_value) = match ci {
    ConstantInfo::DefnInfo(d) => {
      if d.hints == ReducibilityHints::Opaque {
        return None;
      }
      (&d.cnst.level_params, &d.value)
    },
    ConstantInfo::ThmInfo(t) => (&t.cnst.level_params, &t.value),
    _ => return None,
  };

  if levels.len() != def_params.len() {
    return None;
  }

  let val = subst_expr_levels(def_value, def_params, levels);
  Some(foldl_apps(val, args.into_iter()))
}

/// Try to reduce `Lean.reduceBool` / `Lean.reduceNat`.
///
/// These are opaque constants with special kernel reduction rules. In the Lean 4
/// kernel they evaluate their argument using compiled native code. Since both are
/// semantically identity functions (`fun b => b` / `fun n => n`), we simply
/// return the argument and let the WHNF loop continue reducing it via our
/// existing efficient paths (e.g. `try_reduce_nat` handles `Nat.ble` etc. in O(1)).
pub(crate) fn try_reduce_native(name: &Name, args: &[Expr]) -> Option<Expr> {
  if args.len() != 1 {
    return None;
  }
  let reduce_bool = mk_name2("Lean", "reduceBool");
  let reduce_nat = mk_name2("Lean", "reduceNat");
  if *name == reduce_bool || *name == reduce_nat {
    Some(args[0].clone())
  } else {
    None
  }
}

/// Try to reduce nat operations.
pub(crate) fn try_reduce_nat(e: &Expr, env: &Env) -> Option<Expr> {
  if has_fvars(e) {
    return None;
  }

  let (head, args) = unfold_apps(e);
  let name = match head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return None,
  };

  match args.len() {
    1 => {
      if *name == mk_name2("Nat", "succ") {
        let arg_whnf = whnf(&args[0], env);
        let n = get_nat_value(&arg_whnf)?;
        Some(Expr::lit(Literal::NatVal(Nat(n + BigUint::from(1u64)))))
      } else {
        None
      }
    },
    2 => {
      let a_whnf = whnf(&args[0], env);
      let b_whnf = whnf(&args[1], env);
      let a = get_nat_value(&a_whnf)?;
      let b = get_nat_value(&b_whnf)?;

      let result = if *name == mk_name2("Nat", "add") {
        Some(Expr::lit(Literal::NatVal(Nat(a + b))))
      } else if *name == mk_name2("Nat", "sub") {
        Some(Expr::lit(Literal::NatVal(Nat(if a >= b {
          a - b
        } else {
          BigUint::ZERO
        }))))
      } else if *name == mk_name2("Nat", "mul") {
        Some(Expr::lit(Literal::NatVal(Nat(a * b))))
      } else if *name == mk_name2("Nat", "div") {
        Some(Expr::lit(Literal::NatVal(Nat(if b == BigUint::ZERO {
          BigUint::ZERO
        } else {
          a / b
        }))))
      } else if *name == mk_name2("Nat", "mod") {
        Some(Expr::lit(Literal::NatVal(Nat(if b == BigUint::ZERO {
          a
        } else {
          a % b
        }))))
      } else if *name == mk_name2("Nat", "beq") {
        bool_to_expr(a == b)
      } else if *name == mk_name2("Nat", "ble") {
        bool_to_expr(a <= b)
      } else if *name == mk_name2("Nat", "pow") {
        let exp = u32::try_from(&b).unwrap_or(u32::MAX);
        Some(Expr::lit(Literal::NatVal(Nat(a.pow(exp)))))
      } else if *name == mk_name2("Nat", "land") {
        Some(Expr::lit(Literal::NatVal(Nat(a & b))))
      } else if *name == mk_name2("Nat", "lor") {
        Some(Expr::lit(Literal::NatVal(Nat(a | b))))
      } else if *name == mk_name2("Nat", "xor") {
        Some(Expr::lit(Literal::NatVal(Nat(a ^ b))))
      } else if *name == mk_name2("Nat", "shiftLeft") {
        let shift = u64::try_from(&b).unwrap_or(u64::MAX);
        Some(Expr::lit(Literal::NatVal(Nat(a << shift))))
      } else if *name == mk_name2("Nat", "shiftRight") {
        let shift = u64::try_from(&b).unwrap_or(u64::MAX);
        Some(Expr::lit(Literal::NatVal(Nat(a >> shift))))
      } else if *name == mk_name2("Nat", "blt") {
        bool_to_expr(a < b)
      } else {
        None
      };
      result
    },
    _ => None,
  }
}

fn get_nat_value(e: &Expr) -> Option<BigUint> {
  match e.as_data() {
    ExprData::Lit(Literal::NatVal(n), _) => Some(n.0.clone()),
    ExprData::Const(name, _, _) if *name == mk_name2("Nat", "zero") => {
      Some(BigUint::ZERO)
    },
    _ => None,
  }
}

fn bool_to_expr(b: bool) -> Option<Expr> {
  let name =
    if b { mk_name2("Bool", "true") } else { mk_name2("Bool", "false") };
  Some(Expr::cnst(name, vec![]))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
  use super::*;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn nat_type() -> Expr {
    Expr::cnst(mk_name("Nat"), vec![])
  }

  fn nat_zero() -> Expr {
    Expr::cnst(mk_name2("Nat", "zero"), vec![])
  }

  #[test]
  fn test_inst_bvar() {
    let body = Expr::bvar(Nat::from(0));
    let arg = nat_zero();
    let result = inst(&body, &[arg.clone()]);
    assert_eq!(result, arg);
  }

  #[test]
  fn test_inst_nested() {
    // body = Lam(_, Nat, Bvar(1)) — references outer binder
    // After inst with [zero], should become Lam(_, Nat, zero)
    let body = Expr::lam(
      Name::anon(),
      nat_type(),
      Expr::bvar(Nat::from(1)),
      BinderInfo::Default,
    );
    let result = inst(&body, &[nat_zero()]);
    let expected =
      Expr::lam(Name::anon(), nat_type(), nat_zero(), BinderInfo::Default);
    assert_eq!(result, expected);
  }

  #[test]
  fn test_unfold_apps() {
    let f = Expr::cnst(mk_name("f"), vec![]);
    let a = nat_zero();
    let b = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let e = Expr::app(Expr::app(f.clone(), a.clone()), b.clone());
    let (head, args) = unfold_apps(&e);
    assert_eq!(head, f);
    assert_eq!(args.len(), 2);
    assert_eq!(args[0], a);
    assert_eq!(args[1], b);
  }

  #[test]
  fn test_beta_reduce_identity() {
    // (fun x : Nat => x) Nat.zero
    let id = Expr::lam(
      Name::str(Name::anon(), "x".into()),
      nat_type(),
      Expr::bvar(Nat::from(0)),
      BinderInfo::Default,
    );
    let e = Expr::app(id, nat_zero());
    let env = Env::default();
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  #[test]
  fn test_zeta_reduce() {
    // let x : Nat := Nat.zero in x
    let e = Expr::letE(
      Name::str(Name::anon(), "x".into()),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0)),
      false,
    );
    let env = Env::default();
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  // ==========================================================================
  // Delta reduction
  // ==========================================================================

  fn mk_defn_env(name: &str, value: Expr, typ: Expr) -> Env {
    let mut env = Env::default();
    let n = mk_name(name);
    env.insert(
      n.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal { name: n.clone(), level_params: vec![], typ },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n],
      }),
    );
    env
  }

  #[test]
  fn test_delta_unfold() {
    // def myZero := Nat.zero
    // whnf(myZero) = Nat.zero
    let env = mk_defn_env("myZero", nat_zero(), nat_type());
    let e = Expr::cnst(mk_name("myZero"), vec![]);
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  #[test]
  fn test_delta_opaque_no_unfold() {
    // An opaque definition should NOT unfold
    let mut env = Env::default();
    let n = mk_name("opaqueVal");
    env.insert(
      n.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: n.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n.clone()],
      }),
    );
    let e = Expr::cnst(n.clone(), vec![]);
    let result = whnf(&e, &env);
    // Should still be the constant, not unfolded
    assert_eq!(result, e);
  }

  #[test]
  fn test_delta_chained() {
    // def a := Nat.zero, def b := a  =>  whnf(b) = Nat.zero
    let mut env = Env::default();
    let a = mk_name("a");
    let b = mk_name("b");
    env.insert(
      a.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: a.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![a.clone()],
      }),
    );
    env.insert(
      b.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: b.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: Expr::cnst(a, vec![]),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![b.clone()],
      }),
    );
    let e = Expr::cnst(b, vec![]);
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  // ==========================================================================
  // Nat arithmetic reduction
  // ==========================================================================

  fn nat_lit(n: u64) -> Expr {
    Expr::lit(Literal::NatVal(Nat::from(n)))
  }

  #[test]
  fn test_nat_add() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "add"), vec![]), nat_lit(3)),
      nat_lit(4),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(7));
  }

  #[test]
  fn test_nat_sub() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "sub"), vec![]), nat_lit(10)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(7));
  }

  #[test]
  fn test_nat_sub_underflow() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "sub"), vec![]), nat_lit(3)),
      nat_lit(10),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(0));
  }

  #[test]
  fn test_nat_mul() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "mul"), vec![]), nat_lit(6)),
      nat_lit(7),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(42));
  }

  #[test]
  fn test_nat_div() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "div"), vec![]), nat_lit(10)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(3));
  }

  #[test]
  fn test_nat_div_by_zero() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "div"), vec![]), nat_lit(10)),
      nat_lit(0),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(0));
  }

  #[test]
  fn test_nat_mod() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "mod"), vec![]), nat_lit(10)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(1));
  }

  #[test]
  fn test_nat_beq_true() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "beq"), vec![]), nat_lit(5)),
      nat_lit(5),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_nat_beq_false() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "beq"), vec![]), nat_lit(5)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "false"), vec![]));
  }

  #[test]
  fn test_nat_ble_true() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "ble"), vec![]), nat_lit(3)),
      nat_lit(5),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_nat_ble_false() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "ble"), vec![]), nat_lit(5)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "false"), vec![]));
  }

  #[test]
  fn test_nat_pow() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "pow"), vec![]), nat_lit(2)),
      nat_lit(10),
    );
    assert_eq!(whnf(&e, &env), nat_lit(1024));
  }

  #[test]
  fn test_nat_land() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "land"), vec![]), nat_lit(0b1100)),
      nat_lit(0b1010),
    );
    assert_eq!(whnf(&e, &env), nat_lit(0b1000));
  }

  #[test]
  fn test_nat_lor() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "lor"), vec![]), nat_lit(0b1100)),
      nat_lit(0b1010),
    );
    assert_eq!(whnf(&e, &env), nat_lit(0b1110));
  }

  #[test]
  fn test_nat_xor() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "xor"), vec![]), nat_lit(0b1100)),
      nat_lit(0b1010),
    );
    assert_eq!(whnf(&e, &env), nat_lit(0b0110));
  }

  #[test]
  fn test_nat_shift_left() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "shiftLeft"), vec![]), nat_lit(1)),
      nat_lit(8),
    );
    assert_eq!(whnf(&e, &env), nat_lit(256));
  }

  #[test]
  fn test_nat_shift_right() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "shiftRight"), vec![]),
        nat_lit(256),
      ),
      nat_lit(4),
    );
    assert_eq!(whnf(&e, &env), nat_lit(16));
  }

  #[test]
  fn test_nat_blt_true() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "blt"), vec![]), nat_lit(3)),
      nat_lit(5),
    );
    assert_eq!(whnf(&e, &env), Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_nat_blt_false() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "blt"), vec![]), nat_lit(5)),
      nat_lit(3),
    );
    assert_eq!(whnf(&e, &env), Expr::cnst(mk_name2("Bool", "false"), vec![]));
  }

  // ==========================================================================
  // Sort simplification in WHNF
  // ==========================================================================

  #[test]
  fn test_string_lit_proj_reduces() {
    // Build an env with String, String.mk ctor, List, List.cons, List.nil, Char
    let mut env = Env::default();
    let string_name = mk_name("String");
    let string_mk = mk_name2("String", "mk");
    let list_name = mk_name("List");
    let char_name = mk_name("Char");

    // String : Sort 1
    env.insert(
      string_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: string_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![string_name.clone()],
        ctors: vec![string_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // String.mk : List Char → String (1 field, 0 params)
    let list_char = Expr::app(
      Expr::cnst(list_name, vec![Level::succ(Level::zero())]),
      Expr::cnst(char_name, vec![]),
    );
    env.insert(
      string_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: string_mk,
          level_params: vec![],
          typ: Expr::all(
            mk_name("data"),
            list_char,
            Expr::cnst(string_name.clone(), vec![]),
            BinderInfo::Default,
          ),
        },
        induct: string_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );

    // Proj String 0 "hi" should reduce (not return None)
    let proj = Expr::proj(
      string_name,
      Nat::from(0u64),
      Expr::lit(Literal::StrVal("hi".into())),
    );
    let result = whnf(&proj, &env);
    // The result should NOT be a Proj anymore (it should have reduced)
    assert!(
      !matches!(result.as_data(), ExprData::Proj(..)),
      "String projection should reduce, got: {:?}",
      result
    );
  }

  #[test]
  fn test_whnf_sort_simplifies() {
    // Sort(max 0 u) should simplify to Sort(u)
    let env = Env::default();
    let u = Level::param(mk_name("u"));
    let e = Expr::sort(Level::max(Level::zero(), u.clone()));
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::sort(u));
  }

  // ==========================================================================
  // Already-WHNF terms
  // ==========================================================================

  #[test]
  fn test_whnf_sort_unchanged() {
    let env = Env::default();
    let e = Expr::sort(Level::zero());
    let result = whnf(&e, &env);
    assert_eq!(result, e);
  }

  #[test]
  fn test_whnf_lambda_unchanged() {
    // A lambda without applied arguments is already WHNF
    let env = Env::default();
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0)),
      BinderInfo::Default,
    );
    let result = whnf(&e, &env);
    assert_eq!(result, e);
  }

  #[test]
  fn test_whnf_pi_unchanged() {
    let env = Env::default();
    let e =
      Expr::all(mk_name("x"), nat_type(), nat_type(), BinderInfo::Default);
    let result = whnf(&e, &env);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Helper function tests
  // ==========================================================================

  #[test]
  fn test_has_loose_bvars_true() {
    assert!(has_loose_bvars(&Expr::bvar(Nat::from(0))));
  }

  #[test]
  fn test_has_loose_bvars_false_under_binder() {
    // fun x : Nat => x  — bvar(0) is bound, not loose
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0)),
      BinderInfo::Default,
    );
    assert!(!has_loose_bvars(&e));
  }

  #[test]
  fn test_has_loose_bvars_const() {
    assert!(!has_loose_bvars(&nat_zero()));
  }

  #[test]
  fn test_has_fvars_true() {
    assert!(has_fvars(&Expr::fvar(mk_name("x"))));
  }

  #[test]
  fn test_has_fvars_false() {
    assert!(!has_fvars(&nat_zero()));
  }

  #[test]
  fn test_foldl_apps_roundtrip() {
    let f = Expr::cnst(mk_name("f"), vec![]);
    let a = nat_zero();
    let b = nat_type();
    let e = Expr::app(Expr::app(f.clone(), a.clone()), b.clone());
    let (head, args) = unfold_apps(&e);
    let rebuilt = foldl_apps(head, args.into_iter());
    assert_eq!(rebuilt, e);
  }

  #[test]
  fn test_abstr_simple() {
    // abstr(fvar("x"), [fvar("x")]) = bvar(0)
    let x = Expr::fvar(mk_name("x"));
    let result = abstr(&x, &[x.clone()]);
    assert_eq!(result, Expr::bvar(Nat::from(0)));
  }

  #[test]
  fn test_abstr_not_found() {
    // abstr(Nat.zero, [fvar("x")]) = Nat.zero (unchanged)
    let x = Expr::fvar(mk_name("x"));
    let result = abstr(&nat_zero(), &[x]);
    assert_eq!(result, nat_zero());
  }

  #[test]
  fn test_subst_expr_levels_simple() {
    // Sort(u) with u := 0 => Sort(0)
    let u_name = mk_name("u");
    let e = Expr::sort(Level::param(u_name.clone()));
    let result = subst_expr_levels(&e, &[u_name], &[Level::zero()]);
    assert_eq!(result, Expr::sort(Level::zero()));
  }

  // ==========================================================================
  // Nat.rec on large literals — reproduces the hang
  // ==========================================================================

  /// Build a minimal env with Nat, Nat.zero, Nat.succ, and Nat.rec.
  fn mk_nat_rec_env() -> Env {
    let mut env = Env::default();
    let nat_name = mk_name("Nat");
    let zero_name = mk_name2("Nat", "zero");
    let succ_name = mk_name2("Nat", "succ");
    let rec_name = mk_name2("Nat", "rec");

    // Nat : Sort 1
    env.insert(
      nat_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: nat_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![nat_name.clone()],
        ctors: vec![zero_name.clone(), succ_name.clone()],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );

    // Nat.zero : Nat
    env.insert(
      zero_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: zero_name.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        induct: nat_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    // Nat.succ : Nat → Nat
    env.insert(
      succ_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: succ_name.clone(),
          level_params: vec![],
          typ: Expr::all(
            mk_name("n"),
            nat_type(),
            nat_type(),
            BinderInfo::Default,
          ),
        },
        induct: nat_name.clone(),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );

    // Nat.rec.{u} : (motive : Nat → Sort u) → motive Nat.zero →
    //   ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
    // Rules:
    //   Nat.rec m z s Nat.zero => z
    //   Nat.rec m z s (Nat.succ n) => s n (Nat.rec m z s n)
    let u = mk_name("u");
    env.insert(
      rec_name.clone(),
      ConstantInfo::RecInfo(RecursorVal {
        cnst: ConstantVal {
          name: rec_name.clone(),
          level_params: vec![u.clone()],
          typ: Expr::sort(Level::param(u.clone())), // placeholder
        },
        all: vec![nat_name],
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        num_motives: Nat::from(1u64),
        num_minors: Nat::from(2u64),
        rules: vec![
          // Nat.rec m z s Nat.zero => z
          RecursorRule {
            ctor: zero_name,
            n_fields: Nat::from(0u64),
            // RHS is just bvar(1) = z (the zero minor)
            // After substitution: Nat.rec m z s Nat.zero
            //   => rule.rhs applied to [m, z, s]
            //   => z
            rhs: Expr::bvar(Nat::from(1u64)),
          },
          // Nat.rec m z s (Nat.succ n) => s n (Nat.rec m z s n)
          RecursorRule {
            ctor: succ_name,
            n_fields: Nat::from(1u64),
            // RHS = fun n => s n (Nat.rec m z s n)
            // But actually the rule rhs receives [m, z, s] then [n] as args
            // rhs = bvar(0) = s, applied to the field n
            // Actually the recursor rule rhs is applied as:
            //   rhs m z s <fields...>
            // For Nat.succ with 1 field (the predecessor n):
            //   rhs m z s n => s n (Nat.rec.{u} m z s n)
            // So rhs = lam receiving params+minors then fields:
            // Actually, rhs is an expression that gets applied to
            // [params..., motives..., minors..., fields...]
            // For Nat.rec: 0 params, 1 motive, 2 minors, 1 field
            // So rhs gets applied to: m z s n
            // We want: s n (Nat.rec.{u} m z s n)
            // As a closed term using bvars after inst:
            // After being applied to m z s n:
            //   bvar(3) = m, bvar(2) = z, bvar(1) = s, bvar(0) = n
            // We want: s n (Nat.rec.{u} m z s n)
            // = app(app(bvar(1), bvar(0)),
            //        app(app(app(app(Nat.rec.{u}, bvar(3)), bvar(2)), bvar(1)), bvar(0)))
            // But wait, rhs is not a lambda - it gets args applied directly.
            // The rhs just receives the args via Expr::app in try_reduce_rec.
            // So rhs should be a term that, after being applied to m, z, s, n,
            // produces s n (Nat.rec m z s n).
            //
            // Simplest: rhs is a 4-arg lambda
            rhs: Expr::lam(
              mk_name("m"),
              Expr::sort(Level::zero()), // placeholder type
              Expr::lam(
                mk_name("z"),
                Expr::sort(Level::zero()),
                Expr::lam(
                  mk_name("s"),
                  Expr::sort(Level::zero()),
                  Expr::lam(
                    mk_name("n"),
                    nat_type(),
                    // body: s n (Nat.rec.{u} m z s n)
                    // bvar(3)=m, bvar(2)=z, bvar(1)=s, bvar(0)=n
                    Expr::app(
                      Expr::app(
                        Expr::bvar(Nat::from(1u64)), // s
                        Expr::bvar(Nat::from(0u64)), // n
                      ),
                      Expr::app(
                        Expr::app(
                          Expr::app(
                            Expr::app(
                              Expr::cnst(
                                rec_name.clone(),
                                vec![Level::param(u.clone())],
                              ),
                              Expr::bvar(Nat::from(3u64)), // m
                            ),
                            Expr::bvar(Nat::from(2u64)), // z
                          ),
                          Expr::bvar(Nat::from(1u64)), // s
                        ),
                        Expr::bvar(Nat::from(0u64)), // n
                      ),
                    ),
                    BinderInfo::Default,
                  ),
                  BinderInfo::Default,
                ),
                BinderInfo::Default,
              ),
              BinderInfo::Default,
            ),
          },
        ],
        k: false,
        is_unsafe: false,
      }),
    );

    env
  }

  #[test]
  fn test_nat_rec_small_literal() {
    // Nat.rec (fun _ => Nat) 0 (fun n _ => Nat.succ n) 3
    // Should reduce to 3 (identity via recursion)
    let env = mk_nat_rec_env();
    let motive =
      Expr::lam(mk_name("_"), nat_type(), nat_type(), BinderInfo::Default);
    let zero_case = nat_lit(0);
    let succ_case = Expr::lam(
      mk_name("n"),
      nat_type(),
      Expr::lam(
        mk_name("_"),
        nat_type(),
        Expr::app(
          Expr::cnst(mk_name2("Nat", "succ"), vec![]),
          Expr::bvar(Nat::from(1u64)),
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let e = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(
            Expr::cnst(
              mk_name2("Nat", "rec"),
              vec![Level::succ(Level::zero())],
            ),
            motive,
          ),
          zero_case,
        ),
        succ_case,
      ),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(3));
  }

  #[test]
  fn test_nat_rec_large_literal_hangs() {
    // This test demonstrates the O(n) recursor peeling issue.
    // Nat.rec on 65536 (2^16) — would take 65536 recursive steps.
    // We use a timeout-style approach: just verify it works for small n
    // and document that large n hangs.
    let env = mk_nat_rec_env();
    let motive =
      Expr::lam(mk_name("_"), nat_type(), nat_type(), BinderInfo::Default);
    let zero_case = nat_lit(0);
    let succ_case = Expr::lam(
      mk_name("n"),
      nat_type(),
      Expr::lam(
        mk_name("_"),
        nat_type(),
        Expr::app(
          Expr::cnst(mk_name2("Nat", "succ"), vec![]),
          Expr::bvar(Nat::from(1u64)),
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    // Test with 100 — should be fast enough
    let e = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(
            Expr::cnst(
              mk_name2("Nat", "rec"),
              vec![Level::succ(Level::zero())],
            ),
            motive.clone(),
          ),
          zero_case.clone(),
        ),
        succ_case.clone(),
      ),
      nat_lit(100),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(100));

    // nat_lit(65536) would hang here — that's the bug to fix
  }

  // ==========================================================================
  // try_reduce_native tests (Lean.reduceBool / Lean.reduceNat)
  // ==========================================================================

  #[test]
  fn test_reduce_bool_true() {
    // Lean.reduceBool Bool.true → Bool.true
    let args = vec![Expr::cnst(mk_name2("Bool", "true"), vec![])];
    let result = try_reduce_native(&mk_name2("Lean", "reduceBool"), &args);
    assert_eq!(result, Some(Expr::cnst(mk_name2("Bool", "true"), vec![])));
  }

  #[test]
  fn test_reduce_nat_literal() {
    // Lean.reduceNat (lit 42) → lit 42
    let args = vec![nat_lit(42)];
    let result = try_reduce_native(&mk_name2("Lean", "reduceNat"), &args);
    assert_eq!(result, Some(nat_lit(42)));
  }

  #[test]
  fn test_reduce_bool_with_nat_ble() {
    // Lean.reduceBool (Nat.ble 3 5) → passes through the arg
    // WHNF will then reduce Nat.ble 3 5 → Bool.true
    let ble_expr = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "ble"), vec![]), nat_lit(3)),
      nat_lit(5),
    );
    let args = vec![ble_expr.clone()];
    let result = try_reduce_native(&mk_name2("Lean", "reduceBool"), &args);
    assert_eq!(result, Some(ble_expr));

    // Verify WHNF continues reducing the returned argument
    let env = Env::default();
    let full_result = whnf(&result.unwrap(), &env);
    assert_eq!(full_result, Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_reduce_native_wrong_name() {
    let args = vec![nat_lit(1)];
    assert_eq!(try_reduce_native(&mk_name2("Lean", "other"), &args), None);
  }

  #[test]
  fn test_reduce_native_wrong_arity() {
    // 0 args
    let empty: Vec<Expr> = vec![];
    assert_eq!(try_reduce_native(&mk_name2("Lean", "reduceBool"), &empty), None);
    // 2 args
    let two = vec![nat_lit(1), nat_lit(2)];
    assert_eq!(try_reduce_native(&mk_name2("Lean", "reduceBool"), &two), None);
  }

  #[test]
  fn test_nat_rec_65536() {
    let env = mk_nat_rec_env();
    let motive =
      Expr::lam(mk_name("_"), nat_type(), nat_type(), BinderInfo::Default);
    let zero_case = nat_lit(0);
    let succ_case = Expr::lam(
      mk_name("n"),
      nat_type(),
      Expr::lam(
        mk_name("_"),
        nat_type(),
        Expr::app(
          Expr::cnst(mk_name2("Nat", "succ"), vec![]),
          Expr::bvar(Nat::from(1u64)),
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let e = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(
            Expr::cnst(
              mk_name2("Nat", "rec"),
              vec![Level::succ(Level::zero())],
            ),
            motive,
          ),
          zero_case,
        ),
        succ_case,
      ),
      nat_lit(65536),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(65536));
  }
}
