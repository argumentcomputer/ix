//! Substitution and lifting for zero kernel expressions.
//!
//! All functions intern results through `InternTable` for pointer
//! deduplication. In addition, the traversal itself is memoized by
//! content hash for the duration of a single call — expressions are
//! content-addressed DAGs and the same sub-expression may appear many
//! times (well-founded-recursion unfolds, recursor rules with repeated
//! motives, etc.); without per-call memoization we re-walk every shared
//! occurrence, turning a DAG walk into a tree walk and blowing O(N)
//! sharing into O(2^k) work. Mirrors `lean4lean`'s `replaceM` which
//! uses a `PtrMap Expr Expr` for the same reason (see
//! `refs/lean4lean/Lean4Lean/Expr.lean:14`).

use std::sync::LazyLock;

use rustc_hash::FxHashMap;

use super::env::{Addr, InternTable};
use super::expr::{ExprData, FVarId, KExpr};
use super::mode::KernelMode;

/// When set, log every 100K `subst` (top-level) entries. Substitution is
/// called once per `App` in `infer` (plus other sites in whnf / def_eq),
/// and each call recursively rebuilds the body; a check that spends
/// seconds per infer call likely has substs dominating. The counter
/// only fires for the top-level `subst` entry, so recursive sub-calls
/// don't inflate the number.
static IX_SUBST_COUNT_LOG: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_SUBST_COUNT_LOG").is_ok());

static SUBST_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

/// Perform single substitution: `body[arg/Var(depth)]`.
///
/// Replaces `Var(depth)` with `arg` (lifted by `depth`), shifts free
/// variables above `depth` down by 1. Uses `lbr()` for fast-path
/// skipping. The internal traversal is memoized by content hash so
/// shared sub-expressions within `body` are walked once per depth.
///
/// Memoization scratch is borrowed from `env.subst_scratch` to avoid
/// allocating a fresh `FxHashMap` per call. We `mem::take` it out
/// (replacing with an empty placeholder) so the borrow checker lets us
/// thread `&mut env` and `&mut scratch` separately into `subst_cached`,
/// then put it back on the way out. `subst_cached` does not call back
/// into `subst`, so there is no risk of recursive scratch use.
pub fn subst<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  arg: &KExpr<M>,
  depth: u64,
) -> KExpr<M> {
  if *IX_SUBST_COUNT_LOG && depth == 0 {
    let n = SUBST_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if n.is_multiple_of(100_000) && n > 0 {
      eprintln!("[subst] count={n}");
    }
  }
  // Fast path: no loose bound vars at or below `depth` means nothing to
  // substitute; returning the original Arc is cheap and cache-free.
  if body.lbr() <= depth {
    return body.clone();
  }
  let mut cache = std::mem::take(&mut env.subst_scratch);
  cache.clear();
  let result = subst_cached(env, body, arg, depth, &mut cache);
  env.subst_scratch = cache;
  result
}

/// Substitution variant for short-lived WHNF intermediates.
///
/// This deliberately does not use the global [`InternTable`]. It is intended
/// for reductions that may produce a long chain of distinct, never-reused
/// expressions, such as Nat literal recursor peeling. Interning those nodes
/// keeps every predecessor alive for the entire environment check.
pub fn subst_no_intern<M: KernelMode>(
  body: &KExpr<M>,
  arg: &KExpr<M>,
  depth: u64,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }

  match body.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i == depth {
        lift_no_intern(arg, depth, 0)
      } else if i > depth {
        KExpr::var(i - 1, name.clone())
      } else {
        body.clone()
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = subst_no_intern(f, arg, depth);
      let x2 = subst_no_intern(x, arg, depth);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = subst_no_intern(ty, arg, depth);
      let inner2 = subst_no_intern(inner, arg, depth + 1);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = subst_no_intern(ty, arg, depth);
      let inner2 = subst_no_intern(inner, arg, depth + 1);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = subst_no_intern(ty, arg, depth);
      let val2 = subst_no_intern(val, arg, depth);
      let inner2 = subst_no_intern(inner, arg, depth + 1);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = subst_no_intern(val, arg, depth);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::FVar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => body.clone(),
  }
}

/// Inner recursive worker with memoization keyed by `(sub-expr addr,
/// depth)`. Depth enters the key because traversing under a binder
/// increments `depth`, and the substitution's semantics change: under
/// one extra binder, `Var(depth+1)` now targets the original
/// substitution site. Two subtrees with the same address but visited at
/// different depths must not share a result.
fn subst_cached<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  arg: &KExpr<M>,
  depth: u64,
  cache: &mut FxHashMap<(Addr, u64), KExpr<M>>,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }

  // Pointer-identity cache: expressions are content-addressed, so two
  // sub-trees with the same `addr()` are structurally equal, meaning
  // `subst` at the same `depth` must produce the same result. Skipping
  // re-traversal here is the whole point of the cache — for Lean bodies
  // with significant sub-term sharing it turns an O(tree-size) walk
  // into O(dag-size).
  let key = (body.hash_key(), depth);
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }

  let result = match body.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i == depth {
        lift(env, arg, depth, 0)
      } else if i > depth {
        KExpr::var(i - 1, name.clone())
      } else {
        // Unreachable under the outer `lbr() <= depth` guard (Var below
        // `depth` is bound, so its lbr is below depth and we'd have
        // returned early), but keep the explicit branch for clarity.
        let r = body.clone();
        cache.insert(key, r.clone());
        return r;
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = subst_cached(env, f, arg, depth, cache);
      let x2 = subst_cached(env, x, arg, depth, cache);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = subst_cached(env, ty, arg, depth, cache);
      let inner2 = subst_cached(env, inner, arg, depth + 1, cache);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = subst_cached(env, ty, arg, depth, cache);
      let inner2 = subst_cached(env, inner, arg, depth + 1, cache);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = subst_cached(env, ty, arg, depth, cache);
      let val2 = subst_cached(env, val, arg, depth, cache);
      let inner2 = subst_cached(env, inner, arg, depth + 1, cache);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = subst_cached(env, val, arg, depth, cache);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::FVar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => {
      // Closed atoms — the outer `lbr() <= depth` guard should have
      // caught these, so this arm is defensive. FVars carry no loose
      // bound variables (lbr=0) so they always pass through unchanged.
      // Cache to stay consistent with other branches.
      let r = body.clone();
      cache.insert(key, r.clone());
      return r;
    },
  };

  let interned = env.intern_expr(result);
  cache.insert(key, interned.clone());
  interned
}

/// Perform simultaneous substitution: replace `Var(depth)..Var(depth+n-1)`
/// with `substs[0]..substs[n-1]`, shifting free variables above by `-n`.
///
/// Uses the same per-call pointer-identity memoization as `subst` so
/// shared sub-expressions are traversed once per depth level (see the
/// module-level docs).
pub fn simul_subst<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  substs: &[KExpr<M>],
  depth: u64,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }
  // See `subst` for the mem::take/restore pattern. `simul_subst_cached`
  // does not call into `subst`/`simul_subst`, so it is safe to share the
  // single `subst_scratch` between them.
  let mut cache = std::mem::take(&mut env.subst_scratch);
  cache.clear();
  let result = simul_subst_cached(env, body, substs, depth, &mut cache);
  env.subst_scratch = cache;
  result
}

fn simul_subst_cached<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  substs: &[KExpr<M>],
  depth: u64,
  cache: &mut FxHashMap<(Addr, u64), KExpr<M>>,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }

  let key = (body.hash_key(), depth);
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }

  let n = substs.len() as u64;

  let result = match body.data() {
    ExprData::Var(i, _, _) => {
      let i = *i;
      if i >= depth && i < depth + n {
        #[allow(clippy::cast_possible_truncation)]
        // guarded: i < depth + substs.len()
        let r = lift(env, &substs[(i - depth) as usize], depth, 0);
        cache.insert(key, r.clone());
        return r;
      } else if i >= depth + n {
        KExpr::var(i - n, M::meta_field(crate::ix::env::Name::anon()))
      } else {
        let r = body.clone();
        cache.insert(key, r.clone());
        return r;
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = simul_subst_cached(env, f, substs, depth, cache);
      let x2 = simul_subst_cached(env, x, substs, depth, cache);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = simul_subst_cached(env, ty, substs, depth, cache);
      let inner2 = simul_subst_cached(env, inner, substs, depth + 1, cache);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = simul_subst_cached(env, ty, substs, depth, cache);
      let inner2 = simul_subst_cached(env, inner, substs, depth + 1, cache);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = simul_subst_cached(env, ty, substs, depth, cache);
      let val2 = simul_subst_cached(env, val, substs, depth, cache);
      let inner2 = simul_subst_cached(env, inner, substs, depth + 1, cache);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = simul_subst_cached(env, val, substs, depth, cache);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::FVar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => {
      let r = body.clone();
      cache.insert(key, r.clone());
      return r;
    },
  };

  let interned = env.intern_expr(result);
  cache.insert(key, interned.clone());
  interned
}

/// Shift free de Bruijn indices ≥ `cutoff` up by `shift`.
///
/// Used when substituting an argument into a deeper context. Like
/// `subst`, memoizes by content hash within a single call so shared
/// sub-expressions are walked once per cutoff level.
pub fn lift<M: KernelMode>(
  env: &mut InternTable<M>,
  e: &KExpr<M>,
  shift: u64,
  cutoff: u64,
) -> KExpr<M> {
  if shift == 0 || e.lbr() <= cutoff {
    return e.clone();
  }
  // Borrow the dedicated `lift_scratch`. `lift` is invoked from inside
  // `subst_cached`, which already holds `subst_scratch`; using a separate
  // buffer keeps both available simultaneously. `lift_cached` does not
  // call back into `lift`/`subst`/`simul_subst`, so the scratch is safe
  // to share across calls without nested-borrow risk.
  let mut cache = std::mem::take(&mut env.lift_scratch);
  cache.clear();
  let result = lift_cached(env, e, shift, cutoff, &mut cache);
  env.lift_scratch = cache;
  result
}

fn lift_no_intern<M: KernelMode>(
  e: &KExpr<M>,
  shift: u64,
  cutoff: u64,
) -> KExpr<M> {
  if shift == 0 || e.lbr() <= cutoff {
    return e.clone();
  }

  match e.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i >= cutoff { KExpr::var(i + shift, name.clone()) } else { e.clone() }
    },

    ExprData::App(f, x, _) => {
      let f2 = lift_no_intern(f, shift, cutoff);
      let x2 = lift_no_intern(x, shift, cutoff);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, body, _) => {
      let ty2 = lift_no_intern(ty, shift, cutoff);
      let body2 = lift_no_intern(body, shift, cutoff + 1);
      KExpr::lam(name.clone(), bi.clone(), ty2, body2)
    },

    ExprData::All(name, bi, ty, body, _) => {
      let ty2 = lift_no_intern(ty, shift, cutoff);
      let body2 = lift_no_intern(body, shift, cutoff + 1);
      KExpr::all(name.clone(), bi.clone(), ty2, body2)
    },

    ExprData::Let(name, ty, val, body, nd, _) => {
      let ty2 = lift_no_intern(ty, shift, cutoff);
      let val2 = lift_no_intern(val, shift, cutoff);
      let body2 = lift_no_intern(body, shift, cutoff + 1);
      KExpr::let_(name.clone(), ty2, val2, body2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = lift_no_intern(val, shift, cutoff);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::FVar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => e.clone(),
  }
}

fn lift_cached<M: KernelMode>(
  env: &mut InternTable<M>,
  e: &KExpr<M>,
  shift: u64,
  cutoff: u64,
  cache: &mut FxHashMap<(Addr, u64), KExpr<M>>,
) -> KExpr<M> {
  if shift == 0 || e.lbr() <= cutoff {
    return e.clone();
  }

  // `shift` is fixed across a single call, so only `(addr, cutoff)` is
  // needed to identify a unique traversal result.
  let key = (e.hash_key(), cutoff);
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }

  let result = match e.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i >= cutoff {
        KExpr::var(i + shift, name.clone())
      } else {
        let r = e.clone();
        cache.insert(key, r.clone());
        return r;
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = lift_cached(env, f, shift, cutoff, cache);
      let x2 = lift_cached(env, x, shift, cutoff, cache);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, body, _) => {
      let ty2 = lift_cached(env, ty, shift, cutoff, cache);
      let body2 = lift_cached(env, body, shift, cutoff + 1, cache);
      KExpr::lam(name.clone(), bi.clone(), ty2, body2)
    },

    ExprData::All(name, bi, ty, body, _) => {
      let ty2 = lift_cached(env, ty, shift, cutoff, cache);
      let body2 = lift_cached(env, body, shift, cutoff + 1, cache);
      KExpr::all(name.clone(), bi.clone(), ty2, body2)
    },

    ExprData::Let(name, ty, val, body, nd, _) => {
      let ty2 = lift_cached(env, ty, shift, cutoff, cache);
      let val2 = lift_cached(env, val, shift, cutoff, cache);
      let body2 = lift_cached(env, body, shift, cutoff + 1, cache);
      KExpr::let_(name.clone(), ty2, val2, body2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = lift_cached(env, val, shift, cutoff, cache);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::FVar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => {
      let r = e.clone();
      cache.insert(key, r.clone());
      return r;
    },
  };

  let interned = env.intern_expr(result);
  cache.insert(key, interned.clone());
  interned
}

/// Cheap beta reduction: peephole-reduce `App(λ...λ. body, args)` shapes
/// without invoking the full [`subst`] machinery in trivial cases.
///
/// Mirrors `lean4lean`'s `Expr.cheapBetaReduce`
/// (refs/lean4lean/Lean4Lean/Instantiate.lean:8-27) and the C++ kernel's
/// `cheap_beta_reduce` (refs/lean4/src/kernel/instantiate.cpp:211).
///
/// For a spine `App(λx_0 ... λx_{n-1}. body, a_0, ..., a_{m-1})` we peel
/// `i = min(n, m)` lambdas. After peeling:
/// - **Closed body**: if `body.lbr() == 0`, no var refers to the peeled
///   binders or anything outside; rebuild `body @ a_i .. a_{m-1}`.
/// - **Single bvar body**: if `body` is `Var(k)` with `k < i`, the body
///   just selects one of the peeled args. Pick `a_{i-k-1}` and apply the
///   remaining args.
/// - Otherwise: defer to full WHNF; return the input unchanged.
///
/// Used by `inferLambda` / `inferLet` (and equivalents) to clean up
/// redexes that arise when an inferred type has the form
/// `App(λ_. T, x)` — common when motives or `id`-like applications
/// appear in the body's type. Returning a redex-free form here saves
/// downstream `is_def_eq` and `whnf` from instantiating-then-reducing.
pub fn cheap_beta_reduce<M: KernelMode>(
  env: &mut InternTable<M>,
  e: &KExpr<M>,
) -> KExpr<M> {
  // Only Apps can be redexes.
  if !matches!(e.data(), ExprData::App(..)) {
    return e.clone();
  }

  // Collect the spine. Mirrors `tc::collect_app_spine` but inlined to
  // avoid a circular `tc` ↔ `subst` dependency.
  let mut count = 0usize;
  {
    let mut cur = e;
    while let ExprData::App(f, _, _) = cur.data() {
      count += 1;
      cur = f;
    }
  }
  if count == 0 {
    return e.clone();
  }
  let mut args: Vec<KExpr<M>> = Vec::with_capacity(count);
  let mut head = e.clone();
  while let ExprData::App(f, a, _) = head.data() {
    args.push(a.clone());
    head = f.clone();
  }
  args.reverse();

  // Quick exit: head must be a lambda for any peeling to fire.
  if !matches!(head.data(), ExprData::Lam(..)) {
    return e.clone();
  }

  // Peel up to `args.len()` lambdas, advancing `head` to the body.
  let mut i: usize = 0;
  while i < args.len() {
    if let ExprData::Lam(_, _, _, inner, _) = head.data() {
      let inner = inner.clone();
      head = inner;
      i += 1;
    } else {
      break;
    }
  }

  // Case A: body has no free var references. Safe to drop the peeled
  // binders; rebuild App with remaining args.
  if head.lbr() == 0 {
    let mut result = head;
    for arg in &args[i..] {
      result = env.intern_expr(KExpr::app(result, arg.clone()));
    }
    return result;
  }

  // Case B: body is a single Var(k) referring to one of the peeled
  // binders (k < i). The peeled lambdas were applied in spine order, so
  // `Var(0)` is the innermost (last peeled, took `args[i-1]`) and
  // `Var(k)` is `args[i-k-1]`.
  if let ExprData::Var(k, _, _) = head.data() {
    let k = *k;
    if k < i as u64 {
      #[allow(clippy::cast_possible_truncation)]
      let chosen_idx = i - (k as usize) - 1;
      let mut result = args[chosen_idx].clone();
      for arg in &args[i..] {
        result = env.intern_expr(KExpr::app(result, arg.clone()));
      }
      return result;
    }
  }

  // Otherwise the redex needs a real substitution; let WHNF handle it.
  e.clone()
}

/// Instantiate the outermost `n = fvars.len()` loose bound variables in
/// `body` by the corresponding fvars, in reverse order (mirrors
/// `Lean.Expr.instantiateRev` and the C++ kernel's `instantiate_rev`).
///
/// For an opened binder body where `Var(0)` is the innermost bound and
/// `Var(n-1)` the outermost, calling `instantiate_rev(body, [fv_0, ..,
/// fv_{n-1}])` replaces `Var(0) → fv_{n-1}`, ..., `Var(n-1) → fv_0`. Free
/// variables `Var(k)` with `k >= n` shift **down by `n`** because the
/// surrounding `n` binders have been opened and consumed.
///
/// The argument array `fvars` must contain `KExpr`s whose `ExprData` is
/// `FVar(..)`. The function does not enforce this — the lambda head check
/// is the caller's responsibility — but the substitution is only sound
/// when every replacement is fvar-shaped (closed, lbr=0). Other shapes
/// would need their own lifting under each binder, which is what
/// [`simul_subst`] does.
///
/// Fast path: returns `body` unchanged when `body.lbr() == 0` (the body
/// has no loose bvars to instantiate).
pub fn instantiate_rev<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  fvars: &[KExpr<M>],
) -> KExpr<M> {
  if fvars.is_empty() || body.lbr() == 0 {
    return body.clone();
  }
  // Borrow the dedicated `subst_scratch` (same allocation reuse trick as
  // `subst`/`simul_subst`). `instantiate_rev_cached` does not call back
  // into subst/simul_subst/lift, so the scratch is safe to share across
  // top-level calls without nested-borrow risk.
  let mut cache = std::mem::take(&mut env.subst_scratch);
  cache.clear();
  let result = instantiate_rev_cached(env, body, fvars, 0, &mut cache);
  env.subst_scratch = cache;
  result
}

fn instantiate_rev_cached<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  fvars: &[KExpr<M>],
  depth: u64,
  cache: &mut FxHashMap<(Addr, u64), KExpr<M>>,
) -> KExpr<M> {
  // No loose bvars at or below `depth` means nothing to instantiate at
  // this subtree.
  if body.lbr() <= depth {
    return body.clone();
  }

  let key = (body.hash_key(), depth);
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }

  let n = fvars.len() as u64;

  let result = match body.data() {
    ExprData::Var(i, _, _) => {
      let i = *i;
      if i >= depth && i < depth + n {
        // `Var(depth)` corresponds to the innermost peeled binder, which
        // matches `fvars[n-1]` (last element). `Var(depth + n - 1)` is
        // the outermost, matching `fvars[0]`.
        #[allow(clippy::cast_possible_truncation)]
        let idx = (n - 1 - (i - depth)) as usize;
        let r = fvars[idx].clone();
        cache.insert(key, r.clone());
        return r;
      } else if i >= depth + n {
        // Free variable above the instantiated range: shift down by `n`.
        KExpr::var(i - n, M::meta_field(crate::ix::env::Name::anon()))
      } else {
        // i < depth: bound by an inner binder we walked under; unchanged.
        let r = body.clone();
        cache.insert(key, r.clone());
        return r;
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = instantiate_rev_cached(env, f, fvars, depth, cache);
      let x2 = instantiate_rev_cached(env, x, fvars, depth, cache);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = instantiate_rev_cached(env, ty, fvars, depth, cache);
      let inner2 = instantiate_rev_cached(env, inner, fvars, depth + 1, cache);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = instantiate_rev_cached(env, ty, fvars, depth, cache);
      let inner2 = instantiate_rev_cached(env, inner, fvars, depth + 1, cache);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = instantiate_rev_cached(env, ty, fvars, depth, cache);
      let val2 = instantiate_rev_cached(env, val, fvars, depth, cache);
      let inner2 = instantiate_rev_cached(env, inner, fvars, depth + 1, cache);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = instantiate_rev_cached(env, val, fvars, depth, cache);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::FVar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => {
      let r = body.clone();
      cache.insert(key, r.clone());
      return r;
    },
  };

  let interned = env.intern_expr(result);
  cache.insert(key, interned.clone());
  interned
}

/// Inverse of [`instantiate_rev`]: replace each occurrence of the listed
/// fvars in `body` with the appropriate `Var(level)` and shift other
/// loose bvars upward by `n` so the result is closed under `n` new
/// binders. `fvars[0]` becomes `Var(n - 1 + depth)` (outermost), `fvars[n-1]`
/// becomes `Var(depth)` (innermost).
///
/// Used by `LocalContext::mk_lambda` / `mk_pi` to close a body back into
/// a chain of de Bruijn binders after binder opening.
///
/// Fast path: returns `body` unchanged when `!body.has_fvars()`.
pub fn abstract_fvars<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  fvars: &[FVarId],
) -> KExpr<M> {
  if fvars.is_empty() || !body.has_fvars() {
    return body.clone();
  }
  // Build a position map for O(1) fvar → position lookup. For typical
  // usage (n ≤ 16), a linear scan would also be fine, but the map keeps
  // the cost predictable for inductive validation paths that abstract
  // larger fvar sets.
  let mut pos: FxHashMap<FVarId, u64> = FxHashMap::default();
  pos.reserve(fvars.len());
  for (i, fv) in fvars.iter().enumerate() {
    // Innermost (last) gets position 0; outermost (first) gets position
    // `n - 1`, matching the `instantiate_rev` convention.
    pos.insert(*fv, (fvars.len() - 1 - i) as u64);
  }

  let mut cache = std::mem::take(&mut env.subst_scratch);
  cache.clear();
  let n = fvars.len() as u64;
  let result = abstract_fvars_cached(env, body, &pos, n, 0, &mut cache);
  env.subst_scratch = cache;
  result
}

fn abstract_fvars_cached<M: KernelMode>(
  env: &mut InternTable<M>,
  body: &KExpr<M>,
  pos: &FxHashMap<FVarId, u64>,
  n: u64,
  depth: u64,
  cache: &mut FxHashMap<(Addr, u64), KExpr<M>>,
) -> KExpr<M> {
  // If this subtree has neither fvars nor loose bvars >= depth, nothing
  // changes. (Loose bvars below `depth` are bound by enclosing binders we
  // walked under, so they are unaffected.)
  if !body.has_fvars() && body.lbr() <= depth {
    return body.clone();
  }

  let key = (body.hash_key(), depth);
  if let Some(cached) = cache.get(&key) {
    return cached.clone();
  }

  let result = match body.data() {
    ExprData::FVar(id, _, _) => {
      // Replace target fvars with Var(level). Other fvars are leaves and
      // pass through unchanged (they belong to outer abstractions).
      if let Some(&p) = pos.get(id) {
        let new_var =
          KExpr::var(depth + p, M::meta_field(crate::ix::env::Name::anon()));
        let interned = env.intern_expr(new_var);
        cache.insert(key, interned.clone());
        return interned;
      }
      let r = body.clone();
      cache.insert(key, r.clone());
      return r;
    },

    ExprData::Var(i, name, _) => {
      let i = *i;
      // Loose bvars at or above `depth` shift up by `n` because we are
      // wrapping the body in `n` new binders.
      if i >= depth {
        KExpr::var(i + n, name.clone())
      } else {
        let r = body.clone();
        cache.insert(key, r.clone());
        return r;
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = abstract_fvars_cached(env, f, pos, n, depth, cache);
      let x2 = abstract_fvars_cached(env, x, pos, n, depth, cache);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = abstract_fvars_cached(env, ty, pos, n, depth, cache);
      let inner2 = abstract_fvars_cached(env, inner, pos, n, depth + 1, cache);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = abstract_fvars_cached(env, ty, pos, n, depth, cache);
      let inner2 = abstract_fvars_cached(env, inner, pos, n, depth + 1, cache);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = abstract_fvars_cached(env, ty, pos, n, depth, cache);
      let val2 = abstract_fvars_cached(env, val, pos, n, depth, cache);
      let inner2 = abstract_fvars_cached(env, inner, pos, n, depth + 1, cache);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = abstract_fvars_cached(env, val, pos, n, depth, cache);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => {
      let r = body.clone();
      cache.insert(key, r.clone());
      return r;
    },
  };

  let interned = env.intern_expr(result);
  cache.insert(key, interned.clone());
  interned
}

// Internal helper used only by the property tests: allow `ExprData` →
// `KExpr` reconstruction for re-interning in determinism check.
#[cfg(test)]
impl<M: KernelMode> ExprData<M> {
  fn into_kexpr(self) -> KExpr<M> {
    match self {
      ExprData::Var(i, name, _) => KExpr::var(i, name),
      ExprData::Sort(u, _) => KExpr::sort(u),
      ExprData::Const(id, us, _) => KExpr::cnst(id, us),
      ExprData::App(f, a, _) => KExpr::app(f, a),
      ExprData::Lam(n, bi, ty, body, _) => KExpr::lam(n, bi, ty, body),
      ExprData::All(n, bi, ty, body, _) => KExpr::all(n, bi, ty, body),
      ExprData::Let(n, ty, val, body, nd, _) => {
        KExpr::let_(n, ty, val, body, nd)
      },
      ExprData::Prj(id, idx, val, _) => KExpr::prj(id, idx, val),
      ExprData::Nat(n, addr, _) => KExpr::nat(n, addr),
      ExprData::Str(s, addr, _) => KExpr::str(s, addr),
      ExprData::FVar(id, name, _) => KExpr::fvar(id, name),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::level::KUniv;
  use crate::ix::kernel::mode::Anon;
  use lean_ffi::nat::Nat;

  type AE = KExpr<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  #[test]
  fn subst_var_0() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&mut env, &v0, &arg, 0);
    assert_eq!(result, arg);
  }

  #[test]
  fn subst_closed_skip() {
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&mut env, &nat, &arg, 0);
    assert!(result.ptr_eq(&nat));
  }

  #[test]
  fn subst_free_var_shift() {
    let mut env = InternTable::<Anon>::new();
    let v1 = AE::var(1, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&mut env, &v1, &arg, 0);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn subst_app() {
    let mut env = InternTable::<Anon>::new();
    let c = AE::cnst(KId::new(mk_addr("f"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let app = AE::app(c.clone(), v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&mut env, &app, &arg, 0);
    let expected = AE::app(c, arg);
    assert_eq!(result, expected);
  }

  #[test]
  fn subst_under_lambda() {
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v1 = AE::var(1, ());
    // λ(_:Nat). Var(1) — body references outer variable
    let lam = AE::lam((), (), nat.clone(), v1);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&mut env, &lam, &arg, 0);
    // Result: λ(_:Nat). 3
    let expected = AE::lam((), (), nat, arg);
    assert_eq!(result, expected);
  }

  #[test]
  fn subst_bound_var_unchanged() {
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    // λ(_:Nat). Var(0) — body is lambda-bound, closed under binder
    let lam = AE::lam((), (), nat, v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&mut env, &lam, &arg, 0);
    assert!(result.ptr_eq(&lam));
  }

  #[test]
  fn lift_var() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    // lift(Var(0), shift=1, cutoff=0) → Var(1)
    let result = lift(&mut env, &v0, 1, 0);
    assert_eq!(result, AE::var(1, ()));
    // lift(Var(0), shift=1, cutoff=1) → Var(0) (below cutoff)
    let result2 = lift(&mut env, &v0, 1, 1);
    assert!(result2.ptr_eq(&v0));
  }

  #[test]
  fn lift_zero_shift() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = lift(&mut env, &v0, 0, 0);
    assert!(result.ptr_eq(&v0));
  }

  // ---- instantiate_rev ----

  #[test]
  fn instantiate_rev_empty_passthrough() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = instantiate_rev(&mut env, &v0, &[]);
    assert!(result.ptr_eq(&v0));
  }

  #[test]
  fn instantiate_rev_closed_passthrough() {
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let fv0 = AE::fvar(FVarId(0), ());
    let result = instantiate_rev(&mut env, &nat, &[fv0]);
    assert!(result.ptr_eq(&nat));
  }

  #[test]
  fn instantiate_rev_innermost() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let fv0 = AE::fvar(FVarId(0), ());
    // Single-binder body: instantiate Var(0) → fvars[0]
    let result = instantiate_rev(&mut env, &v0, &[fv0.clone()]);
    assert_eq!(result, fv0);
  }

  #[test]
  fn instantiate_rev_outermost() {
    let mut env = InternTable::<Anon>::new();
    let v1 = AE::var(1, ());
    let fv0 = AE::fvar(FVarId(0), ());
    let fv1 = AE::fvar(FVarId(1), ());
    // Two-binder body, body is Var(1): outermost binder → fvars[0]
    let result = instantiate_rev(&mut env, &v1, &[fv0.clone(), fv1]);
    assert_eq!(result, fv0);
  }

  #[test]
  fn instantiate_rev_mix() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let v1 = AE::var(1, ());
    let app = AE::app(v0, v1);
    let fv0 = AE::fvar(FVarId(0), ());
    let fv1 = AE::fvar(FVarId(1), ());
    // Two-binder body: Var(0) → fvars[1]=fv1, Var(1) → fvars[0]=fv0
    let result = instantiate_rev(&mut env, &app, &[fv0.clone(), fv1.clone()]);
    let expected = AE::app(fv1, fv0);
    assert_eq!(result, expected);
  }

  #[test]
  fn instantiate_rev_free_var_shifts_down() {
    let mut env = InternTable::<Anon>::new();
    let v3 = AE::var(3, ());
    let fv0 = AE::fvar(FVarId(0), ());
    let fv1 = AE::fvar(FVarId(1), ());
    // Two binders peeled → Var(3) shifts down to Var(1)
    let result = instantiate_rev(&mut env, &v3, &[fv0, fv1]);
    assert_eq!(result, AE::var(1, ()));
  }

  #[test]
  fn instantiate_rev_under_inner_binder() {
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ()); // bound by inner λ
    let v1 = AE::var(1, ()); // refers to outer (the peeled binder at depth 0)
    let inner = AE::app(v0, v1);
    let lam = AE::lam((), (), nat.clone(), inner);
    let fv0 = AE::fvar(FVarId(0), ());
    let result = instantiate_rev(&mut env, &lam, &[fv0.clone()]);
    // Inside the lambda, Var(0) is still bound, Var(1) becomes fv0.
    let expected = AE::lam((), (), nat, AE::app(AE::var(0, ()), fv0));
    assert_eq!(result, expected);
  }

  // ---- abstract_fvars ----

  #[test]
  fn abstract_fvars_empty_passthrough() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = abstract_fvars(&mut env, &v0, &[]);
    assert!(result.ptr_eq(&v0));
  }

  #[test]
  fn abstract_fvars_no_fvars_passthrough() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = abstract_fvars(&mut env, &v0, &[FVarId(0)]);
    assert!(result.ptr_eq(&v0));
  }

  #[test]
  fn abstract_fvars_single_replacement() {
    let mut env = InternTable::<Anon>::new();
    let fv0 = AE::fvar(FVarId(0), ());
    // One target fvar → becomes Var(0)
    let result = abstract_fvars(&mut env, &fv0, &[FVarId(0)]);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn abstract_fvars_position_mapping() {
    let mut env = InternTable::<Anon>::new();
    let fv0 = AE::fvar(FVarId(0), ());
    let fv1 = AE::fvar(FVarId(1), ());
    let app = AE::app(fv0, fv1);
    // [fv0, fv1]: fv0 outermost (Var(1)), fv1 innermost (Var(0))
    let result = abstract_fvars(&mut env, &app, &[FVarId(0), FVarId(1)]);
    let expected = AE::app(AE::var(1, ()), AE::var(0, ()));
    assert_eq!(result, expected);
  }

  #[test]
  fn abstract_fvars_unrelated_pass_through() {
    let mut env = InternTable::<Anon>::new();
    let fv0 = AE::fvar(FVarId(0), ());
    let fv2 = AE::fvar(FVarId(2), ());
    // fv2 is not in the abstraction list → unchanged
    let result = abstract_fvars(&mut env, &fv2, &[FVarId(0), FVarId(1)]);
    assert!(result.ptr_eq(&fv2));
    let _ = fv0; // silence unused
  }

  #[test]
  fn abstract_fvars_lifts_loose_bvars() {
    let mut env = InternTable::<Anon>::new();
    let fv0 = AE::fvar(FVarId(0), ());
    let v0 = AE::var(0, ());
    let app = AE::app(fv0, v0);
    // Wrap one new binder around `app`; fv0 → Var(0); existing Var(0)
    // (loose) shifts up to Var(1).
    let result = abstract_fvars(&mut env, &app, &[FVarId(0)]);
    let expected = AE::app(AE::var(0, ()), AE::var(1, ()));
    assert_eq!(result, expected);
  }

  #[test]
  fn instantiate_rev_then_abstract_roundtrip() {
    let mut env = InternTable::<Anon>::new();
    // Body: λ. App(#0, #1) — under one extra binder; Var(0) is the inner
    // peeled binder, Var(1) is the outer one.
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let body =
      AE::lam((), (), nat.clone(), AE::app(AE::var(0, ()), AE::var(1, ())));
    let fv_outer_id = FVarId(7);
    let fv_inner_id = FVarId(8);
    let fv_outer = AE::fvar(fv_outer_id, ());
    let fv_inner = AE::fvar(fv_inner_id, ());

    // Open: peel the outer binder around body... actually body itself is a
    // lambda (the outer binder), and its inner is what we want to peel.
    // For simplicity, treat `body` directly as a body under one peeled
    // outer binder, then peel its inner lambda manually.
    let opened_outer = instantiate_rev(&mut env, &body, &[fv_outer.clone()]);
    // opened_outer is now: λ(Nat). App(#0, fv_outer)
    let inner_body = match opened_outer.data() {
      ExprData::Lam(_, _, _, b, _) => b.clone(),
      _ => unreachable!(),
    };
    let opened_inner =
      instantiate_rev(&mut env, &inner_body, &[fv_inner.clone()]);
    // opened_inner is now: App(fv_inner, fv_outer)
    let expected_open = AE::app(fv_inner.clone(), fv_outer.clone());
    assert_eq!(opened_inner, expected_open);

    // Close: abstract back over [fv_outer, fv_inner] — outer first.
    let closed =
      abstract_fvars(&mut env, &opened_inner, &[fv_outer_id, fv_inner_id]);
    // Expected: App(#0, #1) — fv_inner → Var(0), fv_outer → Var(1).
    let expected_closed = AE::app(AE::var(0, ()), AE::var(1, ()));
    assert_eq!(closed, expected_closed);
  }

  #[test]
  fn simul_subst_basic() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let v1 = AE::var(1, ());
    let app = AE::app(v1, v0); // App(Var(1), Var(0))

    let a = AE::nat(Nat::from(1u64), mk_addr("a"));
    let b = AE::nat(Nat::from(2u64), mk_addr("b"));

    // simul_subst([a, b], depth=0):
    //   Var(0) → substs[0] = a
    //   Var(1) → substs[1] = b
    let result = simul_subst(&mut env, &app, &[a.clone(), b.clone()], 0);
    let expected = AE::app(b, a);
    assert_eq!(result, expected);
  }

  #[test]
  fn simul_subst_shift() {
    let mut env = InternTable::<Anon>::new();
    let v2 = AE::var(2, ());

    let a = AE::nat(Nat::from(1u64), mk_addr("a"));
    let b = AE::nat(Nat::from(2u64), mk_addr("b"));

    // Var(2) >= depth+2 → shifted to Var(0)
    let result = simul_subst(&mut env, &v2, &[a, b], 0);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn intern_dedup() {
    let mut env = InternTable::<Anon>::new();
    let _v0 = AE::var(0, ());
    let v2 = AE::var(2, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));

    // Two substitutions producing the same result should be pointer-equal after interning
    let r1 = subst(&mut env, &v2, &arg, 0);
    let r2 = subst(&mut env, &v2, &arg, 0);
    assert!(r1.ptr_eq(&r2), "interned results should be ptr-equal");
  }

  // ---------------------------------------------------------------------
  // cheap_beta_reduce — see lean4lean Instantiate.lean:8-27.
  // ---------------------------------------------------------------------

  #[test]
  fn cheap_beta_non_app_returns_input() {
    let mut env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = cheap_beta_reduce(&mut env, &v0);
    assert!(result.ptr_eq(&v0));

    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let result = cheap_beta_reduce(&mut env, &nat);
    assert!(result.ptr_eq(&nat));
  }

  #[test]
  fn cheap_beta_app_non_lam_head_returns_input() {
    let mut env = InternTable::<Anon>::new();
    let f = AE::cnst(KId::new(mk_addr("f"), ()), Box::new([]));
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let app = env.intern_expr(AE::app(f, arg));
    let result = cheap_beta_reduce(&mut env, &app);
    assert!(result.ptr_eq(&app));
  }

  #[test]
  fn cheap_beta_closed_body_drops_lam() {
    // (λ_:Nat. Nat) 3 → Nat
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let lam = AE::lam((), (), nat.clone(), nat.clone());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let app = AE::app(lam, arg);
    let result = cheap_beta_reduce(&mut env, &app);
    assert_eq!(result, nat);
  }

  #[test]
  fn cheap_beta_bvar_picks_arg() {
    // (λx:Nat. x) 3 → 3
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let lam = AE::lam((), (), nat, v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let app = AE::app(lam, arg.clone());
    let result = cheap_beta_reduce(&mut env, &app);
    assert_eq!(result, arg);
  }

  #[test]
  fn cheap_beta_nested_bvar_picks_outer_arg() {
    // (λa b. a) x y → x  (a is Var(1) under both binders)
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v1 = AE::var(1, ()); // refers to outermost lambda
    // λa:Nat. λb:Nat. a
    let inner_lam = AE::lam((), (), nat.clone(), v1);
    let outer_lam = AE::lam((), (), nat, inner_lam);
    let x = AE::nat(Nat::from(7u64), mk_addr("x"));
    let y = AE::nat(Nat::from(8u64), mk_addr("y"));
    let app = AE::app(AE::app(outer_lam, x.clone()), y);
    let result = cheap_beta_reduce(&mut env, &app);
    assert_eq!(result, x);
  }

  #[test]
  fn cheap_beta_overapplied_appends_remaining() {
    // (λx:Nat. x) y z → y z   (Var(0) body, two args; pick args[0]=y, apply z)
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let lam = AE::lam((), (), nat, v0);
    let y = AE::cnst(KId::new(mk_addr("y"), ()), Box::new([]));
    let z = AE::cnst(KId::new(mk_addr("z"), ()), Box::new([]));
    let app = AE::app(AE::app(lam, y.clone()), z.clone());
    let result = cheap_beta_reduce(&mut env, &app);
    let expected = AE::app(y, z);
    assert_eq!(result, expected);
  }

  #[test]
  fn cheap_beta_non_trivial_body_returns_input() {
    // (λx:Nat. f x) 3 — body is App(f, Var(0)), neither closed nor a single bvar
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let f = AE::cnst(KId::new(mk_addr("f"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let body = AE::app(f, v0);
    let lam = AE::lam((), (), nat, body);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let app = env.intern_expr(AE::app(lam, arg));
    let result = cheap_beta_reduce(&mut env, &app);
    // Non-trivial: defer to WHNF, return original.
    assert_eq!(result, app);
  }

  #[test]
  fn cheap_beta_underapplied_returns_input() {
    // (λa b. a) x — only one arg supplied; body Var(1) but only 1 lam peeled
    // (we peel min(2 lams, 1 arg) = 1, body is `λb. Var(1)` — still a Lam,
    // the loop terminates with i=1 and head=lam, which doesn't match Var
    // case nor closed-body case).
    //
    // Actually after peeling 1 lambda, head is still `λb:Nat. Var(1)`,
    // which has lbr=2 > 0 (Var(1) at this depth), and isn't a Var(k).
    // So we fall through to the no-reduce case.
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v1 = AE::var(1, ());
    let inner_lam = AE::lam((), (), nat.clone(), v1);
    let outer_lam = AE::lam((), (), nat, inner_lam);
    let x = AE::cnst(KId::new(mk_addr("x"), ()), Box::new([]));
    let app = env.intern_expr(AE::app(outer_lam, x));
    let result = cheap_beta_reduce(&mut env, &app);
    assert_eq!(result, app);
  }

  #[test]
  fn cheap_beta_idempotent() {
    // Result of cheap_beta_reduce should itself reduce to itself.
    let mut env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let lam = AE::lam((), (), nat, v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let app = AE::app(lam, arg);
    let r1 = cheap_beta_reduce(&mut env, &app);
    let r2 = cheap_beta_reduce(&mut env, &r1);
    assert_eq!(r1, r2);
  }

  // =========================================================================
  // Property-style tests
  //
  // These use deterministic seeded generators rather than `quickcheck` so
  // they run in the default test harness without extra glue. The
  // generators produce a variety of bounded-depth `KExpr<Anon>` shapes to
  // exercise subst/lift invariants across a broad sample of inputs.
  // =========================================================================

  /// Small deterministic xorshift64 PRNG used for property-style tests.
  /// Avoids pulling `rand` into the kernel test module.
  struct Prng(u64);
  impl Prng {
    fn new(seed: u64) -> Self {
      Prng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF_CAFE_BABE)
    }
    fn next_u64(&mut self) -> u64 {
      let mut x = self.0;
      x ^= x << 13;
      x ^= x >> 7;
      x ^= x << 17;
      self.0 = x;
      x
    }
    fn next_u32(&mut self, bound: u32) -> u32 {
      // Truncating to u32 is intentional for the test RNG.
      #[allow(clippy::cast_possible_truncation)]
      let lo = self.next_u64() as u32;
      lo % bound.max(1)
    }
  }

  /// Generate a bounded-depth `KExpr<Anon>` with de Bruijn indices in
  /// `0..=max_var`. Leaf distribution is biased toward concrete data
  /// (Var/Sort/Const) to produce meaningful expressions.
  fn gen_expr(
    env: &mut InternTable<Anon>,
    rng: &mut Prng,
    depth: u32,
    max_var: u64,
  ) -> AE {
    if depth == 0 {
      // Leaves
      return match rng.next_u32(4) {
        0 => env.intern_expr(AE::var(rng.next_u64() % (max_var + 1), ())),
        1 => env.intern_expr(AE::sort(KUniv::zero())),
        2 => {
          env.intern_expr(AE::cnst(KId::new(mk_addr("c"), ()), Box::new([])))
        },
        _ => env
          .intern_expr(AE::nat(Nat::from(rng.next_u64() % 100), mk_addr("n"))),
      };
    }
    let choice = rng.next_u32(5);
    match choice {
      0 => env.intern_expr(AE::var(rng.next_u64() % (max_var + 1), ())),
      1 => {
        let f = gen_expr(env, rng, depth - 1, max_var);
        let a = gen_expr(env, rng, depth - 1, max_var);
        env.intern_expr(AE::app(f, a))
      },
      2 => {
        let ty = gen_expr(env, rng, depth - 1, max_var);
        let body = gen_expr(env, rng, depth - 1, max_var + 1);
        env.intern_expr(AE::lam((), (), ty, body))
      },
      3 => {
        let ty = gen_expr(env, rng, depth - 1, max_var);
        let body = gen_expr(env, rng, depth - 1, max_var + 1);
        env.intern_expr(AE::all((), (), ty, body))
      },
      _ => env.intern_expr(AE::sort(KUniv::zero())),
    }
  }

  /// The actual maximum loose de Bruijn index found by traversal, for
  /// cross-check against `expr.lbr()`.
  fn observed_lbr(e: &AE) -> u64 {
    fn walk(e: &AE, binders: u64, max: &mut u64) {
      match e.data() {
        ExprData::Var(i, _, _) => {
          if *i >= binders {
            let loose = *i - binders + 1;
            if loose > *max {
              *max = loose;
            }
          }
        },
        ExprData::App(f, a, _) => {
          walk(f, binders, max);
          walk(a, binders, max);
        },
        ExprData::Lam(_, _, ty, body, _) | ExprData::All(_, _, ty, body, _) => {
          walk(ty, binders, max);
          walk(body, binders + 1, max);
        },
        ExprData::Let(_, ty, val, body, _, _) => {
          walk(ty, binders, max);
          walk(val, binders, max);
          walk(body, binders + 1, max);
        },
        ExprData::Prj(_, _, val, _) => walk(val, binders, max),
        ExprData::FVar(..)
        | ExprData::Sort(..)
        | ExprData::Const(..)
        | ExprData::Nat(..)
        | ExprData::Str(..) => {},
      }
    }
    let mut m = 0;
    walk(e, 0, &mut m);
    m
  }

  #[test]
  fn prop_lbr_matches_observed_walk() {
    let mut env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0x1234_5678);
    for _ in 0..200 {
      let e = gen_expr(&mut env, &mut rng, 4, 3);
      let observed = observed_lbr(&e);
      let reported = e.lbr();
      assert_eq!(
        reported, observed,
        "lbr mismatch: reported={reported}, observed={observed}, e={e:?}"
      );
    }
  }

  #[test]
  fn prop_intern_determinism() {
    let mut env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0x55aa_55aa);
    for _ in 0..200 {
      let e = gen_expr(&mut env, &mut rng, 4, 3);
      // Re-interning the same shape should return the same Arc.
      let e2 = env.intern_expr(e.data().clone().into_kexpr());
      assert!(
        e.ptr_eq(&e2),
        "re-interning should produce ptr-equal expressions"
      );
    }
  }

  #[test]
  fn prop_lift_zero_shift_is_identity() {
    let mut env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0xCAFE_F00D);
    for _ in 0..200 {
      let e = gen_expr(&mut env, &mut rng, 4, 3);
      let r = lift(&mut env, &e, 0, 0);
      assert!(r.ptr_eq(&e), "lift with shift=0 must be identity");
    }
  }

  #[test]
  fn prop_subst_preserves_closed_expressions() {
    let mut env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0xDEAD_BEEF);
    // Closed sub-expressions are not walked — verify `subst` returns the
    // same Arc.
    let arg = AE::nat(Nat::from(7u64), mk_addr("arg"));
    for _ in 0..100 {
      let e = gen_expr(&mut env, &mut rng, 3, 0);
      // Only closed (lbr == 0) expressions qualify; skip others.
      if e.lbr() == 0 {
        let r = subst(&mut env, &e, &arg, 0);
        assert!(
          r.ptr_eq(&e),
          "subst must return ptr-equal for closed expressions"
        );
      }
    }
  }
}
