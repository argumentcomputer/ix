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
use super::expr::{ExprData, KExpr};
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
pub fn subst<M: KernelMode>(
  env: &InternTable<M>,
  body: &KExpr<M>,
  arg: &KExpr<M>,
  depth: u64,
) -> KExpr<M> {
  if *IX_SUBST_COUNT_LOG && depth == 0 {
    let n = SUBST_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if n % 100_000 == 0 && n > 0 {
      eprintln!("[subst] count={n}");
    }
  }
  // Fast path: no loose bound vars at or below `depth` means nothing to
  // substitute; returning the original Arc is cheap and cache-free.
  if body.lbr() <= depth {
    return body.clone();
  }
  let mut cache: FxHashMap<(Addr, u64), KExpr<M>> = FxHashMap::default();
  subst_cached(env, body, arg, depth, &mut cache)
}

/// Inner recursive worker with memoization keyed by `(sub-expr addr,
/// depth)`. Depth enters the key because traversing under a binder
/// increments `depth`, and the substitution's semantics change: under
/// one extra binder, `Var(depth+1)` now targets the original
/// substitution site. Two subtrees with the same address but visited at
/// different depths must not share a result.
fn subst_cached<M: KernelMode>(
  env: &InternTable<M>,
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

    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => {
      // Closed atoms — the outer `lbr() <= depth` guard should have
      // caught these, so this arm is defensive. Cache to stay
      // consistent with other branches.
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
  env: &InternTable<M>,
  body: &KExpr<M>,
  substs: &[KExpr<M>],
  depth: u64,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }
  let mut cache: FxHashMap<(Addr, u64), KExpr<M>> = FxHashMap::default();
  simul_subst_cached(env, body, substs, depth, &mut cache)
}

fn simul_subst_cached<M: KernelMode>(
  env: &InternTable<M>,
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

/// Shift free de Bruijn indices ≥ `cutoff` up by `shift`.
///
/// Used when substituting an argument into a deeper context. Like
/// `subst`, memoizes by content hash within a single call so shared
/// sub-expressions are walked once per cutoff level.
pub fn lift<M: KernelMode>(
  env: &InternTable<M>,
  e: &KExpr<M>,
  shift: u64,
  cutoff: u64,
) -> KExpr<M> {
  if shift == 0 || e.lbr() <= cutoff {
    return e.clone();
  }
  let mut cache: FxHashMap<(Addr, u64), KExpr<M>> = FxHashMap::default();
  lift_cached(env, e, shift, cutoff, &mut cache)
}

fn lift_cached<M: KernelMode>(
  env: &InternTable<M>,
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

    ExprData::Sort(..)
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
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &v0, &arg, 0);
    assert_eq!(result, arg);
  }

  #[test]
  fn subst_closed_skip() {
    let env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &nat, &arg, 0);
    assert!(result.ptr_eq(&nat));
  }

  #[test]
  fn subst_free_var_shift() {
    let env = InternTable::<Anon>::new();
    let v1 = AE::var(1, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &v1, &arg, 0);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn subst_app() {
    let env = InternTable::<Anon>::new();
    let c = AE::cnst(KId::new(mk_addr("f"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let app = AE::app(c.clone(), v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &app, &arg, 0);
    let expected = AE::app(c, arg);
    assert_eq!(result, expected);
  }

  #[test]
  fn subst_under_lambda() {
    let env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v1 = AE::var(1, ());
    // λ(_:Nat). Var(1) — body references outer variable
    let lam = AE::lam((), (), nat.clone(), v1);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &lam, &arg, 0);
    // Result: λ(_:Nat). 3
    let expected = AE::lam((), (), nat, arg);
    assert_eq!(result, expected);
  }

  #[test]
  fn subst_bound_var_unchanged() {
    let env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    // λ(_:Nat). Var(0) — body is lambda-bound, closed under binder
    let lam = AE::lam((), (), nat, v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &lam, &arg, 0);
    assert!(result.ptr_eq(&lam));
  }

  #[test]
  fn lift_var() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    // lift(Var(0), shift=1, cutoff=0) → Var(1)
    let result = lift(&env, &v0, 1, 0);
    assert_eq!(result, AE::var(1, ()));
    // lift(Var(0), shift=1, cutoff=1) → Var(0) (below cutoff)
    let result2 = lift(&env, &v0, 1, 1);
    assert!(result2.ptr_eq(&v0));
  }

  #[test]
  fn lift_zero_shift() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = lift(&env, &v0, 0, 0);
    assert!(result.ptr_eq(&v0));
  }

  #[test]
  fn simul_subst_basic() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let v1 = AE::var(1, ());
    let app = AE::app(v1, v0); // App(Var(1), Var(0))

    let a = AE::nat(Nat::from(1u64), mk_addr("a"));
    let b = AE::nat(Nat::from(2u64), mk_addr("b"));

    // simul_subst([a, b], depth=0):
    //   Var(0) → substs[0] = a
    //   Var(1) → substs[1] = b
    let result = simul_subst(&env, &app, &[a.clone(), b.clone()], 0);
    let expected = AE::app(b, a);
    assert_eq!(result, expected);
  }

  #[test]
  fn simul_subst_shift() {
    let env = InternTable::<Anon>::new();
    let v2 = AE::var(2, ());

    let a = AE::nat(Nat::from(1u64), mk_addr("a"));
    let b = AE::nat(Nat::from(2u64), mk_addr("b"));

    // Var(2) >= depth+2 → shifted to Var(0)
    let result = simul_subst(&env, &v2, &[a, b], 0);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn intern_dedup() {
    let env = InternTable::<Anon>::new();
    let _v0 = AE::var(0, ());
    let v2 = AE::var(2, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));

    // Two substitutions producing the same result should be pointer-equal after interning
    let r1 = subst(&env, &v2, &arg, 0);
    let r2 = subst(&env, &v2, &arg, 0);
    assert!(r1.ptr_eq(&r2), "interned results should be ptr-equal");
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
      (self.next_u64() as u32) % bound.max(1)
    }
  }

  /// Generate a bounded-depth `KExpr<Anon>` with de Bruijn indices in
  /// `0..=max_var`. Leaf distribution is biased toward concrete data
  /// (Var/Sort/Const) to produce meaningful expressions.
  fn gen_expr(
    env: &InternTable<Anon>,
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
        ExprData::Sort(..)
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
    let env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0x1234_5678);
    for _ in 0..200 {
      let e = gen_expr(&env, &mut rng, 4, 3);
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
    let env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0x55aa_55aa);
    for _ in 0..200 {
      let e = gen_expr(&env, &mut rng, 4, 3);
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
    let env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0xCAFE_F00D);
    for _ in 0..200 {
      let e = gen_expr(&env, &mut rng, 4, 3);
      let r = lift(&env, &e, 0, 0);
      assert!(r.ptr_eq(&e), "lift with shift=0 must be identity");
    }
  }

  #[test]
  fn prop_subst_preserves_closed_expressions() {
    let env = InternTable::<Anon>::new();
    let mut rng = Prng::new(0xDEAD_BEEF);
    // Closed sub-expressions are not walked — verify `subst` returns the
    // same Arc.
    let arg = AE::nat(Nat::from(7u64), mk_addr("arg"));
    for _ in 0..100 {
      let e = gen_expr(&env, &mut rng, 3, 0);
      // Only closed (lbr == 0) expressions qualify; skip others.
      if e.lbr() == 0 {
        let r = subst(&env, &e, &arg, 0);
        assert!(
          r.ptr_eq(&e),
          "subst must return ptr-equal for closed expressions"
        );
      }
    }
  }
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
    }
  }
}
