module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Substitution primitives over `KExpr`

Mirror: src/ix/kernel/subst.rs (full file).

Two core operations:

* `expr_lift(e, shift, cutoff)` — shift `BVar(i)` to `BVar(i+shift)` when
  `i ≥ cutoff`. Crossing a binder bumps `cutoff` by 1. No-op when
  `shift = 0`.

* `expr_inst1(body, arg, depth)` — substitute `BVar(depth)` with
  `expr_lift(arg, depth, 0)`. Decrement `BVar(i)` for `i > depth`.
  Crossing a binder bumps `depth` by 1.

Aiur memoization caches calls automatically; no explicit cache table.

`KExprNode` lives in `Ix/IxVM/KernelTypes.lean`:
```
enum KExprNode {
  BVar(G), Srt(&KLevel), Const(G, List‹&KLevel›),
  App(KExpr, KExpr), Lam(KExpr, KExpr), Forall(KExpr, KExpr),
  Let(KExpr, KExpr, KExpr), Lit(KLiteral), Proj(G, G, KExpr),
}
```
-/

def subst := ⟦
  -- ============================================================================
  -- expr_lbr
  --
  -- Loose-bvar count: `1 + max(BVar idx)` over loose (non-binder-captured)
  -- variables in `e`. Returns 0 iff `e` is closed (no loose BVars). Aiur
  -- memoization caches per node, so repeat calls on the same KExpr ptr are
  -- O(1). First traversal cost matches a single subst walk; the payoff is
  -- short-circuiting subst that would otherwise re-walk closed subtrees.
  --
  -- Mirror: src/ix/kernel/expr.rs::lbr field on KExprNode (precomputed at
  -- intern time in Rust; computed on demand here, memoized via `store`).
  -- ============================================================================
  fn expr_lbr(e: KExpr) -> G {
    match load(e) {
      KExprNode.BVar(i) => i + 1,
      KExprNode.Srt(_) => 0,
      KExprNode.Const(_, _) => 0,
      KExprNode.Lit(_) => 0,
      KExprNode.App(f, a) => lbr_max(expr_lbr(f), expr_lbr(a)),
      KExprNode.Lam(ty, body) =>
        lbr_max(expr_lbr(ty), lbr_dec(expr_lbr(body))),
      KExprNode.Forall(ty, body) =>
        lbr_max(expr_lbr(ty), lbr_dec(expr_lbr(body))),
      KExprNode.Let(ty, val, body) =>
        lbr_max(lbr_max(expr_lbr(ty), expr_lbr(val)),
                lbr_dec(expr_lbr(body))),
      KExprNode.Proj(_, _, e1) => expr_lbr(e1),
      KExprNode.FVar(_, _) => 0,
    }
  }

  fn lbr_max(a: G, b: G) -> G {
    match u32_less_than(a, b) {
      1 => b,
      0 => a,
    }
  }

  fn lbr_dec(n: G) -> G {
    match n {
      0 => 0,
      _ => n - 1,
    }
  }

  -- ============================================================================
  -- next_fvar
  --
  -- Returns `0` if `e` has no `FVar`, otherwise `i + 1` where `i` is the
  -- maximum `FVar` index in `e`. Used to mint a fresh `FVar` id that
  -- doesn't collide with any existing `FVar` in the expression.
  -- ============================================================================
  fn next_fvar(e: KExpr) -> G {
    match load(e) {
      KExprNode.FVar(i, _) => i + 1,
      KExprNode.BVar(_) => 0,
      KExprNode.Srt(_) => 0,
      KExprNode.Const(_, _) => 0,
      KExprNode.Lit(_) => 0,
      KExprNode.App(f, a) => lbr_max(next_fvar(f), next_fvar(a)),
      KExprNode.Lam(ty, body) => lbr_max(next_fvar(ty), next_fvar(body)),
      KExprNode.Forall(ty, body) => lbr_max(next_fvar(ty), next_fvar(body)),
      KExprNode.Let(ty, val, body) =>
        lbr_max(lbr_max(next_fvar(ty), next_fvar(val)), next_fvar(body)),
      KExprNode.Proj(_, _, e1) => next_fvar(e1),
    }
  }

  -- ============================================================================
  -- expr_open
  --
  -- Open a binder. `outer` is a `Lam(ty, body)`, `Forall(ty, body)`,
  -- or `Let(ty, _, body)`. Mints a fresh `FVar(fid, ty)` where
  -- `fid = next_fvar(outer)` (one past every `FVar` already in `outer`,
  -- so no collision), substitutes `BVar(0)` in `body` with that FVar
  -- via `expr_subst1`, and returns the opened body.
  -- ============================================================================
  fn expr_open(outer: KExpr) -> KExpr {
    let fid = next_fvar(outer);
    match load(outer) {
      KExprNode.Lam(ty, body) =>
        expr_subst1(body, store(KExprNode.FVar(fid, ty)), 0),
      KExprNode.Forall(ty, body) =>
        expr_subst1(body, store(KExprNode.FVar(fid, ty)), 0),
      KExprNode.Let(ty, _, body) =>
        expr_subst1(body, store(KExprNode.FVar(fid, ty)), 0),
    }
  }

  -- ============================================================================
  -- expr_lift
  --
  -- Shift `BVar(i)` → `BVar(i + shift)` when `i ≥ cutoff`. Recursion bumps
  -- `cutoff` by 1 when crossing a binder (Lam/Forall/Let).
  --
  -- Mirrors `src/ix/kernel/subst.rs::lift_no_intern` (line 364-415).
  -- Fast path: when `expr_lbr(e) <= cutoff`, no loose BVar at or above the
  -- cutoff exists, so `e` is unchanged.
  -- ============================================================================
  fn expr_lift(e: KExpr, shift: G, cutoff: G) -> KExpr {
    match shift {
      0 => e,
      _ =>
        let l = expr_lbr(e);
        match u32_less_than(cutoff, l) {
          0 => e,
          1 => expr_lift_walk(e, shift, cutoff),
        },
    }
  }

  fn expr_lift_walk(e: KExpr, shift: G, cutoff: G) -> KExpr {
    match load(e) {
      KExprNode.Srt(_) => e,
      KExprNode.Const(_, _) => e,
      KExprNode.Lit(_) => e,
      KExprNode.FVar(_, _) => e,
      KExprNode.BVar(i) =>
        let lt = u32_less_than(i, cutoff);
        match lt {
          1 => e,
          0 => store(KExprNode.BVar(i + shift)),
        },
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          expr_lift(f, shift, cutoff),
          expr_lift(a, shift, cutoff))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          expr_lift(ty, shift, cutoff),
          expr_lift(body, shift, cutoff + 1))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          expr_lift(ty, shift, cutoff),
          expr_lift(body, shift, cutoff + 1))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_lift(ty, shift, cutoff),
          expr_lift(val, shift, cutoff),
          expr_lift(body, shift, cutoff + 1))),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_lift(e1, shift, cutoff))),
    }
  }

  -- ============================================================================
  -- expr_inst1
  --
  -- Substitute `BVar(depth)` with `expr_lift(arg, depth, 0)` and decrement
  -- `BVar(i)` for `i > depth`. Crossing a binder bumps `depth`.
  --
  -- Mirrors the single-arg form of `src/ix/kernel/subst.rs::instantiate_rev`
  -- with a list of one element. For the lambda-eta case in def_eq we want
  -- `body[BVar(0) := arg]` which is `expr_inst1(body, arg, 0)`.
  -- ============================================================================
  fn expr_inst1(e: KExpr, arg: KExpr, depth: G) -> KExpr {
    -- Fast path: when `expr_lbr(e) <= depth`, no BVar at or above depth
    -- exists in `e`, so the substitution is a no-op.
    let l = expr_lbr(e);
    match u32_less_than(depth, l) {
      0 => e,
      1 => expr_inst1_walk(e, arg, depth),
    }
  }

  fn expr_inst1_walk(e: KExpr, arg: KExpr, depth: G) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) =>
        let lt = u32_less_than(i, depth);
        match lt {
          1 => e,
          0 =>
            match i - depth {
              0 => expr_lift(arg, depth, 0),
              _ => store(KExprNode.BVar(i - 1)),
            },
        },
      KExprNode.Srt(l) => store(KExprNode.Srt(l)),
      KExprNode.Const(idx, lvls) => store(KExprNode.Const(idx, lvls)),
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          expr_inst1(f, arg, depth),
          expr_inst1(a, arg, depth))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          expr_inst1(ty, arg, depth),
          expr_inst1(body, arg, depth + 1))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          expr_inst1(ty, arg, depth),
          expr_inst1(body, arg, depth + 1))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_inst1(ty, arg, depth),
          expr_inst1(val, arg, depth),
          expr_inst1(body, arg, depth + 1))),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_inst1(e1, arg, depth))),
      -- FVar is unaffected by BVar substitution.
      KExprNode.FVar(idx, ty) => store(KExprNode.FVar(idx, ty)),
    }
  }

  -- ============================================================================
  -- expr_subst1
  --
  -- Like `expr_inst1` but assumes `arg` has no loose `BVar`s (FVar-form
  -- under the opening invariant), so the `expr_lift(arg, depth, 0)`
  -- inside `expr_inst1` would be a no-op. Used by the typechecking path
  -- (Whnf/Infer/DefEq); `Inductive.lean` keeps `expr_inst1` since its
  -- callers build BVar-form recursor pieces.
  -- ============================================================================
  fn expr_subst1(e: KExpr, arg: KExpr, depth: G) -> KExpr {
    let l = expr_lbr(e);
    match u32_less_than(depth, l) {
      0 => e,
      1 => expr_subst1_walk(e, arg, depth),
    }
  }

  fn expr_subst1_walk(e: KExpr, arg: KExpr, depth: G) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) =>
        let lt = u32_less_than(i, depth);
        match lt {
          1 => e,
          0 =>
            match i - depth {
              0 => arg,
              _ => store(KExprNode.BVar(i - 1)),
            },
        },
      KExprNode.Srt(l) => store(KExprNode.Srt(l)),
      KExprNode.Const(idx, lvls) => store(KExprNode.Const(idx, lvls)),
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          expr_subst1(f, arg, depth),
          expr_subst1(a, arg, depth))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          expr_subst1(ty, arg, depth),
          expr_subst1(body, arg, depth + 1))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          expr_subst1(ty, arg, depth),
          expr_subst1(body, arg, depth + 1))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_subst1(ty, arg, depth),
          expr_subst1(val, arg, depth),
          expr_subst1(body, arg, depth + 1))),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_subst1(e1, arg, depth))),
      KExprNode.FVar(idx, ty) => store(KExprNode.FVar(idx, ty)),
    }
  }

  -- ============================================================================
  -- expr_close
  --
  -- Inverse of opening with `expr_inst1`. Replaces `FVar(fid, _)` with
  -- `BVar(depth)` and shifts loose `BVar(i)` with `i >= depth` up by 1
  -- to make room for the re-introduced binder. Crossing a binder bumps
  -- `depth` by 1.
  --
  -- Used by `k_infer` to wrap a `Lam`'s inferred body type back in a
  -- `Forall`. Mirrors lean4lean's `abstract_fvars` for the single-FVar
  -- case.
  -- ============================================================================
  fn expr_close(e: KExpr, fid: G, depth: G) -> KExpr {
    match load(e) {
      KExprNode.FVar(i, ty) =>
        match i - fid {
          0 => store(KExprNode.BVar(depth)),
          _ => store(KExprNode.FVar(i, ty)),
        },
      KExprNode.BVar(i) =>
        let lt = u32_less_than(i, depth);
        match lt {
          1 => e,
          0 => store(KExprNode.BVar(i + 1)),
        },
      KExprNode.Srt(l) => store(KExprNode.Srt(l)),
      KExprNode.Const(idx, lvls) => store(KExprNode.Const(idx, lvls)),
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          expr_close(f, fid, depth),
          expr_close(a, fid, depth))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          expr_close(ty, fid, depth),
          expr_close(body, fid, depth + 1))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          expr_close(ty, fid, depth),
          expr_close(body, fid, depth + 1))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_close(ty, fid, depth),
          expr_close(val, fid, depth),
          expr_close(body, fid, depth + 1))),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_close(e1, fid, depth))),
    }
  }
⟧

end IxVM

end
