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

  fn lbr_min(a: G, b: G) -> G {
    match u32_less_than(a, b) {
      1 => a,
      0 => b,
    }
  }

  -- Number of leading `types` frames an expr with loose-bvar-range `base` can
  -- reach. `BVar(i)` reads `types[i]`, and a kept frame's own stored type can
  -- reference further-out frames, so expand `need` to the fixpoint that closes
  -- over every kept frame's loose range. Mirror Rust `ctx_addr_for_lbr`
  -- (tc.rs). Trimming `types` to this prefix canonicalizes the whnf/infer/
  -- def-eq memo key: a closed expr (base 0) keys to the empty context and
  -- shares across all binder depths. Memoized on (types, base).
  fn ctx_reachable(types: List‹KExpr›, base: G) -> G {
    let len = list_length(types);
    ctx_reachable_fix(types, len, lbr_min(base, len))
  }

  fn ctx_reachable_fix(types: List‹KExpr›, len: G, need: G) -> G {
    let scanned = lbr_min(ctx_reachable_scan(types, need, 0, need), len);
    match u32_less_than(need, scanned) {
      1 => ctx_reachable_fix(types, len, scanned),
      0 => need,
    }
  }

  fn ctx_reachable_scan(types: List‹KExpr›, limit: G, i: G, acc: G) -> G {
    match u32_less_than(i, limit) {
      0 => acc,
      1 =>
        let fi = (i + 1) + expr_lbr(list_lookup(types, i));
        ctx_reachable_scan(types, limit, i + 1, lbr_max(acc, fi)),
    }
  }

  -- Trim `types` to the suffix reachable from an expr with loose range `base`.
  -- Fast paths skip the fixpoint: `base == 0` (closed) → empty context;
  -- `base >= len` → nothing to trim. Only partially-open exprs pay the scan.
  fn ctx_trim(types: List‹KExpr›, base: G) -> List‹KExpr› {
    match base {
      0 => store(ListNode.Nil),
      _ =>
        match u32_less_than(base, list_length(types)) {
          0 => types,
          1 => list_take(types, ctx_reachable(types, base)),
        },
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
      KExprNode.BVar(i) =>
        let lt = u32_less_than(i, cutoff);
        match lt {
          1 => e,
          0 => store(KExprNode.BVar(i + shift)),
        },
      KExprNode.Srt(l) => store(KExprNode.Srt(l)),
      KExprNode.Const(idx, lvls) => store(KExprNode.Const(idx, lvls)),
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
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
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
    }
  }
⟧

end IxVM

end
