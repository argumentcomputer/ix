module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Kernel2: substitution over `KExpr`

`expr_subst(e, idx, arg)` — replace every `BVar(idx)` in `e` with `arg`,
bumping `idx` by 1 each time a binder (Lam/Forall/Let body) is crossed.

This is the locally-nameless "open" operation: it does **not** lift the
indices inside `arg`, and it does **not** decrement the other `BVar`s in
`e`. The alternative kernel keeps free variables as `FVar`s, so `arg` is
assumed to have no loose `BVar`s and the remaining `BVar`s in `e` are all
captured by inner binders — no shifting is required. -/

def subst := ⟦
  fn expr_subst(e: KExpr, idx: G, arg: KExpr) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) =>
        match i - idx {
          0 => arg,
          _ => e,
        },
      KExprNode.Srt(_) => e,
      KExprNode.Const(_, _) => e,
      KExprNode.Lit(_) => e,
      KExprNode.App(f, a) =>
        store(KExprNode.App(
          expr_subst(f, idx, arg),
          expr_subst(a, idx, arg))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(
          expr_subst(ty, idx, arg),
          expr_subst(body, idx + 1, arg))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(
          expr_subst(ty, idx, arg),
          expr_subst(body, idx + 1, arg))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_subst(ty, idx, arg),
          expr_subst(val, idx, arg),
          expr_subst(body, idx + 1, arg))),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_subst(e1, idx, arg))),
      -- FVar's type came from an earlier binding, so it has no loose BVars and
      -- cannot reference `idx` (a later binder). Leaf: return unchanged.
      KExprNode.FVar(_, _) => e,
    }
  }
⟧

end IxVM

end
