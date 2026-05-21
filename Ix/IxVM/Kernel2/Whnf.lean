module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Kernel2: weak head normal form

`whnf(e)` reduces `e` until its head constructor is exposed.

Initial implementation — only the cases that need no environment:

* Trivial heads (`Srt`, `Const`, `Lit`, `Forall`, `Lam`, `FVar`) are
  already in WHNF and returned unchanged. `Const` delta-unfolding is not
  done yet.
* `App(f, a)`: reduce `f`; if it is a `Lam`, beta-reduce by opening the
  body with `a` via `expr_subst` (no lift/shift — `a` is locally closed
  and the body has no loose `BVar` other than the bound one). Otherwise
  the application is neutral and rebuilt around the reduced head.
* `Let(_, val, body)`: zeta-reduce by opening `body` with `val`, then keep
  reducing.

`BVar` is assumed unreachable (loose bound vars are replaced by `FVar`s),
so it has no arm. `Proj` reduction is still TODO. -/

def whnf := ⟦
  fn whnf(e: KExpr) -> KExpr {
    match load(e) {
      KExprNode.Srt(_) => e,
      KExprNode.Const(_, _) => e,
      KExprNode.Lit(_) => e,
      KExprNode.Forall(_, _) => e,
      KExprNode.Lam(_, _) => e,
      KExprNode.FVar(_, _) => e,
      KExprNode.App(f, a) => apply(f, a),
      -- Zeta: let x := val in body  ↦  body[BVar(0) := val], then keep reducing.
      KExprNode.Let(_, val, body) => whnf(expr_subst(body, 0, val)),
    }
  }

  fn apply(f: KExpr, a: KExpr) -> KExpr {
    let head = whnf(f);
    match load(head) {
      -- Beta: (λ. body) a  ↦  body[BVar(0) := a], then keep reducing.
      KExprNode.Lam(_, body) => whnf(expr_subst(body, 0, a)),
      -- Neutral application: rebuild around the reduced head.
      _ => store(KExprNode.App(head, a)),
    }
  }
⟧

end IxVM

end
