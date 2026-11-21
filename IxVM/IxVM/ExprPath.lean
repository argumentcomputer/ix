import Aiur.Generic.AST

/-! # Positions in a source expression

`Expr.sub e p` is the subexpression of `e` at the position `p`, a list of child
indices (`Expr.children`: the immediate subexpressions in source order, a match's
scrutinee before its arm bodies). The path-lemma generator (`IxVM.ObsGen`) states
the inversion of a `let` bound to a match as its own theorem about
`Expr.sub f.body p`, and finds `p` with `Expr.find?`. -/

namespace Aiur.Generic.Expr

variable {α : Type}

/-- The immediate subexpressions, in source order. -/
def children : Expr α → List (Expr α)
  | .literal _ | .var _ | .global _ _ => []
  | .tuple es | .array es | .construct _ _ _ es | .constructAs _ _ _ es | .record _ es
  | .update _ es | .builtin _ es | .call _ _ es => es
  | .repeat e _ | .index e _ | .slice e _ _ | .member e _ | .project e _ | .store e
  | .load e | .hint _ e _ | .neg e | .control _ e => [e]
  | .letValue _ x b => [x, b]
  | .binary _ l r => [l, r]
  | .matchValue x arms => x :: arms.map (·.2)

/-- The `i`-th element of a list of subexpressions (`e` past its end). -/
def childAt (e : Expr α) : List (Expr α) → Nat → Expr α
  | x :: _, 0 => x
  | _ :: xs, i + 1 => childAt e xs i
  | [], _ => e

/-- The subexpression at a position. -/
def sub : Expr α → List Nat → Expr α
  | e, [] => e
  | e, i :: p => sub (childAt e e.children i) p

/-- A position of `target` in `e` (the first in pre-order), found by `==`. -/
partial def find? [BEq α] (e target : Expr α) : Option (List Nat) :=
  if e == target then some [] else
    (e.children.zipIdx).firstM fun (c, i) => (find? c target).map (i :: ·)

end Aiur.Generic.Expr
