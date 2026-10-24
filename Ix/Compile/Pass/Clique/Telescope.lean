/-
  Ix.Compile.Pass.Clique.Telescope: reordering a constant's leading binders,
  and the matching permutation of its applications' arguments.

  Lean puts a clique's fixed parameters in the *first* function's order
  (`getFixedParamPerms`, `Elab/PreDefinition/FixedParams.lean`): the
  telescope of `f₀._mutual` (well-founded), of every `f._f` (structural) and of
  the abstracted decreasing proofs that use fixed parameters follows the
  clique's first member. Under `σ` the first member changes, so the telescope
  is permuted (a definitional change). The binders are opened with fresh free
  variables, their bodies transformed, and closed again in the new order; a
  new order in which a binder's type would mention a later binder is refused.
-/
module
public import Ix.Compile.Pass.Clique.Basic
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Level Expr)
open Ix.Compile.Canon (stripMdata)
open Ix.Compile.Image (Local)

/-- Open `m` leading binders (`λ` when `isLam`, else `∀`) with fresh free
variables. Fails when there are fewer. -/
def openBinders (isLam : Bool) (m : Nat) (e : Expr) : TM (Array Local × Expr) := do
  let mut cur := e
  let mut ls : Array Local := #[]
  for _ in [0:m] do
    match isLam, stripMdata cur with
    | true, .lam nm t b bi _ | false, .forallE nm t b bi _ =>
      let t' := instLocals t (ls.map (·.expr))
      let f ← freshFVar
      ls := ls.push { fvar := f, userName := nm, type := t', bi }
      cur := b
    | _, _ => throw s!"openBinders: expected {m} binders"
  return (ls, instLocals cur (ls.map (·.expr)))

/-- Close the binders `xs` (outermost first) over `body`; refuses an order in
which a binder's type mentions a later binder. -/
def closeBinders (isLam : Bool) (xs : Array Local) (body : Expr) : Except String Expr := do
  for (x, i) in xs.zipIdx do
    for y in xs.extract (i + 1) xs.size do
      if mentionsFVar y.fvar x.type then
        throw "closeBinders: the new order breaks a dependency between fixed parameters"
  return if isLam then mkLambda xs body else mkForall xs body

/-- `xs` reordered: new position `p` holds `xs[perm[p]]`; `none` when `perm`
indexes past `xs`. -/
def reorder {α} (perm : Array Nat) (xs : Array α) : Option (Array α) :=
  perm.mapM fun i => xs[i]?

/-- Open `m` binders, transform their types with `kTy` and the body with
`kBody` (the body first, then the types outermost first), and close them in
the order `perm` (new position `p` is old binder `perm[p]`). -/
def withReorderedBinders2 (isLam : Bool) (m : Nat) (perm : Array Nat) (e : Expr)
    (kTy kBody : Expr → TM Expr) : TM Expr := do
  let (xs, body) ← openBinders isLam m e
  let body' ← kBody body
  let mut xs' : Array Local := #[]
  for x in xs do xs' := xs'.push { x with type := ← kTy x.type }
  let some ys := reorder perm xs'
    | throw s!"withReorderedBinders: the order {perm} indexes past the {xs'.size} binders"
  liftE (closeBinders isLam ys body')

/-- `withReorderedBinders2` with one transformation `k` for the binders'
types and the body. -/
def withReorderedBinders (isLam : Bool) (m : Nat) (perm : Array Nat) (e : Expr)
    (k : Expr → TM Expr) : TM Expr :=
  withReorderedBinders2 isLam m perm e k k

/-- The identity permutation of `Fin m`. -/
def idPerm (m : Nat) : Array Nat := (List.range m).toArray

end Ix.Compile.Pass.Clique

end
