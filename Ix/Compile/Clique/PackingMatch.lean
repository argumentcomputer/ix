module

public import Ix.Compile.Clique.Basic

public section

namespace Ix.Compile.Clique

open Ix (Name Expr)
open Ix.Compile.Canon (getAppFnArgs stripMdata)

/-- A variable from outside the packing leaf being compared. Locally bound
variables are rigid and never enter this correspondence. -/
inductive PackingVariable where
  | loose (index : Nat)
  | free (name : Name)
  deriving BEq, Inhabited

/-- A consistent, injective syntactic correspondence across every leaf of one
packing. This is not a proof of type equality or encoding-position ownership;
the transport's region and layout establish where recognition may be used. -/
structure PackingCorrespondence where
  variables : Array (PackingVariable × PackingVariable) := #[]
  deriving Inhabited

def PackingCorrespondence.extend (w : PackingCorrespondence)
    (actual expected : PackingVariable) : Option PackingCorrespondence := do
  if let some (_, old) := w.variables.find? (·.1 == actual) then
    if old == expected then some w else none
  else if w.variables.any (·.2 == expected) then none
  else some { variables := w.variables.push (actual, expected) }

/-- Only these transparent type annotations are erased for recognition. The
original leaf spelling is retained by the caller when it rebuilds a packing. -/
def packingAnnotation? (e : Expr) : Option Expr :=
  match getAppFnArgs (stripMdata e) with
  | (.const n _ _, #[type, _]) =>
    if n == leanName ``optParam || n == leanName ``autoParam then some type else none
  | (.const n _ _, #[type]) =>
    if n == leanName ``outParam || n == leanName ``semiOutParam then some type else none
  | _ => none

/-- Compare binder structure and carry one correspondence throughout the
comparison. External de Bruijn indices are adjusted by the local binder depth;
an external variable can never stand for a binder introduced inside the leaf.
Fuel exhaustion is a recognition failure, never successful evidence. -/
def matchPackingExpr : Nat → Nat → PackingCorrespondence → Expr → Expr →
    Option PackingCorrespondence
  | 0, _, _, _, _ => none
  | fuel + 1, depth, w, actual, expected => do
    if let some type := packingAnnotation? actual then
      return ← matchPackingExpr fuel depth w type expected
    if let some type := packingAnnotation? expected then
      return ← matchPackingExpr fuel depth w actual type
    match actual, expected with
    | .mdata _ a _, b => matchPackingExpr fuel depth w a b
    | a, .mdata _ b _ => matchPackingExpr fuel depth w a b
    | .bvar a _, .bvar b _ =>
      if a < depth || b < depth then
        if a == b then some w else none
      else w.extend (.loose (a - depth)) (.loose (b - depth))
    | .fvar a _, .fvar b _ => w.extend (.free a) (.free b)
    | .bvar a _, .fvar b _ =>
      if a < depth then none else w.extend (.loose (a - depth)) (.free b)
    | .fvar a _, .bvar b _ =>
      if b < depth then none else w.extend (.free a) (.loose (b - depth))
    | .sort a _, .sort b _ => if a == b then some w else none
    | .const a us _, .const b vs _ => if a == b && us == vs then some w else none
    | .app f a _, .app g b _ => do
      let w ← matchPackingExpr fuel depth w f g
      matchPackingExpr fuel depth w a b
    | .lam _ a body _ _, .lam _ b body' _ _
    | .forallE _ a body _ _, .forallE _ b body' _ _ => do
      let w ← matchPackingExpr fuel depth w a b
      matchPackingExpr fuel (depth + 1) w body body'
    | .letE _ a value body _ _, .letE _ b value' body' _ _ => do
      let w ← matchPackingExpr fuel depth w a b
      let w ← matchPackingExpr fuel depth w value value'
      matchPackingExpr fuel (depth + 1) w body body'
    | .lit a _, .lit b _ => if a == b then some w else none
    | .proj a i value _, .proj b j value' _ =>
      if a == b && i == j then matchPackingExpr fuel depth w value value' else none
    | _, _ => none

/-- One correspondence for the complete vector, including relationships
between different leaves. Independent per-leaf matches can lose sharing and
mistake two distinct parameters for one repeated parameter. -/
def matchPackingLeaves (actual expected : Array Expr) : Option PackingCorrespondence := do
  unless actual.size == expected.size do none
  let mut witness : PackingCorrespondence := {}
  for (a, b) in actual.zip expected do
    witness ← matchPackingExpr defaultFuel 0 witness a b
  return witness

end Ix.Compile.Clique

end
