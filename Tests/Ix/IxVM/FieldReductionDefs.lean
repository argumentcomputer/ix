import Lean

/-! # Inductive types whose field or index types reduce (fixtures)

Ordinary, kernel-checked Lean declarations. Lean's kernel builds a recursor
from the head-normal forms of the field and index types (`whnf` at each step
of the telescope), so a field type behind a definition, or one that reduces by
K-like reduction at an earlier field, is an ordinary field, and a recursive
field behind a definition that unfolds to a `∀` is a reflexive one. IxVM must
accept these recursors: its reconstruction head-normalizes the same types in
the context of the binders they mention. -/

namespace Tests.Ix.IxVM.FieldReductionDefs

/-- A function type behind a definition. -/
def Arrow (A B : Type) : Type := A → B

/-- A reflexive field whose `∀` only `whnf` exposes. -/
inductive ArrowTree where
  | leaf : ArrowTree
  | node : Arrow Nat ArrowTree → ArrowTree

/-- A field whose type reduces by K-like reduction at the earlier field `h`. -/
inductive KField where
  | mk : (h : 0 = 0) → @Eq.rec Nat 0 (fun _ _ => Type) Nat 0 h → KField

/-- A recursive field whose type reduces to the block by K-like reduction at the
earlier field `h`. -/
inductive KTree where
  | leaf : KTree
  | node : (h : 0 = 0) → @Eq.rec Nat 0 (fun _ _ => Type) KTree 0 h → KTree

/-- An index telescope that reduces by K-like reduction at the parameter `h`. -/
inductive KIndex (h : 0 = 0) : @Eq.rec Nat 0 (fun _ _ => Type 1) (Nat → Type) 0 h where
  | mk : KIndex h 0

end Tests.Ix.IxVM.FieldReductionDefs
