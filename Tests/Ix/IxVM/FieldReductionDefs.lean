import Lean

/-! # Inductive types whose field or index types reduce (fixtures)

Ordinary, kernel-checked Lean declarations exercising reduction in inductive
telescopes on the native route:

* **Accepted**: non-recursive constructor field reduction (`KField`: a field
  whose type reduces without mentioning the block) and type-former telescope
  reduction (`KIndex`: an index telescope that reduces by K-like reduction at a
  parameter).
* **Declined on the native route**: constructor fields that syntactically
  mention the block in a non-syntactic occurrence (`ArrowTree`, `KTree`,
  `Phantom`), which would require rewriting the stored constructor's field
  domains to classify positivity. -/

namespace Tests.Ix.IxVM.FieldReductionDefs

/-- A function type behind a definition. -/
def Arrow (A B : Type) : Type := A → B

/-- A definition that ignores its type argument. -/
def Tagged (_ : Type) : Type := Nat

/-- A reflexive field whose `∀` only `whnf` exposes (declined on the native route). -/
inductive ArrowTree where
  | leaf : ArrowTree
  | node : Arrow Nat ArrowTree → ArrowTree

/-- A non-recursive field whose type reduces by K-like reduction at `h`. -/
inductive KField where
  | mk : (h : 0 = 0) → @Eq.rec Nat 0 (fun _ _ => Type) Nat 0 h → KField

/-- A recursive field behind K-like reduction at `h` (declined on the native route). -/
inductive KTree where
  | leaf : KTree
  | node : (h : 0 = 0) → @Eq.rec Nat 0 (fun _ _ => Type) KTree 0 h → KTree

/-- A field mentioning the block under an erasing definition (declined on the native route). -/
inductive Phantom where
  | leaf : Phantom
  | mk : Tagged Phantom → Phantom

/-- An index telescope that reduces by K-like reduction at the parameter `h`. -/
inductive KIndex (h : 0 = 0) : @Eq.rec Nat 0 (fun _ _ => Type 1) (Nat → Type) 0 h where
  | mk : KIndex h 0

end Tests.Ix.IxVM.FieldReductionDefs
