/-! # Lean sources of the recursor run-bounds suite

Ordinary Lean declarations, checked by Lean's kernel, that `ixvm-rec-run-bounds`
(`Tests.Ix.IxVM.RecRunBounds`) reads from the test binary's environment and compiles with Ix's
compiler. None is bound by the default role table. -/

namespace Tests.Ix.IxVM.RecRunBoundsDefs

universe u v

/-- A structure with two parameters and two fields. -/
structure Two (α : Type u) (β : Type v) where
  fst : α
  snd : β

/-- An indexed recursive family: one index, a constructor with a recursive field. -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α Nat.zero
  | cons (n : Nat) (a : α) (tl : Vec α n) : Vec α (Nat.succ n)

/-- A recursive type whose recursive field takes an argument, so that its induction hypothesis
has a telescope of one binder. -/
inductive Tree (α : Type u) where
  | leaf : Tree α
  | node (a : α) (kids : Nat → Tree α) : Tree α

end Tests.Ix.IxVM.RecRunBoundsDefs
