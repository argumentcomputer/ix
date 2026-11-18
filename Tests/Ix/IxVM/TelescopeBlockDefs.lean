/-! # Lean sources of the telescope-block suite

Ordinary Lean declarations, checked by Lean's kernel, that `ixvm-telescope-block`
(`Tests.Ix.IxVM.TelescopeBlock`) reads from the test binary's environment and compiles with Ix's
compiler. None is bound by the default role table. -/

namespace Tests.Ix.IxVM.TelescopeBlockDefs

/-- An ordinary inductive type, declared at its telescope: one parameter, one index, two
constructors, one of them recursive. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α Nat.zero
  | cons (n : Nat) (a : α) (v : Vec α n) : Vec α (Nat.succ n)

/-- A structure-like proposition, declared at its telescope: one constructor, no index, a sort
that tests zero. Its install stores a projection table. -/
structure Both : Prop where
  left : True
  right : ∀ n : Nat, n = n

end Tests.Ix.IxVM.TelescopeBlockDefs
