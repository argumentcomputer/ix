/-! # Lean sources of the alias-block suite

Ordinary Lean declarations, checked by Lean's kernel, that `ixvm-alias-block`
(`Tests.Ix.IxVM.AliasBlock`) reads from the test binary's environment and compiles with Ix's
compiler. None is bound by the default role table. -/

namespace Tests.Ix.IxVM.AliasBlockDefs

/-- A definition that reduces to a telescope into a sort. -/
def Rel (α : Type) : Type := α → α → Prop

/-- A family whose former is declared at that definition: one parameter, two indices, and a
declared type `∀ (α : Type), Rel α` that is no syntactic telescope into a sort. -/
inductive R (α : Type) : Rel α where
  | refl (a : α) : R α a a

end Tests.Ix.IxVM.AliasBlockDefs
