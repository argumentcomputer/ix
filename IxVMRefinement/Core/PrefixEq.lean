import IxVMRefinement.Core.Rep

/-! # Equality of an exact binder prefix -/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core

/-- The first `m` binders of two terms are syntactic `∀`s with the same domains and binder
data. -/
def PrefixEq : Nat → KExpr → KExpr → Prop
  | 0, _, _ => True
  | m + 1, .forallE T B bm, .forallE T' B' bm' => T = T' ∧ bm = bm' ∧ PrefixEq m B B'
  | _ + 1, _, _ => False

end IxVM.Refinement.Decl
