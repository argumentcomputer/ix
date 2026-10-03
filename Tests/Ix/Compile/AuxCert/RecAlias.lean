/-! Recursive fields hidden behind a reducible alias (the kernel whnf's field
types when it finds recursive arguments; IndPredBelow builds the Prop `.below`
from the recursor's minors). ix's non-nested Prop `.below` path builds from the
constructor types and recognises recursive fields by their head constant. -/
namespace RecAlias
abbrev Id' (p : Prop) : Prop := p

inductive PA : Nat → Prop
  | base : PA 0
  | step {n : Nat} : Id' (PA n) → PA (n + 1)

theorem PA.triv : ∀ {n : Nat}, PA n → True
  | _, .base => trivial
  | _, .step h => PA.triv h

abbrev IdT (α : Type) : Type := α

inductive TA
  | leaf
  | node : IdT TA → TA

def TA.size : TA → Nat
  | .leaf => 0
  | .node t => TA.size t + 1

theorem ta2 : TA.size (.node (.node .leaf)) = 2 := rfl
end RecAlias
