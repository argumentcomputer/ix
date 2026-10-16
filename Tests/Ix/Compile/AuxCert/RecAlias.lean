/-! Recursive fields hidden behind reducible aliases. The kernel recognizes
these fields when constructing recursor minors, and the Prop `.below`
generator must retain the corresponding induction hypotheses, including when
the alias hides a function telescope. -/
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

-- The function telescope is also hidden by an alias. The ordinary True
-- field must remain nonrecursive while the function field contributes a
-- higher-order induction hypothesis and its corresponding below proof.
abbrev Branches (p : Prop) : Prop := Nat → p

inductive Higher : Prop
  | base
  | node : Id' True → Branches Higher → Higher

theorem Higher.triv : Higher → True
  | .base => trivial
  | .node _ branches => Higher.triv (branches 0)
end RecAlias
