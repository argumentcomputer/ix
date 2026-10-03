/-! Surgery H1b: an SCC split ({B}, {A}) of a mutual block, with structural
recursion on A. Lean's `A.below` has an entry for the B field; the canonical
{A} below does not, so the handler's PProd projections shift. -/
namespace SurgSplit
mutual
inductive A
  | nil : A
  | a : B → A → A
inductive B
  | nil : B
end

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl
end SurgSplit
