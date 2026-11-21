import Aiur.Optimized.PolynomialFacts

namespace Aiur.Optimized.Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- Invert only a nonzero constant in the chosen field. The caller has already
lowered both operands, so their calls and memory effects remain present. -/
def constantInverse? (denominator : Polynomial F) : Option F :=
  match denominator.simplify with
  | .const value => if value = 0 then none else some value⁻¹
  | _ => none

theorem constantInverse?_sound {denominator : Polynomial F} {inverse : F}
    (found : denominator.constantInverse? = some inverse) (assignment : Witness → F) :
    denominator.denote assignment ≠ 0 ∧ inverse = (denominator.denote assignment)⁻¹ := by
  unfold constantInverse? at found
  cases simplified : denominator.simplify <;> simp only [simplified] at found
  all_goals try contradiction
  split at found
  · contradiction
  · rename_i nonzero
    cases found
    have equal := denote_simplify denominator assignment
    rw [simplified] at equal
    change _ = denominator.denote assignment at equal
    rw [← equal]
    exact ⟨nonzero, rfl⟩

end Aiur.Optimized.Polynomial
