import Aiur.Optimized.PolynomialFacts
import Mathlib.Tactic.Ring

namespace Aiur.Optimized.Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- Split an affine expression into the coefficient of one variable and the
remainder. Products are accepted only when one operand simplifies to a constant. -/
def isolate (id : Witness) : Polynomial F → Option (F × Polynomial F)
  | .const value => some (0, .const value)
  | .var other => if other = id then some (1, .const 0) else some (0, .var other)
  | .add left right => do
      let (a, p) ← isolate id left
      let (b, q) ← isolate id right
      return (a + b, .add p q)
  | .sub left right => do
      let (a, p) ← isolate id left
      let (b, q) ← isolate id right
      return (a - b, .sub p q)
  | .mul left right =>
      match simplify left, simplify right with
      | .const c, _ => (isolate id right).map fun (a, p) => (c * a, .mul (.const c) p)
      | _, .const c => (isolate id left).map fun (a, p) => (a * c, .mul p (.const c))
      | _, _ => none

/-- Structural failure to isolate is independent of the selected variable.
Only the resulting coefficient and remainder depend on that variable. -/
theorem isolate_isSome_eq (expr : Polynomial F) (left right : Witness) :
    (expr.isolate left).isSome = (expr.isolate right).isSome := by
  induction expr with
  | const value => rfl
  | var other => simp [isolate]; split <;> split <;> rfl
  | add a b ihA ihB | sub a b ihA ihB =>
      cases ha : isolate left a <;> cases hb : isolate left b <;>
        cases hc : isolate right a <;> cases hd : isolate right b <;>
        simp_all [isolate]
  | mul a b ihA ihB =>
      simp only [isolate]
      split <;> simp_all

theorem isolate_denote {id : Witness} {expr : Polynomial F} {coefficient : F}
    {rest : Polynomial F} (found : expr.isolate id = some (coefficient, rest))
    (assignment : Witness → F) :
    expr.denote assignment = coefficient * assignment id + rest.denote assignment := by
  induction expr generalizing coefficient rest with
  | const c => cases found; simp [Scalar.Circuit.ArithExpr.denote]
  | var other =>
      simp only [isolate] at found
      split at found <;> cases found <;> simp_all [Scalar.Circuit.ArithExpr.denote]
  | add left right ihLeft ihRight | sub left right ihLeft ihRight =>
      simp only [isolate] at found
      cases leftFound : isolate id left with
      | none => simp [leftFound] at found
      | some l =>
          cases rightFound : isolate id right with
          | none => simp [leftFound, rightFound] at found
          | some r =>
              simp [leftFound, rightFound] at found
              obtain ⟨rfl, rfl⟩ := found
              simp only [Scalar.Circuit.ArithExpr.denote, ihLeft leftFound, ihRight rightFound]
              ring
  | mul left right ihLeft ihRight =>
      simp only [isolate] at found
      split at found
      · rename_i c leftEq
        cases rightFound : isolate id right with
        | none => simp [rightFound] at found
        | some r =>
            simp [rightFound] at found
            obtain ⟨rfl, rfl⟩ := found
            have constant := denote_simplify left assignment
            rw [leftEq] at constant
            simp only [Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] at constant ihLeft ihRight ⊢
            rw [← constant, ihRight rightFound]
            ring
      · rename_i c rightEq _
        cases leftFound : isolate id left with
        | none => simp [leftFound] at found
        | some l =>
            simp [leftFound] at found
            obtain ⟨rfl, rfl⟩ := found
            have constant := denote_simplify right assignment
            rw [rightEq] at constant
            simp only [Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] at constant ihLeft ihRight ⊢
            rw [← constant, ihLeft leftFound]
            ring
      · contradiction

/-- Solve only nonzero coefficients in the actual field. -/
def solution? (expr : Polynomial F) (id : Witness) : Option (Polynomial F) := do
  let (coefficient, rest) ← expr.isolate id
  if coefficient = 0 then none
  else some (simplify (.mul (.const (-coefficient⁻¹)) rest))

theorem solution?_sound {expr value : Polynomial F} {id : Witness}
    (found : expr.solution? id = some value) (assignment : Witness → F)
    (zero : expr.denote assignment = 0) : assignment id = value.denote assignment := by
  unfold solution? at found
  cases splitEq : expr.isolate id with
  | none => simp [splitEq] at found
  | some pair =>
      rcases pair with ⟨coefficient, rest⟩
      simp only [splitEq, bind, Option.bind] at found
      split at found
      · contradiction
      · rename_i nonzero
        cases found
        rw [isolate_denote splitEq assignment] at zero
        simp only [denote_simplify, Scalar.Circuit.ArithExpr.denote]
        have equation := congrArg (fun x => coefficient⁻¹ * x) zero
        simp only [mul_add, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul, mul_zero] at equation
        exact (eq_neg_of_add_eq_zero_left equation).trans (by ring)

end Aiur.Optimized.Polynomial
