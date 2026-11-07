import Aiur.Optimized.PolynomialFacts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Aiur.Optimized.LinearNormalization

variable {F : Type} [Field F] [DecidableEq F]

/-- Sparse affine coefficients. Combining equal variables prevents substitutions
from repeatedly expanding different expressions for the same linear value. -/
abbrev Terms (F : Type) := List (Witness × F)

def Terms.denote (terms : Terms F) (assignment : Witness → F) : F :=
  (terms.map (fun (id, coefficient) => coefficient * assignment id)).sum

/-- Merge sorted sparse coefficients. Singleton leaves and scaling preserve
the order, so normalization never needs repeated linear insertion searches. -/
def Terms.add : Terms F → Terms F → Terms F
  | [], right => right
  | left, [] => left
  | (leftId, leftValue) :: left, (rightId, rightValue) :: right =>
      if leftId = rightId then
        if leftValue + rightValue = 0 then Terms.add left right
        else (leftId, leftValue + rightValue) :: Terms.add left right
      else if leftId < rightId then
        (leftId, leftValue) :: Terms.add left ((rightId, rightValue) :: right)
      else (rightId, rightValue) :: Terms.add ((leftId, leftValue) :: left) right
  termination_by left right => left.length + right.length

theorem Terms.denote_add (left right : Terms F) (assignment : Witness → F) :
    (left.add right).denote assignment = left.denote assignment + right.denote assignment := by
  match left, right with
  | [], right => simp [Terms.add, Terms.denote]
  | left, [] => cases left <;> simp [Terms.add, Terms.denote]
  | (leftId, leftValue) :: left, (rightId, rightValue) :: right =>
      by_cases same : leftId = rightId
      · subst rightId
        by_cases zero : leftValue + rightValue = 0
        · simp only [Terms.add, if_pos zero, ↓reduceIte]
          rw [Terms.denote_add left right]
          have zeroMul := congrArg (fun x => x * assignment leftId) zero
          simp only [add_mul, zero_mul] at zeroMul
          simp only [Terms.denote, List.map_cons, List.sum_cons]
          linear_combination -zeroMul
        · simp only [Terms.add, if_neg zero, ↓reduceIte, Terms.denote, List.map_cons, List.sum_cons]
          have ih := Terms.denote_add left right assignment
          simp only [Terms.denote] at ih
          rw [ih]
          ring
      · by_cases before : leftId < rightId
        · simp only [Terms.add, if_neg same, if_pos before, Terms.denote, List.map_cons, List.sum_cons]
          have ih := Terms.denote_add left ((rightId, rightValue) :: right) assignment
          simp only [Terms.denote, List.map_cons, List.sum_cons] at ih
          rw [ih]
          ring
        · simp only [Terms.add, if_neg same, if_neg before, Terms.denote, List.map_cons, List.sum_cons]
          have ih := Terms.denote_add ((leftId, leftValue) :: left) right assignment
          simp only [Terms.denote, List.map_cons, List.sum_cons] at ih
          rw [ih]
          ring
  termination_by left.length + right.length

def Terms.scale (coefficient : F) (terms : Terms F) : Terms F :=
  if coefficient = 0 then [] else terms.map fun (id, value) => (id, coefficient * value)

theorem Terms.denote_scale (coefficient : F) (terms : Terms F) (assignment : Witness → F) :
    (terms.scale coefficient).denote assignment = coefficient * terms.denote assignment := by
  by_cases zero : coefficient = 0
  · simp [Terms.scale, Terms.denote, zero]
  · simp only [Terms.scale, if_neg zero]
    induction terms with
    | nil => simp [Terms.denote]
    | cons head rest ih =>
        rcases head with ⟨id, value⟩
        simp only [List.map_cons, Terms.denote, List.sum_cons] at ih ⊢
        rw [ih]
        ring

structure Affine (F : Type) where
  constant : F
  terms : Terms F

def Affine.denote (form : Affine F) (assignment : Witness → F) : F :=
  form.terms.denote assignment + form.constant

def Affine.add (left right : Affine F) : Affine F :=
  ⟨left.constant + right.constant, left.terms.add right.terms⟩

def Affine.scale (coefficient : F) (form : Affine F) : Affine F :=
  ⟨coefficient * form.constant, form.terms.scale coefficient⟩

@[simp] theorem Affine.denote_add (left right : Affine F) (assignment : Witness → F) :
    (left.add right).denote assignment = left.denote assignment + right.denote assignment := by
  simp only [Affine.add, Affine.denote, Terms.denote_add]
  ring

@[simp] theorem Affine.denote_scale (coefficient : F) (form : Affine F) (assignment : Witness → F) :
    (form.scale coefficient).denote assignment = coefficient * form.denote assignment := by
  simp only [Affine.scale, Affine.denote, Terms.denote_scale]
  ring

def Terms.expression : Terms F → Polynomial F
  | [] => .const 0
  | (id, coefficient) :: rest =>
      .add (.mul (.const coefficient) (.var id)) (Terms.expression rest)

omit [DecidableEq F] in
theorem Terms.expression_denote (terms : Terms F) (assignment : Witness → F) :
    terms.expression.denote assignment = terms.denote assignment := by
  induction terms with
  | nil => simp [Terms.expression, Terms.denote, Scalar.Circuit.ArithExpr.denote]
  | cons head rest ih =>
      rcases head with ⟨id, coefficient⟩
      simpa [Terms.expression, Terms.denote, Scalar.Circuit.ArithExpr.denote] using
        congrArg (coefficient * assignment id + ·) ih

def Affine.expression (form : Affine F) : Polynomial F :=
  Polynomial.simplify (.add form.terms.expression (.const form.constant))

@[simp] theorem Affine.expression_denote (form : Affine F) (assignment : Witness → F) :
    form.expression.denote assignment = form.denote assignment := by
  simp [Affine.expression, Affine.denote, Terms.expression_denote, Scalar.Circuit.ArithExpr.denote]

inductive Result (F : Type) where
  | affine (form : Affine F)
  | nonlinear (expression : Polynomial F)

def Result.expression : Result F → Polynomial F
  | .affine form => form.expression
  | .nonlinear expression => expression

def Result.denote (result : Result F) (assignment : Witness → F) : F :=
  result.expression.denote assignment

def Result.add (left right : Result F) : Result F :=
  match left, right with
  | .affine left, .affine right => .affine (left.add right)
  | left, right => .nonlinear (.add left.expression right.expression)

def Result.sub (left right : Result F) : Result F :=
  match left, right with
  | .affine left, .affine right => .affine (left.add (right.scale (-1)))
  | left, right => .nonlinear (.sub left.expression right.expression)

def Result.mul (left right : Result F) : Result F :=
  match left, right with
  | .affine left, .affine right =>
      if left.terms.isEmpty then .affine (right.scale left.constant)
      else if right.terms.isEmpty then .affine (left.scale right.constant)
      else .nonlinear (.mul left.expression right.expression)
  | left, right => .nonlinear (.mul left.expression right.expression)

@[simp] theorem Result.denote_add (left right : Result F) (assignment : Witness → F) :
    (left.add right).denote assignment = left.denote assignment + right.denote assignment := by
  cases left <;> cases right <;>
    simp [Result.add, Result.denote, Result.expression, Scalar.Circuit.ArithExpr.denote]

@[simp] theorem Result.denote_sub (left right : Result F) (assignment : Witness → F) :
    (left.sub right).denote assignment = left.denote assignment - right.denote assignment := by
  cases left <;> cases right <;>
    simp [Result.sub, Result.denote, Result.expression, Scalar.Circuit.ArithExpr.denote, sub_eq_add_neg]

@[simp] theorem Result.denote_mul (left right : Result F) (assignment : Witness → F) :
    (left.mul right).denote assignment = left.denote assignment * right.denote assignment := by
  cases left with
  | nonlinear left => cases right <;> rfl
  | affine left =>
      cases right with
      | nonlinear right => rfl
      | affine right =>
          simp only [Result.mul]
          split
          · rename_i empty
            have empty : left.terms = [] := List.isEmpty_iff.mp empty
            simp only [Result.denote, Result.expression, Affine.expression_denote, Affine.denote_scale]
            simp [Affine.denote, Terms.denote, empty]
          · split
            · rename_i empty
              have empty : right.terms = [] := List.isEmpty_iff.mp empty
              simp only [Result.denote, Result.expression, Affine.expression_denote, Affine.denote_scale]
              simp [Affine.denote, Terms.denote, empty, mul_comm]
            · rfl

/-- Normalize maximal affine subexpressions without expanding nonlinear products. -/
def normalize : Polynomial F → Result F
  | .const value => .affine ⟨value, []⟩
  | .var id => .affine ⟨0, [(id, 1)]⟩
  | .add left right => (normalize left).add (normalize right)
  | .sub left right => (normalize left).sub (normalize right)
  | .mul left right => (normalize left).mul (normalize right)

theorem normalize_denote (expression : Polynomial F) (assignment : Witness → F) :
    (normalize expression).denote assignment = expression.denote assignment := by
  induction expression with
  | const value => simp [normalize, Result.denote, Result.expression, Affine.denote,
      Terms.denote, Scalar.Circuit.ArithExpr.denote]
  | var id => simp [normalize, Result.denote, Result.expression, Affine.denote,
      Terms.denote, Scalar.Circuit.ArithExpr.denote]
  | add left right ihLeft ihRight =>
      simpa [normalize, Scalar.Circuit.ArithExpr.denote] using congrArg₂ (· + ·) ihLeft ihRight
  | sub left right ihLeft ihRight =>
      simpa [normalize, Scalar.Circuit.ArithExpr.denote] using congrArg₂ (· - ·) ihLeft ihRight
  | mul left right ihLeft ihRight =>
      simpa [normalize, Scalar.Circuit.ArithExpr.denote] using congrArg₂ (· * ·) ihLeft ihRight

end Aiur.Optimized.LinearNormalization

namespace Aiur.Optimized.Polynomial
variable {F : Type} [Field F] [DecidableEq F]

def normalizeLinear (expression : Polynomial F) : Polynomial F :=
  (LinearNormalization.normalize expression).expression

@[simp] theorem denote_normalizeLinear (expression : Polynomial F) (assignment : Witness → F) :
    expression.normalizeLinear.denote assignment = expression.denote assignment :=
  LinearNormalization.normalize_denote expression assignment

end Aiur.Optimized.Polynomial
