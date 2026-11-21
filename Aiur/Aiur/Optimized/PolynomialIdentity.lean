import Aiur.Optimized.PolynomialFacts

namespace Aiur.Optimized.Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- A deliberately conservative, executable polynomial identity check. The
optimizer preserves expression order, so ring expansion is unnecessary. -/
def normalForm (expr : Polynomial F) : Polynomial F := expr.simplify

@[simp] theorem eval_normalForm (expr : Polynomial F) (assignment : Witness → F) :
    expr.normalForm.denote assignment = expr.denote assignment := denote_simplify expr assignment

def Identical (left right : Polynomial F) : Prop := left.normalForm = right.normalForm

instance (left right : Polynomial F) : Decidable (Identical left right) := by
  unfold Identical
  infer_instance

theorem Identical.denote {left right : Polynomial F} (same : Identical left right)
    (assignment : Witness → F) : left.denote assignment = right.denote assignment := by
    simpa only [eval_normalForm] using congrArg (Circuit.ArithExpr.denote assignment) same

end Aiur.Optimized.Polynomial
