import Aiur.Scalar.Circuit.Basic

namespace Aiur.Scalar.Circuit

/-- A structural upper bound on polynomial degree. Constants, including zero,
have degree zero; cancellation and multiplication by zero are not simplified. -/
def ArithExpr.degree : ArithExpr F → Nat
  | .const _ => 0
  | .var _ => 1
  | .add left right | .sub left right => max left.degree right.degree
  | .mul left right => left.degree + right.degree

end Aiur.Scalar.Circuit
