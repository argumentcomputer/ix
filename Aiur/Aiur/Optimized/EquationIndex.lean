import Aiur.Optimized.PolynomialIdentity
import Aiur.Optimized.Index

namespace Aiur.Optimized.EquationIndex

/-- A field-independent discriminator. Collisions only enlarge a bucket;
membership always compares the complete normalized equation. -/
def expressionKey : Polynomial F → Nat
  | .const _ => 0
  | .var id => id + 1
  | .add a b | .sub a b | .mul a b =>
      let left := expressionKey a
      if left == 0 then expressionKey b else left

def key (equation : ScopeId × Polynomial F) : Nat :=
  (hash (equation.1, expressionKey equation.2)).toNat

variable {F : Type} [Field F] [DecidableEq F]

/-- Normalize translated equations once, retaining their activation scopes. -/
def build (equations : List (Equation F)) (translate : Polynomial F → Polynomial F) :
    Std.HashMap Nat (List (ScopeId × Polynomial F)) :=
  Index.build key (equations.map fun eq => (eq.scope, (translate eq.polynomial).normalForm))

theorem member_build (equations : List (Equation F)) (translate : Polynomial F → Polynomial F)
    (scope : ScopeId) (polynomial : Polynomial F) :
    (scope, polynomial.normalForm) ∈
        (build equations translate).getD (key (scope, polynomial.normalForm)) [] ↔
      ∃ equation ∈ equations, equation.scope = scope ∧
        Polynomial.Identical (translate equation.polynomial) polynomial := by
  simp [build, Index.mem_build, Polynomial.Identical]

end Aiur.Optimized.EquationIndex
