import Aiur.Generic.AST

/-! Late circuit lowering uses the core's tuple representation. The only bodies under these
generated bindings are generated variable references and projections, so they
cannot capture names in the operand, even in programmatically built ASTs. -/

namespace Aiur.Generic.ArrayLowering

/-- Copy a value, not its computation. A zero repeat still evaluates `value`. -/
def repeatValue (value : Aiur.Expr α) (length : Nat) : Aiur.Expr α :=
  .letValue (.bind "$array") value (.tuple (List.replicate length (.var "$array")))

/-- The caller has checked `start ≤ stop ≤ length`. An empty slice still
evaluates its operand. The projections add no calls, loads, or auxiliary columns. -/
def sliceValue (value : Aiur.Expr α) (start stop : Nat) : Aiur.Expr α :=
  .letValue (.bind "$array") value
    (.tuple ((List.range (stop - start)).map fun i => .project (.var "$array") (start + i)))

end Aiur.Generic.ArrayLowering
