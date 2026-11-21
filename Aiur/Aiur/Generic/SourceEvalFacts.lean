import Aiur.Generic.ControlEvalSpec

namespace Aiur.Generic.SourceSemantics

/-- Every successful ordinary expression run has a native derivation. Use
`evalOutcome_spec` when observing an exit and `evalFunction_spec` at a function
boundary, where an early return also supplies a successful result. -/
theorem evalExpr_spec [Field F] [DecidableEq F]
    {world : World F} {types : Types} {hints : HintProvider world}
    {locals : Environment F Nat} {fuel : Nat} {expr : Expr F}
    {before after : Heap F} {result : SourceValue F}
    (executed : evalExprWith world hints types locals fuel expr before = .ok (result, after)) :
    EvalExpr world types locals expr before result after :=
  evalOutcome_spec (finishExpression_ok.mp executed)

end Aiur.Generic.SourceSemantics
