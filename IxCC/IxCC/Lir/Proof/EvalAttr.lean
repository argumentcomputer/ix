import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The `lir_eval` simp set

Declared here so that `Lir.Proof.Eval` can tag its equations: a run of
concrete Lir statements over symbolic registers evaluates by
`simp only [lir_eval, …]`.
-/

/-- Equations for evaluating Lir expressions at width 64. -/
register_simp_attr lir_eval
