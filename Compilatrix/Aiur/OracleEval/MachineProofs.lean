import Compilatrix.Aiur.OracleEval.Machine

namespace Compilatrix.Aiur.OracleEval

open _root_.Aiur.Bytecode (Toplevel)

/-- More local transition fuel cannot change a successful replay. -/
theorem run_add_fuel (toplevel : Toplevel) (maxValues : Nat) {fuel : Nat} {task : Task}
    {continuations : List Continuation} {state : State} {result : Result}
    (success : run toplevel maxValues fuel task continuations state = .ok result) (extra : Nat) :
    run toplevel maxValues (fuel + extra) task continuations state = .ok result := by
  induction fuel generalizing task continuations state with
  | zero => simp [run] at success
  | succ fuel ih =>
      simp only [Nat.succ_add, run] at success ⊢
      cases advanced : step toplevel maxValues task continuations state with
      | error error =>
          rw [advanced] at success
          change Except.error error = Except.ok result at success
          cases success
      | ok progress =>
          cases progress with
          | done output =>
              rw [advanced] at success
              exact success
          | more next stack values =>
              rw [advanced] at success
              exact ih success

theorem runFunction_add_fuel (toplevel : Toplevel) (limits : Limits) (function : Nat)
    (inputs : Values) (replies : List Values) {result : Result}
    (success : runFunction toplevel limits function inputs replies = .ok result) (extra : Nat) :
    runFunction toplevel { limits with maxSteps := limits.maxSteps + extra } function inputs replies =
      .ok result := by
  simp only [runFunction] at success ⊢
  cases ready : prepare toplevel limits.maxValues limits.maxReplies limits.maxReplyFields limits.maxObservationFields function inputs replies with
  | error error =>
      rw [ready] at success
      change Except.error error = Except.ok result at success
      cases success
  | ok initial =>
      rw [ready] at success
      exact run_add_fuel toplevel limits.maxValues success extra

end Compilatrix.Aiur.OracleEval
