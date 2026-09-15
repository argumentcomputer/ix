import Compilatrix.Aiur.OracleEval.Machine

namespace Compilatrix.Aiur.OracleEval

open _root_.Aiur.Bytecode (Toplevel)

/-- A finite local bytecode computation. The witness binds the exact toplevel,
function index, inputs, outputs, all demands, and all advice observations.
The answer tape is entirely consumed by the successful replay. -/
def Body (toplevel : Toplevel) (function : Nat) (inputs outputs : Values)
    (demands : List Message) (advice : List AdviceObservation) : Prop :=
  ∃ limits replies result,
    runFunction toplevel limits function inputs replies = .ok result ∧
    result.outputs = outputs ∧ result.demands = demands ∧ result.advice = advice

structure Checked (toplevel : Toplevel) (function : Nat) (inputs : Values) where
  result : Result
  body : Body toplevel function inputs result.outputs result.demands result.advice

def check (toplevel : Toplevel) (limits : Limits) (function : Nat) (inputs : Values)
    (replies : List Values) : Except Error (Checked toplevel function inputs) :=
  match checked : runFunction toplevel limits function inputs replies with
  | .error error => .error error
  | .ok result => .ok ⟨result, ⟨limits, replies, result, checked, rfl, rfl, rfl⟩⟩

theorem adviceAllowed_unrestricted (observations : List AdviceObservation) :
    AdviceAllowed unrestrictedAdvice observations := fun _ _ => rfl

theorem adviceAllowed_mono {left right : AdviceOracle}
    (admits : ∀ request answer, left request answer = true → right request answer = true)
    {observations : List AdviceObservation} (allowed : AdviceAllowed left observations) :
    AdviceAllowed right observations := fun observation member =>
  admits _ _ (allowed observation member)

end Compilatrix.Aiur.OracleEval
