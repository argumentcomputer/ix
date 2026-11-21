import Aiur.Scalar.Correctness
import Aiur.Scalar.Circuit.MemoDerivation
import Aiur.Scalar.EvalCorrectness

namespace Aiur.Scalar

/-- Every successful source evaluation admits a finite memoized circuit graph. -/
theorem memo_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List F} {result : F} (evaluates : EvalCall program name args result) :
    Circuit.MemoAccepts system name args result :=
  (evaluation_complete compiled evaluates).memo

/-- A successful executable run supplies a memoized graph for its result. -/
theorem memo_eval_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List F} {fuel : Nat} {result : F}
    (executed : eval program name args fuel = .ok result) :
    Circuit.MemoAccepts system name args result :=
  memo_complete compiled (eval_spec executed)

end Aiur.Scalar
