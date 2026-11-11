import Aiur.Tuple.Completeness
import Aiur.Tuple.Circuit.MemoDerivation
import Aiur.Tuple.EvalCorrectness

namespace Aiur.Tuple

/-- Successful source evaluation admits a finite memoized graph, with sharing allowed. -/
theorem memo_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F} (evaluated : EvalCall program name args result) :
    Circuit.MemoAccepts system name args result :=
  (evaluation_complete compiled evaluated).memo

/-- Every successful executable run supplies a memoized graph for its result. -/
theorem memo_eval_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {fuel : Nat} {result : Value F}
    (executed : eval program name args fuel = .ok result) :
    Circuit.MemoAccepts system name args result :=
  memo_complete compiled (eval_spec executed)

end Aiur.Tuple
