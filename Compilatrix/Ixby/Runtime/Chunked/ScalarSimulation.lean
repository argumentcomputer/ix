import Compilatrix.Ixby.Runtime.Chunked.Primitive

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Primitive Limits Error Scalar)

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-- The unchanged scalar dispatcher commutes with the representation map,
including wrong tags, wrong arities and value errors. -/
theorem evalScalarUnchecked_sim (primitive : Primitive) (args : List Value) :
    (evalScalarUnchecked primitive args).map Value.toReference =
      primitive.evalScalarUnchecked (args.map Value.toReference) := by
  unfold evalScalarUnchecked Primitive.evalScalarUnchecked
  split <;> simp_all [Except.map, bind, Except.bind, pure, Except.pure, throw,
    MonadExceptOf.throw]
  all_goals
    repeat first | split | (solve | simp_all [Except.map, bind, Except.bind,
      pure, Except.pure, throw, MonadExceptOf.throw])

end Compilatrix.Ixby.Runtime.Chunked
