import Ix.Compiler.IxIR0.RecursionSim
import Ix.Compiler.IxIR0.ProjectionFree

/-! The checked direct recursor is projection-free throughout its reachable
program. Successful evaluator runs therefore supply the actual call-aware
trace required by ownership-lowering progress.
-/

namespace Ix.Compiler.IxIR0.Recursion

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR0.ProjectionFree

theorem directListSafe (schema : Schema) (values : List Nat) :
    ExprSafe (directList schema values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simpa only [ExprSafe, directList, consExpr, app2, syntaxSafe, Bool.true_and] using ih

theorem Plan.directMainSafe (plan : Plan) (address : Address) :
    ExprSafe (plan.directMain address) := by
  cases alias : plan.retainedAlias <;>
    simp [ExprSafe, Plan.directMain, alias, directCall, app2, syntaxSafe, directListSafe]

theorem Plan.targetContextSafe (plan : Plan) (address : Address) :
    CtxSafe { env := Env.ofList (targetDeclarations plan address) } := by
  constructor
  · intro key declaration lookup
    have rows : (targetDeclarations plan address).all (fun row => declSafe row.2) = true := by
      cases alias : plan.retainedAlias <;>
        simp [targetDeclarations, alias, directRecursor, consExpr, app2, declSafe, syntaxSafe]
    unfold Env.ofList at lookup
    obtain ⟨row, found, value⟩ := Option.map_eq_some_iff.mp lookup
    have safe := List.all_eq_true.mp rows row (List.mem_of_find?_eq_some found)
    simpa only [value] using safe
  · intro key arguments result _ oracle
    cases oracle

theorem Recovered.projectionSafe
    {declarations : List (Address × Decl)} {main : Expr}
    (recovery : Recovered declarations main) {fuel : Nat} {value : Value}
    (run : eval { env := Env.ofList (targetDeclarations recovery.checked.plan recovery.address) }
      fuel [] (recovery.checked.plan.directMain recovery.address) = .ok value) :
    ProjectionSafe.Eval
      { env := Env.ofList (targetDeclarations recovery.checked.plan recovery.address) }
      fuel [] (recovery.checked.plan.directMain recovery.address) value :=
  ProjectionFree.Eval.of_run (recovery.checked.plan.targetContextSafe recovery.address)
    ValuesSafe.nil (recovery.checked.plan.directMainSafe recovery.address) run

end Ix.Compiler.IxIR0.Recursion
