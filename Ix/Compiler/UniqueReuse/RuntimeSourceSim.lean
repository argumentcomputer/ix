import Ix.Compiler.UniqueReuse.Runtime
import Ix.Compiler.IxIR0.UniqueReverseSim
import Ix.Compiler.SimApply

namespace Ix.Compiler.UniqueReuse.Runtime

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.Recursion
open Ix.Compiler.IxIR0.UniqueReverse (listValue literalRun reverseOnto_nil)

def functionValue (schema : IxIR0.UniqueReverse.Schema) : IxIR0.Value := .clos .linear [] (body schema)

theorem SourceShape.evaluates {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    (shape : SourceShape declarations main) :
    Evaluates { env := IxIR0.Env.ofList declarations } [] main (functionValue shape.schema) := by
  simpa only [shape.mainEq, functionValue] using evaluatesDef shape.entry
    (evaluatesLam { env := IxIR0.Env.ofList declarations } [] .linear _)

theorem SourceShape.applies {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    (shape : SourceShape declarations main) (values : List Nat) :
    Applies { env := IxIR0.Env.ofList declarations } (functionValue shape.schema)
      (listValue shape.schema values) (listValue shape.schema values.reverse) := by
  apply appliesClosure
  have run := literalRun (ctx := { env := IxIR0.Env.ofList declarations }) shape.declarationsAt
    (evaluatesVar (by rfl : [listValue shape.schema values][0]? = some (listValue shape.schema values)))
    (evaluatesNullary (ctx := { env := IxIR0.Env.ofList declarations }) shape.declarationsAt.nil)
  simpa only [body, reverseOnto_nil] using run

theorem applies_unique {ctx : IxIR0.Ctx} {function argument left right : IxIR0.Value}
    (first : Applies ctx function argument left) (second : Applies ctx function argument right) : left = right := by
  obtain ⟨a, ha⟩ := first
  obtain ⟨b, hb⟩ := second
  have ha' := IxIR0.apply_mono (fuel' := a + b) (by omega) ha
  have hb' := IxIR0.apply_mono (fuel' := a + b) (by omega) hb
  exact Except.ok.inj (ha'.symm.trans hb')

/-- The same compiled function preserves every represented runtime argument.
Successful source application remains the forward-preservation premise. -/
theorem Compilation.sourceRefines
    {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    {functionFuel applyFuel : Nat} {function argument result : Ixon.Eval.Value} {values : List Nat}
    (oracles : @Sim.OracleRel compilation.erased.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config)
      functionFuel entry.frame [] entry.source = .ok function)
    (argumentWF : argument.SharingWF)
    (argumentRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw }
      argument (listValue compilation.schema values) compilation.erased.memberScope)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config)
      applyFuel function argument = .ok result) :
    @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList compilation.erased.erasure.result.raw }
      result (listValue compilation.schema values.reverse) compilation.erased.memberScope := by
  letI : Sim.MemberScope := compilation.erased.memberScope
  obtain ⟨_, _, functionRun, functionRel⟩ := compilation.erased.sourceRefines oracles contextWF evaluated
  have functionEq := Evaluates.unique ⟨_, functionRun⟩ compilation.source.shape.evaluates
  rw [functionEq] at functionRel
  have functionWF := (Ixon.Eval.eval_inlineSharing contextWF entry.frameSharingWF .nil
    compilation.erased.entrySharesBelow evaluated).2
  obtain ⟨_, _, resultRun, resultRel⟩ := Sim.apply_sim_inlineSharing compilation.erased.members
    oracles contextWF functionWF argumentWF applied functionRel argumentRel
  have resultEq := applies_unique ⟨_, resultRun⟩ (compilation.source.shape.applies values)
  simpa only [resultEq, Compilation.schema] using resultRel

end Ix.Compiler.UniqueReuse.Runtime
