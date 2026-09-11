import Ix.Compiler.Borrow.Runtime
import Ix.Compiler.SimApply

namespace Ix.Compiler.Borrow.Runtime

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR0.Recursion (Evaluates Applies)

private theorem frameWF (root : Address) : (Pipeline.validatedMainFrame root).SharingWF := by
  constructor
  · rfl
  · intro index member found
    simp [Pipeline.validatedMainFrame] at found

/-- Project the actual source compiler's erasure certificate, including its
mutual-member scope. No source execution is performed by selection. -/
theorem erasureFunction {constants root config eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    {fuel : Nat} {function : Ixon.Eval.Value}
    (oracles : @Sim.OracleRel attached.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList attached.source.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) fuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok function) :
    ∃ targetFuel targetFunction,
      IxIR0.eval { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
        targetFuel [] (.ref root) = .ok targetFunction ∧
      @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
        { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
        function targetFunction attached.source.memberScope := by
  letI : Sim.MemberScope := attached.source.memberScope
  have inlined := Ixon.Eval.eval_inlineSharing contextWF (frameWF root) .nil
    (by rfl) evaluated
  have entry := attached.source.entry.related
  rw [EraseValidator.inlineTables_tablesOfFrame] at entry
  obtain ⟨fuel, value, run, related⟩ := Sim.erasure_sim_with_members
    attached.source.members oracles inlined.1 entry (by
      simpa [Ixon.Eval.valuesInlineSharing] using
        (Sim.EnvRel.nil (ectx := (Pipeline.validatedEvalCtx constants config).inlineSharing)
          (ictx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw })
          (refs := (Pipeline.validatedMainFrame root).inlineSharing.refs)
          (muts := (Pipeline.validatedMainFrame root).inlineSharing.selfMuts)
          (sa := (Pipeline.validatedMainFrame root).inlineSharing.selfAddr)))
  rw [attached.source.entryTarget] at run
  exact ⟨fuel, value, run, related⟩

private theorem applies_unique {ctx : IxIR0.Ctx} {function argument left right : IxIR0.Value}
    (first : Applies ctx function argument left) (second : Applies ctx function argument right) : left = right := by
  obtain ⟨a, ha⟩ := first
  obtain ⟨b, hb⟩ := second
  have ha' := IxIR0.apply_mono (fuel' := a + b) (by omega) ha
  have hb' := IxIR0.apply_mono (fuel' := a + b) (by omega) hb
  exact Except.ok.inj (ha'.symm.trans hb')

/-- Source preservation on every represented argument. Sharing and oracle
premises are the existing erasure boundary; the function/application proof
comes from the checked source graph and never from a supplied callback. -/
theorem Certified.sourcePreservation {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (certified : Certified attached options) (argument : Source.Argument)
    {functionFuel applyFuel : Nat} {function sourceArgument result : Ixon.Eval.Value}
    (oracles : @Sim.OracleRel attached.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList attached.source.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) functionFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok function)
    (argumentWF : sourceArgument.SharingWF)
    (argumentRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
      sourceArgument argument.value attached.source.memberScope)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config)
      applyFuel function sourceArgument = .ok result) :
    @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
      result (.lit (.nat (argument.result certified.target.schema.zeroResult certified.target.schema.succResult)))
      attached.source.memberScope := by
  letI : Sim.MemberScope := attached.source.memberScope
  obtain ⟨_, _, functionRun, functionRel⟩ := erasureFunction attached oracles contextWF evaluated
  have functionEq := Evaluates.unique ⟨_, functionRun⟩ certified.source.evaluates
  rw [functionEq] at functionRel
  have functionWF := (Ixon.Eval.eval_inlineSharing contextWF (frameWF root) .nil (by rfl) evaluated).2
  obtain ⟨_, _, resultRun, resultRel⟩ := Sim.apply_sim_inlineSharing attached.source.members
    oracles contextWF functionWF argumentWF applied functionRel argumentRel
  have resultEq := applies_unique ⟨_, resultRun⟩ (certified.source.applies argument)
  simpa only [resultEq] using resultRel

/-- The same accepted source function has two actual target executions on
every owned runtime heap in the stated domain. Their scalar results agree,
both reclaim the whole input, and borrowing removes exactly two RC ticks. -/
theorem Certified.runtimePreservation {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (certified : Certified attached options) (argument : Source.Argument) (field : IxIR2.Eval.RVal)
    {store : IxIR2.Eval.Store} {location rc : Nat}
    (input : IxIR2.Borrow.Open.Input certified.target.schema (argument.target field) store location rc)
    (mode : IxIR2.Eval.Interpretation) (exit : IxIR2.Borrow.Open.Exit) :
    let target := certified.target
    let number := argument.result target.schema.zeroResult target.schema.succResult
    ∃ fuel output,
      IxIR2.Eval.Steps (IxIR2.Borrow.Open.context attached.target.artifact.validationContext attached.target.artifact.program)
        mode (target.entry.beforeBody.ownedCost (argument.target field).fieldCost)
        (IxIR2.Borrow.Open.start target.entry.before location store (fuel + 2) exit)
        (IxIR2.Borrow.Open.finish (IxIR2.Borrow.Open.bump output 2) 0 number exit) ∧
      IxIR2.Eval.Steps (IxIR2.Borrow.Open.context attached.target.artifact.validationContext target.rewrite.program)
        mode (target.entry.afterBody.readCost (argument.target field).fieldCost + 3)
        (IxIR2.Borrow.Open.start (IxIR2.Borrow.ownedWrapper target.entry.summary.borrowed target.entry.before)
          location store (fuel + 1) exit)
        (IxIR2.Borrow.Open.finish output 0 number exit) ∧
      IxIR2.Borrow.Open.FullyReleased output ∧ IxIR2.Borrow.Open.FullyReleased (IxIR2.Borrow.Open.bump output 2) ∧
      output.peakLiveNodes = store.peakLiveNodes ∧ output.heap.rcops < (IxIR2.Borrow.Open.bump output 2).heap.rcops := by
  simpa only [Source.Argument.target_result] using
    certified.target.strictImprovement mode (argument.target field) input exit

/-- Compose the actual source erasure/application certificate with the two
public target runners. The input relation needs only the observed outer tag;
the ownership contract governs reclamation of the entire target payload. -/
theorem Certified.sourceToRuntime {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (certified : Certified attached options) (argument : Source.Argument) (field : IxIR2.Eval.RVal)
    {functionFuel applyFuel : Nat} {function sourceArgument result : Ixon.Eval.Value}
    (oracles : @Sim.OracleRel attached.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList attached.source.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) functionFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok function)
    (argumentWF : sourceArgument.SharingWF)
    (argumentRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
      sourceArgument argument.value attached.source.memberScope)
    (applied : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config)
      applyFuel function sourceArgument = .ok result)
    {store : IxIR2.Eval.Store} {location rc : Nat}
    (input : IxIR2.Borrow.Open.Input certified.target.schema (argument.target field) store location rc)
    (mode : IxIR2.Eval.Interpretation) :
    let target := certified.target
    let major := argument.target field
    let number := argument.result target.schema.zeroResult target.schema.succResult
    ∃ fuel output,
      @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
        { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
        result (.lit (.nat number)) attached.source.memberScope ∧
      IxIR2.Eval.runFunction
        (IxIR2.Borrow.Open.context attached.target.artifact.validationContext attached.target.artifact.program)
        mode target.entry.before #[.loc location] (target.entry.beforeBody.ownedCost major.fieldCost)
        (fuel + 2) store = .ok {
          store := IxIR2.Borrow.Open.bump output 2, value := .lit (.nat number)
          controlRemaining := 0, heapRemaining := 0 } ∧
      IxIR2.Eval.runFunction
        (IxIR2.Borrow.Open.context attached.target.artifact.validationContext target.rewrite.program)
        mode (IxIR2.Borrow.ownedWrapper target.entry.summary.borrowed target.entry.before) #[.loc location]
        (target.entry.afterBody.readCost major.fieldCost + 3) (fuel + 1) store = .ok {
          store := output, value := .lit (.nat number), controlRemaining := 0, heapRemaining := 0 } ∧
      IxIR2.Borrow.Open.FullyReleased output ∧
      IxIR2.Borrow.Open.FullyReleased (IxIR2.Borrow.Open.bump output 2) ∧
      output.peakLiveNodes = store.peakLiveNodes ∧
      (IxIR2.Borrow.Open.bump output 2).heap.rcops = output.heap.rcops + 2 := by
  have source := certified.sourcePreservation argument oracles contextWF evaluated argumentWF argumentRel applied
  obtain ⟨fuel, output, before, after, clean, beforeClean, peak⟩ :=
    certified.target.runFunctions mode (argument.target field) input
  refine ⟨fuel, output, source, ?_, ?_, clean, beforeClean, peak, rfl⟩
  · simpa only [Source.Argument.target_result] using before
  · simpa only [Source.Argument.target_result] using after

end Ix.Compiler.Borrow.Runtime
