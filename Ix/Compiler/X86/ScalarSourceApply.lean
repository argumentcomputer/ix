import Ix.Compiler.X86.ScalarSourceSelect
import Ix.Compiler.Pipeline
import Ix.Compiler.SimApply

namespace Ix.Compiler.X86.Scalar.Source
open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.Recursion
open Ix.Compiler.IxIR0.NatArithmetic (Represents)

def Selected.rawBody {declarations root} (selected : Selected declarations root) : IxIR0.Expr :=
  expression selected.primitives selected.entries (parameters 2) selected.entryFunction.body

def Selected.rawFunction {declarations root} (selected : Selected declarations root) : IxIR0.Value :=
  .clos .many [] (.lam .many selected.rawBody)

theorem Selected.evaluates {declarations root} (selected : Selected declarations root) :
    IxIR0.Recursion.Evaluates { env := IxIR0.Env.ofList declarations } [] (.ref root) selected.rawFunction := by
  obtain ⟨address, found, declared⟩ := selected.matched.functions _ _ selected.functionFound
  have same : address = root := Option.some.inj (found.symm.trans selected.rootFound)
  subst address
  have declared : IxIR0.Env.ofList declarations root =
      some (.defn .shared (.lam .many (.lam .many selected.rawBody))) := by
    simpa only [functionBody, selected.binary, lambda, Selected.rawBody] using declared
  exact evaluatesDef declared (evaluatesLam _ _ _ _)

theorem Selected.applies {declarations root} (selected : Selected declarations root)
    {left right : IxIR0.Value} {a b number : Nat}
    (leftRep : Represents selected.primitives.arithmetic left a)
    (rightRep : Represents selected.primitives.arithmetic right b)
    (evaluated : NatEvaluates selected.scalar.program.functions selected.entryFunction.body #[a, b] number) :
    ∃ result,
      Applies { env := IxIR0.Env.ofList declarations } selected.rawFunction left (.clos .many [left] selected.rawBody) ∧
      Applies { env := IxIR0.Env.ofList declarations } (.clos .many [left] selected.rawBody) right result ∧
      Represents selected.primitives.arithmetic result number := by
  have valid := (selected.scalar.function_valid selected.functionFound).2
  obtain ⟨result, bodyRun, resultRep⟩ := raw_evaluates selected.matched evaluated selected.scalar.program.entry
    (by simpa [selected.binary] using valid)
    _ _ (bindings_two leftRep rightRep)
  exact ⟨result, appliesClosure (evaluatesLam _ _ _ _), appliesClosure bodyRun, resultRep⟩

theorem applies_unique {ctx : IxIR0.Ctx} {function argument left right : IxIR0.Value}
    (first : Applies ctx function argument left) (second : Applies ctx function argument right) : left = right := by
  obtain ⟨a, first⟩ := first
  obtain ⟨b, second⟩ := second
  exact Except.ok.inj ((IxIR0.apply_mono (fuel' := a + b) (by omega) first).symm.trans
    (IxIR0.apply_mono (fuel' := a + b) (by omega) second))

/-- Reuse the checked source erasure certificate for an exported closure.
The later native attachment does not alter or revalidate source semantics. -/
theorem Selected.sourceFunction
    {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel)
    (selected : Selected source.erasure.result.raw root)
    {fuel : Nat} {function : Ixon.Eval.Value}
    (oracles : @Sim.OracleRel source.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList source.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) fuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok function) :
    @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList source.erasure.result.raw } function selected.rawFunction source.memberScope := by
  letI : Sim.MemberScope := source.memberScope
  have frameWF : (Pipeline.validatedMainFrame root).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [Pipeline.validatedMainFrame] at found
  have inlined := Ixon.Eval.eval_inlineSharing contextWF frameWF .nil (by rfl) evaluated
  have entry := source.entry.related
  rw [EraseValidator.inlineTables_tablesOfFrame] at entry
  obtain ⟨targetFuel, value, run, related⟩ := Sim.erasure_sim_with_members source.members oracles inlined.1 entry (by
    simpa [Ixon.Eval.valuesInlineSharing] using
      (Sim.EnvRel.nil (ectx := (Pipeline.validatedEvalCtx constants config).inlineSharing)
        (ictx := { env := IxIR0.Env.ofList source.erasure.result.raw })
        (refs := (Pipeline.validatedMainFrame root).inlineSharing.refs)
        (muts := (Pipeline.validatedMainFrame root).inlineSharing.selfMuts)
        (sa := (Pipeline.validatedMainFrame root).inlineSharing.selfAddr)))
  rw [source.entryTarget] at run
  have same := (IxIR0.Recursion.Evaluates.unique ⟨targetFuel, run⟩ selected.evaluates)
  exact same ▸ related

theorem Selected.sourceApplies
    {constants : List (Address × Constant)} {root : Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel)
    (selected : Selected source.erasure.result.raw root)
    {function left right intermediate result : Ixon.Eval.Value} {fuel firstFuel secondFuel : Nat}
    {rawLeft rawRight : IxIR0.Value} {a b number : Nat}
    (oracles : @Sim.OracleRel source.memberScope (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList source.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (functionWF : function.SharingWF) (leftWF : left.SharingWF) (rightWF : right.SharingWF)
    (entry : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) fuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok function)
    (first : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) firstFuel function left = .ok intermediate)
    (second : Ixon.Eval.apply (Pipeline.validatedEvalCtx constants config) secondFuel intermediate right = .ok result)
    (leftRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList source.erasure.result.raw } left rawLeft source.memberScope)
    (rightRel : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList source.erasure.result.raw } right rawRight source.memberScope)
    (leftRep : Represents selected.primitives.arithmetic rawLeft a)
    (rightRep : Represents selected.primitives.arithmetic rawRight b)
    (evaluated : NatEvaluates selected.scalar.program.functions selected.entryFunction.body #[a, b] number) :
    ∃ rawResult,
      @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
        { env := IxIR0.Env.ofList source.erasure.result.raw } result rawResult source.memberScope ∧
      Represents selected.primitives.arithmetic rawResult number := by
  letI : Sim.MemberScope := source.memberScope
  have functionRel := selected.sourceFunction source oracles contextWF entry
  obtain ⟨rawResult, firstRun, secondRun, resultRep⟩ := selected.applies leftRep rightRep evaluated
  obtain ⟨firstTargetFuel, middle, applied, middleRel⟩ := Sim.apply_sim_inlineSharing
    source.members oracles contextWF functionWF leftWF first functionRel leftRel
  have same := applies_unique ⟨firstTargetFuel, applied⟩ firstRun
  subst middle
  have middleWF := (Ixon.Eval.apply_inlineSharing contextWF functionWF leftWF first).2
  obtain ⟨secondTargetFuel, finalValue, applied, resultRel⟩ := Sim.apply_sim_inlineSharing
    source.members oracles contextWF middleWF rightWF second middleRel rightRel
  have same := applies_unique ⟨secondTargetFuel, applied⟩ secondRun
  exact ⟨rawResult, same ▸ resultRel, resultRep⟩

end Ix.Compiler.X86.Scalar.Source
