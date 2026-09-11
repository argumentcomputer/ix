import Ix.Compiler.UniqueReuse.Pipeline
import Ix.Compiler.UniqueReuse.TargetSim

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR0.UniqueReverse (Plan)

def OwnedSemantics (plan : Plan) : Prop :=
  ∃ fuel store value reclaimed,
    IxIR1.runOwnedMain { decls := IxIR1.Env.ofList (declarations plan.schema) }
      .unique (mainCode plan) fuel = .ok (store, value) ∧
    MainResult plan store value ∧
    IxIR1.dropUVal { decls := IxIR1.Env.ofList (declarations plan.schema) }
      (3 * plan.values.length + 2) store value = .ok reclaimed ∧
    reclaimed.live = 0 ∧ reclaimed.frees = reclaimed.allocs ∧
    Released1 store reclaimed (plan.values.length + 1) []

theorem ownedSemantics (plan : Plan) : OwnedSemantics plan := by
  obtain ⟨fuel, store, value, run, result⟩ := mainExists plan
  obtain ⟨reclaimed, release, released⟩ := release1
    { decls := IxIR1.Env.ofList (declarations plan.schema) } result.owned result.list
  have live := released.live release
  refine ⟨fuel, store, value, reclaimed, run, result, by simpa using release, ?_, ?_, by simpa using released⟩
  · rw [result.live] at live
    simp only [List.length_reverse] at live
    omega
  · rw [released.allocs, released.frees, result.allocs, result.frees]
    simp only [List.length_reverse]
    omega

def TargetSemantics (plan : Plan) (reuse : Bool) (mode : IxIR2.Eval.Interpretation)
    (extraControl heapFuel : Nat) (result : IxIR2.Eval.Result) : Prop :=
  IxIR2.Eval.runMain (Target.context plan reuse) mode (IxIR2.UniqueLower.program plan reuse)
    (Target.controlCost plan reuse + extraControl) heapFuel = .ok result ∧
  Target.MainResult plan reuse mode result.store result.value ∧
  result.controlRemaining = extraControl ∧ result.heapRemaining = heapFuel ∧
  ∃ reclaimed,
    IxIR2.Eval.dropUnique (2 * plan.values.length + 1) result.store result.value = .ok (reclaimed, 0) ∧
    reclaimed.live = 0 ∧ reclaimed.heap.frees = reclaimed.heap.allocs ∧
    Released2 result.store reclaimed (plan.values.length + 1) []

theorem targetSemantics (plan : Plan) (reuse : Bool) (mode : IxIR2.Eval.Interpretation)
    (extraControl heapFuel : Nat) : ∃ result, TargetSemantics plan reuse mode extraControl heapFuel result := by
  obtain ⟨result, run, semantics, control, heap⟩ := Target.mainRuns plan reuse mode extraControl heapFuel
  exact ⟨result, run, semantics, control, heap, semantics.reclaims⟩

def BackendSemantics {plan : Plan} {limits : IxIR2.Validate.Limits} : Backend plan limits → Prop
  | .ownedOnly _ => True
  | .translated target => ∀ extraControl heapFuel,
      ∃ baseline selected logical,
        TargetSemantics plan false .physical extraControl heapFuel baseline ∧
        TargetSemantics plan target.selection.reused .physical extraControl heapFuel selected ∧
        TargetSemantics plan target.selection.reused .logical extraControl heapFuel logical ∧
        Target.CostLaws plan baseline.store selected.store target.selection.reused

theorem backendSemantics {plan : Plan} {limits : IxIR2.Validate.Limits}
    (backend : Backend plan limits) : BackendSemantics backend := by
  cases backend with
  | ownedOnly _ => trivial
  | translated target =>
      intro extraControl heapFuel
      obtain ⟨baseline, base⟩ := targetSemantics plan false .physical extraControl heapFuel
      obtain ⟨selected, physical⟩ := targetSemantics plan target.selection.reused .physical extraControl heapFuel
      obtain ⟨logical, semantic⟩ := targetSemantics plan target.selection.reused .logical extraControl heapFuel
      exact ⟨baseline, selected, logical, base, physical, semantic, Target.costLaws base.2.1 physical.2.1⟩

structure SourceResult {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    (value : Ixon.Eval.Value) : Prop where
  related : @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.source.erasure.result.raw }
    value compilation.plan.value compilation.source.memberScope
  owned : OwnedSemantics compilation.plan
  backend : BackendSemantics compilation.backend

/-- Source-to-heap refinement, complete reclamation, and comparative static
reuse laws from the actual compiler certificate. Optional target failure
retains the proved consuming execution. No heap, liveness, shape, ownership,
or cost hypothesis is added to the established source contract. -/
theorem Compilation.sourceRefinesWithCostLaws
    {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel entry.frame []
      entry.source = .ok sourceValue) : SourceResult compilation sourceValue :=
  ⟨compilation.lowered.checked.sourceValue horacles hctx hsource,
    ownedSemantics compilation.plan, backendSemantics compilation.backend⟩

end Ix.Compiler.UniqueReuse
