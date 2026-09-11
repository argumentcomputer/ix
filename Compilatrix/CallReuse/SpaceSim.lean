import Compilatrix.CallReuse.MapSim
import Compilatrix.IxIR2.SpaceExecution

/-! The finite-storage runner uses the actual source compiler's selected
physical map. Profiling checks representability once; sufficient independent
capacities preserve its source value and full shared-result reclamation. -/

namespace Compilatrix.CallReuse.MapLowered

open Compilatrix.IxIR2.Eval

variable {declarations : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
  {recovery : IxIR0.MapRecovery.Recovered declarations main} {fuel : Nat}

def spaceContext (lowered : MapLowered recovery fuel) : Context :=
  Context.ofProgram lowered.reuse.target lowered.attached.target.artifact.validationContext.schemas

theorem finite_refines (lowered : MapLowered recovery fuel)
    {sourceFuel controlFuel heapFuel : Nat} {sourceValue : IxIR0.Value}
    (sourceRun : IxIR0.eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main = .ok sourceValue)
    {layout : Space.Layout} {observed : Space.Profile}
    (profiled : Space.profile layout lowered.reuse.policy lowered.spaceContext controlFuel
      (initialMachine lowered.reuse.target.main #[] heapFuel) = .ok observed)
    (capacity : Space.Capacity) (sufficient : observed.demand.within capacity = true) :
    Space.run layout capacity lowered.reuse.policy lowered.spaceContext controlFuel
        (initialMachine lowered.reuse.target.main #[] heapFuel) = .ok observed ∧
      lowered.PhysicalValueRel sourceValue observed.result ∧ observed.result.SharedResources := by
  have ran := Space.execute_erases profiled
  have entry := lowered.reuse.mainEntry lowered.attached.target.artifact.mainArity
    lowered.attached.target.artifact.mainNonempty
  rw [← Policy.runMain_eq_runMachine entry.1 entry.2] at ran
  obtain ⟨witnessControl, witnessHeap, witness, sourceExecution, related, resources, _⟩ :=
    lowered.physicalMainCostLaws sourceRun
  obtain ⟨stores, values⟩ := Policy.runMain_success_unique entry.1 entry.2 sourceExecution ran
  refine ⟨Space.profile_sufficient profiled sufficient, ?_, ?_⟩
  · simpa only [PhysicalValueRel, stores, values] using related
  · simpa only [Result.SharedResources, stores, values] using resources

end Compilatrix.CallReuse.MapLowered

namespace Compilatrix.CallReuse.MapCompilation

open Compilatrix.IxIR2.Eval

/-- Original Ixon source contracts compose with checked map recovery,
ordinary ownership lowering, selected suspended calls and finite storage. -/
theorem finite_refines {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
    {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}
    (compilation : MapCompilation constants root config eraseFuel lowerFuel)
    {recovery : IxIR0.MapRecovery.Recovered compilation.source.erasure.result.raw (.ref root)}
    (lowered : MapLowered recovery lowerFuel)
    (selected : compilation.outcome = .recovered recovery lowered)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (oracles : @Compilatrix.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (contextWF : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (sourceRun : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue)
    {layout : Space.Layout} {observed : Space.Profile} {controlFuel heapFuel : Nat}
    (profiled : Space.profile layout lowered.reuse.policy lowered.spaceContext controlFuel
      (initialMachine lowered.reuse.target.main #[] heapFuel) = .ok observed)
    (capacity : Space.Capacity) (sufficient : observed.demand.within capacity = true) :
    Space.run layout capacity lowered.reuse.policy lowered.spaceContext controlFuel
        (initialMachine lowered.reuse.target.main #[] heapFuel) = .ok observed ∧
      ∃ rawValue, compilation.SourceValueRel sourceValue rawValue ∧
        lowered.PhysicalValueRel rawValue observed.result ∧ observed.result.SharedResources := by
  obtain ⟨rawFuel, rawValue, rawRun, related⟩ := compilation.sourceRefines oracles contextWF sourceRun
  rw [selected] at rawRun
  obtain ⟨ran, physical, resources⟩ := lowered.finite_refines rawRun profiled capacity sufficient
  exact ⟨ran, rawValue, related, physical, resources⟩

end Compilatrix.CallReuse.MapCompilation

namespace Compilatrix.IxIR2.Eval.Space

/-- Reclamation releases ownership but retains the append-only backing arena. -/
theorem release_committedBytes (layout : Layout) {fuel remaining : Nat}
    {store released : Store} {value : RVal}
    (release : releaseShared fuel store value = .ok (released, remaining)) :
    layout.committedBytes released = layout.committedBytes store := by
  have slots := (releaseShared_slotGrowth release).2
  have allocs := (releaseShared_allocationCounters release).1
  rw [allocs] at slots
  have equal : released.slots = store.slots := by omega
  simp only [Layout.committedBytes, equal]

end Compilatrix.IxIR2.Eval.Space
