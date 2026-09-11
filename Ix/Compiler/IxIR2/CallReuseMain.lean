import Ix.Compiler.IxIR2.CallReuseSimulation
import Ix.Compiler.IxIR2.CallEvalFuel

/-! Executable whole-main refinement for the actual v1 compiler output. -/

namespace Ix.Compiler.IxIR2.CallReuse

open Eval
open Sim

theorem Output.mainSimulation {limits : Validate.Limits} {validation : Validate.Context} {source : Program}
    (output : Output limits validation source) {controlFuel heapFuel : Nat} {baseline : Result}
    (arity : source.main.signature.params.size = 0) (nonempty : source.main.blocks.isEmpty = false)
    (run : Eval.runMain (Context.ofProgram source validation.schemas) .physical source
      controlFuel heapFuel = .ok baseline) :
    ∃ selectedControl selected mapping,
      Policy.runMain policy (Context.ofProgram output.target validation.schemas) .physical output.target
        selectedControl heapFuel = .ok selected ∧
      HeapMap baseline.store selected.store mapping ∧
      IxIR1.Sim.RValIso (MapRel mapping) baseline.value selected.value ∧
      baseline.heapRemaining ≤ selected.heapRemaining ∧
      baseline.store.allocationEvents = selected.store.allocationEvents ∧
      baseline.store.CostBounds selected.store := by
  have mainReady : functionReady source.main = true := by
    have ready := output.sourceReady
    simp only [programReady, Bool.and_eq_true] at ready
    exact ready.1
  rw [Eval.runMain_eq_runMachine arity nonempty] at run
  obtain ⟨count, _, steps⟩ := Eval.runMachine_steps run
  have initial := initialMachine_related (limits := limits) (validation := validation)
    (sourceContext := Context.ofProgram source validation.schemas) (heapFuel := heapFuel) mainReady arity
  obtain ⟨mapping, selectedCount, selectedFinal, targetSteps, related⟩ :=
    simulate_to_halt (ContextRel.ofProgram limits validation source)
      (programReady_context output.sourceReady) rfl initial steps ⟨baseline.value, rfl⟩
  rcases selectedFinal with ⟨selectedStore, selectedFuel, selectedControl⟩
  cases related.control with
  | halted values =>
      rename_i selectedValue
      let selected : Result :=
        { store := selectedStore, value := selectedValue, controlRemaining := 0, heapRemaining := selectedFuel }
      refine ⟨selectedCount, selected, mapping, ?_, related.transition.state.heap, values, related.fuel, ?_, ?_⟩
      · rw [Policy.runMain_eq_runMachine
          (show output.target.main.signature.params.size = 0 from arity)
          (rewriteFunction_nonempty nonempty)]
        have executed := targetSteps.runMachine (controlFuel := 0)
        simpa only [Nat.add_zero, Policy.runMachine, policy, Output.target, rewriteProgram, selected] using executed
      · have counted := related.transition.events
        change baseline.store.allocationEvents + 0 = selected.store.allocationEvents + 0 at counted
        simpa only [Nat.add_zero] using counted
      · exact related.transition.costs.preserves (Store.CostBounds.refl {})

theorem Selection.mainEntry {limits : Validate.Limits} {validation : Validate.Context}
    {source : Program} (selection : Selection limits validation source)
    (arity : source.main.signature.params.size = 0) (nonempty : source.main.blocks.isEmpty = false) :
    selection.target.main.signature.params.size = 0 ∧ selection.target.main.blocks.isEmpty = false := by
  cases selection with
  | optimized output produced => exact ⟨arity, rewriteFunction_nonempty nonempty⟩
  | baseline checked error rejected => exact ⟨arity, nonempty⟩

/-- The chosen policy executes the actual checked selection. At a closed
compiler endpoint the allocation-history map gives the existing semantic heap
relation, including fallback to the unchanged checked baseline. -/
theorem Selection.mainSimulation {limits : Validate.Limits} {validation : Validate.Context}
    {source : Program} (selection : Selection limits validation source)
    {controlFuel heapFuel : Nat} {baseline : Result}
    (arity : source.main.signature.params.size = 0) (nonempty : source.main.blocks.isEmpty = false)
    (run : Eval.runMain (Context.ofProgram source validation.schemas) .physical source
      controlFuel heapFuel = .ok baseline)
    (closed : IxIR1.Sim.StoreClosed baseline.store.heap)
    (live : IxIR1.Sim.LiveRVal baseline.store.heap baseline.value) :
    ∃ selectedControl selected locRel,
      Policy.runMain selection.policy (Context.ofProgram selection.target validation.schemas)
        .physical selection.target selectedControl heapFuel = .ok selected ∧
      ReuseSim.StableHeapRel baseline.store selected.store locRel ∧
      IxIR1.Sim.RValIso locRel baseline.value selected.value ∧
      baseline.heapRemaining ≤ selected.heapRemaining ∧
      baseline.store.allocationEvents = selected.store.allocationEvents ∧
      baseline.CostBounds selected := by
  cases selection with
  | optimized output produced =>
      obtain ⟨control, selected, mapping, executed, heaps, values, budget, events, costs⟩ :=
        output.mainSimulation arity nonempty run
      exact ⟨control, selected, LiveMapRel baseline.store mapping, executed,
        heaps.toStable closed, heaps.toHeapIso_value closed values live, budget, events, costs⟩
  | baseline checked error rejected =>
      exact ⟨controlFuel, baseline, Eq,
        by simpa only [Selection.policy, Selection.target, Policy.runMain_v0] using run,
        .contents ⟨rfl⟩,
        IxIR1.Sim.RValIso.refl _, Nat.le_refl _, rfl, Store.CostBounds.refl _⟩

end Ix.Compiler.IxIR2.CallReuse
