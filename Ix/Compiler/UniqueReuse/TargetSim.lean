import Ix.Compiler.UniqueReuse.TargetResources
import Ix.Compiler.UniqueReuse.LowerSim
import Ix.Compiler.UniqueReuse.SourceSim

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Plan)

/-- Successful executions at any source fuel have the compiler-derived
ownership and finite-list view, by determinism of the ordinary evaluator. -/
theorem consumingMainResult (plan : Plan) {fuel : Nat} {store : IxIR1.Store} {value : IxIR1.RVal}
    (run : IxIR1.runOwnedMain { decls := IxIR1.Env.ofList (declarations plan.schema) } .unique
      (mainCode plan) fuel = .ok (store, value)) : MainResult plan store value := by
  obtain ⟨canonicalFuel, canonicalStore, canonicalValue, canonicalRun, result⟩ := mainExists plan
  have left := IxIR1.runCode_mono (Nat.le_max_left fuel canonicalFuel) (runOwnedMain_ok run).1
  have right := IxIR1.runCode_mono (Nat.le_max_right fuel canonicalFuel) (runOwnedMain_ok canonicalRun).1
  have same : (store, value) = (canonicalStore, canonicalValue) := Except.ok.inj (left.symm.trans right)
  have hs := congrArg Prod.fst same
  have hv := congrArg Prod.snd same
  dsimp only at hs hv
  subst canonicalStore canonicalValue
  exact result

end Ix.Compiler.UniqueReuse

namespace Ix.Compiler.IxIR2.UniqueLower

open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Plan)
open Ix.Compiler.UniqueReuse

/-- The consuming translation preserves the exact finite value of every
successful run of its indexed IxIR₁ input. Ownership is obtained from that
compiler input, rather than required from the caller. -/
theorem Translation.forwardSimulation {source : Lower.Input} {plan : Plan} {limits : Validate.Limits}
    (translation : Translation source plan limits)
    {sourceFuel : Nat} {sourceStore : IxIR1.Store} {sourceValue : IxIR1.RVal}
    (run : IxIR1.runOwnedMain { decls := IxIR1.Env.ofList source.declarations }
      source.mainResult source.main sourceFuel = .ok (sourceStore, sourceValue))
    (mode : Eval.Interpretation) (extraControl heapFuel : Nat) (functions : FunctionRel) :
    ∃ result,
      Eval.runMain (Target.context plan false) mode (program plan false)
        (Target.controlCost plan false + extraControl) heapFuel = .ok result ∧
      ValueGraph functions sourceStore plan.value sourceValue ∧
      ValueGraph functions result.store.heap plan.value result.value ∧
      Target.MainResult plan false mode result.store result.value ∧
      result.controlRemaining = extraControl ∧ result.heapRemaining = heapFuel := by
  have sourceResult : MainResult plan sourceStore sourceValue := by
    rw [translation.sourceEq] at run
    exact consumingMainResult plan run
  obtain ⟨result, targetRun, targetResult, control, heap⟩ := Target.mainRuns plan false mode extraControl heapFuel
  exact ⟨result, targetRun, sourceResult.list.graph functions, targetResult.list.graph functions,
    targetResult, control, heap⟩

end Ix.Compiler.IxIR2.UniqueLower
