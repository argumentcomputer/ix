import Ix.Compiler.UniqueReuse.Native
import Ix.Compiler.UniqueReuse.PipelineSim
import Ix.Compiler.X86.UniqueResult

/-! Source refinement for the actual checked native selection. The source
contract is unchanged; the native conclusion constructs its heap from a fresh
arena and proves both calls, the value graph, resource agreement, and complete
reclamation. No caller-supplied list, ownership, or cost premise is required. -/

namespace Ix.Compiler.UniqueReuse.Native

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.X86
open Ix.Compiler.X86.UniqueABI
open Ix.Compiler.X86.UniqueExecution

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

/-- The full source constructor identities interpret the selected ABI tags. -/
def ValueRel (schema : IxIR0.UniqueReverse.Schema) (memory : Memory) (value : IxIR0.Value) (root : Word) : Prop :=
  ∃ values nodes, value = IxIR0.UniqueReverse.listValue schema values ∧ NativeList memory values root nodes

structure Execution {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (layout : Layout) (registers : Registers) (outside : Memory) (runtime : Runtime)
    (returned : State) (returnedMemory : Memory) (reclaimed : State) (reclaimedMemory : Memory) : Prop where
  returnedResult : UniqueExecution.LoopResult layout output.words.reverse (mainCounts output.words.length)
    ⟨registers, initialWords layout⟩ returned
  returnedView : Realizes layout outside returned.words returnedMemory
  value : ValueRel compilation.plan.schema returnedMemory compilation.plan.value (returned.registers .rax)
  graph : NativeList returnedMemory compilation.plan.values.reverse (returned.registers .rax)
    (chainNodes layout 1 output.words.length)
  mainRun : runFrom runtime output.main (UniqueTarget.controlCost output.words)
    ⟨registers, initialMemory layout outside⟩ = haltedLeaf (returned.core returnedMemory) 4 13
  reclaimedResult : Reclaimed layout output.words.length ⟨registers, initialWords layout⟩ reclaimed
  reclaimedView : Realizes layout outside reclaimed.words reclaimedMemory
  releaseRun : runFrom runtime output.release (UniqueTarget.releaseCost output.words.length)
    (returned.core returnedMemory) = haltedLeaf (reclaimed.core reclaimedMemory) 2 13

theorem Execution.mainSafe {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    {output : Output compilation} {layout : Layout} {registers : Registers} {outside : Memory} {runtime : Runtime}
    {returned reclaimed : State} {returnedMemory reclaimedMemory : Memory}
    (execution : Execution output layout registers outside runtime returned returnedMemory reclaimed reclaimedMemory)
    (count : Nat) (bound : count ≤ UniqueTarget.controlCost output.words) (fault : Trap) :
    (runFrom runtime output.main count ⟨registers, initialMemory layout outside⟩).status ≠ .trapped fault :=
  run_prefix_not_trapped execution.mainRun rfl count bound fault

theorem Execution.releaseSafe {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    {output : Output compilation} {layout : Layout} {registers : Registers} {outside : Memory} {runtime : Runtime}
    {returned reclaimed : State} {returnedMemory reclaimedMemory : Memory}
    (execution : Execution output layout registers outside runtime returned returnedMemory reclaimed reclaimedMemory)
    (count : Nat) (bound : count ≤ UniqueTarget.releaseCost output.words.length) (fault : Trap) :
    (runFrom runtime output.release count (returned.core returnedMemory)).status ≠ .trapped fault :=
  run_prefix_not_trapped execution.releaseRun rfl count bound fault

theorem Output.executes {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (layout : Layout) (registers : Registers)
    (capacity : output.words.length + 2 ≤ layout.capacity) (context : registers .rdi = layout.base)
    (outside : Memory) (runtime : Runtime) :
    ∃ returned returnedMemory reclaimed reclaimedMemory,
      Execution output layout registers outside runtime returned returnedMemory reclaimed reclaimedMemory := by
  obtain ⟨returned, returnedMemory, reclaimed, reclaimedMemory, result, returnedView, graph, mainRun,
    reclaimedResult, reclaimedView, releaseRun⟩ := mainAndRelease layout output.words registers capacity context
      outside runtime output.main output.release output.mainProduced output.releaseProduced
  rw [output.valuesExact, ← result.result] at graph
  exact ⟨returned, returnedMemory, reclaimed, reclaimedMemory, result, returnedView,
    ⟨compilation.plan.values.reverse, _, rfl, graph⟩, graph, mainRun, reclaimedResult, reclaimedView, releaseRun⟩

def targetCounts (store : IxIR2.Eval.Store) : Counts :=
  { allocs := store.heap.allocs
    frees := store.heap.frees
    reuses := store.heap.reuses
    live := store.live
    peak := store.peakLiveNodes
    payload := store.reusedPayloadUnits }

/-- Resource observations agree with the physical, statically reused IxIR₂
execution selected by the same compilation certificate. -/
theorem Output.costsAgree {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) {layout : Layout} {before after : State}
    (native : UniqueExecution.LoopResult layout output.words.reverse (mainCounts output.words.length) before after)
    {store : IxIR2.Eval.Store} {value : IxIR1.RVal}
    (target : Target.MainResult compilation.plan true .physical store value) :
    CountsAt layout (targetCounts store) after.words := by
  have equal : targetCounts store = mainCounts output.words.length := by
    simp [targetCounts, target.allocs, target.frees, target.reuses, target.live, target.peak, target.payload,
      Target.freshPerCons, Target.reusesPerCons, Target.inPlace, output.sourceLength, mainCounts]
  rw [equal]
  exact native.countsAt

/-- A concrete witness needs no additional native-memory hypothesis. General
clients can instead use `executes` with any valid arena base and larger capacity. -/
def Output.canonicalLayout {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) : Layout :=
  { base := 0x1000
    capacity := output.words.length + 2
    capacityBound := Nat.add_le_add_right output.lengthBound 2
    aligned := by decide
    nonzero := by decide
    fits := by
      have bound := output.lengthBound
      change output.words.length ≤ 64 at bound
      change 4096 + 80 + 32 * (output.words.length + 2) ≤ 18446744073709551616
      omega }

structure SourceNativeResult {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (sourceValue : Ixon.Eval.Value) : Prop where
  source : SourceResult compilation sourceValue
  native : ∀ (layout : Layout) (registers : Registers), output.words.length + 2 ≤ layout.capacity → registers .rdi = layout.base →
    ∀ (outside : Memory) (runtime : Runtime), ∃ returned returnedMemory reclaimed reclaimedMemory,
      Execution output layout registers outside runtime returned returnedMemory reclaimed reclaimedMemory

theorem Output.sourceRefines {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel entry.frame []
      entry.source = .ok sourceValue) : SourceNativeResult output sourceValue :=
  ⟨compilation.sourceRefinesWithCostLaws horacles hctx hsource, output.executes⟩

theorem SourceNativeResult.witness {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    {output : Output compilation} {sourceValue : Ixon.Eval.Value} (result : SourceNativeResult output sourceValue) :
    ∃ returned returnedMemory reclaimed reclaimedMemory,
      Execution output output.canonicalLayout (Registers.zero.set .rdi output.canonicalLayout.base)
        Memory.unmapped Runtime.rejecting returned returnedMemory reclaimed reclaimedMemory :=
  result.native output.canonicalLayout _ (Nat.le_refl _) (by simp) Memory.unmapped Runtime.rejecting

end Ix.Compiler.UniqueReuse.Native
