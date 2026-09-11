import Ix.Compiler.X86.RuntimeScan
import Ix.Compiler.X86.UniqueResult

/-! The complete runtime-input native call and its release. The input heap is
supplied through a bounded ownership relation; all execution conclusions use
the one checked program and the ordinary typed x86 byte-memory runner. -/

namespace Ix.Compiler.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution

variable {foldCounters : Bool}

theorem initializeInput (layout : Layout) (values : List Word) (state : State)
    (capacity : values.length + 2 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (root : state.registers .rdx = layout.cell values.length) (chain : DownChain layout state.words values)
    (counts : CountsAt layout (readyCounts (values.length + 1)) state.words) :
    ∃ after, Trace layout (allocate nilTag 0 (.imm 0) .rsi) state after ∧ Initialized layout values state after := by
  let after := allocateState state layout (values.length + 1) nilTag 0 (.imm 0) .rsi
  have allocation := allocateTrace layout state (values.length + 1) nilTag 0 (.imm 0) .rsi
    (by omega) context counts.cursor
  have words : after.words = allocatedWords state.words (values.length + 1) nilTag 0 0 := by
    simpa [after] using allocateState_words state layout (values.length + 1) nilTag 0 (.imm 0) .rsi rfl
  refine ⟨after, allocation, ?_, ?_, ?_, ?_, allocateState_destination state layout (values.length + 1) nilTag 0 (.imm 0) .rsi,
    ?_, allocateState_saved state layout (values.length + 1) nilTag 0 (.imm 0) .rsi rfl⟩
  · rw [words]
    apply chain.mono
    intro index bound field fieldBound
    exact allocatedWords_other state.words (by omega) fieldBound _ _ _
  · change CellAt after.words (values.length + 1) nilTag 0 0
    rw [words]
    exact allocatedWords_cell _ _ _ _ _
  · rw [words]
    simpa [Nat.add_assoc] using counts.allocate (values.length + 1) nilTag 0 0
  · exact (allocateState_other state layout (values.length + 1) nilTag 0 (.imm 0) .rsi .rdx
      (by decide) (by decide) (by decide) (by decide)).trans root
  · exact (allocateState_other state layout (values.length + 1) nilTag 0 (.imm 0) .rsi .rdi
      (by decide) (by decide) (by decide) (by decide)).trans context

theorem mainSteps (layout : Layout) (values : List Word) (state : State)
    (input : Input layout values state) (capacity : values.length + 2 ≤ layout.capacity)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    ∃ after nextMemory, LoopResult layout values.reverse (mainCounts values.length) state after ∧
      Realizes layout outside after.words nextMemory ∧
      Steps runtime (RuntimeTarget.checked foldCounters) (RuntimeTarget.controlCost values.length foldCounters) (leaf (state.core memory) 0 0)
        (haltedLeaf (after.core nextMemory) 4 13) := by
  obtain ⟨prepared, result, validation⟩ := validationSteps (foldCounters := foldCounters) layout values state input capacity outside memory represented runtime
  have preparedView : Realizes layout outside prepared.words memory := result.words.symm ▸ represented
  obtain ⟨initialized, allocation, initializedResult⟩ := initializeInput layout values prepared capacity result.context result.root
    (result.words.symm ▸ input.chain) (result.words.symm ▸ input.counts)
  obtain ⟨allocatedMemory, allocatedView, allocationSteps⟩ := allocation.jump outside memory preparedView runtime (RuntimeTarget.checked foldCounters) 2 3
    ⟨rfl, by decide⟩ (hasBlock 3 (by decide))
  have invariant : LoopInvariant layout values [] (readyCounts (values.length + 2)) initialized :=
    ⟨initializedResult.input, initializedResult.accumulator, initializedResult.counts, initializedResult.inputRoot,
      initializedResult.accRoot, initializedResult.context⟩
  obtain ⟨after, nextMemory, loopResult, finalView, loop⟩ := loopStepsFor layout values [] (readyCounts (values.length + 2))
    initialized invariant (by simpa using capacity) (by simp [readyCounts]) outside allocatedMemory allocatedView
    runtime (RuntimeTarget.checked foldCounters) (RuntimeTarget.loopInstructions foldCounters)
    (RuntimeTarget.loopCode foldCounters) (RuntimeTarget.loopTrace foldCounters layout)
  refine ⟨after, nextMemory, ?_, finalView, ?_⟩
  · have saved := (result.saved.trans initializedResult.saved).trans loopResult.saved
    simp only [List.append_nil, readyCounts_finish] at loopResult
    exact { loopResult with saved }
  · have all := validation.append (allocationSteps.append loop)
    have cost : RuntimeTarget.validationCost values.length +
        ((allocate nilTag 0 (.imm 0) .rsi).length + 1 +
          (((RuntimeTarget.loopInstructions foldCounters).length + 3) * values.length + 16)) =
        RuntimeTarget.controlCost values.length foldCounters := by
      cases foldCounters <;>
        simp [RuntimeTarget.validationCost, RuntimeTarget.controlCost, allocate_length,
          RuntimeTarget.loopInstructions, UniqueCounterFold.instructions, consInstructions,
          reserveCons, reuseCons, changeCounter] <;> omega
    rw [cost] at all
    exact all

theorem mainRuns (layout : Layout) (values : List Word) (state : State)
    (input : Input layout values state) (capacity : values.length + 2 ≤ layout.capacity)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    ∃ after nextMemory, LoopResult layout values.reverse (mainCounts values.length) state after ∧
      Realizes layout outside after.words nextMemory ∧
      runFrom runtime (RuntimeTarget.checked foldCounters) (RuntimeTarget.controlCost values.length foldCounters) (state.core memory) =
        haltedLeaf (after.core nextMemory) 4 13 := by
  obtain ⟨after, nextMemory, result, finalView, steps⟩ := mainSteps (foldCounters := foldCounters) layout values state input capacity outside memory represented runtime
  exact ⟨after, nextMemory, result, finalView, steps.run_eq⟩

structure Execution (layout : Layout) (values : List Word) (before : State) (memory outside : Memory) (runtime : Runtime)
    (returned : State) (returnedMemory : Memory) (reclaimed : State) (reclaimedMemory : Memory)
    (foldCounters : Bool := false) : Prop where
  returnedResult : LoopResult layout values.reverse (mainCounts values.length) before returned
  returnedView : Realizes layout outside returned.words returnedMemory
  graph : NativeList returnedMemory ((values.map UInt64.toNat).reverse) (returned.registers .rax)
    (chainNodes layout 1 values.length)
  mainRun : runFrom runtime (RuntimeTarget.checked foldCounters) (RuntimeTarget.controlCost values.length foldCounters) (before.core memory) =
    haltedLeaf (returned.core returnedMemory) 4 13
  reclaimedResult : Reclaimed layout values.length before reclaimed
  reclaimedView : Realizes layout outside reclaimed.words reclaimedMemory
  releaseRun : runFrom runtime RuntimeTarget.releaseChecked (releaseCost values.length) (returned.core returnedMemory) =
    haltedLeaf (reclaimed.core reclaimedMemory) 2 13

theorem executes (layout : Layout) (values : List Word) (state : State)
    (input : Input layout values state) (capacity : values.length + 2 ≤ layout.capacity)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    ∃ returned returnedMemory reclaimed reclaimedMemory,
      Execution layout values state memory outside runtime returned returnedMemory reclaimed reclaimedMemory foldCounters := by
  obtain ⟨returned, returnedMemory, result, returnedView, mainRun⟩ := mainRuns (foldCounters := foldCounters) layout values state input capacity outside memory represented runtime
  have graph := result.chain.native returnedView (by simp; omega)
  obtain ⟨reclaimed, reclaimedMemory, released, reclaimedView, releaseRun⟩ := releaseRuns layout values.reverse 1
    (mainCounts values.length) returned result.chain result.countsAt result.root result.context
    (by simp; omega) (by simp [mainCounts]) outside returnedMemory returnedView runtime RuntimeTarget.releaseChecked rfl
  refine ⟨returned, returnedMemory, reclaimed, reclaimedMemory, result, returnedView,
    by simpa [result.result] using graph, mainRun, ?_, reclaimedView, by simpa using releaseRun⟩
  refine ⟨by simpa using released.countsAt, ?_, released.result, result.saved.trans released.saved⟩
  intro index bound
  by_cases zero : index = 0
  · subst index
    apply result.freedNil.mono
    intro field fieldBound
    exact released.frame 0 (Or.inl (by decide)) field fieldBound
  · exact released.freed index (by omega) (by simp; omega)

theorem Execution.mainSafe {layout : Layout} {values : List Word} {before returned reclaimed : State}
    {memory outside returnedMemory reclaimedMemory : Memory} {runtime : Runtime}
    (execution : Execution layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory foldCounters)
    (count : Nat) (bound : count ≤ RuntimeTarget.controlCost values.length foldCounters) (fault : Trap) :
    (runFrom runtime (RuntimeTarget.checked foldCounters) count (before.core memory)).status ≠ .trapped fault :=
  run_prefix_not_trapped execution.mainRun rfl count bound fault

theorem Execution.releaseSafe {layout : Layout} {values : List Word} {before returned reclaimed : State}
    {memory outside returnedMemory reclaimedMemory : Memory} {runtime : Runtime}
    (execution : Execution layout values before memory outside runtime returned returnedMemory reclaimed reclaimedMemory foldCounters)
    (count : Nat) (bound : count ≤ releaseCost values.length) (fault : Trap) :
    (runFrom runtime RuntimeTarget.releaseChecked count (returned.core returnedMemory)).status ≠ .trapped fault :=
  run_prefix_not_trapped execution.releaseRun rfl count bound fault

end Ix.Compiler.X86.RuntimeExecution
