import Compilatrix.X86.PhysicalHeapObject

namespace Compilatrix.X86.HeapEntry
open WordRegion HeapArena

def rejected (state : State) : State := (state.setReg .rax 0).setReg .rdx 1

theorem reject_trace (workspace : Workspace) (state : State) :
    SafeTrace workspace.layout.region [] HeapTarget.rejectInstructions state (fun _ => False)
      (rejected state) (fun _ => False) :=
  (SafeTrace.mov workspace.layout.region [] state (fun _ => False) .rax (.imm 0)).append
    (SafeTrace.mov workspace.layout.region [] (state.setReg .rax 0) (fun _ => False) .rdx (.imm 1))

theorem capacity_tooLarge (state : State) (memory : Memory) (large : capacity < (state.words 1).toNat) :
    (HeapTarget.capacityCompare capacity).holds .unsignedGt ((guarded state).core memory) = true := by
  simp only [HeapTarget.capacityCompare, Compare.holds, Condition.holds, State.core, Core.readReg, guarded,
    State.setReg_registers, beq_self_eq_true, if_true, AluSource.eval,
    HeapArena.signed_nat (by decide : capacity < 2147483648), Straight.truncate_w64]
  apply decide_eq_true
  change (UInt64.ofNat capacity).toNat < (state.words 1).toNat
  rw [UInt64.toNat_ofNat_of_lt' (by decide : capacity < UInt64.size)]
  exact large

theorem capacity_tooSmall (state : State) (memory : Memory) {demand : Nat}
    (small : demand ≤ capacity) (short : (state.words 1).toNat < demand) :
    (HeapTarget.capacityCompare demand).holds .unsignedLt ((guarded state).core memory) = true := by
  have immediate : demand < 2147483648 := by simp only [capacity] at small; omega
  simp only [HeapTarget.capacityCompare, Compare.holds, Condition.holds, State.core, Core.readReg, guarded,
    State.setReg_registers, beq_self_eq_true, if_true, AluSource.eval, HeapArena.signed_nat immediate, Straight.truncate_w64]
  apply decide_eq_true
  change (state.words 1).toNat < (UInt64.ofNat demand).toNat
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [capacity, UInt64.size] at *; omega : demand < UInt64.size)]
  exact short

theorem reject_guard_steps {checked : X86.Checked} {baseline : Bool} {target : BlockId} {demand : Nat} {plan : HeapTarget.EntryPlan}
    (code : Code checked baseline target demand plan) (workspace : Workspace) (state : State) (outside memory : Memory)
    (represented : Realizes workspace.layout.region outside state.words memory)
    (base : state.registers .rdx = workspace.layout.region.base) (small : demand ≤ capacity)
    (invalid : (state.words 1).toNat < demand ∨ capacity < (state.words 1).toNat) :
    ∃ count nextMemory, Realizes workspace.layout.region outside (guarded state).words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting checked count (fun _ => False) (inFrame (state.core memory) plan.entry 0 [])
        (fun _ => False) (inFrame ((guarded state).core nextMemory) plan.reject 0 []) := by
  by_cases large : capacity < (state.words 1).toNat
  · obtain ⟨nextMemory, nextView, first⟩ := (capacity_trace base).branch outside memory represented checked plan.entry plan.reject plan.lower
      (HeapTarget.capacityCompare capacity) .unsignedGt code.capacity true (capacity_tooLarge state Memory.unmapped large) code.reject.hasBlock
    exact ⟨2, nextMemory, nextView, first⟩
  · obtain ⟨nextMemory, nextView, first⟩ := (capacity_trace base).branch outside memory represented checked plan.entry plan.reject plan.lower
      (HeapTarget.capacityCompare capacity) .unsignedGt code.capacity false (capacity_upper state Memory.unmapped (by omega)) code.lower.hasBlock
    have second := code.lower.safe_branch Runtime.rejecting ((guarded state).core nextMemory) [] (fun _ => False) true
      (capacity_tooSmall state nextMemory small (by omega)) code.reject.hasBlock
    exact ⟨3, nextMemory, nextView, first.append second⟩

/-- Capacity rejection reaches RET before the adapter writes any workspace
word. The caller receives RAX=0, RDX=1 and its original saved registers. -/
theorem root_reject {checked : X86.Checked} {baseline : Bool} {target : BlockId} {demand : Nat} {entry : HeapTarget.EntryPlan}
    (code : Code checked baseline target demand entry) (entryAt : checked.program.entry = entry.entry)
    (workspace : Workspace) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (base : core.readReg .rdx = workspace.layout.region.base) (small : demand ≤ capacity)
    (invalid : (core.memory.read64 (workspace.layout.region.address 1)).toNat < demand ∨
      capacity < (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true) :
    Nonempty (RootRun checked core workspace 0 1 (stateOf workspace core).words) := by
  let before := stateOf workspace core
  have initialView : Realizes workspace.layout.region core.memory before.words core.memory :=
    realizes_initial _ _ readable writable
  obtain ⟨count, guardMemory, guardView, guardSteps⟩ := reject_guard_steps code workspace before core.memory core.memory initialView base small invalid
  obtain ⟨nextMemory, nextView, rejectedSteps⟩ := (reject_trace workspace (guarded before)).steps core.memory guardMemory guardView
    Runtime.rejecting checked entry.reject 0 code.reject.segment (by simpa using code.reject.fits)
  let after := rejected (guarded before)
  have stable : Scalar.Stable before after := by
    apply (Scalar.Stable.setReg before .rax _ (by simp)).trans
    exact (Scalar.Stable.setReg (guarded before) .rax 0 (by simp)).trans (Scalar.Stable.setReg _ .rdx 1 (by simp))
  have finalStack : after.registers .rsp = core.readReg .rsp := stable .rsp (by simp)
  have returned := code.reject.safe_leaf_ret (after.core nextMemory) (fun _ => False) (fun _ _ h => h)
  refine ⟨{
    count := count + 2 + 1, after := haltedLeaf (after.core nextMemory) entry.reject 2
    holes := fun _ => False, safe := fun _ h => h.elim, readable := fun _ _ _ _ h => h.elim
    represented := nextView, steps := ?_, halted := rfl, result := rfl, status := rfl
    stack := finalStack, saved := stable.snapshot core.memory nextMemory, returnSlot := ?_ }⟩
  · have initial : inFrame (before.core core.memory) entry.entry 0 [] = Machine.initial checked core := by
      simp [before, stateOf, Machine.initial, inFrame, State.core, entryAt]
    simpa only [initial, Nat.zero_add, HeapTarget.rejectInstructions, List.length_cons, List.length_nil] using
      (guardSteps.append rejectedSteps).append returned
  · change nextMemory.read64? (after.registers .rsp) = .ok (core.memory.read64 (core.readReg .rsp))
    rw [finalStack, stack]
    simp only [Memory.read64?, Memory.read?, Width.bytes, nextView.readable _ workspace.external_bound,
      ↓reduceIte, Except.ok.injEq]
    exact nextView.view workspace.externalTop workspace.external_bound

end Compilatrix.X86.HeapEntry

namespace Compilatrix.X86.PhysicalHeap
open HeapArena

theorem Compiled.rejectsCapacity {schemas program root baseline provenance}
    (compiled : Compiled schemas program root baseline provenance) (workspace : Workspace) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (arena : core.readReg .rdx = workspace.layout.region.base)
    (invalid : (core.memory.read64 (workspace.layout.region.address 1)).toNat < compiled.selected.entryInterface.allocations ∨
      capacity < (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true)
    (base : Word) (flags : ByteEval.Flags) :
    Nonempty (HeapEntry.ObjectResult compiled.object.bytes compiled.input.exportName base flags core workspace 0 1
      (HeapEntry.stateOf workspace core).words) := by
  have code := HeapEntry.code compiled.native.entryVerified
  obtain ⟨rejected⟩ := HeapEntry.root_reject code compiled.native.entryAt workspace core stack arena
    (by simpa [maxAllocations, capacity] using compiled.selected.allocationBound) invalid readable writable
  have stream : Stream.Valid compiled.native.target.program compiled.input.encoded := by
    rw [compiled.encoded]
    exact compiled.stream.valid
  exact rejected.object stream compiled.object.valid compiled.entry base flags

end Compilatrix.X86.PhysicalHeap
