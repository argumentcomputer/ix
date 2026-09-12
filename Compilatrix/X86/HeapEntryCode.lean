import Compilatrix.X86.HeapEntryState

namespace Compilatrix.X86.HeapEntry
open WordRegion HeapArena

structure Code (checked : X86.Checked) (baseline : Bool) (target : BlockId) (demand : Nat) (plan : HeapTarget.EntryPlan) : Prop where
  capacity : BlockCode checked plan.entry [.load .w64 .rax (HeapArena.memory .rdx 1)]
    (.branch (HeapTarget.capacityCompare HeapArena.capacity) .unsignedGt plan.reject plan.lower)
  lower : BlockCode checked plan.lower [] (.branch (HeapTarget.capacityCompare demand) .unsignedLt plan.reject plan.adapter)
  adapter : BlockCode checked plan.adapter (HeapTarget.adapter baseline target) .ret
  reject : BlockCode checked plan.reject HeapTarget.rejectInstructions .ret

theorem code {checked : X86.Checked} {baseline : Bool} {target : BlockId} {demand : Nat} {plan : HeapTarget.EntryPlan}
    (matched : plan.matches checked.program baseline target demand = true) : Code checked baseline target demand plan := by
  simp only [HeapTarget.EntryPlan.matches, Bool.and_eq_true] at matched
  exact ⟨Scalar.blockMatches_code matched.1.1.1, Scalar.blockMatches_code matched.1.1.2,
    Scalar.blockMatches_code matched.1.2, Scalar.blockMatches_code matched.2⟩

theorem capacity_trace {workspace : Workspace} {state : State}
    (base : state.registers .rdx = workspace.layout.region.base) :
    SafeTrace workspace.layout.region [] [.load .w64 .rax (HeapArena.memory .rdx 1)] state (fun _ => False)
      (guarded state) (fun _ => False) :=
  SafeTrace.load workspace.layout.region [] state (fun _ => False) .rax (HeapArena.memory .rdx 1) 1
    (workspace.layout.header_bound (by decide))
    (by rw [HeapArena.memory_eval state .rdx (by decide), base]; rfl) (fun _ _ h => h)

theorem capacity_upper (state : State) (memory : Memory) (bound : (state.words 1).toNat ≤ capacity) :
    (HeapTarget.capacityCompare capacity).holds .unsignedGt ((guarded state).core memory) = false := by
  simp only [HeapTarget.capacityCompare, Compare.holds, Condition.holds, State.core, Core.readReg, guarded,
    State.setReg_registers, beq_self_eq_true, if_true, AluSource.eval, HeapArena.signed_nat (by decide : capacity < 2147483648), Straight.truncate_w64]
  apply decide_eq_false
  change ¬(UInt64.ofNat capacity).toNat < (state.words 1).toNat
  rw [UInt64.toNat_ofNat_of_lt' (by decide : capacity < UInt64.size)]
  omega

theorem capacity_lower (state : State) (memory : Memory) {demand : Nat}
    (small : demand ≤ capacity) (enough : demand ≤ (state.words 1).toNat) :
    (HeapTarget.capacityCompare demand).holds .unsignedLt ((guarded state).core memory) = false := by
  have immediate : demand < 2147483648 := by simp only [capacity] at small; omega
  simp only [HeapTarget.capacityCompare, Compare.holds, Condition.holds, State.core, Core.readReg, guarded,
    State.setReg_registers, beq_self_eq_true, if_true, AluSource.eval, HeapArena.signed_nat immediate, Straight.truncate_w64]
  apply decide_eq_false
  change ¬(state.words 1).toNat < (UInt64.ofNat demand).toNat
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [capacity, UInt64.size] at *; omega : demand < UInt64.size)]
  omega

theorem guard_steps {checked : X86.Checked} {baseline : Bool} {target : BlockId} {demand : Nat} {plan : HeapTarget.EntryPlan}
    (code : Code checked baseline target demand plan) (workspace : Workspace) (state : State) (outside memory : Memory)
    (represented : Realizes workspace.layout.region outside state.words memory)
    (base : state.registers .rdx = workspace.layout.region.base)
    (bound : (state.words 1).toNat ≤ capacity) (enough : demand ≤ (state.words 1).toNat) :
    ∃ nextMemory, Realizes workspace.layout.region outside (guarded state).words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting checked 3 (fun _ => False) (inFrame (state.core memory) plan.entry 0 [])
        (fun _ => False) (inFrame ((guarded state).core nextMemory) plan.adapter 0 []) := by
  obtain ⟨nextMemory, nextView, first⟩ := (capacity_trace base).branch outside memory represented checked plan.entry plan.reject plan.lower
    (HeapTarget.capacityCompare capacity) .unsignedGt code.capacity false (capacity_upper state Memory.unmapped bound) code.lower.hasBlock
  have second := code.lower.safe_branch Runtime.rejecting ((guarded state).core nextMemory) [] (fun _ => False) false
    (capacity_lower state nextMemory (by omega) enough) code.adapter.hasBlock
  exact ⟨nextMemory, nextView, by simpa only [List.length_cons, List.length_nil, Bool.false_eq_true, if_false] using first.append second⟩

end Compilatrix.X86.HeapEntry
