import Compilatrix.UniqueReuse.AllocatingSourceSim

namespace Compilatrix.X86.Stream

theorem MemoryRelated.empty_eq {logical physical : Memory}
    (related : MemoryRelated (fun _ => False) logical physical) : logical = physical := by
  cases logical
  cases physical
  simp only [Memory.mk.injEq]
  exact ⟨funext (fun address => related.bytes address id), related.readable, related.writable⟩

end Compilatrix.X86.Stream

namespace Compilatrix.UniqueReuse.Runtime.AllocatingNative
open Compilatrix.X86 Compilatrix.X86.UniqueABI Compilatrix.X86.UniqueExecution Compilatrix.X86.UniqueTarget

/-- Every outside byte except the helper's eight-byte return slot is exact,
both when the main object returns and after release of its actual result. -/
theorem ByteExecution.frame {main release : Object} {layout : Layout} {values : List Word} {before : State}
    {memory outside : Memory} {stack : Allocating.Stack layout} {base returnAddress : Word} {flags : ByteEval.Flags}
    {returned reclaimed : State} {returnedMemory reclaimedMemory : Memory} {mainCount releaseCount : Nat}
    {byteReturned byteReclaimed : ByteEval.State}
    (execution : ByteExecution main release layout values before memory outside stack base returnAddress flags
      returned reclaimed returnedMemory reclaimedMemory mainCount releaseCount byteReturned byteReclaimed)
    (initial : Realizes layout outside before.words memory) (address : Word)
    (outsideHeap : layout.allowed address = false) (outsideCall : ¬stack.holes address) :
    byteReturned.core.memory.bytes address = memory.bytes address ∧
      byteReclaimed.core.memory.bytes address = memory.bytes address := by
  have first : byteReturned.core.memory.bytes address = memory.bytes address := by
    rw [← execution.mainRelated.memory.bytes address outsideCall]
    change returnedMemory.bytes address = memory.bytes address
    rw [execution.returnedView.frame address outsideHeap]
    rw [Allocating.afterOutside, Memory.write64_bytes_outside]
    · exact (initial.frame address outsideHeap).symm
    · intro offset bound equal
      exact outsideCall (Or.inr ⟨offset, bound, equal⟩)
  exact ⟨first, by rw [execution.releasedMemory, execution.reclaimedView.frame address outsideHeap]; exact first⟩

/-- Insufficient arena bytes reject at the exported ELF entry before any
heap or stack write. The proof derives E2 safety for the rejection path. -/
theorem Object.capacityRejects (object : Object) (role : object.role = .main)
    (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (insufficient : layout.bytes < requiredBytes length)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (base returnAddress : Word) (flags : ByteEval.Flags)
    (caller : memory.read64? (state.registers .rsp) = .ok returnAddress) :
    ∃ count finalState, 0 < count ∧ count ≤ 45 ∧
      ObjectEval.run object.bytes Native.Role.main.symbol base count (state.core memory) flags = .ok finalState ∧
      finalState.rip = returnAddress ∧ finalState.core.memory = memory ∧ finalState.core.readReg .rax = 0 ∧
      finalState.core.readReg .rsp = state.registers .rsp + 8 := by
  have short : layout.capacity < length + 2 := by have := layout.enough_bytes_iff length; omega
  have rejected := RuntimeExecution.capacityRejectedSteps (foldCounters := object.foldCounters) (callAllocator := true)
    layout length state bounded short counts context argument outside memory represented X86.Runtime.rejecting
  have stream : Stream.Valid (Allocating.checked object.foldCounters).program object.encoded :=
    by simpa [role, roleChecked] using object.streamValid
  have valid : ELF.Valid (ELF.Input.mk object.encoded (Allocating.checked object.foldCounters).program.entry
      Native.Role.main.symbol object.provenance) object.bytes := by simpa [role, roleChecked] using object.objectValid
  obtain ⟨count, finalState, positive, bound, ran, pc, related⟩ :=
    ObjectEval.run_safeSteps stream valid rfl base (state.core memory) flags rejected.1 rfl
      (by
        change memory.read64? ((RuntimeExecution.capacityRejectedState state).registers .rsp) = .ok returnAddress
        rw [rejected.2 .rsp rfl]
        exact caller)
  refine ⟨count, finalState, positive, bound, ran, pc, related.memory.empty_eq.symm, ?_, ?_⟩
  · rw [← related.readReg .rax]
    rfl
  · rw [← related.readReg .rsp]
    change (RuntimeExecution.capacityRejectedState state).registers .rsp + 8 = _
    rw [rejected.2 .rsp rfl]

end Compilatrix.UniqueReuse.Runtime.AllocatingNative
