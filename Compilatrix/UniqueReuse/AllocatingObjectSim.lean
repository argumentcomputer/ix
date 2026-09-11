import Compilatrix.UniqueReuse.AllocatingNative
import Compilatrix.UniqueReuse.RuntimeObjectSim
import Compilatrix.X86.AllocatingExecution
import Compilatrix.X86.SafeStepsObject

namespace Compilatrix.X86.Allocating
open UniqueABI UniqueExecution

theorem Stack.return_preserved {layout : Layout} (stack : Stack layout) {values : List Word}
    {beforeWords afterWords : Words} {outside memory afterMemory : Memory} {returnAddress : Word}
    (first : Realizes layout outside beforeWords memory)
    (last : Realizes layout (afterOutside layout stack values outside) afterWords afterMemory)
    (permissions : afterMemory.readable = memory.readable)
    (caller : memory.read64? stack.top = .ok returnAddress) :
    afterMemory.read64? stack.top = .ok returnAddress := by
  let value := if values.isEmpty then token 26 0 else token 27 10
  have written := first.writeOutside stack.slot value (fun _ bound => stack.outside (by decide : 0 < 3) bound)
  have bytes := written.readOutside last stack.top (fun _ bound => stack.outside (by decide : 2 < 3) bound)
  have unchanged : (memory.write64 stack.slot value).read64 stack.top = memory.read64 stack.top := by
    apply Memory.readLittle_congr
    intro offset bound
    apply Memory.write64_bytes_outside
    intro other otherBound
    exact stack.distinct (by decide : 2 < 3) (by decide : 0 < 3) (by decide) bound otherBound
  have bytes : afterMemory.read64 stack.top = memory.read64 stack.top := bytes.trans unchanged
  change (if Memory.rangeAllowed afterMemory.readable stack.top 8 then Except.ok (afterMemory.read64 stack.top)
    else Except.error (⟨.read, stack.top, 8⟩ : MemoryFault)) = Except.ok returnAddress
  rw [permissions, bytes]
  exact caller

theorem Stack.byteView {layout : Layout} (stack : Stack layout) {outside logical physical : Memory} {words : Words}
    (view : Realizes layout outside words logical)
    (related : Stream.MemoryRelated stack.holes logical physical) : Realizes layout physical words physical := by
  refine ⟨?_, ?_, ?_, fun _ _ => rfl⟩
  · intro slot bound
    change physical.read .w64 (layout.address slot) = words slot
    rw [← related.read .w64 _ ((stack.heapAccess [] (by simp)).reads slot bound)]
    exact view.view slot bound
  · simpa only [← related.readable] using view.readable
  · simpa only [← related.writable] using view.writable

theorem returned_core {program : Program} {base : Word} {holes : Stream.Holes}
    {state : State} {memory : Memory} {physical : Core}
    (related : Stream.CoreRelated program base holes []
      ((state.core memory).setReg .rsp (state.registers .rsp + 8)) physical) :
    state.core physical.memory = physical.setReg .rsp (state.registers .rsp) := by
  change Core.mk state.registers physical.memory = Core.mk (physical.registers.set .rsp (state.registers .rsp)) physical.memory
  apply congrArg (fun registers => Core.mk registers physical.memory)
  funext register
  rw [← related.registers]
  cases register <;> simp [State.core, Core.setReg, Registers.set]

end Compilatrix.X86.Allocating

namespace Compilatrix.UniqueReuse.Runtime.AllocatingNative
open Compilatrix.X86 Compilatrix.X86.UniqueABI Compilatrix.X86.UniqueExecution Compilatrix.X86.UniqueTarget

structure ByteExecution (main release : Object) (layout : Layout) (values : List Word) (before : State)
    (memory outside : Memory) (stack : Allocating.Stack layout) (base returnAddress : Word) (flags : ByteEval.Flags)
    (returned reclaimed : State) (returnedMemory reclaimedMemory : Memory)
    (mainCount releaseCount : Nat) (byteReturned byteReclaimed : ByteEval.State) : Prop where
  returnedResult : LoopResult layout values.reverse (mainCounts values.length) before returned
  returnedView : Realizes layout (Allocating.afterOutside layout stack values outside) returned.words returnedMemory
  mainSafe : Stream.SafeSteps X86.Runtime.rejecting (Allocating.checked main.foldCounters)
    (Allocating.controlCost values.length main.foldCounters) (fun _ => False) (leaf (before.core memory) 0 0)
    stack.holes (haltedLeaf (returned.core returnedMemory) 4 13)
  mainPositive : 0 < mainCount
  mainBound : mainCount ≤ 3 * Allocating.controlCost values.length main.foldCounters
  mainRun : ObjectEval.run main.bytes Native.Role.main.symbol base mainCount (before.core memory) flags = .ok byteReturned
  mainReturn : byteReturned.rip = returnAddress
  mainRelated : Stream.CoreRelated (Allocating.checked main.foldCounters).program base stack.holes []
    ((returned.core returnedMemory).setReg .rsp (returned.registers .rsp + 8)) byteReturned.core
  graph : NativeList byteReturned.core.memory ((values.map UInt64.toNat).reverse) (byteReturned.core.readReg .rax)
    (chainNodes layout 1 values.length)
  reclaimedResult : Reclaimed layout values.length before reclaimed
  reclaimedView : Realizes layout byteReturned.core.memory reclaimed.words reclaimedMemory
  releasePositive : 0 < releaseCount
  releaseBound : releaseCount ≤ 3 * releaseCost values.length
  releaseRun : ObjectEval.run release.bytes Native.Role.release.symbol base releaseCount
    (byteReturned.core.setReg .rsp stack.top) byteReturned.flags = .ok byteReclaimed
  releaseReturn : Stream.Returned (reclaimed.core reclaimedMemory) returnAddress byteReclaimed
  releasedMemory : byteReclaimed.core.memory = reclaimedMemory
  releasedValue : byteReclaimed.core.readReg .rax = 0

set_option maxHeartbeats 800000 in
/-- The real ELF call returns an owned native graph. The separate release
entry runs on that exact byte-memory result after the caller restores RSP. -/
theorem byte_execution (layout : Layout) (values : List Word) (before : State)
    (input : RuntimeExecution.Input layout values before) (capacity : values.length + 2 ≤ layout.capacity)
    (stack : Allocating.Stack layout) (pointer : before.registers .rsp = stack.top)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (available : stack.Available memory) (returnAddress : Word) (caller : memory.read64? stack.top = .ok returnAddress)
    (main release : Object) (mainRole : main.role = .main) (releaseRole : release.role = .release)
    (base : Word) (flags : ByteEval.Flags) :
    ∃ returned reclaimed returnedMemory reclaimedMemory mainCount releaseCount byteReturned byteReclaimed,
      ByteExecution main release layout values before memory outside stack base returnAddress flags
        returned reclaimed returnedMemory reclaimedMemory mainCount releaseCount byteReturned byteReclaimed := by
  obtain ⟨returned, returnedMemory, result, view, steps⟩ := Allocating.mainSteps layout values before input capacity
    stack pointer outside memory represented available main.foldCounters
  have returnedPointer : returned.registers .rsp = stack.top := (result.saved .rsp rfl).trans pointer
  have mainRead := stack.return_preserved represented view steps.steps.rejecting_permissions.1 caller
  have mainStream : Stream.Valid (Allocating.checked main.foldCounters).program main.encoded :=
    by simpa [mainRole, roleChecked] using main.streamValid
  have mainObject : ELF.Valid (ELF.Input.mk main.encoded (Allocating.checked main.foldCounters).program.entry
      Native.Role.main.symbol main.provenance) main.bytes := by simpa [mainRole, roleChecked] using main.objectValid
  obtain ⟨mainCount, byteReturned, positive, bound, ran, returnedPC, related⟩ :=
    ObjectEval.run_safeSteps mainStream mainObject rfl base (before.core memory) flags steps rfl
      (by
        change returnedMemory.read64? (returned.registers .rsp) = .ok returnAddress
        rw [returnedPointer]
        exact mainRead)
  change Stream.CoreRelated _ _ _ []
    ((returned.core returnedMemory).setReg .rsp (returned.registers .rsp + 8)) byteReturned.core at related
  have byteView := stack.byteView view related.memory
  have graph := result.chain.native byteView (by simp; omega)
  have byteRead : byteReturned.core.memory.read64? stack.top = .ok returnAddress := by
    change byteReturned.core.memory.read? .w64 stack.top = .ok returnAddress
    rw [← related.memory.read? .w64 stack.top stack.returnClean]
    exact mainRead
  obtain ⟨reclaimed, reclaimedMemory, released, reclaimedView, releaseSteps⟩ := releaseSteps layout values.reverse 1
    (mainCounts values.length) returned result.chain result.countsAt result.root result.context
    (by simp; omega) (by simp [mainCounts]) byteReturned.core.memory byteReturned.core.memory byteView
    X86.Runtime.rejecting RuntimeTarget.releaseChecked rfl
  have reclaimResult : Reclaimed layout values.length before reclaimed := by
    refine ⟨by simpa using released.countsAt, ?_, released.result, result.saved.trans released.saved⟩
    intro index bound
    by_cases zero : index = 0
    · subst index
      exact result.freedNil.mono (fun field fieldBound => released.frame 0 (Or.inl (by decide)) field fieldBound)
    · exact released.freed index (by omega) (by simp; omega)
  have releaseRead : reclaimedMemory.read64? (reclaimed.registers .rsp) = .ok returnAddress := by
    rw [reclaimResult.saved .rsp rfl, pointer]
    exact Native.caller_read_preserved ⟨(fun _ bound => stack.outside (by decide : 2 < 3) bound), byteRead⟩ byteView reclaimedView
      releaseSteps.rejecting_permissions.1
  have releaseStream : Stream.Valid RuntimeTarget.releaseChecked.program release.encoded :=
    by simpa [releaseRole, roleChecked] using release.streamValid
  have releaseObject : ELF.Valid (ELF.Input.mk release.encoded RuntimeTarget.releaseChecked.program.entry
      Native.Role.release.symbol release.provenance) release.bytes := by simpa [releaseRole, roleChecked] using release.objectValid
  obtain ⟨releaseCount, byteReclaimed, releasePositive, releaseBound, releaseRan, releaseReturned⟩ :=
    ObjectEval.run_from_typed releaseStream releaseObject rfl (Native.role_callFree .release)
      X86.Runtime.rejecting base (releaseCost values.length) (returned.core byteReturned.core.memory) byteReturned.flags
      (by simpa [runFrom, Machine.initial, leaf, show RuntimeTarget.releaseChecked.program.entry = 0 from rfl]
        using releaseSteps.run_eq) rfl releaseRead
  refine ⟨returned, _, returnedMemory, reclaimedMemory, mainCount, releaseCount, byteReturned, byteReclaimed,
    result, view, steps, positive, bound, ran, returnedPC, related, ?_, reclaimResult, reclaimedView,
    releasePositive, releaseBound, ?_, releaseReturned, ?_, ?_⟩
  · rw [← related.readReg .rax]
    simpa [Core.setReg, Core.readReg, State.core, result.result] using graph
  · rw [Allocating.returned_core related, returnedPointer] at releaseRan
    exact releaseRan
  · rw [releaseReturned.1]
    rfl
  · rw [releaseReturned.1]
    simpa [Core.setReg, Core.readReg, State.core, haltedLeaf, leaf] using reclaimResult.result

end Compilatrix.UniqueReuse.Runtime.AllocatingNative
