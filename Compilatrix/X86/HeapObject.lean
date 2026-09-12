import Compilatrix.X86.HeapAdapter
import Compilatrix.X86.ScalarObject

namespace Compilatrix.X86.HeapEntry
open WordRegion HeapArena

def stateOf (workspace : Workspace) (core : Core) : State :=
  ⟨core.registers, fun index => core.memory.read64 (workspace.layout.region.address index)⟩

structure RootRun (checked : X86.Checked) (core : Core) (workspace : Workspace) (value tag : Word) (words : Words) where
  count : Nat
  after : Machine
  holes : Stream.Holes
  safe : Scalar.HolesIn workspace.layout.region workspace.externalTop holes
  readable : HeapRuns.ReadableHeap workspace.layout holes
  represented : Realizes workspace.layout.region core.memory words after.core.memory
  steps : Stream.SafeSteps Runtime.rejecting checked count (fun _ => False) (Machine.initial checked core) holes after
  halted : after.status = .halted value
  result : after.core.readReg .rax = value
  status : after.core.readReg .rdx = tag
  stack : after.core.readReg .rsp = core.readReg .rsp
  saved : after.core.calleeSavedSnapshot = core.calleeSavedSnapshot
  returnSlot : after.core.memory.read64? (after.core.readReg .rsp) = .ok (core.memory.read64 (core.readReg .rsp))

theorem root_run {checked : X86.Checked} {baseline : Bool} {demand parameters : Nat} {entry : HeapTarget.EntryPlan}
    {callee : HeapTarget.FunctionPlan} {entries : Array BlockId} (code : Code checked baseline callee.entry demand entry)
    (calleeCode : HeapTarget.FunctionCode checked entries parameters callee) (entryAt : checked.program.entry = entry.entry)
    (workspace : Workspace) (core : Core) (after : State)
    (preserved : Scalar.Preserves workspace.frame 0
      (Scalar.enterState workspace.frame parameters (called baseline workspace entry (stateOf workspace core))) after)
    (body : HeapRuns.BodyContract checked callee.body callee.exit workspace.layout workspace.frame
      (Scalar.enterState workspace.frame parameters (called baseline workspace entry (stateOf workspace core))) after)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (base : core.readReg .rdx = workspace.layout.region.base)
    (enough : demand ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true) :
    Nonempty (RootRun checked core workspace (after.registers .rax) 0 after.words) := by
  let before := stateOf workspace core
  have initialView : Realizes workspace.layout.region core.memory before.words core.memory :=
    realizes_initial _ _ readable writable
  obtain ⟨guardMemory, guardView, guardSteps⟩ := guard_steps code workspace before core.memory core.memory initialView base bound enough
  obtain ⟨executed⟩ := adapter_steps code calleeCode workspace before after preserved body core.memory guardMemory guardView stack base
  have stable := completed_stable stack preserved
  have finalStack : (completed workspace after).registers .rsp = workspace.layout.region.address workspace.externalTop := by
    simp [completed]
  have returnReadable := executed.safe.readable workspace.external_bound (.inr (Nat.le_refl _))
  have retSteps := code.adapter.safe_leaf_ret ((completed workspace after).core executed.memory) executed.holes
    (by change Stream.ReadableData executed.holes ((completed workspace after).registers .rsp) 8; rw [finalStack]; exact returnReadable)
  refine ⟨{
    count := 3 + executed.count + 1
    after := haltedLeaf ((completed workspace after).core executed.memory) entry.adapter (HeapTarget.adapter baseline callee.entry).length
    holes := executed.holes, safe := executed.safe, readable := executed.readable, represented := executed.represented
    steps := ?_, halted := ?_, result := completed_value workspace after, status := completed_tag workspace after
    stack := stable .rsp (by simp), saved := stable.snapshot core.memory executed.memory, returnSlot := ?_ }⟩
  · have initial : inFrame (before.core core.memory) entry.entry 0 [] = Machine.initial checked core := by
      simp [before, stateOf, Machine.initial, inFrame, State.core, entryAt]
    simpa only [initial] using (guardSteps.append executed.steps).append retSteps
  · simp [haltedLeaf, State.core, Core.readReg]
  · change executed.memory.read64? ((completed workspace after).registers .rsp) = .ok (core.memory.read64 (core.readReg .rsp))
    rw [finalStack, stack]
    simp only [Memory.read64?, Memory.read?, Width.bytes, executed.represented.readable _ workspace.external_bound,
      ↓reduceIte, Except.ok.injEq]
    change executed.memory.read64 (workspace.layout.region.address workspace.externalTop) = _
    rw [executed.represented.view _ workspace.external_bound]
    have finalWords := (HeapRuns.finish_preserves workspace.frame parameters (called baseline workspace entry before) after
      (by simp [called, State.call]) preserved).2 workspace.externalTop (by simp only [Workspace.externalTop]; omega)
    exact finalWords.trans (called_external baseline workspace entry before)

theorem Output.entry_code {schemas program root baseline} {selected : PhysicalHeap.Selected schemas program root}
    (output : HeapTarget.Output selected baseline) {plan : HeapTarget.FunctionPlan} (found : output.plans[selected.entry]? = some plan) :
    Code output.target baseline plan.entry selected.entryInterface.allocations output.entry := by
  apply code
  simpa only [Array.getElem?_map, found, Option.map_some, Option.getD_some] using output.entryVerified

theorem Output.root_run {schemas program root baseline} {selected : PhysicalHeap.Selected schemas program root}
    (output : HeapTarget.Output selected baseline) {plan : HeapTarget.FunctionPlan} (found : output.plans[selected.entry]? = some plan)
    (workspace : Workspace) (core : Core) (after : State)
    (body : HeapRuns.Run workspace.layout output.plans output.parameters workspace.frame plan.body
      (Scalar.enterState workspace.frame (output.parameters[selected.entry]?.getD 0)
        (called baseline workspace output.entry (stateOf workspace core))) after)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (base : core.readReg .rdx = workspace.layout.region.base)
    (enough : selected.entryInterface.allocations ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true) :
    Nonempty (RootRun output.target core workspace (after.registers .rax) 0 after.words) := by
  have entryCode := Output.entry_code output found
  have functionCode := output.functions_code selected.entry plan found
  exact HeapEntry.root_run entryCode functionCode output.entryAt workspace core after (body.preserves workspace.separate)
    (body.native output.functions_code plan.exit functionCode.body functionCode.exit.hasBlock) stack base enough bound readable writable

structure ObjectResult (bytes : ByteArray) (exportName : String) (base : Word) (flags : ByteEval.Flags)
    (core : Core) (workspace : Workspace) (value tag : Word) (words : Words) where
  count : Nat
  finalState : ByteEval.State
  positive : 0 < count
  run : ObjectEval.run bytes exportName base count core flags = .ok finalState
  returned : finalState.rip = core.memory.read64 (core.readReg .rsp)
  result : finalState.core.readReg .rax = value
  status : finalState.core.readReg .rdx = tag
  stack : finalState.core.readReg .rsp = core.readReg .rsp + 8
  saved : finalState.core.calleeSavedSnapshot = core.calleeSavedSnapshot
  heap : ∀ index < heapWords, finalState.core.memory.read64 (workspace.layout.region.address index) = words index
  outside : ∀ address, workspace.layout.region.allowed address = false → finalState.core.memory.bytes address = core.memory.bytes address

/-- The exported symbol, return address, heap words, and caller register
state are observed by executing the parsed ELF bytes. -/
theorem RootRun.object {checked : X86.Checked} {core : Core} {workspace : Workspace} {value tag : Word} {words : Words}
    (executed : RootRun checked core workspace value tag words) {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry) (base : Word) (flags : ByteEval.Flags) :
    Nonempty (ObjectResult bytes input.exportName base flags core workspace value tag words) := by
  obtain ⟨count, finalState, positive, _, run, returned, related⟩ :=
    ObjectEval.run_safeSteps stream object entry base core flags executed.steps executed.halted executed.returnSlot
  refine ⟨⟨count, finalState, positive, run, returned, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [Core.setReg, Core.readReg, Registers.set] using (related.readReg .rax).symm.trans (by
      simpa [Core.setReg, Core.readReg, Registers.set] using executed.result)
  · simpa [Core.setReg, Core.readReg, Registers.set] using (related.readReg .rdx).symm.trans (by
      simpa [Core.setReg, Core.readReg, Registers.set] using executed.status)
  · have same : executed.after.core.registers .rsp = core.registers .rsp := executed.stack
    simpa [Core.setReg, Core.readReg, Registers.set, same] using (related.readReg .rsp).symm
  · have same : finalState.core.calleeSavedSnapshot = executed.after.core.calleeSavedSnapshot := by
      change SysV.calleeSaved.map finalState.core.readReg = SysV.calleeSaved.map executed.after.core.readReg
      have equal := congrArg (fun registers => SysV.calleeSaved.map registers) related.registers.symm
      simpa [Core.setReg, Core.readReg, SysV.calleeSaved, Registers.set] using equal
    exact same.trans executed.saved
  · intro index bound
    have read := related.memory.read .w64 (workspace.layout.region.address index) (executed.readable index bound)
    exact read.symm.trans (executed.represented.view index (Nat.lt_of_lt_of_le bound workspace.layout.enough))
  · intro address outside
    have visible : ¬executed.holes address := by
      intro hidden
      obtain ⟨slot, offset, bound, _, _, small, equal⟩ := executed.safe address hidden
      have allowed := workspace.layout.region.byteAllowed bound small
      rw [← equal, outside] at allowed
      contradiction
    exact (related.memory.bytes address visible).symm.trans (executed.represented.frame address outside)

end Compilatrix.X86.HeapEntry
