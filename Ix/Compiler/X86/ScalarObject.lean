import Ix.Compiler.X86.ScalarCapacity
import Ix.Compiler.X86.SafeStepsObject

namespace Ix.Compiler.X86

theorem BlockCode.safe_leaf_ret {checked : Checked} {block : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions .ret) (core : Core) (holes : Stream.Holes)
    (readable : Stream.ReadableData holes (core.readReg .rsp) 8) :
    Stream.SafeSteps Runtime.rejecting checked 1 holes (inFrame core block instructions.length [])
      holes (haltedLeaf core block instructions.length) := by
  have safe : Stream.SafeAt checked.program holes (inFrame core block instructions.length []) := by
    simp [Stream.SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found, readable]
  have executed := code.ret Runtime.rejecting core
  simpa only [code.holeStep] using Stream.SafeSteps.single safe executed

namespace Scalar
open WordRegion

structure RootRun (output : X86.Checked) (core : Core) (stack : Stack) (result : Option Word) where
  count : Nat
  after : Machine
  holes : Stream.Holes
  holesIn : HolesIn stack.layout stack.frame.top holes
  steps : Stream.SafeSteps Runtime.rejecting output count (fun _ => False) (Machine.initial output core) holes after
  halted : after.status = .halted (result.getD 0)
  value : after.core.readReg .rax = result.getD 0
  tag : after.core.readReg .rdx = returnTag result
  stackPointer : after.core.readReg .rsp = core.readReg .rsp
  saved : after.core.calleeSavedSnapshot = core.calleeSavedSnapshot
  outside : ∀ address, stack.layout.allowed address = false → after.core.memory.bytes address = core.memory.bytes address
  returnSlot : after.core.memory.read64? (after.core.readReg .rsp) = .ok (core.memory.read64 (core.readReg .rsp))

theorem Output.root_run {checked : Scalar.Checked} (output : Output checked)
    {function : Function} {values : Array Word} {result : Option Word}
    (found : checked.program.functions[checked.program.entry]? = some function)
    (arity : values.size = function.parameters)
    (evaluated : Evaluates checked.program.functions function.body values result)
    (stack : Stack) (depth : checked.program.entry < stack.depth) (core : Core)
    (stackPointer : core.readReg .rsp = stack.layout.address stack.frame.top)
    (arguments : ArgumentsAt values ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩)
    (readable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.readable (stack.layout.address index) 8 = true)
    (writable : ∀ index < stack.layout.slots, Memory.rangeAllowed core.memory.writable (stack.layout.address index) 8 = true) :
    Nonempty (RootRun output.target core stack result) := by
  let state : State := ⟨core.registers, fun index => core.memory.read64 (stack.layout.address index)⟩
  have represented : Realizes stack.layout core.memory state.words core.memory := realizes_initial _ _ readable writable
  obtain ⟨plan, planFound, code⟩ := output.function_code found
  have entry : output.target.program.entry = plan.entry := by simpa [planFound] using output.entry
  obtain ⟨executed⟩ := output.function_contract found code arity evaluated (stack.rank_capacity depth) (Nat.le_refl _) (returns := [])
    core.memory core.memory state (fun _ => False) arguments stackPointer (HolesIn.empty _ _)
    (by intro active member; cases member) represented
  have finalStack : (executed.after.core executed.memory).readReg .rsp = stack.layout.address stack.frame.top :=
    (executed.stable .rsp (by simp)).trans stackPointer
  have exitCode := code.exit result
  have safe := executed.safeHoles.readable stack.frame.bound (.inr (Nat.le_refl _))
  have retSteps := exitCode.safe_leaf_ret (executed.after.core executed.memory) executed.holes (finalStack ▸ safe)
  have offset : (tagInstructions result ++ epilogue).length = returnOffset result := by cases result <;> rfl
  rw [offset] at retSteps
  refine ⟨{
    count := executed.count + 1
    after := haltedLeaf (executed.after.core executed.memory) (returnBlock plan result) (returnOffset result)
    holes := executed.holes, holesIn := executed.safeHoles, steps := ?_, halted := ?_, value := executed.resultValue, tag := executed.resultTag
    stackPointer := executed.stable .rsp (by simp), saved := executed.stable.snapshot core.memory executed.memory
    outside := executed.represented.frame, returnSlot := ?_ }⟩
  · have initial : inFrame (state.core core.memory) plan.entry 0 [] = Machine.initial output.target core := by
      simp [Machine.initial, inFrame, state, State.core, entry]
    simpa only [initial] using executed.steps.append retSteps
  · simpa [haltedLeaf, State.core, Core.readReg] using executed.resultValue
  · change executed.memory.read64? (executed.after.registers .rsp) = .ok (core.memory.read64 (core.readReg .rsp))
    change executed.after.registers .rsp = stack.layout.address stack.frame.top at finalStack
    rw [finalStack, stackPointer]
    simp only [Memory.read64?, Memory.read?, Width.bytes, executed.represented.readable _ stack.frame.bound, ↓reduceIte, Except.ok.injEq]
    change executed.memory.read64 (stack.layout.address stack.frame.top) = core.memory.read64 (stack.layout.address stack.frame.top)
    rw [executed.represented.view _ stack.frame.bound, executed.preserved _ (Nat.le_refl _)]

/-- The object bytes select both text and the exported entry. Safety and
typed execution are derived from the structural scalar compiler theorem. -/
theorem RootRun.object {checked : X86.Checked} {core : Core} {stack : Stack} {result : Option Word}
    (executed : RootRun checked core stack result) {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry) (base : Word) (flags : ByteEval.Flags) :
    ∃ count finalState, 0 < count ∧ count ≤ 3 * executed.count ∧
      ObjectEval.run bytes input.exportName base count core flags = .ok finalState ∧
      finalState.rip = core.memory.read64 (core.readReg .rsp) ∧
      Stream.CoreRelated checked.program base executed.holes []
        (executed.after.core.setReg .rsp (executed.after.core.readReg .rsp + 8)) finalState.core :=
  ObjectEval.run_safeSteps stream object entry base core flags executed.steps executed.halted executed.returnSlot

/-- Complete observable machine behavior of the parsed exported object. -/
structure ObjectResult (bytes : ByteArray) (exportName : String) (base : Word)
    (flags : ByteEval.Flags) (core : Core) (stack : Stack) (result : Option Word) where
  count : Nat
  finalState : ByteEval.State
  positive : 0 < count
  run : ObjectEval.run bytes exportName base count core flags = .ok finalState
  returned : finalState.rip = core.memory.read64 (core.readReg .rsp)
  value : finalState.core.readReg .rax = result.getD 0
  tag : finalState.core.readReg .rdx = returnTag result
  stackPointer : finalState.core.readReg .rsp = core.readReg .rsp + 8
  saved : finalState.core.calleeSavedSnapshot = core.calleeSavedSnapshot
  outside : ∀ address, stack.layout.allowed address = false → finalState.core.memory.bytes address = core.memory.bytes address

theorem RootRun.objectResult {checked : X86.Checked} {core : Core} {stack : Stack} {result : Option Word}
    (executed : RootRun checked core stack result) {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry) (base : Word) (flags : ByteEval.Flags) :
    Nonempty (ObjectResult bytes input.exportName base flags core stack result) := by
  obtain ⟨count, finalState, positive, bounded, run, returned, related⟩ := executed.object stream object entry base flags
  refine ⟨⟨count, finalState, positive, run, returned, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [Core.setReg, Core.readReg, Registers.set] using (related.readReg .rax).symm.trans (by
      simpa [Core.setReg, Core.readReg, Registers.set] using executed.value)
  · simpa [Core.setReg, Core.readReg, Registers.set] using (related.readReg .rdx).symm.trans (by
      simpa [Core.setReg, Core.readReg, Registers.set] using executed.tag)
  · have same : executed.after.core.registers .rsp = core.registers .rsp := executed.stackPointer
    simpa [Core.setReg, Core.readReg, Registers.set, same] using (related.readReg .rsp).symm
  · have same : finalState.core.calleeSavedSnapshot = executed.after.core.calleeSavedSnapshot := by
      change SysV.calleeSaved.map finalState.core.readReg = SysV.calleeSaved.map executed.after.core.readReg
      have equal := congrArg (fun registers => SysV.calleeSaved.map registers) related.registers.symm
      simpa [Core.setReg, Core.readReg, SysV.calleeSaved, Registers.set] using equal
    exact same.trans executed.saved
  · intro address outside
    have visible : ¬executed.holes address := by
      intro hidden
      obtain ⟨slot, offset, bound, below, partition, small, equal⟩ := executed.holesIn address hidden
      have allowed := stack.layout.byteAllowed bound small
      rw [← equal, outside] at allowed
      contradiction
    exact (related.memory.bytes address visible).symm.trans (executed.outside address outside)

end Scalar
end Ix.Compiler.X86
