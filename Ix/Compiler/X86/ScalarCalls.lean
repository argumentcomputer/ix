import Ix.Compiler.X86.ScalarArguments
import Ix.Compiler.X86.WordRegionSafeCalls

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem Frame.child_address {layout : Layout} (frame : Frame layout) (enough : 67 ≤ frame.top) :
    layout.address frame.stackIndex - 8 = layout.address (frame.child enough).top := by
  have shifted := layout.subtract (slot := frame.stackIndex) (count := 1) (by simp [Frame.stackIndex]; omega)
  simpa [Frame.stackIndex, Frame.child, frameStride, Nat.sub_sub] using shifted

theorem FramesAbove.child {layout : Layout} {frame : Frame layout} {returns : List ReturnFrame}
    (frames : FramesAbove layout frame.top returns) (enough : 67 ≤ frame.top)
    (newFrame : ReturnFrame) (address : newFrame.returnSlot = layout.address (frame.child enough).top) :
    FramesAbove layout (frame.child enough).top (newFrame :: returns) := by
  intro active member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨_, (frame.child enough).bound, Nat.le_refl _, address⟩
  · obtain ⟨index, bound, above, location⟩ := frames active old
    exact ⟨index, bound, by simp only [Frame.child, frameStride]; omega, location⟩

theorem call_preserves {layout : Layout} (frame : Frame layout) (enough : 67 ≤ frame.top)
    {locals : Nat} (small : locals ≤ maxLocals) (before after : State) (block : BlockId)
    (stable : Stable (before.call layout (frame.child enough).top block 2) after)
    (words : ∀ index, (frame.child enough).top ≤ index →
      after.words index = (before.call layout (frame.child enough).top block 2).words index) :
    Preserves frame locals before (after.setReg .rsp (before.registers .rsp)) := by
  refine ⟨?_, ?_⟩
  · intro register saved
    have same := stable register saved
    cases register <;> simp_all [State.call]
  · intro index above
    have high : (frame.child enough).top < index := by
      simp only [Frame.child, frameStride, maxLocals] at *
      omega
    simpa [State.call, Words.set, Nat.ne_of_gt high] using words index (Nat.le_of_lt high)

theorem failed_holds (state : State) (result : Option Word) (memory : Memory)
    (tag : state.registers .rdx = returnTag result) :
    failedCompare.holds .ne (state.core memory) = result.isNone := by
  cases result <;> simp [failedCompare, Compare.holds, Condition.holds, State.core, Core.readReg,
    AluSource.eval, signExtend32, tag, returnTag]

theorem call_contract {checked : X86.Checked} {entries : Array BlockId} {source : Function} {calleePlan : FunctionPlan}
    {layout : Layout} {frame : Frame layout} {values supplied : Array Word} {rootTop : Nat} {returns : List ReturnFrame}
    {entry success failure : BlockId} {function : Nat} {arguments : Array Atom} {result : Option Word}
    (enough : 67 ≤ frame.top) (below : frame.top ≤ rootTop)
    (small : arguments.size ≤ 2) (mapped : arguments.mapM (Atom.eval values) = some supplied)
    (code : BlockCode checked entry (callInstructions calleePlan.entry arguments) (.branch failedCompare .ne failure success))
    (calleeCode : FunctionCode checked entries source calleePlan)
    (successValid : checked.program.hasBlock success = true) (failureValid : checked.program.hasBlock failure = true)
    (callee : ∀ activeReturns, FunctionContract checked calleePlan layout (frame.child enough) supplied rootTop activeReturns result) :
    ExprContract checked (.call entry function arguments) success failure layout frame values rootTop returns result := by
  intro outside memory state holes framed valuesAt safeHoles frames represented
  have argumentTrace := arguments_safeTrace framed valuesAt safeHoles small mapped (returns := returns)
  have argumentSegment : Straight.Segment checked entry 0
      [load .rdi (arguments[0]?.getD (.constant 0)), load .rsi (arguments[1]?.getD (.constant 0))] := by
    refine ⟨_, code.found, ?_⟩
    intro index bound
    have alternatives : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bound; omega
    rcases alternatives with rfl | rfl <;> rfl
  obtain ⟨argumentMemory, argumentView, argumentSteps⟩ := argumentTrace.steps outside memory represented
    Runtime.rejecting checked entry 0 argumentSegment (by change 2 < UInt32.size; decide)
  let ready := argumentsState state supplied
  have readyPreserved : Preserves frame values.size state ready := arguments_preserves frame values.size state supplied
  have readyFramed := readyPreserved.1.framed framed
  have address : ready.registers .rsp - 8 = layout.address (frame.child enough).top :=
    readyFramed.2 ▸ frame.child_address enough
  have callSegment : Straight.Segment checked entry 2 [.call calleePlan.entry] :=
    Straight.Segment.tail (Straight.Segment.tail code.segment)
  have disjoint := frames.disjoint (frame.child enough).bound (by simp only [Frame.child, frameStride]; omega)
  obtain ⟨callMemory, callView, callSteps⟩ := call_safeStep argumentView (frame.child enough).bound address callSegment
    (by decide) calleeCode.prologue.hasBlock (readyFramed.2 ▸ frame.call_aligned) disjoint (holes := holes)
  let active := callFrame (ready.core argumentMemory) entry 2
  have activeSlot : active.returnSlot = layout.address (frame.child enough).top := address
  have activeFrames := frames.child enough active activeSlot
  have hidden := safeHoles.add_return (frame.child enough).bound
    (by simp only [Frame.child, frameStride]; omega) (frame.child enough).partition
  have readyArguments := arguments_ready state supplied (mapped_arguments small mapped).1
  obtain ⟨executed⟩ := callee (active :: returns) outside callMemory (ready.call layout (frame.child enough).top entry 2)
    _ (by simpa [ArgumentsAt, State.call] using readyArguments) (by simp [State.call]) hidden activeFrames callView
  have stack : (executed.after.core executed.memory).readReg .rsp = active.returnSlot := by
    change executed.after.registers .rsp = active.returnSlot
    rw [executed.stable .rsp (by simp), activeSlot]
    simp [State.call]
  have readable : executed.memory.read64? active.returnSlot = .ok active.continuation.encode := by
    rw [activeSlot]
    simp only [Memory.read64?, Memory.read?, Width.bytes, executed.represented.readable _ (frame.child enough).bound,
      ↓reduceIte, Except.ok.injEq]
    change executed.memory.read64 (layout.address (frame.child enough).top) = active.continuation.encode
    rw [executed.represented.view _ (frame.child enough).bound, executed.preserved _ (Nat.le_refl _)]
    simp [State.call, active, callFrame]
  have saved : (executed.after.core executed.memory).calleeSavedMatch active.calleeSaved = true := by
    simp only [Core.calleeSavedMatch, beq_iff_eq]
    rw [executed.stable.snapshot callMemory executed.memory]
    simp [active, callFrame, Core.calleeSavedSnapshot, SysV.calleeSaved, State.call,
      State.core, Core.readReg, State.setReg, State.setWord, Registers.set]
  have exitCode := calleeCode.exit result
  have retSteps := exitCode.safe_ret Runtime.rejecting (executed.after.core executed.memory) active returns executed.holes stack readable saved
  let resumed := executed.after.setReg .rsp (ready.registers .rsp)
  have returnAddress : active.returnSlot + 8 = ready.registers .rsp := by
    change (ready.registers .rsp - 8) + 8 = ready.registers .rsp
    exact UInt64.sub_add_cancel _ _
  have retEffect :
      { core := (executed.after.core executed.memory).setReg .rsp (active.returnSlot + 8),
        pc := active.continuation, returns, status := Status.running } =
      inFrame (resumed.core executed.memory) entry 3 returns := by
    rw [returnAddress]
    rfl
  rw [retEffect] at retSteps
  have resumedPreserved := call_preserves frame enough valuesAt.1 ready executed.after entry executed.stable executed.preserved
  have resumedTag : resumed.registers .rdx = returnTag result := by simpa [resumed] using executed.resultTag
  have branchSteps := code.safe_branch Runtime.rejecting (resumed.core executed.memory) returns executed.holes result.isNone
    (failed_holds resumed result executed.memory resumedTag) (by cases result <;> assumption)
  have label : (if result.isNone then failure else success) = destination success failure result := by cases result <;> rfl
  rw [label] at branchSteps
  refine ⟨{
    count := 2 + 1 + executed.count + 1 + 1, after := resumed, memory := executed.memory, holes := executed.holes
    represented := executed.represented, safeHoles := executed.safeHoles
    preserved := readyPreserved.trans resumedPreserved
    resultAt := ?_, steps := ?_ }⟩
  · intro value same
    simpa [resumed, same] using executed.resultValue
  · have offset : (tagInstructions result ++ epilogue).length = returnOffset result := by cases result <;> rfl
    rw [offset] at retSteps
    simpa only [callInstructions, List.length_cons, List.length_nil, Nat.zero_add, Plan.entry] using
      (((argumentSteps.append callSteps).append executed.steps).append retSteps).append branchSteps

end Ix.Compiler.X86.Scalar
