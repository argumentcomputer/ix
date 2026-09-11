import Ix.Compiler.X86.ScalarComposition

namespace Ix.Compiler.X86.Scalar
open WordRegion

structure FunctionCode (checked : X86.Checked) (entries : Array BlockId)
    (source : Function) (plan : FunctionPlan) : Prop where
  expression : plan.body.expression = source.body
  prologue : BlockCode checked plan.entry (Scalar.prologue source.parameters) (.jump plan.body.entry)
  success : BlockCode checked plan.success successInstructions .ret
  failure : BlockCode checked plan.failure failureInstructions .ret
  body : plan.body.matches checked.program entries source.parameters plan.success plan.failure = true

theorem FunctionPlan.code {checked : X86.Checked} {entries : Array BlockId} {source : Function} {plan : FunctionPlan}
    (matched : plan.matches checked.program entries source = true) : FunctionCode checked entries source plan := by
  simp only [FunctionPlan.matches, Bool.and_eq_true, beq_iff_eq] at matched
  exact ⟨matched.1.1.1.1, blockMatches_code matched.1.1.1.2, blockMatches_code matched.1.1.2,
    blockMatches_code matched.1.2, matched.2⟩

def tagInstructions : Option Word → List Instr
  | some _ => [.mov .w64 .rdx (.imm 0)]
  | none => [.mov .w64 .rax (.imm 0), .mov .w64 .rdx (.imm 1)]

def tagState (result : Option Word) (state : State) : State :=
  match result with
  | some _ => state.setReg .rdx 0
  | none => (state.setReg .rax 0).setReg .rdx 1

theorem tag_safeTrace (layout : Layout) (returns : List ReturnFrame) (result : Option Word)
    (state : State) (holes : Stream.Holes) :
    SafeTrace layout returns (tagInstructions result) state holes (tagState result state) holes := by
  cases result with
  | none => exact (SafeTrace.mov _ _ _ _ _ _).append (SafeTrace.mov _ _ _ _ _ _)
  | some value => exact SafeTrace.mov _ _ _ _ _ _

theorem tag_preserves {layout : Layout} (frame : Frame layout) (locals : Nat) (result : Option Word) (state : State) :
    Preserves frame locals state (tagState result state) := by
  cases result with
  | none => exact (Preserves.setReg _ _ _ _ _ (by simp)).trans (Preserves.setReg _ _ _ _ _ (by simp))
  | some value => exact Preserves.setReg _ _ _ _ _ (by simp)

@[simp] theorem tag_words (result : Option Word) (state : State) : (tagState result state).words = state.words := by
  cases result <;> rfl

theorem tag_result {result : Option Word} {state : State} (value : ResultAt result state) :
    (tagState result state).registers .rax = result.getD 0 ∧
    (tagState result state).registers .rdx = returnTag result := by
  cases result with
  | none => simp [tagState, returnTag]
  | some result => simp [tagState, returnTag, value result rfl]

@[simp] theorem enter_registers {layout : Layout} (frame : Frame layout) (parameters : Nat) (state : State) :
    (enterState frame parameters state).registers = (frameState frame state).registers := by
  unfold enterState
  split <;> (try split) <;> rfl

theorem leave_stable {layout : Layout} (frame : Frame layout) (parameters : Nat) (before after : State)
    (stack : before.registers .rsp = layout.address frame.top)
    (preserved : Preserves frame parameters (enterState frame parameters before) after) :
    Stable before (leaveState frame after) := by
  have base : after.words frame.baseIndex = before.registers .rbp := by
    rw [preserved.2 _ (by simp only [Frame.baseIndex]; omega), enter_savedBase]
  intro register saved
  have same := preserved.1 register saved
  cases register <;> simp only [callerSaved] at saved <;> (try contradiction)
  all_goals simp_all [leaveState, frameState, pushState]

theorem FunctionCode.exit {checked : X86.Checked} {entries : Array BlockId} {source : Function} {plan : FunctionPlan}
    (code : FunctionCode checked entries source plan) (result : Option Word) :
    BlockCode checked (returnBlock plan result) (tagInstructions result ++ epilogue) .ret := by
  cases result
  · exact code.failure
  · exact code.success

theorem function_contract {checked : X86.Checked} {entries : Array BlockId} {source : Function} {plan : FunctionPlan}
    {layout : Layout} {frame : Frame layout} {values : Array Word} {rootTop : Nat} {returns : List ReturnFrame}
    {result : Option Word}
    (code : FunctionCode checked entries source plan) (arity : values.size = source.parameters)
    (body : ExprContract checked plan.body plan.success plan.failure layout frame values rootTop returns result) :
    FunctionContract checked plan layout frame values rootTop returns result := by
  intro outside memory state holes arguments stack safeHoles frames represented
  obtain ⟨bodyMemory, bodyView, prologueSteps⟩ := (enter_safeTrace frame source.parameters state holes stack frames).jump
    outside memory represented checked plan.entry plan.body.entry code.prologue (Plan.entry_valid code.body)
  obtain ⟨executed⟩ := body outside bodyMemory _ _ (enter_framed frame source.parameters state)
    (by simpa only [arity] using enter_values frame state values arguments)
    (safeHoles.enter frame source.parameters) frames bodyView
  have preserved := executed.preserved.trans (tag_preserves frame values.size result executed.after)
  have framed := preserved.1.framed (enter_framed frame source.parameters state)
  have exitTrace := (tag_safeTrace layout returns result executed.after executed.holes).append
    (leave_safeTrace frame (tagState result executed.after) executed.holes framed executed.safeHoles)
  have exitCode := code.exit result
  obtain ⟨exitMemory, exitView, exitSteps⟩ := exitTrace.steps outside executed.memory executed.represented
    Runtime.rejecting checked (returnBlock plan result) 0 exitCode.segment (by simpa using exitCode.fits)
  have value := tag_result executed.resultAt
  refine ⟨{
    count := (Scalar.prologue source.parameters).length + 1 + executed.count + (tagInstructions result ++ epilogue).length
    after := leaveState frame (tagState result executed.after), memory := exitMemory, holes := executed.holes
    represented := exitView, safeHoles := executed.safeHoles
    stable := leave_stable frame source.parameters state _ stack (by simpa only [arity] using preserved)
    preserved := ?_, resultValue := ?_, resultTag := ?_, steps := ?_ }⟩
  · intro index above
    change (tagState result executed.after).words index = state.words index
    rw [preserved.2 _ (by omega), enter_words_above _ _ _ _ above]
  · simpa [leaveState] using value.1
  · simpa [leaveState] using value.2
  · have label : destination plan.success plan.failure result = returnBlock plan result := by cases result <;> rfl
    have offset : (tagInstructions result ++ epilogue).length = returnOffset result := by cases result <;> rfl
    have bodySteps := executed.steps
    rw [label] at bodySteps
    have combined := (prologueSteps.append bodySteps).append exitSteps
    simpa only [Nat.zero_add, offset] using combined

end Ix.Compiler.X86.Scalar
