import Ix.Compiler.X86.ScalarPrimitives

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem Plan.entry_valid {checked : X86.Checked} {entries : Array BlockId} {plan : Plan}
    {locals : Nat} {success failure : BlockId}
    (matched : plan.matches checked.program entries locals success failure = true) :
    checked.program.hasBlock plan.entry = true := by
  induction plan generalizing locals success failure with
  | atom entry value => exact (blockMatches_code matched).hasBlock
  | add entry left right => exact (blockMatches_code matched).hasBlock
  | sub entry underflow ordinary left right =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact (blockMatches_code matched.1.1).hasBlock
  | letE join value body ihValue ihBody =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact ihValue matched.1.2
  | branch entry scrutinee zero successor ihZero ihSuccessor =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact (blockMatches_code matched.1.1).hasBlock
  | call entry function arguments =>
      simp only [Plan.matches] at matched
      split at matched
      · contradiction
      · exact (blockMatches_code matched).hasBlock

theorem let_contract {checked : X86.Checked} {layout : Layout} {frame : Frame layout}
    {values : Array Word} {rootTop : Nat} {returns : List ReturnFrame}
    {join success failure : BlockId} {value body : Plan} {bound : Word} {result : Option Word}
    (small : values.size < maxLocals)
    (code : BlockCode checked join [.spill (slot values.size) .rax] (.jump body.entry))
    (bodyValid : checked.program.hasBlock body.entry = true)
    (first : ExprContract checked value join failure layout frame values rootTop returns (some bound))
    (rest : ExprContract checked body success failure layout frame (values.push bound) rootTop returns result) :
    ExprContract checked (.letE join value body) success failure layout frame values rootTop returns result := by
  intro outside memory state holes framed valuesAt safeHoles frames represented
  obtain ⟨leading⟩ := first outside memory state holes framed valuesAt safeHoles frames represented
  have middleFramed := leading.preserved.1.framed framed
  have middleValues := leading.preserved.values valuesAt
  have stored : SafeTrace layout returns [.spill (slot values.size) .rax] leading.after leading.holes
      (leading.after.setWord (frame.localIndex values.size) bound)
      (Stream.clearRange leading.holes (layout.address (frame.localIndex values.size)) 8) := by
    simpa only [leading.resultAt bound rfl] using SafeTrace.spill layout returns leading.after leading.holes
      (slot values.size) .rax (frame.localIndex values.size) (frame.local_bound values.size)
      (by rw [middleFramed.1]; exact frame.local_address small) (frame.local_disjoint frames values.size)
  obtain ⟨joinMemory, joinView, joinSteps⟩ := stored.jump outside leading.memory leading.represented checked join body.entry code bodyValid
  obtain ⟨trailing⟩ := rest outside joinMemory _ _ ((Stable.setWord _ _ _).framed middleFramed) (middleValues.push small bound)
    (leading.safeHoles.clear _ _) frames joinView
  refine ⟨{
    count := leading.count + 2 + trailing.count, after := trailing.after, memory := trailing.memory, holes := trailing.holes
    represented := trailing.represented, safeHoles := trailing.safeHoles, resultAt := trailing.resultAt
    preserved := leading.preserved.trans ((Preserves.fresh frame small leading.after bound).trans
      (trailing.preserved.weaken (smaller := values.size) (by simp)))
    steps := ?_ }⟩
  simpa only [destination, Plan.entry, List.length_cons, List.length_nil] using (leading.steps.append joinSteps).append trailing.steps

theorem let_overflow_contract {checked : X86.Checked} {layout : Layout} {frame : Frame layout}
    {values : Array Word} {rootTop : Nat} {returns : List ReturnFrame}
    {join success failure : BlockId} {value body : Plan}
    (first : ExprContract checked value join failure layout frame values rootTop returns none) :
    ExprContract checked (.letE join value body) success failure layout frame values rootTop returns none := by
  intro outside memory state holes framed valuesAt safeHoles frames represented
  obtain ⟨leading⟩ := first outside memory state holes framed valuesAt safeHoles frames represented
  exact ⟨{ leading with steps := leading.steps }⟩

theorem zero_holds (state : State) (value : Word) (memory : Memory) :
    zeroCompare.holds .eq ((state.setReg .rax value).core memory) = (value == 0) := by
  simp [zeroCompare, Compare.holds, Condition.holds, State.core, State.setReg,
    Core.readReg, Registers.set, AluSource.eval, signExtend32]

theorem branch_contract {checked : X86.Checked} {layout : Layout} {frame : Frame layout}
    {values : Array Word} {rootTop : Nat} {returns : List ReturnFrame}
    {entry success failure : BlockId} {scrutinee : Atom} {zero successor : Plan}
    {value : Word} {result : Option Word}
    (found : scrutinee.eval values = some value)
    (code : BlockCode checked entry [load .rax scrutinee] (.branch zeroCompare .eq zero.entry successor.entry))
    (valid : checked.program.hasBlock (if value == 0 then zero.entry else successor.entry) = true)
    (taken : ExprContract checked (if value == 0 then zero else successor) success failure layout frame values rootTop returns result) :
    ExprContract checked (.branch entry scrutinee zero successor) success failure layout frame values rootTop returns result := by
  intro outside memory state holes framed valuesAt safeHoles frames represented
  have preserved := Preserves.setReg frame values.size state .rax value (by simp)
  obtain ⟨branchMemory, branchView, branchSteps⟩ := (load_safeTrace framed valuesAt safeHoles .rax found).branch
    outside memory represented checked entry zero.entry successor.entry zeroCompare .eq code (value == 0)
    (zero_holds state value Memory.unmapped) valid
  obtain ⟨trailing⟩ := taken outside branchMemory _ holes (preserved.1.framed framed) (preserved.values valuesAt)
    safeHoles frames branchView
  have label : (if value == 0 then zero else successor).entry = if value == 0 then zero.entry else successor.entry := by split <;> rfl
  have trailingSteps := trailing.steps
  rw [label] at trailingSteps
  exact ⟨{
    count := 2 + trailing.count, after := trailing.after, memory := trailing.memory, holes := trailing.holes
    represented := trailing.represented, safeHoles := trailing.safeHoles, resultAt := trailing.resultAt
    preserved := preserved.trans trailing.preserved, steps := branchSteps.append trailingSteps }⟩

end Ix.Compiler.X86.Scalar
