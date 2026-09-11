import Ix.Compiler.X86.ScalarContracts
import Ix.Compiler.X86.WordRegionSafeControl

namespace Ix.Compiler.X86.Scalar
open WordRegion

variable {checked : X86.Checked} {layout : Layout} {frame : Frame layout} {values : Array Word}
  {outside memory : Memory} {state : State} {holes : Stream.Holes} {rootTop : Nat} {returns : List ReturnFrame}

theorem atom_run {entry success failure : BlockId} {source : Atom} {value : Word}
    (code : BlockCode checked entry [load .rax source] (.jump success))
    (valid : checked.program.hasBlock success = true)
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state)
    (safeHoles : HolesIn layout rootTop holes) (represented : Realizes layout outside state.words memory)
    (found : source.eval values = some value) :
    Nonempty (ExprRun checked (.atom entry source) success failure layout frame values outside memory state holes
      rootTop returns (some value)) := by
  obtain ⟨nextMemory, nextView, steps⟩ :=
    (load_safeTrace framed valuesAt safeHoles .rax found).jump outside memory represented checked entry success code valid
  exact ⟨{
    count := 2, after := state.setReg .rax value, memory := nextMemory, holes
    represented := nextView, preserved := Preserves.setReg _ _ _ _ _ (by simp), safeHoles
    resultAt := by intro result equal; cases Option.some.inj equal; simp
    steps := steps }⟩

theorem add_destination (success failure : BlockId) (left right : Word) :
    (if ExactNat.overflow left right then failure else success) = destination success failure (ExactNat.add left right) := by
  unfold ExactNat.add
  split <;> rfl

theorem sum_result (state : State) (left right : Word) : ResultAt (ExactNat.add left right) (sumState state left right) := by
  intro result equal
  unfold ExactNat.add at equal
  split at equal
  · contradiction
  · cases Option.some.inj equal
    simp [sumState]

theorem add_run {entry success failure : BlockId} {left right : Atom} {a b : Word}
    (code : BlockCode checked entry (addInstructions left right) (.branch carryCompare .unsignedLt failure success))
    (successValid : checked.program.hasBlock success = true) (failureValid : checked.program.hasBlock failure = true)
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state)
    (safeHoles : HolesIn layout rootTop holes) (represented : Realizes layout outside state.words memory)
    (leftValue : left.eval values = some a) (rightValue : right.eval values = some b) :
    Nonempty (ExprRun checked (.add entry left right) success failure layout frame values outside memory state holes
      rootTop returns (ExactNat.add a b)) := by
  obtain ⟨nextMemory, nextView, steps⟩ := (add_safeTrace framed valuesAt safeHoles leftValue rightValue).branch
    outside memory represented checked entry failure success carryCompare .unsignedLt code
    (ExactNat.overflow a b) (carry_holds state a b Memory.unmapped)
    (by split <;> assumption)
  rw [add_destination] at steps
  exact ⟨{
    count := 5, after := sumState state a b, memory := nextMemory, holes
    represented := nextView, preserved := sum_preserves _ _ _ _ _, safeHoles
    resultAt := sum_result _ _ _, steps := steps }⟩

theorem operands_holds (state : State) (left right : Word) (memory : Memory) :
    operandsCompare.holds .unsignedLt ((operandsState state left right).core memory) = decide (left < right) := by
  simp [operandsCompare, Compare.holds, Condition.holds, operandsState, State.core, State.setReg,
    Core.readReg, Registers.set, AluSource.eval]

theorem sub_run {entry underflow ordinary success failure : BlockId} {left right : Atom} {a b : Word}
    (code : BlockCode checked entry [load .rax left, load .rcx right]
      (.branch operandsCompare .unsignedLt underflow ordinary))
    (underflowCode : BlockCode checked underflow [.mov .w64 .rax (.imm 0)] (.jump success))
    (ordinaryCode : BlockCode checked ordinary [.alu .sub .w64 .rax (.reg .rcx)] (.jump success))
    (valid : checked.program.hasBlock success = true)
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state)
    (safeHoles : HolesIn layout rootTop holes) (represented : Realizes layout outside state.words memory)
    (leftValue : left.eval values = some a) (rightValue : right.eval values = some b) :
    Nonempty (ExprRun checked (.sub entry underflow ordinary left right) success failure layout frame values
      outside memory state holes rootTop returns (some (ExactNat.sub a b))) := by
  obtain ⟨middleMemory, middleView, leading⟩ := (operands_safeTrace framed valuesAt safeHoles leftValue rightValue).branch
    outside memory represented checked entry underflow ordinary operandsCompare .unsignedLt code (decide (a < b))
    (operands_holds state a b Memory.unmapped)
    (by split; exact underflowCode.hasBlock; exact ordinaryCode.hasBlock)
  by_cases less : a < b
  · simp only [less, decide_true, ↓reduceIte] at leading
    obtain ⟨finalMemory, finalView, suffix⟩ :=
      (SafeTrace.mov layout returns (operandsState state a b) holes .rax (.imm 0)).jump
        outside middleMemory middleView checked underflow success underflowCode valid
    exact ⟨{
      count := 5, after := (operandsState state a b).setReg .rax 0, memory := finalMemory, holes
      represented := finalView, safeHoles
      preserved := (operands_preserves _ _ _ _ _).trans (Preserves.setReg _ _ _ _ _ (by simp))
      resultAt := by intro result equal; simp only [ExactNat.sub, if_pos less, Option.some.injEq] at equal; subst result; simp
      steps := by simpa [destination, Plan.entry] using leading.append suffix }⟩
  · simp only [less, decide_false, Bool.false_eq_true, ↓reduceIte] at leading
    have trace : SafeTrace layout returns [.alu .sub .w64 .rax (.reg .rcx)] (operandsState state a b) holes
        ((operandsState state a b).setReg .rax (a - b)) holes := by
      simpa [operandsState, AluOp.eval] using SafeTrace.alu layout returns (operandsState state a b) holes .sub .rax (.reg .rcx)
    obtain ⟨finalMemory, finalView, suffix⟩ := trace.jump outside middleMemory middleView checked ordinary success ordinaryCode valid
    exact ⟨{
      count := 5, after := (operandsState state a b).setReg .rax (a - b), memory := finalMemory, holes
      represented := finalView, safeHoles
      preserved := (operands_preserves _ _ _ _ _).trans (Preserves.setReg _ _ _ _ _ (by simp))
      resultAt := by intro result equal; simp only [ExactNat.sub, if_neg less, Option.some.injEq] at equal; subst result; simp
      steps := by simpa [destination, Plan.entry] using leading.append suffix }⟩

end Ix.Compiler.X86.Scalar
