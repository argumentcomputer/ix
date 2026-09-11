import Ix.Compiler.X86.ScalarSafeFrames
import Ix.Compiler.X86.SafeControl

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem Preserves.setReg {layout : Layout} (frame : Frame layout) (locals : Nat) (state : State)
    (register : GPR) (value : Word) (scratch : SysV.isCallerSaved register = true) :
    Preserves frame locals state (state.setReg register value) :=
  ⟨Stable.setReg _ _ _ scratch, fun _ _ => rfl⟩

theorem Preserves.weaken {layout : Layout} {frame : Frame layout} {smaller larger : Nat} {before after : State}
    (preserved : Preserves frame larger before after) (bound : smaller ≤ larger) :
    Preserves frame smaller before after :=
  ⟨preserved.1, fun index high => preserved.2 index (by omega)⟩

theorem Preserves.fresh {layout : Layout} (frame : Frame layout) {locals : Nat} (bound : locals < maxLocals)
    (state : State) (value : Word) :
    Preserves frame locals state (state.setWord (frame.localIndex locals) value) := by
  refine ⟨Stable.setWord _ _ _, fun index high => ?_⟩
  apply Words.set_other
  have enough := frame.enough
  simp only [Frame.localIndex, maxLocals] at *
  omega

theorem ValuesAt.push {layout : Layout} {frame : Frame layout} {values : Array Word} {state : State}
    (valuesAt : ValuesAt frame values state) (bound : values.size < maxLocals) (value : Word) :
    ValuesAt frame (values.push value) (state.setWord (frame.localIndex values.size) value) := by
  refine ⟨by simp only [Array.size_push]; omega, ?_⟩
  intro index small
  simp only [Array.size_push] at small
  by_cases previous : index < values.size
  · have different : frame.localIndex index ≠ frame.localIndex values.size := by
      intro equal
      have := frame.local_injective (by omega) bound equal
      omega
    simp only [State.setWord_words, Words.set_other _ _ _ _ different,
      Array.getElem_push_lt previous]
    exact valuesAt.2 index previous
  · have equal : index = values.size := by omega
    subst index
    simp

theorem load_safeTrace {layout : Layout} {frame : Frame layout} {values : Array Word} {state : State}
    {returns : List ReturnFrame} {rootTop : Nat} {holes : Stream.Holes}
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state)
    (valid : HolesIn layout rootTop holes) (destination : GPR)
    {source : Atom} {value : Word} (found : source.eval values = some value) :
    SafeTrace layout returns [load destination source] state holes (state.setReg destination value) holes := by
  cases source with
  | constant number =>
      simp only [Atom.eval, Option.some.injEq] at found
      subst value
      exact SafeTrace.mov _ _ _ _ _ _
  | var index =>
      simp only [Atom.eval] at found
      obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
      have small : index < maxLocals := by have := valuesAt.1; omega
      have loaded : state.words (frame.localIndex index) = value := (valuesAt.2 index bound).trans equal
      have address : state.registers .rbp - (slot index).displacement = layout.address (frame.localIndex index) := by
        rw [framed.1]
        exact frame.local_address small
      simpa only [load, loaded] using SafeTrace.reload layout returns state holes destination (slot index)
        (frame.localIndex index) (frame.local_bound index) address
        (valid.readable (frame.local_bound index) (.inl (frame.local_ordinary small)))

def operandsState (state : State) (left right : Word) : State := (state.setReg .rax left).setReg .rcx right
def sumState (state : State) (left right : Word) : State :=
  ((operandsState state left right).setReg .r10 left).setReg .rax (left + right)

theorem operands_preserves {layout : Layout} (frame : Frame layout) (locals : Nat) (state : State) (left right : Word) :
    Preserves frame locals state (operandsState state left right) :=
  (Preserves.setReg frame locals state .rax left (by simp)).trans
    (Preserves.setReg frame locals _ .rcx right (by simp))

theorem sum_preserves {layout : Layout} (frame : Frame layout) (locals : Nat) (state : State) (left right : Word) :
    Preserves frame locals state (sumState state left right) :=
  ((operands_preserves frame locals state left right).trans
    (Preserves.setReg frame locals _ .r10 left (by simp))).trans
    (Preserves.setReg frame locals _ .rax (left + right) (by simp))

theorem operands_safeTrace {layout : Layout} {frame : Frame layout} {values : Array Word} {state : State}
    {returns : List ReturnFrame} {rootTop : Nat} {holes : Stream.Holes} {left right : Atom} {a b : Word}
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state) (valid : HolesIn layout rootTop holes)
    (leftValue : left.eval values = some a) (rightValue : right.eval values = some b) :
    SafeTrace layout returns [load .rax left, load .rcx right] state holes (operandsState state a b) holes := by
  have preserved := Preserves.setReg frame values.size state .rax a (by simp)
  exact (load_safeTrace framed valuesAt valid .rax leftValue).append
    (load_safeTrace (preserved.1.framed framed) (preserved.values valuesAt) valid .rcx rightValue)

theorem add_safeTrace {layout : Layout} {frame : Frame layout} {values : Array Word} {state : State}
    {returns : List ReturnFrame} {rootTop : Nat} {holes : Stream.Holes} {left right : Atom} {a b : Word}
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state) (valid : HolesIn layout rootTop holes)
    (leftValue : left.eval values = some a) (rightValue : right.eval values = some b) :
    SafeTrace layout returns (addInstructions left right) state holes (sumState state a b) holes := by
  have saved := SafeTrace.mov layout returns (operandsState state a b) holes .r10 (.reg .rax)
  have added := SafeTrace.alu layout returns ((operandsState state a b).setReg .r10 a) holes .add .rax (.reg .rcx)
  simp [operandsState, AluOp.eval] at saved added
  simpa [addInstructions, sumState, operandsState] using
    ((operands_safeTrace framed valuesAt valid leftValue rightValue).append saved).append added

theorem carry_holds (state : State) (left right : Word) (memory : Memory) :
    carryCompare.holds .unsignedLt ((sumState state left right).core memory) = ExactNat.overflow left right := by
  simp [carryCompare, Compare.holds, Condition.holds, sumState, operandsState, State.core, State.setReg,
    Core.readReg, Registers.set, AluSource.eval, ExactNat.overflow]

end Ix.Compiler.X86.Scalar
