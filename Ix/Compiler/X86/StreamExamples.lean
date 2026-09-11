import Ix.Compiler.X86.ObjectExecution
import Ix.Compiler.X86.StreamDecidable
import Ix.Compiler.X86.EvalExamples

/-! Kernel checks and shared regression inputs for complete certified streams.
The call cases include nested frames and reuse of a released return slot. -/

namespace Ix.Compiler.X86.StreamExamples

def reusedCalls : Program := {
  entry := 0
  blocks := #[
    { instructions := #[.push .rbp, .call 1, .call 2,
        .store .w64 { base := some .rsp, displacement := 0xfffffff8 } .rax,
        .load .w64 .rcx { base := some .rsp, displacement := 0xfffffff8 }, .pop .rbp]
      terminator := .ret },
    { instructions := #[.mov .w64 .rax (.imm 41)], terminator := .ret },
    { instructions := #[.alu .add .w64 .rax (.imm 1)], terminator := .ret }] }

def nestedCalls : Program := {
  entry := 0
  blocks := #[
    { instructions := #[.push .rbp, .call 1, .pop .rbp], terminator := .ret },
    { instructions := #[.push .rbp, .call 2, .pop .rbp], terminator := .ret },
    { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }

def tailCall : Program := {
  entry := 0
  blocks := #[{ instructions := #[], terminator := .tailCall 1 },
    { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }

def core : Core := { (Core.empty 0x8008) with memory := Memory.flat.write64 0x8008 0xff00 }

def reusedChecked : Checked := ⟨reusedCalls, by decide +kernel⟩
def nestedChecked : Checked := ⟨nestedCalls, by decide +kernel⟩

def certified (program : Program) : Bool :=
  match program.check with
  | .error _ => false
  | .ok checked => (Stream.encode checked).isOk

example : certified reusedCalls = true := by decide +kernel
example : certified nestedCalls = true := by decide +kernel
example : certified Examples.arithmeticProgram = true := by decide +kernel
example : certified Examples.runtimeProgram = true := by decide +kernel

example : (runFrom Runtime.rejecting reusedChecked 11 core).status = .halted 42 := by decide +kernel
example : (runFrom Runtime.rejecting nestedChecked 10 core).status = .halted 42 := by decide +kernel

-- A released slot stays masked after RET, and a later ordinary store clears
-- the bytes it overwrites. The mask never hides register differences.
example (holes : Stream.Holes) (address : Word) :
    ¬Stream.clearRange (Stream.addRange holes address 8) address 8 address := by
  intro hidden
  exact hidden.2 ⟨0, by decide, by simp⟩

example (program : Program) (base : Word) (memory : Memory) (frame : ReturnFrame)
    (mapped : Stream.FramesMapped program base memory [frame]) :
    Stream.SlotMapped program base memory frame := mapped frame (by simp)

theorem reused_safe : Stream.SafeTrace Runtime.rejecting reusedChecked 11 (fun _ => False)
    (Machine.initial reusedChecked core) := by
  decide +kernel

theorem nested_safe : Stream.SafeTrace Runtime.rejecting nestedChecked 10 (fun _ => False)
    (Machine.initial nestedChecked core) := by
  decide +kernel

end Ix.Compiler.X86.StreamExamples
