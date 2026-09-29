import Compilatrix.X86.ObjectExecution
import Compilatrix.X86.StreamDecidable
import Compilatrix.X86.EvalExamples

/-! Kernel checks and shared regression inputs for complete certified streams.
The call cases include nested frames and reuse of a released return slot. -/

namespace Compilatrix.X86.StreamExamples

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

/-! ## The failure exit (note 05 §6.1)

An export wrapper saves the callee-saved registers and its stack pointer
(`entrySp`, at `[r15 − 64]` with `r15 = rdi + 64`), then calls `depth`
nested functions; at depth 0 it fails before calling. The innermost fails
with status 1: `mov eax, 1` and the exit group's `unwind [r15 − 64]`, which
reloads the wrapper's stack pointer and drops every ghost frame above it.
The epilogue restores the caller's registers and returns `rax:rdx = 1:0`. -/

def entrySlot : MemAddr := { base := some .r15, displacement := 0xffffffc0 }

def wrapperPrologue : Array Instr :=
  #[.push .rbx, .push .rbp, .push .r12, .push .r13, .push .r14, .push .r15, .alu .sub .w64 .rsp (.imm 8),
    .lea .r15 { base := some .rdi, displacement := 64 }, .store .w64 entrySlot .rsp]

/-- Blocks 1–3 are the exit group: `fail₁`, the failure exit and the
epilogue. -/
def exitGroup : Array Block := #[
  { instructions := #[.mov .w32 .rax (.imm 1)], terminator := .jump 2 },
  { instructions := #[.unwind entrySlot, .alu .xor .w32 .rdx (.reg .rdx)], terminator := .jump 3 },
  { instructions := #[.alu .add .w64 .rsp (.imm 8), .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbp, .pop .rbx]
    terminator := .ret }]

def unwindCalls (depth : Nat) : Program :=
  let wrapper : Block :=
    if depth == 0 then { instructions := wrapperPrologue, terminator := .jump 1 }
    else { instructions := wrapperPrologue ++ #[.call 4, .mov .w64 .rdx (.reg .rax), .alu .xor .w32 .rax (.reg .rax)]
           terminator := .jump 3 }
  let functions : Array Block := (Array.range depth).map fun index =>
    if index + 1 == depth then { instructions := #[], terminator := .jump 1 }
    else { instructions := #[.push .rbp, .call (UInt32.ofNat (5 + index)), .pop .rbp], terminator := .ret }
  { entry := 0, blocks := #[wrapper] ++ exitGroup ++ functions }

def unwindChecked : Checked := ⟨unwindCalls 3, by decide +kernel⟩

example : certified (unwindCalls 3) = true := by decide +kernel

example : (runFrom Runtime.rejecting unwindChecked 40 core).status = .halted 1 := by decide +kernel

/-- Three nested calls fail through the exit group: every step meets the
concrete stack/data conditions, so `run_with_calls`, `SafeSteps` and
`ObjectEval.run_exit` apply to the failing run. -/
theorem unwind_safe : Stream.SafeTrace Runtime.rejecting unwindChecked 40 (fun _ => False)
    (Machine.initial unwindChecked core) := by
  decide +kernel

end Compilatrix.X86.StreamExamples
