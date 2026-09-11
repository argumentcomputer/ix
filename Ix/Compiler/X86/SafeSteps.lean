import Ix.Compiler.X86.StreamTrace
import Ix.Compiler.X86.FrameCalls

namespace Ix.Compiler.X86.Stream

/-- Composable checked steps with the return-slot mask at both ends. These
steps imply the existing E2 safety predicate; no byte execution is assumed. -/
inductive SafeSteps (runtime : Runtime) (checked : Checked) :
    Nat → Holes → Machine → Holes → Machine → Prop where
  | refl (holes : Holes) (machine : Machine) : SafeSteps runtime checked 0 holes machine holes machine
  | cons {before middle after : Machine} {holes finalHoles : Holes} {count : Nat}
      (safe : SafeAt checked.program holes before)
      (first : step runtime checked before = middle)
      (rest : SafeSteps runtime checked count (holeStep checked.program before holes) middle finalHoles after) :
      SafeSteps runtime checked (count + 1) holes before finalHoles after

theorem SafeSteps.steps {runtime : Runtime} {checked : Checked} {count : Nat}
    {before after : Machine} {holes finalHoles : Holes}
    (safe : SafeSteps runtime checked count holes before finalHoles after) :
    Steps runtime checked count before after := by
  induction safe with
  | refl => exact .refl _
  | cons _ first _ ih => exact .cons first ih

theorem SafeSteps.safeTrace {runtime : Runtime} {checked : Checked} {count : Nat}
    {before after : Machine} {holes finalHoles : Holes}
    (safe : SafeSteps runtime checked count holes before finalHoles after) :
    SafeTrace runtime checked count holes before := by
  induction safe with
  | refl => trivial
  | @cons before middle after holes finalHoles count access first rest ih =>
      simp only [SafeTrace, first]
      refine ⟨access, ?_⟩
      cases middle.status <;> simp_all

theorem SafeSteps.append {runtime : Runtime} {checked : Checked} {first second : Nat}
    {before middle after : Machine} {holes middleHoles finalHoles : Holes}
    (left : SafeSteps runtime checked first holes before middleHoles middle)
    (right : SafeSteps runtime checked second middleHoles middle finalHoles after) :
    SafeSteps runtime checked (first + second) holes before finalHoles after := by
  induction left with
  | refl => simpa using right
  | cons access one rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using SafeSteps.cons access one (ih right)

theorem SafeSteps.single {runtime : Runtime} {checked : Checked}
    {before after : Machine} {holes : Holes}
    (safe : SafeAt checked.program holes before) (one : step runtime checked before = after) :
    SafeSteps runtime checked 1 holes before (holeStep checked.program before holes) after :=
  .cons safe one (.refl _ _)

theorem safeAt_linear {program : Program} {machine : Machine} {holes : Holes}
    {block : Block} {instruction : Instr}
    (found : program.blocks[machine.pc.block.toNat]? = some block)
    (located : block.instructions[machine.pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true)
    (access : OperationSafe holes machine.returns (Encode.instructionOperation instruction) machine.core) :
    SafeAt program holes machine := by
  cases instruction <;> simp_all [SafeAt, Encode.linearInstruction]

theorem holeStep_linear {program : Program} {machine : Machine} {holes : Holes}
    {block : Block} {instruction : Instr}
    (found : program.blocks[machine.pc.block.toNat]? = some block)
    (located : block.instructions[machine.pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true) :
    holeStep program machine holes = nextHoles holes (Encode.instructionOperation instruction) machine.core := by
  cases instruction <;> simp_all [holeStep, Encode.linearInstruction]

end Ix.Compiler.X86.Stream
