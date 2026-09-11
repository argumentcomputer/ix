import Ix.Compiler.X86.WordRegionExecution
import Ix.Compiler.X86.SafeSteps

namespace Ix.Compiler.X86.WordRegion

theorem Effect.linear {layout : Layout} {instruction : Instr} {before after : State}
    (effect : Effect layout instruction before after) : Encode.linearInstruction instruction = true := by
  cases effect <;> rfl

theorem operationSafe_memory (instruction : Instr) (state : State) (memory : Memory)
    (holes : Stream.Holes) (returns : List ReturnFrame) :
    Stream.OperationSafe holes returns (Encode.instructionOperation instruction) (state.core memory) =
      Stream.OperationSafe holes returns (Encode.instructionOperation instruction) (state.core Memory.unmapped) := by
  cases instruction <;> rfl

theorem nextHoles_memory (instruction : Instr) (state : State) (memory : Memory) (holes : Stream.Holes) :
    Stream.nextHoles holes (Encode.instructionOperation instruction) (state.core memory) =
      Stream.nextHoles holes (Encode.instructionOperation instruction) (state.core Memory.unmapped) := by
  cases instruction <;> rfl

inductive SafeTrace (layout : Layout) (returns : List ReturnFrame) :
    List Instr → State → Stream.Holes → State → Stream.Holes → Prop where
  | nil (state : State) (holes : Stream.Holes) : SafeTrace layout returns [] state holes state holes
  | cons {instruction : Instr} {instructions : List Instr} {before middle after : State}
      {holes finalHoles : Stream.Holes}
      (effect : Effect layout instruction before middle)
      (access : Stream.OperationSafe holes returns (Encode.instructionOperation instruction) (before.core Memory.unmapped))
      (rest : SafeTrace layout returns instructions middle
        (Stream.nextHoles holes (Encode.instructionOperation instruction) (before.core Memory.unmapped)) after finalHoles) :
      SafeTrace layout returns (instruction :: instructions) before holes after finalHoles

theorem SafeTrace.append {layout : Layout} {returns : List ReturnFrame} {left right : List Instr}
    {before middle after : State} {holes middleHoles finalHoles : Stream.Holes}
    (first : SafeTrace layout returns left before holes middle middleHoles)
    (second : SafeTrace layout returns right middle middleHoles after finalHoles) :
    SafeTrace layout returns (left ++ right) before holes after finalHoles := by
  induction first with
  | nil => exact second
  | cons effect access rest ih => exact .cons effect access (ih second)

theorem SafeTrace.trace {layout : Layout} {returns : List ReturnFrame} {instructions : List Instr}
    {before after : State} {holes finalHoles : Stream.Holes}
    (safe : SafeTrace layout returns instructions before holes after finalHoles) :
    Trace layout instructions before after := by
  induction safe with
  | nil => exact .nil _
  | cons effect _ _ ih => exact .cons effect ih

theorem SafeTrace.steps {layout : Layout} {returns : List ReturnFrame} {instructions : List Instr}
    {before after : State} {holes finalHoles : Stream.Holes}
    (safe : SafeTrace layout returns instructions before holes after finalHoles)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (checked : Checked) (block : BlockId) (offset : Nat)
    (segment : Straight.Segment checked block offset instructions)
    (fits : offset + instructions.length < UInt32.size) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps runtime checked instructions.length holes (inFrame (before.core memory) block offset returns)
        finalHoles (inFrame (after.core nextMemory) block (offset + instructions.length) returns) := by
  induction safe generalizing memory offset with
  | nil state holes => exact ⟨memory, represented, Stream.SafeSteps.refl _ _⟩
  | @cons instruction instructions before middle after holes finalHoles effect access rest ih =>
      obtain ⟨nextMemory, nextView, executed⟩ := effect.sound outside memory represented
      obtain ⟨code, found, reads⟩ := segment
      have offsetBound : offset < UInt32.size := by simp only [List.length_cons] at fits; omega
      have head := reads 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero] at head
      have foundAt : checked.program.blocks[(inFrame (before.core memory) block offset returns).pc.block.toNat]? =
          some code := found
      have headAt : code.instructions[(inFrame (before.core memory) block offset returns).pc.offset.toNat]? =
          some instruction := by simpa only [inFrame, UInt32.toNat_ofNat_of_lt' offsetBound] using head
      have one : step runtime checked (inFrame (before.core memory) block offset returns) =
          inFrame (middle.core nextMemory) block (offset + 1) returns := by
        simp only [step, inFrame, UInt32.toNat_ofNat_of_lt' offsetBound, found, head]
        rw [executed runtime checked _ rfl]
        exact inFrame_advance _ _ _ _ (by simp only [List.length_cons] at fits; omega)
      have safeAt : Stream.SafeAt checked.program holes (inFrame (before.core memory) block offset returns) := by
        apply Stream.safeAt_linear foundAt headAt effect.linear
        exact (operationSafe_memory instruction before memory holes returns).symm ▸ access
      have changed := Stream.holeStep_linear (holes := holes) foundAt headAt effect.linear
      rw [show (inFrame (before.core memory) block offset returns).core = before.core memory from rfl,
        nextHoles_memory] at changed
      obtain ⟨finalMemory, finalView, remaining⟩ := ih nextMemory nextView (offset + 1)
        (Straight.Segment.tail ⟨code, found, reads⟩) (by simp only [List.length_cons] at fits; omega)
      refine ⟨finalMemory, finalView, ?_⟩
      rw [← changed] at remaining
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Stream.SafeSteps.cons safeAt one remaining

end Ix.Compiler.X86.WordRegion
