import Compilatrix.X86.RuntimeInspect
import Compilatrix.X86.SafeControl

/-! Heap instruction traces remain safe in the presence of native return
slots. Every heap read avoids the byte-address mask, and every heap write
avoids all active return frames. The allocator's existing word-level traces
therefore compose with CALL/RET and the certified ELF execution theorem. -/

namespace Compilatrix.X86.UniqueExecution
open UniqueABI

structure HeapAccess (layout : Layout) (holes : Stream.Holes) (returns : List ReturnFrame) : Prop where
  reads : ∀ slot < layout.slots, Stream.ReadableData holes (layout.address slot) 8
  writes : ∀ slot < layout.slots, Stream.FramesDisjoint returns (layout.address slot) 8

theorem HeapAccess.empty (layout : Layout) : HeapAccess layout (fun _ => False) [] :=
  ⟨fun _ _ _ _ => id, by simp [Stream.FramesDisjoint]⟩

theorem clearRange_unchanged {holes : Stream.Holes} {address : Word} {count : Nat}
    (clean : Stream.ReadableData holes address count) : Stream.clearRange holes address count = holes := by
  funext candidate
  apply propext
  constructor
  · exact And.left
  · intro hidden
    refine ⟨hidden, ?_⟩
    rintro ⟨offset, bound, rfl⟩
    exact clean offset bound hidden

@[simp] theorem State.address_normalized (state : State) (address : MemAddr) :
    state.address (Encode.normalizedAddress address) = state.address address :=
  Encode.normalizedAddress_eval address (state.core Memory.unmapped)

theorem Effect.safe {layout : Layout} {instruction : Instr} {before after : State}
    (effect : Effect layout instruction before after) {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : HeapAccess layout holes returns) (memory : Memory) :
    Encode.linearInstruction instruction = true ∧
      Stream.OperationSafe holes returns (Encode.instructionOperation instruction) (before.core memory) ∧
      Stream.nextHoles holes (Encode.instructionOperation instruction) (before.core memory) = holes := by
  cases effect with
  | mov | lea | alu => simp [Encode.linearInstruction, Encode.instructionOperation, Stream.OperationSafe,
      Stream.operationReads, Stream.operationWrites, Stream.nextHoles]
  | load _ _ _ slot bound address =>
      simpa [Encode.linearInstruction, Encode.instructionOperation, Stream.OperationSafe, Stream.operationReads,
        Stream.operationWrites, Stream.nextHoles, State.address_core, address, Width.bytes] using access.reads slot bound
  | store _ _ _ slot bound address =>
      simpa [Encode.linearInstruction, Encode.instructionOperation, Stream.OperationSafe, Stream.operationReads,
        Stream.operationWrites, Stream.nextHoles, State.address_core, address, Width.bytes] using
        And.intro (access.writes slot bound) (clearRange_unchanged (access.reads slot bound))

theorem Trace.safeSteps {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : HeapAccess layout holes returns) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block : BlockId) (offset : Nat) (segment : Straight.Segment checked block offset instructions)
    (fits : offset + instructions.length < UInt32.size) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps runtime checked instructions.length holes (inFrame (before.core memory) block offset returns)
        holes (inFrame (after.core nextMemory) block (offset + instructions.length) returns) := by
  induction trace generalizing memory offset with
  | nil state => exact ⟨memory, represented, Stream.SafeSteps.refl _ _⟩
  | @cons instruction instructions before middle after effect rest ih =>
      obtain ⟨nextMemory, nextView, executed⟩ := effect.sound outside memory represented
      obtain ⟨code, found, reads⟩ := segment
      have offsetBound : offset < UInt32.size := by simp only [List.length_cons] at fits; omega
      have head := reads 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero] at head
      have foundAt : checked.program.blocks[(inFrame (before.core memory) block offset returns).pc.block.toNat]? = some code := found
      have headAt : code.instructions[(inFrame (before.core memory) block offset returns).pc.offset.toNat]? = some instruction := by
        simpa only [inFrame, UInt32.toNat_ofNat_of_lt' offsetBound] using head
      have one : step runtime checked (inFrame (before.core memory) block offset returns) =
          inFrame (middle.core nextMemory) block (offset + 1) returns := by
        simp only [step, inFrame, UInt32.toNat_ofNat_of_lt' offsetBound, found, head]
        rw [executed runtime checked _ rfl]
        exact inFrame_advance _ _ _ _ (by simp only [List.length_cons] at fits; omega)
      have safe := effect.safe access memory
      have safeAt := Stream.safeAt_linear foundAt headAt safe.1 safe.2.1
      have changed := (Stream.holeStep_linear (holes := holes) foundAt headAt safe.1).trans safe.2.2
      obtain ⟨finalMemory, finalView, remaining⟩ := ih nextMemory nextView (offset + 1)
        (Straight.Segment.tail ⟨code, found, reads⟩) (by simp only [List.length_cons] at fits; omega)
      refine ⟨finalMemory, finalView, ?_⟩
      have remaining' : Stream.SafeSteps runtime checked instructions.length
          (Stream.holeStep checked.program (inFrame (before.core memory) block offset returns) holes)
          (inFrame (middle.core nextMemory) block (offset + 1) returns)
          holes (inFrame (after.core finalMemory) block (offset + 1 + instructions.length) returns) := by
        rw [changed]
        exact remaining
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Stream.SafeSteps.cons safeAt one remaining'

theorem Trace.safeSteps_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    {holes : Stream.Holes} {returns : List ReturnFrame} (access : HeapAccess layout holes returns)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (checked : Checked) (block : BlockId) (offset : Nat)
    (segment : Straight.Segment checked block offset instructions) (fits : offset + instructions.length < UInt32.size) :
    Stream.SafeSteps runtime checked instructions.length holes (inFrame (before.core memory) block offset returns)
      holes (inFrame (after.core memory) block (offset + instructions.length) returns) := by
  obtain ⟨nextMemory, _, safe⟩ := trace.safeSteps access outside memory represented runtime checked block offset segment fits
  have ordinary := (trace.sound_readOnly readonly outside memory represented).steps_inFrame
    runtime checked block offset returns segment fits
  have same : nextMemory = memory := congrArg (fun machine => machine.core.memory)
    (safe.steps.run_eq.symm.trans ordinary.run_eq)
  simpa [same] using safe

theorem Trace.safeJump {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : HeapAccess layout holes returns) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block target : BlockId) (code : BlockCode checked block instructions (.jump target))
    (valid : checked.program.hasBlock target = true) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps runtime checked (instructions.length + 1) holes (inFrame (before.core memory) block 0 returns)
        holes (inFrame (after.core nextMemory) target 0 returns) := by
  obtain ⟨nextMemory, view, first⟩ := trace.safeSteps access outside memory represented runtime checked block 0 code.segment
    (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact ⟨nextMemory, view, first.append (code.safe_jump valid runtime _ returns holes)⟩

theorem Trace.safeBranch {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : HeapAccess layout holes returns) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block yes no : BlockId) (comparison : Compare) (condition : Condition)
    (code : BlockCode checked block instructions (.branch comparison condition yes no)) (answer : Bool)
    (holds : comparison.holds condition (after.core Memory.unmapped) = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps runtime checked (instructions.length + 1) holes (inFrame (before.core memory) block 0 returns)
        holes (inFrame (after.core nextMemory) (if answer then yes else no) 0 returns) := by
  obtain ⟨nextMemory, view, first⟩ := trace.safeSteps access outside memory represented runtime checked block 0 code.segment
    (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact ⟨nextMemory, view, first.append (code.safe_branch runtime _ returns holes answer
    ((after.compare_core nextMemory comparison condition).trans holds) valid)⟩

theorem Trace.safeBranch_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    {holes : Stream.Holes} {returns : List ReturnFrame} (access : HeapAccess layout holes returns)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (checked : Checked) (block yes no : BlockId) (comparison : Compare) (condition : Condition)
    (code : BlockCode checked block instructions (.branch comparison condition yes no)) (answer : Bool)
    (holds : comparison.holds condition (after.core Memory.unmapped) = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    Stream.SafeSteps runtime checked (instructions.length + 1) holes (inFrame (before.core memory) block 0 returns)
      holes (inFrame (after.core memory) (if answer then yes else no) 0 returns) := by
  have first := trace.safeSteps_readOnly readonly access outside memory represented runtime checked block 0 code.segment
    (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact first.append (code.safe_branch runtime _ returns holes answer ((after.compare_core memory comparison condition).trans holds) valid)

theorem Trace.safeJump_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    {holes : Stream.Holes} {returns : List ReturnFrame} (access : HeapAccess layout holes returns)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (checked : Checked) (block target : BlockId)
    (code : BlockCode checked block instructions (.jump target)) (valid : checked.program.hasBlock target = true) :
    Stream.SafeSteps runtime checked (instructions.length + 1) holes (inFrame (before.core memory) block 0 returns)
      holes (inFrame (after.core memory) target 0 returns) := by
  have first := trace.safeSteps_readOnly readonly access outside memory represented runtime checked block 0 code.segment
    (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact first.append (code.safe_jump valid runtime _ returns holes)

theorem _root_.Compilatrix.X86.BlockCode.safe_halt {checked : Checked} {block : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions .ret) (runtime : Runtime) (core : Core) (holes : Stream.Holes)
    (returnSlot : Stream.ReadableData holes (core.readReg .rsp) 8) :
    Stream.SafeSteps runtime checked 1 holes (leaf core block instructions.length)
      holes (haltedLeaf core block instructions.length) := by
  have safe : Stream.SafeAt checked.program holes (leaf core block instructions.length) := by
    simpa [Stream.SafeAt, leaf, UInt32.toNat_ofNat_of_lt' code.fits, code.found] using returnSlot
  have one := Stream.SafeSteps.single safe (code.ret runtime core)
  simpa only [show leaf core block instructions.length = inFrame core block instructions.length [] from rfl,
    code.holeStep] using one

theorem Trace.safeHalt {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) {holes : Stream.Holes}
    (access : HeapAccess layout holes []) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block : BlockId) (code : BlockCode checked block instructions .ret)
    (returnSlot : Stream.ReadableData holes (after.registers .rsp) 8) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps runtime checked (instructions.length + 1) holes (leaf (before.core memory) block 0)
        holes (haltedLeaf (after.core nextMemory) block instructions.length) := by
  obtain ⟨nextMemory, view, first⟩ := trace.safeSteps access outside memory represented runtime checked block 0 code.segment
    (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact ⟨nextMemory, view, first.append (code.safe_halt runtime _ holes returnSlot)⟩

end Compilatrix.X86.UniqueExecution
