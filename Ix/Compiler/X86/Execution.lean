import Ix.Compiler.X86.Memory

/-! Finite execution and straight-line composition for the existing typed
x86 evaluator. Instruction effects below are propositions about `executeInstr`;
there is no additional instruction interpreter or runtime assumption. -/

namespace Ix.Compiler.X86

theorem run_of_not_running (runtime : Runtime) (checked : Checked) (fuel : Nat)
    (machine : Machine) (finished : machine.status ≠ .running) :
    run runtime checked fuel machine = machine := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [run, step_of_not_running _ _ _ finished]
      cases status : machine.status with
      | running => exact False.elim (finished status)
      | halted result => rfl
      | trapped fault => rfl

theorem run_succ (runtime : Runtime) (checked : Checked) (fuel : Nat) (machine : Machine) :
    run runtime checked (fuel + 1) machine = run runtime checked fuel (step runtime checked machine) := by
  rw [run]
  cases status : (step runtime checked machine).status with
  | running => rfl
  | halted result => exact (run_of_not_running _ _ _ _ (by simp [status])).symm
  | trapped fault => exact (run_of_not_running _ _ _ _ (by simp [status])).symm

theorem run_add (runtime : Runtime) (checked : Checked) (first second : Nat) (machine : Machine) :
    run runtime checked (first + second) machine =
      run runtime checked second (run runtime checked first machine) := by
  induction first generalizing machine with
  | zero => simp [run]
  | succ first ih =>
      rw [Nat.succ_add, run_succ, run_succ, ih]

/-- A terminating run has no trapped prefix, since faults are absorbing in
the existing evaluator. This includes memory and ABI contract faults. -/
theorem run_prefix_not_trapped {runtime : Runtime} {checked : Checked} {count : Nat}
    {before after : Machine} {result : Word}
    (execution : run runtime checked count before = after) (halted : after.status = .halted result)
    (prefixCount : Nat) (bound : prefixCount ≤ count) (fault : Trap) :
    (run runtime checked prefixCount before).status ≠ .trapped fault := by
  intro trapped
  have split : count = prefixCount + (count - prefixCount) := by omega
  rw [split, run_add] at execution
  rw [run_of_not_running _ _ _ _ (by simp [trapped])] at execution
  rw [← execution, trapped] at halted
  contradiction

inductive Steps (runtime : Runtime) (checked : Checked) : Nat → Machine → Machine → Prop where
  | refl (machine) : Steps runtime checked 0 machine machine
  | cons {before middle after : Machine} {count : Nat}
      (first : step runtime checked before = middle)
      (rest : Steps runtime checked count middle after) : Steps runtime checked (count + 1) before after

theorem Steps.append {runtime : Runtime} {checked : Checked} {first second : Nat}
    {before middle after : Machine} (left : Steps runtime checked first before middle)
    (right : Steps runtime checked second middle after) :
    Steps runtime checked (first + second) before after := by
  induction left with
  | refl => simpa using right
  | cons one rest ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons one (ih right)

theorem Steps.run_eq {runtime : Runtime} {checked : Checked} {count : Nat}
    {before after : Machine} (steps : Steps runtime checked count before after) :
    run runtime checked count before = after := by
  induction steps with
  | refl => rfl
  | cons first rest ih => rw [run_succ, first, ih]

theorem Steps.single {runtime : Runtime} {checked : Checked} {before after : Machine}
    (one : step runtime checked before = after) : Steps runtime checked 1 before after :=
  .cons one (.refl after)

/-- A running leaf state at a natural-number instruction offset. -/
def leaf (core : Core) (block : BlockId) (offset : Nat) : Machine :=
  { core, pc := { block, offset := UInt32.ofNat offset }, returns := [], status := .running }

def haltedLeaf (core : Core) (block : BlockId) (offset : Nat) : Machine :=
  { leaf core block offset with status := .halted (core.readReg .rax) }

/-- Lookup evidence for a complete emitted block, including a nonwrapping PC. -/
structure BlockCode (checked : Checked) (block : BlockId) (instructions : List Instr)
    (terminator : Terminator) : Prop where
  found : checked.program.blocks[block.toNat]? =
    some { instructions := instructions.toArray, terminator }
  fits : instructions.length < UInt32.size

theorem BlockCode.terminator {checked : Checked} {block : BlockId} {instructions : List Instr}
    {terminator : Terminator} (code : BlockCode checked block instructions terminator)
    (runtime : Runtime) (core : Core) :
    step runtime checked (leaf core block instructions.length) =
      executeTerminator checked terminator (leaf core block instructions.length) := by
  simp [step, leaf, UInt32.toNat_ofNat_of_lt' code.fits, code.found]

theorem BlockCode.jump {checked : Checked} {block target : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions (.jump target))
    (valid : checked.program.hasBlock target = true) (runtime : Runtime) (core : Core) :
    step runtime checked (leaf core block instructions.length) = leaf core target 0 := by
  rw [code.terminator]
  simp [executeTerminator, Machine.goto, valid, leaf]

theorem BlockCode.branch {checked : Checked} {block yes no : BlockId} {instructions : List Instr}
    {comparison : Compare} {condition : Condition}
    (code : BlockCode checked block instructions (.branch comparison condition yes no))
    (runtime : Runtime) (core : Core) (answer : Bool)
    (holds : comparison.holds condition core = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    step runtime checked (leaf core block instructions.length) =
      leaf core (if answer then yes else no) 0 := by
  rw [code.terminator]
  simp [executeTerminator, leaf, holds, Machine.goto, valid]

theorem BlockCode.ret {checked : Checked} {block : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions .ret) (runtime : Runtime) (core : Core) :
    step runtime checked (leaf core block instructions.length) = haltedLeaf core block instructions.length := by
  rw [code.terminator]
  rfl

theorem leaf_advance (core after : Core) (block : BlockId) {offset : Nat}
    (fits : offset + 1 < UInt32.size) :
    (leaf core block offset).advanceWith after = leaf after block (offset + 1) := by
  have notLast : UInt32.ofNat offset ≠ 0xffffffff := by
    intro equal
    have equal := congrArg UInt32.toNat equal
    rw [UInt32.toNat_ofNat_of_lt' (by omega)] at equal
    change offset = 4294967295 at equal
    simp only [UInt32.size] at fits
    omega
  simp [leaf, Machine.advanceWith, PC.next?, notLast, UInt32.ofNat_add]

namespace Straight

/-- A non-control instruction's effect, stated in the existing evaluator. -/
def Effect (instruction : Instr) (before after : Core) : Prop :=
  ∀ (runtime : Runtime) (checked : Checked) (machine : Machine), machine.core = before →
    executeInstr runtime checked instruction machine = machine.advanceWith after

inductive Sequence : List Instr → Core → Core → Prop where
  | nil (core) : Sequence [] core core
  | cons {instruction : Instr} {instructions : List Instr} {before middle after : Core}
      (first : Effect instruction before middle) (rest : Sequence instructions middle after) :
      Sequence (instruction :: instructions) before after

theorem Sequence.append {left right : List Instr} {before middle after : Core}
    (first : Sequence left before middle) (second : Sequence right middle after) :
    Sequence (left ++ right) before after := by
  induction first with
  | nil => exact second
  | cons first rest ih => exact .cons first (ih second)

theorem Effect.mov (core : Core) (destination : GPR) (source : MoveSource) :
    Effect (.mov .w64 destination source) core (core.setReg destination (source.eval core)) := by
  intro runtime checked machine equal
  simp [executeInstr, equal, Core.writeReg]

theorem Effect.lea (core : Core) (destination : GPR) (source : MemAddr) :
    Effect (.lea destination source) core (core.setReg destination (source.eval core)) := by
  intro runtime checked machine equal
  simp [executeInstr, equal]

theorem Effect.alu (core : Core) (operation : AluOp) (destination : GPR) (source : AluSource) :
    Effect (.alu operation .w64 destination source) core
      (core.setReg destination (operation.eval (core.readReg destination) (source.eval core))) := by
  intro runtime checked machine equal
  simp [executeInstr, equal, Core.writeReg]

@[simp] theorem truncate_w64 (value : Word) : Width.truncate .w64 value = value := by
  apply UInt64.toBitVec_inj.mp
  change value.toBitVec &&& BitVec.allOnes 64 = value.toBitVec
  exact BitVec.and_allOnes

theorem Effect.load (core : Core) (destination : GPR) (source : MemAddr) (value : Word)
    (allowed : Memory.rangeAllowed core.memory.readable (source.eval core) 8 = true)
    (loaded : core.memory.read64 (source.eval core) = value) :
    Effect (.load .w64 destination source) core (core.setReg destination value) := by
  intro runtime checked machine equal
  change core.memory.read .w64 (source.eval core) = value at loaded
  simp [executeInstr, equal, Core.loadReg?, Memory.read?, Width.bytes, allowed,
    loaded] <;> rfl

theorem Effect.store (core : Core) (destination : MemAddr) (source : GPR)
    (allowed : Memory.rangeAllowed core.memory.writable (destination.eval core) 8 = true) :
    Effect (.store .w64 destination source) core
      { core with memory := core.memory.write64 (destination.eval core) (core.readReg source) } := by
  intro runtime checked machine equal
  simp [executeInstr, equal, Core.storeReg?, Memory.write?, Width.bytes, allowed, Memory.write64] <;> rfl

/-- Consecutive instruction lookup, independent of any prefix/suffix syntax. -/
def Segment (checked : Checked) (block : BlockId) (offset : Nat) (instructions : List Instr) : Prop :=
  ∃ code, checked.program.blocks[block.toNat]? = some code ∧
    ∀ i < instructions.length, code.instructions[offset + i]? = instructions[i]?

theorem _root_.Ix.Compiler.X86.BlockCode.segment {checked : Checked} {block : BlockId}
    {instructions : List Instr} {terminator : Terminator}
    (code : BlockCode checked block instructions terminator) : Segment checked block 0 instructions := by
  refine ⟨_, code.found, ?_⟩
  intro i bound
  simp

theorem Segment.tail {checked : Checked} {block : BlockId} {offset : Nat}
    {instruction : Instr} {instructions : List Instr}
    (segment : Segment checked block offset (instruction :: instructions)) :
    Segment checked block (offset + 1) instructions := by
  obtain ⟨code, found, reads⟩ := segment
  refine ⟨code, found, ?_⟩
  intro i bound
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reads (i + 1) (by simpa using bound)

theorem Sequence.steps {instructions : List Instr} {before after : Core}
    (sequence : Sequence instructions before after) (runtime : Runtime) (checked : Checked)
    (block : BlockId) (offset : Nat) (segment : Segment checked block offset instructions)
    (fits : offset + instructions.length < UInt32.size) :
    Steps runtime checked instructions.length (leaf before block offset)
      (leaf after block (offset + instructions.length)) := by
  induction sequence generalizing offset with
  | nil core => simpa using Steps.refl (runtime := runtime) (checked := checked) (leaf core block offset)
  | @cons instruction instructions before middle after first rest ih =>
      obtain ⟨code, found, reads⟩ := segment
      have offsetBound : offset < UInt32.size := by simp only [List.length_cons] at fits; omega
      have head := reads 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero] at head
      have one : step runtime checked (leaf before block offset) = leaf middle block (offset + 1) := by
        simp only [step, leaf, UInt32.toNat_ofNat_of_lt' offsetBound, found, head]
        rw [first runtime checked _ rfl]
        exact leaf_advance _ _ _ (by simp only [List.length_cons] at fits; omega)
      have next := ih (offset + 1) (Segment.tail ⟨code, found, reads⟩) (by
        simp only [List.length_cons] at fits
        omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons one next

end Straight
end Ix.Compiler.X86
