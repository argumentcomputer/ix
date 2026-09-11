import Ix.Compiler.X86.Execution
import Ix.Compiler.X86.UniqueTarget

/-! Word views of native instruction effects. Every load/store supplies an
in-bounds arena slot and an equality to the actual effective address. The
soundness theorem reconstructs execution over the existing byte memory. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI

structure State where
  registers : Registers
  words : Words

theorem State.ext {left right : State} (registers : left.registers = right.registers)
    (words : left.words = right.words) : left = right := by
  cases left
  cases right
  cases registers
  cases words
  rfl

def State.core (state : State) (memory : Memory) : Core := ⟨state.registers, memory⟩
def State.setReg (state : State) (register : GPR) (value : Word) : State :=
  { state with registers := state.registers.set register value }
def State.setWord (state : State) (slot : Nat) (value : Word) : State :=
  { state with words := state.words.set slot value }
def State.address (state : State) (address : MemAddr) : Word := address.eval (state.core Memory.unmapped)
def State.move (state : State) (source : MoveSource) : Word := source.eval (state.core Memory.unmapped)
def State.alu (state : State) (source : AluSource) : Word := source.eval (state.core Memory.unmapped)

@[simp] theorem State.address_core (state : State) (memory : Memory) (address : MemAddr) :
    address.eval (state.core memory) = state.address address := rfl
@[simp] theorem State.move_core (state : State) (memory : Memory) (source : MoveSource) :
    source.eval (state.core memory) = state.move source := by cases source <;> rfl
@[simp] theorem State.alu_core (state : State) (memory : Memory) (source : AluSource) :
    source.eval (state.core memory) = state.alu source := by cases source <;> rfl

inductive Effect (layout : Layout) : Instr → State → State → Prop where
  | mov (state : State) (destination : GPR) (source : MoveSource) :
      Effect layout (.mov .w64 destination source) state (state.setReg destination (state.move source))
  | lea (state : State) (destination : GPR) (source : MemAddr) :
      Effect layout (.lea destination source) state (state.setReg destination (state.address source))
  | alu (state : State) (operation : AluOp) (destination : GPR) (source : AluSource) :
      Effect layout (.alu operation .w64 destination source) state
        (state.setReg destination (operation.eval (state.registers destination) (state.alu source)))
  | load (state : State) (destination : GPR) (source : MemAddr) (slot : Nat)
      (bound : slot < layout.slots) (address : state.address source = layout.address slot) :
      Effect layout (.load .w64 destination source) state (state.setReg destination (state.words slot))
  | store (state : State) (destination : MemAddr) (source : GPR) (slot : Nat)
      (bound : slot < layout.slots) (address : state.address destination = layout.address slot) :
      Effect layout (.store .w64 destination source) state (state.setWord slot (state.registers source))

inductive Trace (layout : Layout) : List Instr → State → State → Prop where
  | nil (state) : Trace layout [] state state
  | cons {instruction : Instr} {instructions : List Instr} {before middle after : State}
      (first : Effect layout instruction before middle) (rest : Trace layout instructions middle after) :
      Trace layout (instruction :: instructions) before after

theorem Trace.append {layout : Layout} {left right : List Instr} {before middle after : State}
    (first : Trace layout left before middle) (second : Trace layout right middle after) :
    Trace layout (left ++ right) before after := by
  induction first with
  | nil => exact second
  | cons first rest ih => exact .cons first (ih second)

theorem Effect.sound {layout : Layout} {instruction : Instr} {before after : State}
    (effect : Effect layout instruction before after) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Straight.Effect instruction (before.core memory) (after.core nextMemory) := by
  cases effect with
  | mov _ destination source =>
      refine ⟨memory, represented, ?_⟩
      have effect := Straight.Effect.mov (before.core memory) destination source
      rw [State.move_core] at effect
      simpa [State.core, State.setReg, Core.setReg] using effect
  | lea _ destination source =>
      refine ⟨memory, represented, ?_⟩
      have effect := Straight.Effect.lea (before.core memory) destination source
      rw [State.address_core] at effect
      simpa [State.core, State.setReg, Core.setReg] using effect
  | alu _ operation destination source =>
      refine ⟨memory, represented, ?_⟩
      have effect := Straight.Effect.alu (before.core memory) operation destination source
      rw [State.alu_core] at effect
      simpa [State.core, State.setReg, Core.setReg, Core.readReg] using effect
  | load _ destination source slot bound address =>
      refine ⟨memory, represented, ?_⟩
      have allowed : Memory.rangeAllowed memory.readable (source.eval (before.core memory)) 8 = true := by
        rw [State.address_core, address]; exact represented.readable slot bound
      have loaded : memory.read64 (source.eval (before.core memory)) = before.words slot := by
        rw [State.address_core, address]; exact represented.view slot bound
      exact
        Straight.Effect.load (before.core memory) destination source (before.words slot) allowed loaded
  | store _ destination source slot bound address =>
      refine ⟨memory.write64 (layout.address slot) (before.registers source), represented.write64 bound _, ?_⟩
      have allowed : Memory.rangeAllowed memory.writable (destination.eval (before.core memory)) 8 = true := by
        rw [State.address_core, address]; exact represented.writable slot bound
      have stored := Straight.Effect.store (before.core memory) destination source allowed
      rw [State.address_core, address] at stored
      simpa [State.core, State.setWord, Core.readReg] using stored

theorem Trace.sound {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Straight.Sequence instructions (before.core memory) (after.core nextMemory) := by
  induction trace generalizing memory with
  | nil state => exact ⟨memory, represented, .nil _⟩
  | cons first rest ih =>
      obtain ⟨middle, middleView, one⟩ := first.sound outside memory represented
      obtain ⟨finalMemory, finalView, following⟩ := ih middle middleView
      exact ⟨finalMemory, finalView, .cons one following⟩

theorem Trace.steps {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block : BlockId) (offset : Nat) (segment : Straight.Segment checked block offset instructions)
    (fits : offset + instructions.length < UInt32.size) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Steps runtime checked instructions.length (leaf (before.core memory) block offset)
        (leaf (after.core nextMemory) block (offset + instructions.length)) := by
  obtain ⟨nextMemory, finalView, sequence⟩ := trace.sound outside memory represented
  exact ⟨nextMemory, finalView, sequence.steps runtime checked block offset segment fits⟩

end Ix.Compiler.X86.UniqueExecution
