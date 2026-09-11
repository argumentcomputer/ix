import Ix.Compiler.X86.WordRegion
import Ix.Compiler.X86.FrameExecution

namespace Ix.Compiler.X86.WordRegion

structure State where
  registers : Registers
  words : Words

def State.core (state : State) (memory : Memory) : Core := ⟨state.registers, memory⟩
def State.setReg (state : State) (register : GPR) (value : Word) : State :=
  { state with registers := state.registers.set register value }
def State.setWord (state : State) (slot : Nat) (value : Word) : State :=
  { state with words := state.words.set slot value }
def State.move (state : State) (source : MoveSource) : Word := source.eval (state.core Memory.unmapped)
def State.alu (state : State) (source : AluSource) : Word := source.eval (state.core Memory.unmapped)

@[simp] theorem State.move_core (state : State) (memory : Memory) (source : MoveSource) :
    source.eval (state.core memory) = state.move source := by cases source <;> rfl
@[simp] theorem State.alu_core (state : State) (memory : Memory) (source : AluSource) :
    source.eval (state.core memory) = state.alu source := by cases source <;> rfl
@[simp] theorem State.setReg_registers (state : State) (register candidate : GPR) (value : Word) :
    (state.setReg register value).registers candidate =
      if candidate == register then value else state.registers candidate := rfl
@[simp] theorem State.setWord_registers (state : State) (slot : Nat) (value : Word) :
    (state.setWord slot value).registers = state.registers := rfl
@[simp] theorem State.setReg_words (state : State) (register : GPR) (value : Word) :
    (state.setReg register value).words = state.words := rfl
@[simp] theorem State.setWord_words (state : State) (slot : Nat) (value : Word) :
    (state.setWord slot value).words = state.words.set slot value := rfl
@[simp] theorem State.move_imm (state : State) (value : Word) : state.move (.imm value) = value := rfl
@[simp] theorem State.move_reg (state : State) (register : GPR) :
    state.move (.reg register) = state.registers register := rfl
@[simp] theorem State.alu_reg (state : State) (register : GPR) :
    state.alu (.reg register) = state.registers register := rfl

@[simp] theorem State.setReg_setReg (state : State) (register : GPR) (first second : Word) :
    (state.setReg register first).setReg register second = state.setReg register second := by
  simp [State.setReg]

/-- Each memory effect supplies its finite slot and actual effective address. -/
inductive Effect (layout : Layout) : Instr → State → State → Prop where
  | mov (state : State) (destination : GPR) (source : MoveSource) :
      Effect layout (.mov .w64 destination source) state (state.setReg destination (state.move source))
  | alu (state : State) (operation : AluOp) (destination : GPR) (source : AluSource) :
      Effect layout (.alu operation .w64 destination source) state
        (state.setReg destination (operation.eval (state.registers destination) (state.alu source)))
  | push (state : State) (source : GPR) (slot : Nat) (bound : slot < layout.slots)
      (address : state.registers .rsp - 8 = layout.address slot) :
      Effect layout (.push source) state
        ((state.setReg .rsp (layout.address slot)).setWord slot (state.registers source))
  | pop (state : State) (destination : GPR) (slot : Nat) (bound : slot < layout.slots)
      (address : state.registers .rsp = layout.address slot) :
      Effect layout (.pop destination) state
        ((state.setReg .rsp (layout.address slot + 8)).setReg destination (state.words slot))
  | allocFrame (state : State) (size : FrameSize) :
      Effect layout (.allocFrame size) state (state.setReg .rsp (state.registers .rsp - size.bytes))
  | freeFrame (state : State) (size : FrameSize) :
      Effect layout (.freeFrame size) state (state.setReg .rsp (state.registers .rsp + size.bytes))
  | spill (state : State) (destination : StackSlot) (source : GPR) (slot : Nat)
      (bound : slot < layout.slots)
      (address : state.registers .rbp - destination.displacement = layout.address slot) :
      Effect layout (.spill destination source) state (state.setWord slot (state.registers source))
  | reload (state : State) (destination : GPR) (source : StackSlot) (slot : Nat)
      (bound : slot < layout.slots)
      (address : state.registers .rbp - source.displacement = layout.address slot) :
      Effect layout (.reload destination source) state (state.setReg destination (state.words slot))

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
      exact effect
  | alu _ operation destination source =>
      refine ⟨memory, represented, ?_⟩
      have effect := Straight.Effect.alu (before.core memory) operation destination source
      rw [State.alu_core] at effect
      exact effect
  | push _ source slot bound address =>
      refine ⟨memory.write64 (layout.address slot) (before.registers source), represented.write64 bound _, ?_⟩
      have allowed : Memory.rangeAllowed memory.writable (before.registers .rsp - 8) 8 = true :=
        address ▸ represented.writable slot bound
      have effect := Straight.Effect.push (before.core memory) source allowed
      simpa only [State.core, Core.readReg, State.setReg, State.setWord, Core.setReg, address] using effect
  | pop _ destination slot bound address =>
      refine ⟨memory, represented, ?_⟩
      have allowed : Memory.rangeAllowed memory.readable (before.registers .rsp) 8 = true :=
        address ▸ represented.readable slot bound
      have loaded : memory.read64 (before.registers .rsp) = before.words slot :=
        address ▸ represented.view slot bound
      have effect := Straight.Effect.pop (before.core memory) destination (before.words slot) allowed loaded
      simpa only [State.core, Core.readReg, State.setReg, Core.setReg, address] using effect
  | allocFrame _ size => exact ⟨memory, represented, Straight.Effect.allocFrame _ size⟩
  | freeFrame _ size => exact ⟨memory, represented, Straight.Effect.freeFrame _ size⟩
  | spill _ destination source slot bound address =>
      refine ⟨memory.write64 (layout.address slot) (before.registers source), represented.write64 bound _, ?_⟩
      have allowed : Memory.rangeAllowed memory.writable (before.registers .rbp - destination.displacement) 8 = true :=
        address ▸ represented.writable slot bound
      have effect := Straight.Effect.spill (before.core memory) destination source allowed
      simpa only [State.core, Core.readReg, State.setWord, address] using effect
  | reload _ destination source slot bound address =>
      refine ⟨memory, represented, ?_⟩
      have allowed : Memory.rangeAllowed memory.readable (before.registers .rbp - source.displacement) 8 = true :=
        address ▸ represented.readable slot bound
      have loaded : memory.read64 (before.registers .rbp - source.displacement) = before.words slot :=
        address ▸ represented.view slot bound
      have effect := Straight.Effect.reload (before.core memory) destination source (before.words slot) allowed loaded
      exact effect

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
    (block : BlockId) (offset : Nat) (returns : List ReturnFrame)
    (segment : Straight.Segment checked block offset instructions)
    (fits : offset + instructions.length < UInt32.size) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Steps runtime checked instructions.length (inFrame (before.core memory) block offset returns)
        (inFrame (after.core nextMemory) block (offset + instructions.length) returns) := by
  obtain ⟨nextMemory, finalView, sequence⟩ := trace.sound outside memory represented
  exact ⟨nextMemory, finalView, sequence.steps_inFrame runtime checked block offset returns segment fits⟩

end Ix.Compiler.X86.WordRegion
