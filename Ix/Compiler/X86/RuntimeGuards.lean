import Ix.Compiler.X86.RuntimeInspect
import Ix.Compiler.X86.UniqueMain

namespace Ix.Compiler.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution RuntimeTarget

variable {foldCounters : Bool}

structure Input (layout : Layout) (values : List Word) (state : State) : Prop where
  chain : DownChain layout state.words values
  counts : CountsAt layout (readyCounts (values.length + 1)) state.words
  context : state.registers .rdi = layout.base
  length : state.registers .rsi = UInt64.ofNat values.length

theorem hasBlock (block : BlockId) (bound : block.toNat < 26) :
    (RuntimeTarget.checked foldCounters).program.hasBlock block = true := by
  simpa [RuntimeTarget.checked, RuntimeTarget.program, Program.hasBlock] using bound

theorem and_seven (value : Word) : value &&& 7 = value % 8 := by
  apply UInt64.toNat_inj.mp
  change value.toNat &&& 7 = value.toNat % 8
  exact Nat.and_two_pow_sub_one_eq_mod value.toNat 3

theorem and_thirtyOne (value : Word) : value &&& 31 = value % 32 := by
  apply UInt64.toNat_inj.mp
  change value.toNat &&& 31 = value.toNat % 32
  exact Nat.and_two_pow_sub_one_eq_mod value.toNat 5

def alignmentState (state : State) : State := state.setReg .rax (state.registers .rdi &&& 7)

theorem alignmentTrace (layout : Layout) (state : State) :
    Trace layout alignmentInstructions state (alignmentState state) := by
  refine .cons (.mov _ _ _) (.cons (.alu _ _ _ _) ?_)
  simpa [alignmentState, AluOp.eval, signExtend32] using Trace.nil (layout := layout) (alignmentState state)

def byteCount (count : Word) : Word := (count + 1) * 8 * 4

theorem byteCount_nat (count : Nat) : byteCount (UInt64.ofNat count) = UInt64.ofNat (cellBytes * (count + 1)) := by
  simp only [byteCount, cellBytes, UInt64.ofNat_mul, UInt64.ofNat_add]
  rw [UInt64.mul_assoc]
  exact UInt64.mul_comm _ _

def cursorState (state : State) : State :=
  ((state.setReg .r10 (state.registers .rsi + 1)).setReg .rax
    (byteCount (state.registers .rsi))).setReg .r11 (state.words Field.cursor.index)

theorem cursorTrace (layout : Layout) (state : State) (context : state.registers .rdi = layout.base) :
    Trace layout cursorInstructions state (cursorState state) := by
  let first := state.setReg .r10 (state.registers .rsi + 1)
  let second := first.setReg .rax ((state.registers .rsi + 1) * 8)
  let third := second.setReg .rax (byteCount (state.registers .rsi))
  have one : Trace layout [.lea .r10 (memoryOperand .rsi 1)] state first := by
    refine .cons (.lea _ _ _) ?_
    simpa [first, operand_address state .rsi 1 (by decide)] using Trace.nil (layout := layout) first
  have two : Trace layout [.lea .rax { index := some .r10, scale := .eight }] first second := by
    refine .cons (.lea _ _ _) ?_
    simpa [first, second, State.address, State.core, MemAddr.eval, Core.readReg, IndexReg.gpr, Scale.word,
      signExtend32] using Trace.nil (layout := layout) second
  have three : Trace layout [.lea .rax { index := some .rax, scale := .four }] second third := by
    refine .cons (.lea _ _ _) ?_
    simpa [second, third, byteCount, State.address, State.core, MemAddr.eval, Core.readReg, IndexReg.gpr,
      Scale.word, signExtend32] using Trace.nil (layout := layout) third
  have four : Trace layout [Instr.load .w64 .r11 (header .cursor)] third (cursorState state) := by
    refine .cons (.load _ _ _ Field.cursor.index (layout.field_bound .cursor)
      (header_address third layout .cursor (by simpa [third, second, first] using context))) ?_
    simpa [third, second, first, cursorState] using Trace.nil (layout := layout) (cursorState state)
  exact ((one.append two).append three).append four

def capacityState (state : State) : State :=
  (state.setReg .rcx (state.words Field.capacity.index)).setReg .r11 (state.registers .rax + 32)

theorem capacityTrace (layout : Layout) (state : State) (context : state.registers .rdi = layout.base) :
    Trace layout capacityInstructions state (capacityState state) := by
  refine .cons (.load _ _ _ Field.capacity.index (layout.field_bound .capacity)
    (header_address state layout .capacity context)) (.cons (.lea _ _ _) ?_)
  simpa [capacityState, cellBytes, operand_address _ .rax 32 (by decide)] using
    Trace.nil (layout := layout) (capacityState state)

def capacityAlignmentState (state : State) : State := state.setReg .r11 (state.registers .rcx &&& 31)

theorem capacityAlignmentTrace (layout : Layout) (state : State) :
    Trace layout capacityAlignmentInstructions state (capacityAlignmentState state) := by
  refine .cons (.mov _ _ _) (.cons (.alu _ _ _ _) ?_)
  simpa [capacityAlignmentState, AluOp.eval, signExtend32] using
    Trace.nil (layout := layout) (capacityAlignmentState state)

def headerState (state : State) (field : Field) : State := state.setReg .r11 (state.words field.index)

theorem headerTrace (layout : Layout) (state : State) (field : Field)
    (context : state.registers .rdi = layout.base) :
    Trace layout (headerInstructions field) state (headerState state field) :=
  .cons (.load _ _ _ field.index (layout.field_bound field) (header_address state layout field context)) (.nil _)

theorem guardSteps {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (block next : BlockId) (left : GPR) (right : AluSource) (condition : Condition)
    (code : BlockCode (RuntimeTarget.checked foldCounters) block instructions (.branch (wordCompare left right) condition next 6))
    (holds : (wordCompare left right).holds condition (after.core Memory.unmapped) = true)
    (nextBound : next.toNat < 26) :
    Steps runtime (RuntimeTarget.checked foldCounters) (instructions.length + 1) (leaf (before.core memory) block 0)
      (leaf (after.core memory) next 0) :=
  trace.branch_readOnly readonly outside memory represented runtime (RuntimeTarget.checked foldCounters) block next 6
    (wordCompare left right) condition code true holds (hasBlock (foldCounters := foldCounters) next nextBound)

theorem headerSteps (layout : Layout) (state : State) (field : Field)
    (context : state.registers .rdi = layout.base) (outside memory : Memory)
    (represented : Realizes layout outside state.words memory) (runtime : Runtime) (block next : BlockId)
    (right : AluSource)
    (code : BlockCode (RuntimeTarget.checked foldCounters) block (headerInstructions field) (.branch (wordCompare .r11 right) .eq next 6))
    (holds : (wordCompare .r11 right).holds .eq ((headerState state field).core Memory.unmapped) = true)
    (nextBound : next.toNat < 26) :
    Steps runtime (RuntimeTarget.checked foldCounters) 2 (leaf (state.core memory) block 0)
      (leaf ((headerState state field).core memory) next 0) :=
  guardSteps (foldCounters := foldCounters) (headerTrace layout state field context) rfl outside memory represented runtime block next
    .r11 right .eq code holds nextBound

end Ix.Compiler.X86.RuntimeExecution
