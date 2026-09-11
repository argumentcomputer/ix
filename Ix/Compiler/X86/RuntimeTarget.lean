import Ix.Compiler.X86.UniqueControl
import Ix.Compiler.X86.UniqueCounterFold

/-! One native reversal function for all admitted input lists. `rdi` points to
the arena and `rsi` supplies the number of cons cells. Validation reads only
the descriptor and canonical cells; it never follows an untrusted tail.
Every rejection returns zero before the first write. -/

namespace Ix.Compiler.X86.RuntimeTarget

open UniqueABI UniqueTarget

def policyTag (foldCounters : Bool := false) : String :=
  if foldCounters then "unique-reverse-runtime-x86/2" else "unique-reverse-runtime-x86/1"
def abiTag : String := "unique-list-runtime-arena/1"

def wordCompare (left : GPR) (right : AluSource) : Compare := { width := .w64, left, right }
def guard (instructions : List Instr) (left : GPR) (right : AluSource)
    (condition : Condition) (next : BlockId) : Block :=
  { instructions := instructions.toArray, terminator := .branch (wordCompare left right) condition next 6 }

def alignmentInstructions : List Instr := [.mov .w64 .rax (.reg .rdi), .alu .and .w64 .rax (.imm 7)]

def cursorInstructions : List Instr :=
  [.lea .r10 (memoryOperand .rsi 1),
   .lea .rax { index := some .r10, scale := .eight },
   .lea .rax { index := some .rax, scale := .four },
   .load .w64 .r11 (header .cursor)]

def capacityInstructions : List Instr :=
  [.load .w64 .rcx (header .capacity), .lea .r11 (memoryOperand .rax cellBytes)]

def capacityAlignmentInstructions : List Instr :=
  [.mov .w64 .r11 (.reg .rcx), .alu .and .w64 .r11 (.imm 31)]

def headerInstructions (field : Field) : List Instr := [.load .w64 .r11 (header field)]

def nilInstructions : List Instr :=
  [.lea .rdx (memoryOperand .rdi headerBytes),
   .lea .r8 (memoryOperand .rdx cellBytes), .mov .w64 .r9 (.reg .rsi),
   .load .w64 .rcx (memoryOperand .rdx 0),
   .load .w64 .r11 (memoryOperand .rdx 8), .alu .or .w64 .rcx (.reg .r11),
   .load .w64 .r11 (memoryOperand .rdx 16), .alu .or .w64 .rcx (.reg .r11),
   .load .w64 .r11 (memoryOperand .rdx 24), .alu .or .w64 .rcx (.reg .r11)]

def fieldInstructions (offset : Nat) : List Instr := [.load .w64 .rcx (memoryOperand .r8 offset)]

def advanceInstructions : List Instr :=
  [.mov .w64 .rdx (.reg .r8), .lea .r8 (memoryOperand .r8 cellBytes), .alu .sub .w64 .r9 (.imm 1)]

def loopInstructions (foldCounters : Bool) : List Instr :=
  if foldCounters then UniqueCounterFold.instructions else consInstructions

theorem loopTrace (foldCounters : Bool) (layout : Layout) (state : UniqueExecution.State) (index : Nat)
    (indexBound : index < layout.capacity) (context : state.registers .rdi = layout.base)
    (pointer : state.registers .rdx = layout.cell index) :
    UniqueExecution.Trace layout (loopInstructions foldCounters) state (UniqueExecution.consState state index) := by
  cases foldCounters
  · exact UniqueExecution.consTrace layout state index indexBound context pointer
  · exact UniqueCounterFold.trace layout state index indexBound context pointer

def program (foldCounters : Bool := false) : Program :=
  { entry := 0
    blocks := #[
      guard [] .rsi (.imm 64) .unsignedLe 1,
      guard alignmentInstructions .rax (.imm 0) .eq 7,
      { instructions := (allocate nilTag 0 (.imm 0) .rsi).toArray, terminator := .jump 3 },
      { instructions := #[.load .w64 .rcx (memoryOperand .rdx 0)]
        terminator := .branch (wordCompare .rcx (.imm 0)) .eq 4 5 },
      { instructions := (releaseCell .rdx ++ [Instr.mov .w64 .rax (.reg .rsi)]).toArray, terminator := .ret },
      { instructions := (loopInstructions foldCounters).toArray, terminator := .jump 3 },
      { instructions := #[.mov .w64 .rax (.imm 0)], terminator := .ret },
      guard [] .rdi (.imm 0) .ne 8,
      guard cursorInstructions .r11 (.reg .rax) .eq 9,
      guard capacityInstructions .rcx (.reg .r11) .unsignedGe 10,
      guard [] .rcx (.imm 2112) .unsignedLe 11,
      guard capacityAlignmentInstructions .r11 (.imm 0) .eq 12,
      guard (headerInstructions .allocs) .r11 (.reg .r10) .eq 13,
      guard (headerInstructions .frees) .r11 (.imm 0) .eq 14,
      guard (headerInstructions .reuses) .r11 (.imm 0) .eq 15,
      guard (headerInstructions .live) .r11 (.reg .r10) .eq 16,
      guard (headerInstructions .peak) .r11 (.reg .r10) .eq 17,
      guard (headerInstructions .rcops) .r11 (.imm 0) .eq 18,
      guard (headerInstructions .payload) .r11 (.imm 0) .eq 19,
      guard (headerInstructions .reservations) .r11 (.imm 0) .eq 20,
      guard nilInstructions .rcx (.imm 0) .eq 21,
      { instructions := #[], terminator := .branch (wordCompare .r9 (.imm 0)) .eq 2 22 },
      guard (fieldInstructions 0) .rcx (.imm 1) .eq 23,
      guard (fieldInstructions 16) .rcx (.reg .rdx) .eq 24,
      guard (fieldInstructions 24) .rcx (.imm 0) .eq 25,
      { instructions := advanceInstructions.toArray, terminator := .jump 21 }] }

theorem wellFormed (foldCounters : Bool := false) : (program foldCounters).wellFormed = true := by
  cases foldCounters <;>
  simp [program, Program.wellFormed, Program.hasBlock, Block.offsetsFit, Block.targetsValid,
    Instr.targetsValid, Terminator.targetsValid, guard, alignmentInstructions, cursorInstructions,
    capacityInstructions, capacityAlignmentInstructions, headerInstructions, nilInstructions,
    fieldInstructions, advanceInstructions, allocate, changeCounter, consInstructions, reserveCons,
    reuseCons, releaseCell, loopInstructions, UniqueCounterFold.instructions]

def checked (foldCounters : Bool := false) : Checked := ⟨program foldCounters, wellFormed foldCounters⟩

theorem releaseWellFormed : UniqueTarget.releaseProgram.wellFormed = true := by
  simp [UniqueTarget.releaseProgram, Program.wellFormed, Program.hasBlock, Block.offsetsFit, Block.targetsValid,
    Instr.targetsValid, Terminator.targetsValid, releaseCell, changeCounter]

def releaseChecked : Checked := ⟨UniqueTarget.releaseProgram, releaseWellFormed⟩

theorem loopCode (foldCounters : Bool := false) :
    UniqueExecution.LoopCode (checked foldCounters) (loopInstructions foldCounters) := by
  cases foldCounters <;>
  refine ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, ?_, ?_, ?_⟩ <;> decide

def validationCost (length : Nat) : Nat := 11 * length + 45
def controlCost (length : Nat) (foldCounters : Bool := false) : Nat :=
  if foldCounters then 30 * length + 82 else 42 * length + 82

theorem controlCost_saving (length : Nat) : controlCost length true + 12 * length = controlCost length := by
  simp [controlCost]
  omega

end Ix.Compiler.X86.RuntimeTarget
