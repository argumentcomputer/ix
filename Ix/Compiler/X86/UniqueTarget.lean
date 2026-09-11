import Ix.Compiler.X86.UniqueABI

/-! Native instruction emission for the checked unique reversal shape. Both
entry points are System V leaves: they use caller-saved registers and perform
all heap operations with the existing typed memory/arithmetic instructions.
The main entry checks available arena bytes before its first write. -/

namespace Ix.Compiler.X86.UniqueTarget

open UniqueABI

def policyTag : String := "unique-reverse-x86/1"

def memoryOperand (base : GPR) (offset : Nat := 0) : MemAddr :=
  { base := some base, displacement := UInt32.ofNat offset }

def header (field : Field) : MemAddr := memoryOperand .rdi (8 * field.index)

def changeCounter (field : Field) (operation : AluOp) (amount : Imm32) : List Instr :=
  [.load .w64 .r11 (header field), .alu operation .w64 .r11 (.imm amount),
   .store .w64 (header field) .r11]

def allocate (tag head : Word) (tail : MoveSource) (destination : GPR) : List Instr :=
  [.load .w64 .rax (header .cursor),
   .lea .r11 (memoryOperand .rax cellBytes), .store .w64 (header .cursor) .r11,
   .lea .rax { base := some .rdi, index := some .rax, displacement := 80 },
   .mov .w64 .rcx (.imm tag), .store .w64 (memoryOperand .rax 0) .rcx,
   .mov .w64 .rcx (.imm head), .store .w64 (memoryOperand .rax 8) .rcx,
   .mov .w64 .rcx tail, .store .w64 (memoryOperand .rax 16) .rcx,
   .mov .w64 .rcx (.imm 0), .store .w64 (memoryOperand .rax 24) .rcx] ++
  changeCounter .allocs .add 1 ++ changeCounter .live .add 1 ++
  [.store .w64 (header .peak) .r11, .mov .w64 destination (.reg .rax)]

def inputCons : List Word → List Instr
  | [] => []
  | value :: rest => allocate consTag value (.reg .rdx) .rdx ++ inputCons rest

def inputInstructions (values : List Word) : List Instr :=
  allocate nilTag 0 (.imm 0) .rdx ++ inputCons values.reverse ++
    allocate nilTag 0 (.imm 0) .rsi

def reserveCons : List Instr :=
  [.load .w64 .r8 (memoryOperand .rdx 8), .load .w64 .r9 (memoryOperand .rdx 16),
   .mov .w64 .rcx (.imm reservedTag), .store .w64 (memoryOperand .rdx 0) .rcx] ++
  changeCounter .reservations .add 1 ++ changeCounter .live .sub 1

def reuseCons : List Instr :=
  [.store .w64 (memoryOperand .rdx 8) .r8, .store .w64 (memoryOperand .rdx 16) .rsi,
   .mov .w64 .rcx (.imm consTag), .store .w64 (memoryOperand .rdx 0) .rcx] ++
  changeCounter .reservations .sub 1 ++ changeCounter .live .add 1 ++
  changeCounter .reuses .add 1 ++ changeCounter .payload .add 2

def releaseCell (pointer : GPR) : List Instr :=
  [.mov .w64 .rcx (.imm freedTag), .store .w64 (memoryOperand pointer 0) .rcx,
   .mov .w64 .rcx (.imm 0), .store .w64 (memoryOperand pointer 8) .rcx,
   .store .w64 (memoryOperand pointer 16) .rcx, .store .w64 (memoryOperand pointer 24) .rcx] ++
  changeCounter .frees .add 1 ++ changeCounter .live .sub 1

def consInstructions : List Instr :=
  reserveCons ++ reuseCons ++ [.mov .w64 .rsi (.reg .rdx), .mov .w64 .rdx (.reg .r9)]

def requiredBytes (values : List Word) : Nat := cellBytes * (values.length + 2)

def program (values : List Word) : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[.load .w64 .rax (header .cursor), .load .w64 .r11 (header .capacity)]
        terminator := .branch { width := .w64, left := .rax, right := .reg .r11 } .unsignedLe 1 6 },
      { instructions := #[.alu .sub .w64 .r11 (.reg .rax)]
        terminator := .branch { width := .w64, left := .r11, right := .imm (UInt32.ofNat (requiredBytes values)) }
          .unsignedGe 2 6 },
      { instructions := (inputInstructions values).toArray, terminator := .jump 3 },
      { instructions := #[.load .w64 .rcx (memoryOperand .rdx 0)]
        terminator := .branch { width := .w64, left := .rcx, right := .imm 0 } .eq 4 5 },
      { instructions := (releaseCell .rdx ++ [Instr.mov .w64 .rax (.reg .rsi)]).toArray, terminator := .ret },
      { instructions := consInstructions.toArray, terminator := .jump 3 },
      { instructions := #[.mov .w64 .rax (.imm 0)], terminator := .ret }] }

/-- The separate release entry receives the descriptor in `rdi` and the
returned root in `rsi`. It returns zero after releasing every cell. -/
def releaseProgram : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[.load .w64 .rcx (memoryOperand .rsi 0)]
        terminator := .branch { width := .w64, left := .rcx, right := .imm 0 } .eq 2 1 },
      { instructions := ([Instr.load .w64 .rdx (memoryOperand .rsi 16)] ++ releaseCell .rsi ++
          [Instr.mov .w64 .rsi (.reg .rdx)]).toArray
        terminator := .jump 0 },
      { instructions := (releaseCell .rsi ++ [Instr.mov .w64 .rax (.imm 0)]).toArray
        terminator := .ret }] }

@[simp] theorem allocate_length (tag head : Word) (tail : MoveSource) (destination : GPR) :
    (allocate tag head tail destination).length = 20 := rfl

@[simp] theorem inputCons_length (values : List Word) :
    (inputCons values).length = 20 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [inputCons, ih]; omega

@[simp] theorem inputInstructions_length (values : List Word) :
    (inputInstructions values).length = 20 * values.length + 40 := by
  simp [inputInstructions]; omega

def controlCost (values : List Word) : Nat := 51 * values.length + 62
def releaseCost (length : Nat) : Nat := 17 * length + 16

end Ix.Compiler.X86.UniqueTarget
