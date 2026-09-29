import Compilatrix.X86.Encode
import Compilatrix.X86.EvalExamples

/-!
Golden encoder checks for the table-driven encoder.  These byte strings are
also decoded independently by `scripts/CheckX86Encoder.lean`; keeping the
Lean expectations here makes every ordinary build catch encoder drift before
the external check.  Memory operands use the shortest displacement, and REX
appears only when a field needs it.
-/

namespace Compilatrix.X86.Encode.Examples

open Compilatrix.X86
open Compilatrix.X86.Encode

def expected (values : Array UInt8) : ByteArray := ByteArray.mk values

def instr (instruction : Instr) : ByteArray := (encodeInstr instruction).bytes

#guard instr (.mov .w64 .rax (.imm 42)) ==
  expected #[0x48, 0xb8, 0x2a, 0, 0, 0, 0, 0, 0, 0]

-- REX selects SIL rather than DH.
#guard instr (.mov .w8 .rsi (.imm 7)) == expected #[0x40, 0xb6, 0x07]

#guard instr (.mov .w64 .r9 (.reg .r10)) == expected #[0x4d, 0x89, 0xd1]

-- disp8, SIB, REX.X and REX.B; `movzx r32, r/m8` zero-extends to 64 bits.
#guard instr (.load .w8 .r9
    { base := some .r12, index := some .r13, scale := .eight, displacement := 16 }) ==
  expected #[0x47, 0x0f, 0xb6, 0x4c, 0xec, 0x10]

-- No REX at all.
#guard instr (.load .w16 .rax { base := some .rbx, displacement := 4 }) ==
  expected #[0x0f, 0xb7, 0x43, 0x04]

-- An absolute address keeps SIB with disp32.
#guard instr (.load .w32 .r8 { base := none, displacement := 0x100 }) ==
  expected #[0x44, 0x8b, 0x04, 0x25, 0, 0x01, 0, 0]

#guard instr (.store .w64 { base := some .rbp, displacement := 0xfffffff8 } .r12) ==
  expected #[0x4c, 0x89, 0x65, 0xf8]

-- A zero displacement is omitted, except from RBP/R13 bases (mode 1, disp8 0).
#guard instr (.store .w64 { base := some .rbx } .rax) == expected #[0x48, 0x89, 0x03]
#guard instr (.store .w64 { base := some .r13 } .rax) == expected #[0x49, 0x89, 0x45, 0x00]
#guard instr (.store .w64 { base := some .rsp } .rax) == expected #[0x48, 0x89, 0x04, 0x24]
#guard instr (.store .w64 { base := some .r12, displacement := 0x80 } .rax) ==
  expected #[0x49, 0x89, 0x84, 0x24, 0x80, 0, 0, 0]

#guard instr (.lea .r10
    { base := some .rbx, index := some .r9, scale := .four, displacement := 32 }) ==
  expected #[0x4e, 0x8d, 0x54, 0x8b, 0x20]

#guard instr (.alu .add .w64 .rax (.imm 2)) == expected #[0x48, 0x81, 0xc0, 0x02, 0, 0, 0]

#guard instr (.alu .sub .w8 .rsi (.imm 1)) == expected #[0x40, 0x80, 0xee, 0x01]

#guard instr (.alu .xor .w32 .r9 (.reg .r10)) == expected #[0x45, 0x31, 0xd1]

#guard instr (.alu .add .w32 .rax (.reg .rcx)) == expected #[0x01, 0xc8]

#guard instr (.imul .w64 .r9 .r10) == expected #[0x4d, 0x0f, 0xaf, 0xca]

#guard instr (.push .r12) == expected #[0x41, 0x54]
#guard instr (.pop .r12) == expected #[0x41, 0x5c]
#guard instr (.push .rbp) == expected #[0x55]

#guard instr (.allocFrame { units16 := 1 }) == expected #[0x48, 0x81, 0xec, 0x10, 0, 0, 0]

#guard instr (.freeFrame { units16 := 1 }) == expected #[0x48, 0x81, 0xc4, 0x10, 0, 0, 0]

#guard instr (.spill { index := 0 } .r12) == expected #[0x4c, 0x89, 0x65, 0xf8]

#guard instr (.reload .r12 { index := 0 }) == expected #[0x4c, 0x8b, 0x65, 0xf8]

#guard instr (.spill { index := 0x7fff } .r12) ==
  expected #[0x4c, 0x89, 0xa5, 0, 0, 0xfc, 0xff]

#guard encodeCompare { width := .w64, left := .rax, right := .imm 42 } ==
  expected #[0x48, 0x81, 0xf8, 0x2a, 0, 0, 0]

#guard encodeCompare { width := .w32, left := .r9, right := .reg .r10 } ==
  expected #[0x45, 0x39, 0xd1]

def directCallPlaceholderAccepted : Bool :=
  let chunk := encodeInstr (.call 3)
  chunk.bytes == expected #[0xe8, 0, 0, 0, 0] &&
    chunk.fixups == #[{ offset := 1, target := .block 3 }]

#guard directCallPlaceholderAccepted

def runtimeCallPlaceholderAccepted : Bool :=
  let chunk := encodeInstr (.callRuntime .allocate)
  chunk.bytes == expected #[0xe8, 0, 0, 0, 0] &&
    chunk.fixups == #[{ offset := 1, target := .intrinsic .allocate }]

#guard runtimeCallPlaceholderAccepted

#guard (encodeTerminator (.jump 1)).bytes ==
  expected #[0xe9, 0, 0, 0, 0]

#guard (encodeTerminator (.branch
    { width := .w64, left := .rax, right := .imm 42 }
    .eq 1 2)).bytes ==
  expected #[0x48, 0x81, 0xf8, 0x2a, 0, 0, 0,
    0x0f, 0x84, 0, 0, 0, 0,
    0xe9, 0, 0, 0, 0]

#guard (encodeTerminator (.tailCall 1)).bytes ==
  expected #[0xe9, 0, 0, 0, 0]

#guard (encodeTerminator .ret).bytes == expected #[0xc3]

def arithmeticProgramBytesAccepted : Bool :=
  match Compilatrix.X86.Encode.Program.encode
      Compilatrix.X86.Examples.arithmeticProgram with
  | .error _ => false
  | .ok output =>
      output.text == expected #[
        0x48, 0xb8, 0x28, 0, 0, 0, 0, 0, 0, 0,
        0x48, 0x81, 0xc0, 0x02, 0, 0, 0,
        0x48, 0x81, 0xf8, 0x2a, 0, 0, 0,
        0x0f, 0x84, 0x05, 0, 0, 0,
        0xe9, 0x01, 0, 0, 0,
        0xc3,
        0x48, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0,
        0xc3] &&
      output.blockOffsets == #[0, 35, 36] &&
      output.relocations.isEmpty

#guard arithmeticProgramBytesAccepted

def directCallProgramBytesAccepted : Bool :=
  match Compilatrix.X86.Encode.Program.encode
      Compilatrix.X86.Examples.callProgram with
  | .error _ => false
  | .ok output =>
      output.text == expected #[
        0x55,
        0xe8, 0x09, 0, 0, 0,
        0x5d,
        0x48, 0x81, 0xc0, 0x02, 0, 0, 0,
        0xc3,
        0x48, 0xb8, 0x28, 0, 0, 0, 0, 0, 0, 0,
        0xc3] &&
      output.blockOffsets == #[0, 15] &&
      output.relocations.isEmpty

#guard directCallProgramBytesAccepted

def runtimeRelocationAccepted : Bool :=
  match Compilatrix.X86.Encode.Program.encode
      Compilatrix.X86.Examples.runtimeProgram with
  | .error _ => false
  | .ok output =>
      output.text == expected #[
        0x55,
        0x48, 0xbf, 0x10, 0, 0, 0, 0, 0, 0, 0,
        0x48, 0xbe, 0x08, 0, 0, 0, 0, 0, 0, 0,
        0xe8, 0, 0, 0, 0,
        0x5d,
        0xc3] &&
      output.relocations == #[
        { offset := 22
          symbol := "compilatrix_rt_allocate"
          addend := -4 }]

#guard runtimeRelocationAccepted

def malformedProgramRejected : Bool :=
  match Compilatrix.X86.Encode.Program.encode
      Compilatrix.X86.Examples.invalidTargetProgram with
  | .error .malformedControl => true
  | _ => false

#guard malformedProgramRejected

end Compilatrix.X86.Encode.Examples
