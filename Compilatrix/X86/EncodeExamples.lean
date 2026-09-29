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

-- A 64-bit move of a value below 2^32 uses `mov r32, imm32`, which zero-extends.
#guard instr (.mov .w64 .rax (.imm 42)) == expected #[0xb8, 0x2a, 0, 0, 0]

-- A value that sign-extends from 32 bits uses `mov r/m64, imm32`.
#guard instr (.mov .w64 .rax (.imm 0xffffffffffffffff)) ==
  expected #[0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff]

-- Only a value that needs all 64 bits uses `movabs`.
#guard instr (.mov .w64 .rax (.imm 0x100000000)) ==
  expected #[0x48, 0xb8, 0, 0, 0, 0, 0x01, 0, 0, 0]

#guard instr (.mov .w32 .r9 (.imm 5)) == expected #[0x41, 0xb9, 0x05, 0, 0, 0]

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

-- An immediate that sign-extends from a byte uses `83 /d ib`.
#guard instr (.alu .add .w64 .rax (.imm 2)) == expected #[0x48, 0x83, 0xc0, 0x02]
#guard instr (.alu .and .w16 .rcx (.imm 0xffff)) == expected #[0x66, 0x83, 0xe1, 0xff]
#guard instr (.alu .or .w32 .r8 (.imm 0xffffff80)) == expected #[0x41, 0x83, 0xc8, 0x80]

-- Otherwise the full-size immediate: `81 /d id` (or `80 /d ib` at byte width).
#guard instr (.alu .add .w64 .rax (.imm 200)) == expected #[0x48, 0x81, 0xc0, 0xc8, 0, 0, 0]
#guard instr (.alu .xor .w16 .rdx (.imm 0x1234)) == expected #[0x66, 0x81, 0xf2, 0x34, 0x12]
#guard instr (.alu .sub .w8 .rsi (.imm 1)) == expected #[0x40, 0x80, 0xee, 0x01]

#guard instr (.alu .xor .w32 .r9 (.reg .r10)) == expected #[0x45, 0x31, 0xd1]

#guard instr (.alu .add .w32 .rax (.reg .rcx)) == expected #[0x01, 0xc8]

#guard instr (.imul .w64 .r9 .r10) == expected #[0x4d, 0x0f, 0xaf, 0xca]

-- Three-operand multiply: `6B /r ib` for a byte immediate, else `69 /r id`.
#guard instr (.imulImm .w64 .r9 .r10 3) == expected #[0x4d, 0x6b, 0xca, 0x03]
#guard instr (.imulImm .w32 .rax .rcx 1000) == expected #[0x69, 0xc1, 0xe8, 0x03, 0, 0]

#guard instr (.push .r12) == expected #[0x41, 0x54]
#guard instr (.pop .r12) == expected #[0x41, 0x5c]
#guard instr (.push .rbp) == expected #[0x55]

#guard instr (.allocFrame { units16 := 1 }) == expected #[0x48, 0x83, 0xec, 0x10]

#guard instr (.freeFrame { units16 := 1 }) == expected #[0x48, 0x83, 0xc4, 0x10]

#guard instr (.allocFrame { units16 := 8 }) == expected #[0x48, 0x81, 0xec, 0x80, 0, 0, 0]

#guard instr (.spill { index := 0 } .r12) == expected #[0x4c, 0x89, 0x65, 0xf8]

#guard instr (.reload .r12 { index := 0 }) == expected #[0x4c, 0x8b, 0x65, 0xf8]

#guard instr (.spill { index := 0x7fff } .r12) ==
  expected #[0x4c, 0x89, 0xa5, 0, 0, 0xfc, 0xff]

#guard encodeCompare { width := .w64, left := .rax, right := .imm 42 } ==
  expected #[0x48, 0x83, 0xf8, 0x2a]

#guard encodeCompare { width := .w32, left := .rbx, right := .imm 0x10000 } ==
  expected #[0x81, 0xfb, 0, 0, 0x01, 0]

#guard encodeCompare { width := .w32, left := .r9, right := .reg .r10 } ==
  expected #[0x45, 0x39, 0xd1]

/-! Phase 1 rows (M1.B1): `div`, shifts by imm8 and `cl`, `test`, `setcc`,
`cmovcc`, `op r, r/m`, and the `mov rsp, [r15 − 64]` of the failure exit. -/

def row (o : Op) (args : List Arg) : ByteArray := encodeOp o args

#guard row { mn := .div, w := .w64, form := .M } [.reg .rcx] == expected #[0x48, 0xf7, 0xf1]
#guard row { mn := .div, w := .w32, form := .M } [.reg .r9] == expected #[0x41, 0xf7, 0xf1]
#guard row { mn := .shl, w := .w64, form := .MI } [.reg .rax, .imm 3] == expected #[0x48, 0xc1, 0xe0, 0x03]
#guard row { mn := .shr, w := .w64, form := .MI } [.reg .r9, .imm 1] == expected #[0x49, 0xc1, 0xe9, 0x01]
#guard row { mn := .sar, w := .w64, form := .MC } [.reg .rdi] == expected #[0x48, 0xd3, 0xff]
-- REX selects SIL rather than DH.
#guard row { mn := .shl, w := .w8, form := .MC } [.reg .rsi] == expected #[0x40, 0xd2, 0xe6]
#guard row { mn := .shr, w := .w32, form := .MI } [.mem { base := some .rbx, displacement := 8 }, .imm 2] ==
  expected #[0xc1, 0x6b, 0x08, 0x02]
#guard row { mn := .test, w := .w64, form := .MI } [.reg .rdi, .imm 1] ==
  expected #[0x48, 0xf7, 0xc7, 0x01, 0, 0, 0]
#guard row { mn := .test, w := .w8, form := .MI } [.reg .rdi, .imm 1] == expected #[0x40, 0xf6, 0xc7, 0x01]
#guard row { mn := .test, w := .w32, form := .MR } [.reg .rax, .reg .rcx] == expected #[0x85, 0xc8]
#guard row (Op.setccM .eq) [.reg .rax] == expected #[0x0f, 0x94, 0xc0]
#guard row (Op.setccM .unsignedLt) [.reg .r9] == expected #[0x41, 0x0f, 0x92, 0xc1]
#guard row (Op.setccM .signedLt) [.reg .rsi] == expected #[0x40, 0x0f, 0x9c, 0xc6]
#guard row (Op.cmovRM .ne .w64) [.reg .rax, .reg .rcx] == expected #[0x48, 0x0f, 0x45, 0xc1]
#guard row (Op.cmovRM .signedLt .w32) [.reg .r10, .mem { base := some .rbx, displacement := 8 }] ==
  expected #[0x44, 0x0f, 0x4c, 0x53, 0x08]
-- The prologue's stack check compares with the context's `stackLimit`.
#guard row { mn := .cmp, w := .w64, form := .RM } [.reg .r11, .mem { base := some .r15, displacement := 0xffffffc8 }] ==
  expected #[0x4d, 0x3b, 0x5f, 0xc8]
#guard row { mn := .add, w := .w64, form := .RM } [.reg .rax, .mem { base := some .rbx }] ==
  expected #[0x48, 0x03, 0x03]
-- The failure exit's `unwind [r15 − 64]` is the `mov r64, r/m64` row.
#guard row { mn := .mov, w := .w64, form := .RM } [.reg .rsp, .mem { base := some .r15, displacement := 0xffffffc0 }] ==
  expected #[0x49, 0x8b, 0x67, 0xc0]

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
  expected #[0x48, 0x83, 0xf8, 0x2a,
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
        0xb8, 0x28, 0, 0, 0,
        0x48, 0x83, 0xc0, 0x02,
        0x48, 0x83, 0xf8, 0x2a,
        0x0f, 0x84, 0x05, 0, 0, 0,
        0xe9, 0x01, 0, 0, 0,
        0xc3,
        0xb8, 0, 0, 0, 0,
        0xc3] &&
      output.blockOffsets == #[0, 24, 25] &&
      output.relocations.isEmpty

#guard arithmeticProgramBytesAccepted

def directCallProgramBytesAccepted : Bool :=
  match Compilatrix.X86.Encode.Program.encode
      Compilatrix.X86.Examples.callProgram with
  | .error _ => false
  | .ok output =>
      output.text == expected #[
        0x55,
        0xe8, 0x06, 0, 0, 0,
        0x5d,
        0x48, 0x83, 0xc0, 0x02,
        0xc3,
        0xb8, 0x28, 0, 0, 0,
        0xc3] &&
      output.blockOffsets == #[0, 12] &&
      output.relocations.isEmpty

#guard directCallProgramBytesAccepted

def runtimeRelocationAccepted : Bool :=
  match Compilatrix.X86.Encode.Program.encode
      Compilatrix.X86.Examples.runtimeProgram with
  | .error _ => false
  | .ok output =>
      output.text == expected #[
        0x55,
        0xbf, 0x10, 0, 0, 0,
        0xbe, 0x08, 0, 0, 0,
        0xe8, 0, 0, 0, 0,
        0x5d,
        0xc3] &&
      output.relocations == #[
        { offset := 12
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
