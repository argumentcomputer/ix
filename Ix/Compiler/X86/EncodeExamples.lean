import Ix.Compiler.X86.Encode
import Ix.Compiler.X86.EvalExamples

/-!
Golden E0 encoder checks.  These byte strings are also decoded independently
by `scripts/CheckX86Encoder.lean`; keeping the Lean expectations here makes
every ordinary build catch local encoder drift before the external check.
-/

namespace Ix.Compiler.X86.Encode.Examples

open Ix.Compiler.X86
open Ix.Compiler.X86.Encode

def expected (values : Array UInt8) : ByteArray := ByteArray.mk values

#guard encodeMov .w64 .rax (.imm 42) ==
  expected #[0x48, 0xb8, 0x2a, 0, 0, 0, 0, 0, 0, 0]

#guard encodeMov .w8 .rsi (.imm 7) ==
  expected #[0x40, 0xb6, 0x07]

#guard encodeMov .w64 .r9 (.reg .r10) ==
  expected #[0x4d, 0x89, 0xd1]

#guard encodeLoad .w8 .r9
    { base := some .r12, index := some .r13, scale := .eight,
      displacement := 16 } ==
  expected #[0x4f, 0x0f, 0xb6, 0x8c, 0xec, 0x10, 0, 0, 0]

#guard encodeLoad .w16 .rax { base := some .rbx, displacement := 4 } ==
  expected #[0x48, 0x0f, 0xb7, 0x83, 0x04, 0, 0, 0]

#guard encodeLoad .w32 .r8 { base := none, displacement := 0x100 } ==
  expected #[0x44, 0x8b, 0x04, 0x25, 0, 0x01, 0, 0]

#guard encodeStore .w64 { base := some .rbp, displacement := 0xfffffff8 }
    .r12 ==
  expected #[0x4c, 0x89, 0xa5, 0xf8, 0xff, 0xff, 0xff]

#guard encodeLea .r10
    { base := some .rbx, index := some .r9, scale := .four,
      displacement := 32 } ==
  expected #[0x4e, 0x8d, 0x94, 0x8b, 0x20, 0, 0, 0]

#guard encodeAlu .add .w64 .rax (.imm 2) ==
  expected #[0x48, 0x81, 0xc0, 0x02, 0, 0, 0]

#guard encodeAlu .sub .w8 .rsi (.imm 1) ==
  expected #[0x40, 0x80, 0xee, 0x01]

#guard encodeAlu .xor .w32 .r9 (.reg .r10) ==
  expected #[0x45, 0x31, 0xd1]

#guard encodeImul .w64 .r9 .r10 ==
  expected #[0x4d, 0x0f, 0xaf, 0xca]

#guard encodePush .r12 == expected #[0x41, 0x54]
#guard encodePop .r12 == expected #[0x41, 0x5c]

#guard frameBytes true { units16 := 1 } ==
  expected #[0x48, 0x81, 0xec, 0x10, 0, 0, 0]

#guard frameBytes false { units16 := 1 } ==
  expected #[0x48, 0x81, 0xc4, 0x10, 0, 0, 0]

#guard encodeSpill { index := 0 } .r12 ==
  expected #[0x4c, 0x89, 0xa5, 0xf8, 0xff, 0xff, 0xff]

#guard encodeReload .r12 { index := 0 } ==
  expected #[0x4c, 0x8b, 0xa5, 0xf8, 0xff, 0xff, 0xff]

#guard encodeCompare
    { width := .w64, left := .rax, right := .imm 42 } ==
  expected #[0x48, 0x81, 0xf8, 0x2a, 0, 0, 0]

#guard encodeCompare
    { width := .w32, left := .r9, right := .reg .r10 } ==
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
  match Ix.Compiler.X86.Encode.Program.encode
      Ix.Compiler.X86.Examples.arithmeticProgram with
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
  match Ix.Compiler.X86.Encode.Program.encode
      Ix.Compiler.X86.Examples.callProgram with
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
  match Ix.Compiler.X86.Encode.Program.encode
      Ix.Compiler.X86.Examples.runtimeProgram with
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
  match Ix.Compiler.X86.Encode.Program.encode
      Ix.Compiler.X86.Examples.invalidTargetProgram with
  | .error .malformedControl => true
  | _ => false

#guard malformedProgramRejected

end Ix.Compiler.X86.Encode.Examples
