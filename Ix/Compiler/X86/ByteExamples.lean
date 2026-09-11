import Ix.Compiler.X86.ByteBranch
import Ix.Compiler.X86.ByteCall

/-! Small kernel-evaluated checks of independently specified bytes and effects.
The compiled gate supplies the larger matrix and complete native text runs. -/

namespace Ix.Compiler.X86.ByteExamples

open Encode (bytes)

-- REX changes byte-register code six to SIL, preserving RSI's upper bits.
#guard (ByteEval.step (bytes [0x40, 0xb6, 0x12]) 0x1000
  ⟨(Core.empty 0x8008).setReg .rsi 0x1234567890abcdef, 0x1000, {}⟩).toOption.map
    (fun state => (state.core.readReg .rsi, state.rip)) == some (0x1234567890abcd12, 0x1003)

-- A 32-bit register move clears the destination's upper half.
#guard (ByteEval.step (bytes [0x45, 0x89, 0xd1]) 0
  ⟨((Core.empty 0).setReg .r9 0xffffffffffffffff).setReg .r10 0x9876543280000000, 0, {}⟩).toOption.map
    (fun state => state.core.readReg .r9) == some 0x80000000

-- R12 is a valid extended SIB index; code four without REX.X means no index.
#guard Decode.one [0x4e, 0x8d, 0x8c, 0xe5, 0xff, 0xff, 0xff, 0xff] ==
  some (.lea .r9 { base := some .rbp, index := some .r12, scale := .eight, displacement := 0xffffffff }, [])
#guard Decode.one [0x4c, 0x8d, 0x0c, 0x25, 0xff, 0xff, 0xff, 0xff] ==
  some (.lea .r9 { displacement := 0xffffffff }, [])

-- The sign of the subtraction result alone gives the wrong signed answer.
#guard (ByteEval.aluFlags .sub .w64 0x8000000000000000 1).overflow == some true
#guard (ByteEval.aluFlags .sub .w64 0x8000000000000000 1).sign == some false
#guard (ByteEval.aluFlags .sub .w64 0x8000000000000000 1).test .signedLt == some true

-- imm32 is signed at width 64; POP RSP installs the popped value last.
#guard (ByteEval.step (bytes [0x48, 0x81, 0xc0, 0xff, 0xff, 0xff, 0xff]) 0
  ⟨(Core.empty 0).setReg .rax 0, 0, {}⟩).toOption.map (fun state => state.core.readReg .rax) ==
    some 0xffffffffffffffff
#guard (ByteEval.step (bytes [0x5c]) 0
  ⟨{ (Core.empty 0x8008) with memory := Memory.flat.write64 0x8008 0x9000 }, 0, {}⟩).toOption.map
    (fun state => state.core.readReg .rsp) == some 0x9000

#guard Decode.one [0x48, 0xb8, 1, 2, 3] == none
#guard Decode.one [0x88, 0xe0] == none
#guard (ByteEval.mulFlags .w64 0x7fffffffffffffff 2).zero == none
#guard (ByteEval.mulFlags .w64 0x7fffffffffffffff 2).overflow == some true

end Ix.Compiler.X86.ByteExamples
