import Ix.Compiler.X86.EncodeExecution
import Ix.Compiler.X86.EncodePatch

/-! Local byte-PC and control-transfer laws. These consume encoded bytes and
state explicit return-slot and symbolic-PC obligations for later composition. -/

namespace Ix.Compiler.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

theorem call_decodeAt (displacement : Imm32) (before after : ByteArray) :
    Decode.decodeAt (before ++ (byte 0xe8 ++ imm32Bytes displacement) ++ after) before.size =
      some ⟨.call displacement, 5⟩ := by
  simpa [imm32Bytes] using decodeAt_of_one (byte 0xe8 ++ imm32Bytes displacement) before after
    (.call displacement) (call_decode displacement after.data.toList) (by simp [imm32Bytes]) (by simp [imm32Bytes])

theorem jump_decodeAt (displacement : Imm32) (before after : ByteArray) :
    Decode.decodeAt (before ++ (byte 0xe9 ++ imm32Bytes displacement) ++ after) before.size =
      some ⟨.jump displacement, 5⟩ := by
  simpa [imm32Bytes] using decodeAt_of_one (byte 0xe9 ++ imm32Bytes displacement) before after
    (.jump displacement) (jump_decode displacement after.data.toList) (by simp [imm32Bytes]) (by simp [imm32Bytes])

theorem branch_decodeAt (condition : Condition) (displacement : Imm32) (before after : ByteArray) :
    Decode.decodeAt (before ++ (bytes [0x0f, nearOpcode condition] ++ imm32Bytes displacement) ++ after) before.size =
      some ⟨.branch condition displacement, 6⟩ := by
  simpa [imm32Bytes] using decodeAt_of_one (bytes [0x0f, nearOpcode condition] ++ imm32Bytes displacement)
    before after (.branch condition displacement) (branch_decode condition displacement after.data.toList)
    (by simp [imm32Bytes]) (by simp [imm32Bytes])

theorem ret_decodeAt (before after : ByteArray) :
    Decode.decodeAt (before ++ byte 0xc3 ++ after) before.size = some ⟨.ret, 1⟩ := by
  simpa using decodeAt_of_one (byte 0xc3) before after .ret (ret_decode after.data.toList) (by simp) (by simp)

theorem relative_resolves (next target : Nat) (fits : fitsSigned32 ((target : Int) - next) = true) :
    ByteEval.relative (UInt64.ofNat next) (Int32.ofInt ((target : Int) - next)).toUInt32 = UInt64.ofNat target := by
  apply UInt64.toBitVec_inj.mp
  simp only [ByteEval.relative, UInt64.toBitVec_add, UInt64.toBitVec_ofNat', signExtend32_ofInt _ fits]
  change BitVec.ofInt 64 (next : Int) + BitVec.ofInt 64 ((target : Int) - next) = BitVec.ofInt 64 (target : Int)
  rw [← BitVec.ofInt_add]
  congr 1
  omega

theorem relative_resolves_base (base : Word) (next target : Nat)
    (fits : fitsSigned32 ((target : Int) - next) = true) :
    ByteEval.relative (base + UInt64.ofNat next) (Int32.ofInt ((target : Int) - next)).toUInt32 =
      base + UInt64.ofNat target := by
  simpa [ByteEval.relative, UInt64.add_assoc] using congrArg (base + ·) (relative_resolves next target fits)

theorem call_bytes_execution (displacement : Imm32) (state : ByteEval.State) :
    ByteEval.step (byte 0xe8 ++ imm32Bytes displacement) state.rip state =
      match state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + 5) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { state.core.setReg .rsp (state.core.readReg .rsp - 8) with memory }
          rip := ByteEval.relative (state.rip + 5) displacement, flags := state.flags } := by
  have decode := call_decodeAt displacement ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at decode
  simp only [ByteEval.step, UInt64.sub_self, UInt64.toNat_zero, decode, ByteEval.execute]
  cases state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + 5) <;>
    simp [Except.mapError]

theorem ret_bytes_execution (state : ByteEval.State) :
    ByteEval.step (byte 0xc3) state.rip state =
      match state.core.memory.read64? (state.core.readReg .rsp) with
      | .error fault => .error (.memory fault)
      | .ok target => .ok { state with core := state.core.setReg .rsp (state.core.readReg .rsp + 8), rip := target } := by
  have decode := ret_decodeAt ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at decode
  simp only [ByteEval.step, UInt64.sub_self, UInt64.toNat_zero, decode, ByteEval.execute]
  cases state.core.memory.read64? (state.core.readReg .rsp) <;> simp [Except.mapError]

theorem jump_bytes_execution (displacement : Imm32) (state : ByteEval.State) :
    ByteEval.step (byte 0xe9 ++ imm32Bytes displacement) state.rip state =
      .ok { state with rip := ByteEval.relative (state.rip + 5) displacement } := by
  have decode := jump_decodeAt displacement ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at decode
  simp [ByteEval.step, decode, ByteEval.execute]

end Ix.Compiler.X86.Encode
