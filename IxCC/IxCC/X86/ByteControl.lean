import IxCC.X86.EncodeExecution
import IxCC.X86.EncodePatch

/-! Local byte-PC and control-transfer laws. These consume encoded bytes and
state explicit return-slot and symbolic-PC obligations for later composition. -/

namespace IxCC.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

/-! ## Control rows on the byte machine -/

theorem restrict_test (flags : ByteEval.Flags) (condition : Condition) :
    (flags.restrict condition.reads).test condition = flags.test condition := by
  cases condition <;> rfl

/-- `jcc` takes its branch exactly when its condition holds on the current
flags, and faults when a flag it reads is undefined. -/
theorem execute_branch (condition : Condition) (displacement : Imm32) (length : Nat)
    (state : ByteEval.State) :
    ByteEval.execute ⟨.branch condition displacement, length⟩ state =
      match state.flags.test condition with
      | none => .error (.undefinedCondition condition)
      | some take => .ok { state with
          rip := if take then ByteEval.relative (state.rip + UInt64.ofNat length) displacement
            else state.rip + UInt64.ofNat length } := by
  simp only [ByteEval.execute, Decode.Operation.branch, Op.jccRel32, desc, Table.jccDesc, Table.jccSem,
    restrict_test]
  cases state.flags.test condition with
  | none => rfl
  | some take => cases take <;> rfl

theorem execute_jump (displacement : Imm32) (length : Nat) (state : ByteEval.State) :
    ByteEval.execute ⟨.jump displacement, length⟩ state =
      .ok { state with rip := ByteEval.relative (state.rip + UInt64.ofNat length) displacement } := rfl

theorem execute_call (displacement : Imm32) (length : Nat) (state : ByteEval.State) :
    ByteEval.execute ⟨.call displacement, length⟩ state =
      match state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + UInt64.ofNat length) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { state.core.setReg .rsp (state.core.readReg .rsp - 8) with memory }
          rip := ByteEval.relative (state.rip + UInt64.ofNat length) displacement, flags := state.flags } := by
  simp only [ByteEval.execute, Decode.Operation.call, Op.callRel32]
  cases state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + UInt64.ofNat length) <;> rfl

theorem execute_ret (length : Nat) (state : ByteEval.State) :
    ByteEval.execute ⟨.ret, length⟩ state =
      match state.core.memory.read64? (state.core.readReg .rsp) with
      | .error fault => .error (.memory fault)
      | .ok target => .ok { state with core := state.core.setReg .rsp (state.core.readReg .rsp + 8), rip := target } := by
  simp only [ByteEval.execute, Decode.Operation.ret, Op.retZO]
  cases state.core.memory.read64? (state.core.readReg .rsp) <;> rfl

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
  simp only [ByteEval.step, UInt64.sub_self, UInt64.toNat_zero, decode, ByteEval.execute, Decode.Operation.call, Op.callRel32]
  cases state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + 5) <;>
    simp [Except.mapError, ByteEval.relative]

theorem ret_bytes_execution (state : ByteEval.State) :
    ByteEval.step (byte 0xc3) state.rip state =
      match state.core.memory.read64? (state.core.readReg .rsp) with
      | .error fault => .error (.memory fault)
      | .ok target => .ok { state with core := state.core.setReg .rsp (state.core.readReg .rsp + 8), rip := target } := by
  have decode := ret_decodeAt ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at decode
  simp only [ByteEval.step, UInt64.sub_self, UInt64.toNat_zero, decode, ByteEval.execute, Decode.Operation.ret, Op.retZO]
  cases state.core.memory.read64? (state.core.readReg .rsp) <;> simp [Except.mapError]

theorem jump_bytes_execution (displacement : Imm32) (state : ByteEval.State) :
    ByteEval.step (byte 0xe9 ++ imm32Bytes displacement) state.rip state =
      .ok { state with rip := ByteEval.relative (state.rip + 5) displacement } := by
  have decode := jump_decodeAt displacement ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at decode
  simp [ByteEval.step, decode, ByteEval.execute, Decode.Operation.jump, Op.jmpRel32, ByteEval.relative]

end IxCC.X86.Encode
