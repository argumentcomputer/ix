import Compilatrix.X86.ByteControl

/-! The emitted CMP/Jcc/JMP recipe executes from its actual bytes. The
comparison is the `cmp` row the typed branch evaluates. -/

namespace Compilatrix.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def branchBytes (comparison : Compare) (condition : Condition) (yes no : Imm32) : ByteArray :=
  encodeCompare comparison ++ (bytes [0x0f, nearOpcode condition] ++ imm32Bytes yes) ++
    (byte 0xe9 ++ imm32Bytes no)

theorem jcc_placeholder_bytes (condition : Condition) :
    encodeOp (Op.jccRel32 condition) [.imm 0] = bytes [0x0f, nearOpcode condition] ++ imm32Bytes 0 := by
  have list := branch_bytes condition 0
  simp only [signExtend32_zero] at list
  simp [encodeOp, list, imm32Bytes, littleEndian, bytes_append]

theorem jmp_placeholder_bytes : encodeOp Op.jmpRel32 [.imm 0] = byte 0xe9 ++ imm32Bytes 0 := by
  have list := rel_bytes Op.jmpRel32 rfl rfl 0
  simp only [signExtend32_zero] at list
  simp [encodeOp, list, imm32Bytes, littleEndian, bytes_append, byte]
  rfl

theorem branchBytes_origin (comparison : Compare) (condition : Condition) (yes no : BlockId) :
    (encodeTerminator (.branch comparison condition yes no)).bytes = branchBytes comparison condition 0 0 := by
  simp [encodeTerminator, Chunk.append, Chunk.raw, rel32_bytes, branchBytes, jcc_placeholder_bytes,
    jmp_placeholder_bytes, ByteArray.append_assoc]

theorem branchBytes_compare (comparison : Compare) (condition : Condition) (yes no : Imm32) :
    Decode.decodeAt (branchBytes comparison condition yes no) 0 =
      some ⟨.op comparison.row.1 comparison.row.2, (encodeCompare comparison).size⟩ := by
  have decoded := decodeAt_of_one (encodeCompare comparison) ByteArray.empty
    ((bytes [0x0f, nearOpcode condition] ++ imm32Bytes yes) ++ (byte 0xe9 ++ imm32Bytes no))
    _ (encodeCompare_decode comparison _) (compare_size comparison).1 (compare_size comparison).2
  simpa [branchBytes, ByteArray.append_assoc] using decoded

theorem branchBytes_branch (comparison : Compare) (condition : Condition) (yes no : Imm32) :
    Decode.decodeAt (branchBytes comparison condition yes no) (encodeCompare comparison).size =
      some ⟨.branch condition yes, 6⟩ :=
  branch_decodeAt condition yes (encodeCompare comparison) (byte 0xe9 ++ imm32Bytes no)

theorem branchBytes_jump (comparison : Compare) (condition : Condition) (yes no : Imm32) :
    Decode.decodeAt (branchBytes comparison condition yes no) ((encodeCompare comparison).size + 6) =
      some ⟨.jump no, 5⟩ := by
  simpa [branchBytes, imm32Bytes] using jump_decodeAt no
    (encodeCompare comparison ++ (bytes [0x0f, nearOpcode condition] ++ imm32Bytes yes)) ByteArray.empty

def comparedState (comparison : Compare) (state : ByteEval.State) : ByteEval.State :=
  { state with
    rip := state.rip + UInt64.ofNat (encodeCompare comparison).size
    flags := comparison.flags state.core }

@[simp] theorem comparedState_test (comparison : Compare) (condition : Condition) (state : ByteEval.State) :
    (comparedState comparison state).flags.test condition = some (comparison.holds condition state.core) :=
  Compare.flags_test comparison condition state.core

theorem compare_step (comparison : Compare) (length : Nat) (state : ByteEval.State) :
    ByteEval.execute ⟨.op comparison.row.1 comparison.row.2, length⟩ state =
      .ok { state with rip := state.rip + UInt64.ofNat length, flags := comparison.flags state.core } := by
  have linear : comparison.row.1.linear = true := by
    cases comparison with
    | mk width left right => cases right <;> rfl
  rw [execute_linear linear, Compare.exec_eq, Compare.flags_eq]

theorem branch_step_compare (comparison : Compare) (condition : Condition) (yes no : Imm32)
    (state : ByteEval.State) :
    ByteEval.step (branchBytes comparison condition yes no) state.rip state =
      .ok (comparedState comparison state) := by
  simp only [ByteEval.step, UInt64.sub_self, UInt64.toNat_zero, branchBytes_compare, compare_step]
  rfl

theorem offset_after (rip : Word) (count : Nat) (bound : count < UInt64.size) :
    (rip + UInt64.ofNat count - rip).toNat = count := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel, UInt64.toNat_ofNat_of_lt' bound]

theorem branch_step_branch (comparison : Compare) (condition : Condition) (yes no : Imm32)
    (state : ByteEval.State) :
    ByteEval.step (branchBytes comparison condition yes no) state.rip (comparedState comparison state) =
      .ok { comparedState comparison state with
        rip := if comparison.holds condition state.core then
          ByteEval.relative ((comparedState comparison state).rip + 6) yes
        else (comparedState comparison state).rip + 6 } := by
  have bound := compare_size comparison
  have offset := offset_after state.rip (encodeCompare comparison).size (by
    simp only [UInt64.size]; omega)
  simp only [ByteEval.step, comparedState] at offset ⊢
  rw [offset, branchBytes_branch]
  dsimp only
  rw [execute_branch]
  change (match (comparedState comparison state).flags.test condition with
    | none => _ | some take => _) = _
  rw [comparedState_test]
  rfl

def fallthroughState (comparison : Compare) (state : ByteEval.State) : ByteEval.State :=
  { comparedState comparison state with rip := (comparedState comparison state).rip + 6 }

theorem branch_step_jump (comparison : Compare) (condition : Condition) (yes no : Imm32)
    (state : ByteEval.State) :
    ByteEval.step (branchBytes comparison condition yes no) state.rip (fallthroughState comparison state) =
      .ok { fallthroughState comparison state with
        rip := ByteEval.relative ((fallthroughState comparison state).rip + 5) no } := by
  have bound := compare_size comparison
  have offset := offset_after state.rip ((encodeCompare comparison).size + 6) (by
    simp only [UInt64.size]; omega)
  simp only [UInt64.ofNat_add] at offset
  change (state.rip + (UInt64.ofNat (encodeCompare comparison).size + 6) - state.rip).toNat =
    (encodeCompare comparison).size + 6 at offset
  simp only [ByteEval.step, fallthroughState, comparedState]
  rw [show state.rip + UInt64.ofNat (encodeCompare comparison).size + 6 =
    state.rip + (UInt64.ofNat (encodeCompare comparison).size + 6) by rw [UInt64.add_assoc]]
  rw [offset, branchBytes_jump]
  dsimp only
  rw [execute_jump]
  rfl

/-- Taken branches use CMP/Jcc; untaken branches additionally execute JMP.
The theorem reads real bytes, retains the comparison flags, and preserves the
entire core on both paths. -/
theorem branch_bytes_execution (comparison : Compare) (condition : Condition) (yes no : Imm32)
    (state : ByteEval.State) :
    ByteEval.run (branchBytes comparison condition yes no) state.rip
      (if comparison.holds condition state.core then 2 else 3) state =
      .ok { comparedState comparison state with
        rip := if comparison.holds condition state.core then
          ByteEval.relative ((comparedState comparison state).rip + 6) yes
        else ByteEval.relative ((comparedState comparison state).rip + 6 + 5) no } := by
  have jumped := branch_step_jump comparison condition yes no state
  simp only [fallthroughState] at jumped
  cases take : comparison.holds condition state.core <;>
    simp [take, ByteEval.run, branch_step_compare, branch_step_branch, jumped]

/-- Applying both actual rel32 fixups to the emitted terminator yields the
same bytes consumed by `branch_bytes_execution`. Layout supplies the signed
values and checks their range; the local patch law is valid for all Ints. -/
theorem branch_patch (comparison : Compare) (condition : Condition) (yes no : BlockId)
    (yesDisplacement noDisplacement : Int) :
    (do
      let first ← patchSigned32 (encodeTerminator (.branch comparison condition yes no)).bytes
        ((encodeCompare comparison).size + 2) yesDisplacement
      patchSigned32 first ((encodeCompare comparison).size + 7) noDisplacement) =
    .ok (branchBytes comparison condition (Int32.ofInt yesDisplacement).toUInt32
      (Int32.ofInt noDisplacement).toUInt32) := by
  have first : patchSigned32 (branchBytes comparison condition 0 0)
      ((encodeCompare comparison).size + 2) yesDisplacement =
      .ok (branchBytes comparison condition (Int32.ofInt yesDisplacement).toUInt32 0) := by
    simpa [branchBytes, signed32Bytes, imm32_zero_bytes, ByteArray.append_assoc] using
      patchSigned32_splice (encodeCompare comparison ++ bytes [0x0f, nearOpcode condition])
        (byte 0xe9 ++ bytes [0, 0, 0, 0]) 0 0 0 0 yesDisplacement
  have second : patchSigned32
      (branchBytes comparison condition (Int32.ofInt yesDisplacement).toUInt32 0)
      ((encodeCompare comparison).size + 7) noDisplacement =
      .ok (branchBytes comparison condition (Int32.ofInt yesDisplacement).toUInt32
        (Int32.ofInt noDisplacement).toUInt32) := by
    simpa [branchBytes, signed32Bytes, imm32_zero_bytes,
      ByteArray.append_assoc, Nat.add_assoc] using
      patchSigned32_splice
        (encodeCompare comparison ++ (bytes [0x0f, nearOpcode condition] ++ signed32Bytes yesDisplacement) ++ byte 0xe9)
        ByteArray.empty 0 0 0 0 noDisplacement
  rw [branchBytes_origin, first]
  exact second

end Compilatrix.X86.Encode
