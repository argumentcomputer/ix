import IxCC.X86.ByteControl

/-! The emitted producer/Jcc/JMP recipe executes from its actual bytes. The
producer is the row the typed branch runs (a `cmp` or `test` in any operand
form, or `add`/`sub` for carry and borrow); a compare-and-branch is the
instance whose producer is its comparison's `cmp` row. -/

namespace IxCC.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def branchBytes (producer : Op) (args : List Arg) (condition : Condition) (yes no : Imm32) : ByteArray :=
  encodeOp producer args ++ (bytes [0x0f, nearOpcode condition] ++ imm32Bytes yes) ++
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

theorem branchBytes_origin (producer : Op) (args : List Arg) (condition : Condition) (yes no : BlockId) :
    (encodeTerminator (.branch producer args condition yes no)).bytes = branchBytes producer args condition 0 0 := by
  simp [encodeTerminator, Chunk.append, Chunk.raw, rel32_bytes, branchBytes, jcc_placeholder_bytes,
    jmp_placeholder_bytes, ByteArray.append_assoc]

theorem branchBytes_producer {producer : Op} {args : List Arg} (row : producer ∈ Op.rows)
    (ok : producer.argsOk args = true) (condition : Condition) (yes no : Imm32) :
    Decode.decodeAt (branchBytes producer args condition yes no) 0 =
      some ⟨.op producer args, (encodeOp producer args).size⟩ := by
  have decoded := decodeAt_of_one (encodeOp producer args) ByteArray.empty
    ((bytes [0x0f, nearOpcode condition] ++ imm32Bytes yes) ++ (byte 0xe9 ++ imm32Bytes no))
    _ (encodeOp_decode producer args row ok _) (row_size row args).1 (row_size row args).2
  simpa [branchBytes, ByteArray.append_assoc] using decoded

theorem branchBytes_branch (producer : Op) (args : List Arg) (condition : Condition) (yes no : Imm32) :
    Decode.decodeAt (branchBytes producer args condition yes no) (encodeOp producer args).size =
      some ⟨.branch condition yes, 6⟩ :=
  branch_decodeAt condition yes (encodeOp producer args) (byte 0xe9 ++ imm32Bytes no)

theorem branchBytes_jump (producer : Op) (args : List Arg) (condition : Condition) (yes no : Imm32) :
    Decode.decodeAt (branchBytes producer args condition yes no) ((encodeOp producer args).size + 6) =
      some ⟨.jump no, 5⟩ := by
  simpa [branchBytes, imm32Bytes] using jump_decodeAt no
    (encodeOp producer args ++ (bytes [0x0f, nearOpcode condition] ++ imm32Bytes yes)) ByteArray.empty

/-- The state after the producer: its core and flags, RIP past its bytes. -/
def producedState (producer : Op) (args : List Arg) (state : ByteEval.State) (core : Core)
    (flags : ByteEval.Flags) : ByteEval.State :=
  { core, flags, rip := state.rip + UInt64.ofNat (encodeOp producer args).size }

theorem producer_step {producer : Op} {args : List Arg} (linear : producer.linear = true) (length : Nat)
    (state : ByteEval.State) {core : Core} {flags : ByteEval.Flags}
    (produced : producer.exec args state.core state.flags = .ok (core, flags)) :
    ByteEval.execute ⟨.op producer args, length⟩ state = .ok { core, flags, rip := state.rip + UInt64.ofNat length } := by
  rw [execute_linear linear, produced]

theorem branch_step_producer {producer : Op} {args : List Arg} (row : producer ∈ Op.rows)
    (ok : producer.argsOk args = true) (linear : producer.linear = true) (condition : Condition) (yes no : Imm32)
    (state : ByteEval.State) {core : Core} {flags : ByteEval.Flags}
    (produced : producer.exec args state.core state.flags = .ok (core, flags)) :
    ByteEval.step (branchBytes producer args condition yes no) state.rip state =
      .ok (producedState producer args state core flags) := by
  simp only [ByteEval.step, UInt64.sub_self, UInt64.toNat_zero, branchBytes_producer row ok,
    producer_step linear _ state produced]
  rfl

theorem offset_after (rip : Word) (count : Nat) (bound : count < UInt64.size) :
    (rip + UInt64.ofNat count - rip).toNat = count := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel, UInt64.toNat_ofNat_of_lt' bound]

theorem branch_step_branch {producer : Op} {args : List Arg} (row : producer ∈ Op.rows) (condition : Condition)
    (yes no : Imm32) (state : ByteEval.State) (core : Core) {flags : ByteEval.Flags} {take : Bool}
    (tested : flags.test condition = some take) :
    ByteEval.step (branchBytes producer args condition yes no) state.rip (producedState producer args state core flags) =
      .ok { producedState producer args state core flags with
        rip := if take then ByteEval.relative ((producedState producer args state core flags).rip + 6) yes
        else (producedState producer args state core flags).rip + 6 } := by
  have bound := row_size row args
  have offset := offset_after state.rip (encodeOp producer args).size (by
    simp only [UInt64.size]; omega)
  simp only [ByteEval.step, producedState] at offset ⊢
  rw [offset, branchBytes_branch]
  dsimp only
  rw [execute_branch]
  change (match flags.test condition with | none => _ | some take => _) = _
  rw [tested]
  rfl

def fallthroughState (producer : Op) (args : List Arg) (state : ByteEval.State) (core : Core)
    (flags : ByteEval.Flags) : ByteEval.State :=
  { producedState producer args state core flags with rip := (producedState producer args state core flags).rip + 6 }

theorem branch_step_jump {producer : Op} {args : List Arg} (row : producer ∈ Op.rows) (condition : Condition)
    (yes no : Imm32) (state : ByteEval.State) (core : Core) (flags : ByteEval.Flags) :
    ByteEval.step (branchBytes producer args condition yes no) state.rip (fallthroughState producer args state core flags) =
      .ok { fallthroughState producer args state core flags with
        rip := ByteEval.relative ((fallthroughState producer args state core flags).rip + 5) no } := by
  have bound := row_size row args
  have offset := offset_after state.rip ((encodeOp producer args).size + 6) (by
    simp only [UInt64.size]; omega)
  simp only [UInt64.ofNat_add] at offset
  change (state.rip + (UInt64.ofNat (encodeOp producer args).size + 6) - state.rip).toNat =
    (encodeOp producer args).size + 6 at offset
  simp only [ByteEval.step, fallthroughState, producedState]
  rw [show state.rip + UInt64.ofNat (encodeOp producer args).size + 6 =
    state.rip + (UInt64.ofNat (encodeOp producer args).size + 6) by rw [UInt64.add_assoc]]
  rw [offset, branchBytes_jump]
  dsimp only
  rw [execute_jump]
  rfl

/-- Taken branches run the producer and Jcc; untaken branches also run JMP.
The theorem reads real bytes, keeps the producer's core and flags, and holds
for any producer row that succeeds with the condition's flags defined. -/
theorem branch_bytes_execution {producer : Op} {args : List Arg} (row : producer ∈ Op.rows)
    (ok : producer.argsOk args = true) (linear : producer.linear = true) (condition : Condition)
    (yes no : Imm32) (state : ByteEval.State) {core : Core} {flags : ByteEval.Flags}
    (produced : producer.exec args state.core state.flags = .ok (core, flags)) {take : Bool}
    (tested : flags.test condition = some take) :
    ByteEval.run (branchBytes producer args condition yes no) state.rip (if take then 2 else 3) state =
      .ok { producedState producer args state core flags with
        rip := if take then ByteEval.relative ((producedState producer args state core flags).rip + 6) yes
        else ByteEval.relative ((producedState producer args state core flags).rip + 6 + 5) no } := by
  have jumped := branch_step_jump (args := args) row condition yes no state core flags
  simp only [fallthroughState] at jumped
  have first := branch_step_producer row ok linear condition yes no state produced
  have second := branch_step_branch row condition yes no state core (args := args) tested
  cases take <;> simp [ByteEval.run, first, second, jumped]

/-- The state after a comparison's `cmp` row. -/
def comparedState (comparison : Compare) (state : ByteEval.State) : ByteEval.State :=
  producedState comparison.row.1 comparison.row.2 state state.core (comparison.flags state.core)

@[simp] theorem comparedState_test (comparison : Compare) (condition : Condition) (state : ByteEval.State) :
    (comparedState comparison state).flags.test condition = some (comparison.holds condition state.core) :=
  Compare.flags_test comparison condition state.core

theorem compare_produced (comparison : Compare) (state : ByteEval.State) :
    comparison.row.1.exec comparison.row.2 state.core state.flags = .ok (state.core, comparison.flags state.core) := by
  rw [Compare.exec_eq, Compare.flags_eq]

/-- The compare-and-branch instance of `branch_bytes_execution`: the
comparison's `cmp` row keeps the core and its flags decide the branch. -/
theorem compare_branch_bytes_execution (comparison : Compare) (condition : Condition) (yes no : Imm32)
    (state : ByteEval.State) :
    ByteEval.run (branchBytes comparison.row.1 comparison.row.2 condition yes no) state.rip
      (if comparison.holds condition state.core then 2 else 3) state =
      .ok { comparedState comparison state with
        rip := if comparison.holds condition state.core then
          ByteEval.relative ((comparedState comparison state).rip + 6) yes
        else ByteEval.relative ((comparedState comparison state).rip + 6 + 5) no } :=
  branch_bytes_execution (Compare.row_ok comparison).1 (Compare.row_ok comparison).2 (Compare.row_linear comparison)
    condition yes no state (compare_produced comparison state) (Compare.flags_test comparison condition state.core)

/-- Applying both actual rel32 fixups to the emitted terminator yields the
same bytes consumed by `branch_bytes_execution`. Layout supplies the signed
values and checks their range; the local patch law is valid for all Ints. -/
theorem branch_patch (producer : Op) (args : List Arg) (condition : Condition) (yes no : BlockId)
    (yesDisplacement noDisplacement : Int) :
    (do
      let first ← patchSigned32 (encodeTerminator (.branch producer args condition yes no)).bytes
        ((encodeOp producer args).size + 2) yesDisplacement
      patchSigned32 first ((encodeOp producer args).size + 7) noDisplacement) =
    .ok (branchBytes producer args condition (Int32.ofInt yesDisplacement).toUInt32
      (Int32.ofInt noDisplacement).toUInt32) := by
  have first : patchSigned32 (branchBytes producer args condition 0 0)
      ((encodeOp producer args).size + 2) yesDisplacement =
      .ok (branchBytes producer args condition (Int32.ofInt yesDisplacement).toUInt32 0) := by
    simpa [branchBytes, signed32Bytes, imm32_zero_bytes, ByteArray.append_assoc] using
      patchSigned32_splice (encodeOp producer args ++ bytes [0x0f, nearOpcode condition])
        (byte 0xe9 ++ bytes [0, 0, 0, 0]) 0 0 0 0 yesDisplacement
  have second : patchSigned32
      (branchBytes producer args condition (Int32.ofInt yesDisplacement).toUInt32 0)
      ((encodeOp producer args).size + 7) noDisplacement =
      .ok (branchBytes producer args condition (Int32.ofInt yesDisplacement).toUInt32
        (Int32.ofInt noDisplacement).toUInt32) := by
    simpa [branchBytes, signed32Bytes, imm32_zero_bytes,
      ByteArray.append_assoc, Nat.add_assoc] using
      patchSigned32_splice
        (encodeOp producer args ++ (bytes [0x0f, nearOpcode condition] ++ signed32Bytes yesDisplacement) ++ byte 0xe9)
        ByteArray.empty 0 0 0 0 noDisplacement
  rw [branchBytes_origin, first]
  exact second

end IxCC.X86.Encode
