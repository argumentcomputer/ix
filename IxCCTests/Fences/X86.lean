import IxCC.X86.Basic
import IxCC.X86.Table.Index
import IxCC.X86.Table.Safe
import IxCC.X86.Constructors
import IxCC.X86.StreamEffects
import IxCC.X86.ByteBranch
import IxCC.X86.ByteCall
import IxCC.X86.ByteControl
import IxCC.X86.DecodeWindow
import IxCC.X86.ELFLink
import IxCC.X86.ELFValidate
import IxCC.X86.EncodeExecution
import IxCC.X86.EncodeForms
import IxCC.X86.EncodeLength
import IxCC.X86.EncodePatch
import IxCC.X86.Eval
import IxCC.X86.ExactNat
import IxCC.X86.Memory
import IxCC.X86.ObjectExecution
import IxCC.X86.SafeControl
import IxCC.X86.SafeStepsObject
import IxCC.X86.StreamCalls
import IxCC.X86.StreamControl
import IxCC.X86.StreamExamples
import IxCC.X86.StreamIndexed
import IxCC.X86.StreamLayout
import IxCC.X86.StreamLinear
import IxCC.X86.StreamPermissions
import IxCC.X86.StreamRun
import IxCC.X86.StreamSpec
import IxCC.X86.StreamTrace

/-! Required axiom fences for X86; expected messages are preserved verbatim. -/

/-- info: 'IxCC.X86.Instr.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Instr.inV0

/-- info: 'IxCC.X86.Terminator.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Terminator.inV0

/-- info: 'IxCC.X86.Program.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Program.inV0

/-- info: 'IxCC.X86.Checked.inV0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Checked.inV0

/-- info: 'IxCC.X86.step_of_not_running' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.step_of_not_running

/-- info: 'IxCC.X86.Core.applyIntrinsicResult_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Core.applyIntrinsicResult_rsp

/-- info: 'IxCC.X86.Core.applyIntrinsicResult_calleeSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Core.applyIntrinsicResult_calleeSaved

/-- info: 'IxCC.X86.Memory.read64_write64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Memory.read64_write64

/-- info: 'IxCC.X86.Encode.instruction_decodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.instruction_decodeAt

/-- info: 'IxCC.X86.Encode.terminator_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.terminator_decode

/-- info: 'IxCC.X86.Encode.encoded_instruction_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.encoded_instruction_execution

/-- info: 'IxCC.X86.Encode.compare_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.compare_execution

/-- info: 'IxCC.X86.Encode.branch_bytes_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.branch_bytes_execution

/-- info: 'IxCC.X86.Encode.branch_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.branch_patch

/-- info: 'IxCC.X86.Encode.call_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.call_pair

/-- info: 'IxCC.X86.Encode.call_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.call_fault

/-- info: 'IxCC.X86.Encode.ret_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.ret_pair

/-- info: 'IxCC.X86.Encode.relative_resolves_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.relative_resolves_base

/-- info: 'IxCC.X86.Encode.patchSigned32_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.patchSigned32_splice

/-- info: 'IxCC.X86.Encode.signed32_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.signed32_checked

/-- info: 'IxCC.X86.Stream.pcOffset_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.pcOffset_injective

/-- info: 'IxCC.X86.Stream.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.check_sound

/-- info: 'IxCC.X86.Decode.decodeWindowAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Decode.decodeWindowAt_eq

/-- info: 'IxCC.X86.Stream.checkPrepared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.checkPrepared_eq

/-- info: 'IxCC.X86.Stream.checkIndexed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.checkIndexed_eq

/-- info: 'IxCC.X86.Stream.checkIndexed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.checkIndexed_sound

/-- info: 'IxCC.X86.Stream.linear_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.linear_step

/-- info: 'IxCC.X86.Stream.branch_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.branch_at

/-- info: 'IxCC.X86.Stream.branch_fall_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.branch_fall_at

/-- info: 'IxCC.X86.Stream.call_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.call_progress

/-- info: 'IxCC.X86.Stream.ret_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.ret_progress

/-- info: 'IxCC.X86.Stream.run_to_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.run_to_return

/-- info: 'IxCC.X86.Stream.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.run_with_calls

/-- info: 'IxCC.X86.Stream.run_permissions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.run_permissions

/-- info: 'IxCC.X86.StreamExamples.reused_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.StreamExamples.reused_safe

/-- info: 'IxCC.X86.StreamExamples.nested_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.StreamExamples.nested_safe

/-- info: 'IxCC.X86.ELF.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.check_sound

/-- info: 'IxCC.X86.ELF.Valid.text' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ELF.Valid.text

/-- info: 'IxCC.X86.ELF.Valid.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.Valid.entry

/-- info: 'IxCC.X86.ELF.Valid.exported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.Valid.exported

/-- info: 'IxCC.X86.ELFLink.pc32_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFLink.pc32_call

/-- info: 'IxCC.X86.ELFLink.Applied.resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFLink.Applied.resolves

/-- info: 'IxCC.X86.ELFLink.runtime_call_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFLink.runtime_call_transfer

/-- info: 'IxCC.X86.ObjectEval.run_from_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.run_from_typed

/-- info: 'IxCC.X86.ObjectEval.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.run_with_calls

/-- info: 'IxCC.X86.ExactNat.encode_some_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ExactNat.encode_some_iff

/-- info: 'IxCC.X86.ExactNat.add_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ExactNat.add_some_iff

/-- info: 'IxCC.X86.ExactNat.sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ExactNat.sub_toNat

/-- info: 'IxCC.X86.ObjectEval.run_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.run_safeSteps


/-! Instruction table (C2): kernel-decided table facts and the class-generic
E1/E2 laws. -/

/-- info: 'IxCC.X86.table_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.table_injective

/-- info: 'IxCC.X86.table_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.table_reachable

/-- info: 'IxCC.X86.table_shaped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.table_shaped

/-- info: 'IxCC.X86.table_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.table_bounded

/-- info: 'IxCC.X86.Encode.table_flagsFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.table_flagsFree

/-- info: 'IxCC.X86.Encode.row_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.row_decode

/-- info: 'IxCC.X86.Encode.instruction_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.instruction_decode

/-- info: 'IxCC.X86.Instr.mov_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Instr.mov_wellFormed

/-- info: 'IxCC.X86.Instr.alu_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Instr.alu_wellFormed

/-- info: 'IxCC.X86.Instr.allocFrame_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Instr.allocFrame_wellFormed

/-- info: 'IxCC.X86.Encode.row_execution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.row_execution

/-- info: 'IxCC.X86.Encode.instruction_execution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.instruction_execution

/-- info: 'IxCC.X86.Compare.holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Compare.holds_eq

/-- info: 'IxCC.X86.Decode.one_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Decode.one_stable

/-- info: 'IxCC.X86.Stream.run_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.run_pair

/-- info: 'IxCC.X86.Stream.operation_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.operation_pair

/-- info: 'IxCC.X86.executeInstr_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.executeInstr_alu

/-- info: 'IxCC.X86.executeInstr_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.executeInstr_load

/-! Phase 1 table rows (M1.B1): row safety, fused pairs, branch producers and the
failure exit. -/

/-- info: 'IxCC.X86.Op.safe_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Op.safe_ok

/-- info: 'IxCC.X86.Encode.compare_branch_bytes_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.compare_branch_bytes_execution

/-- info: 'IxCC.X86.executeTerminator_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.executeTerminator_compare

/-- info: 'IxCC.X86.Terminator.compare_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Terminator.compare_wellFormed

/-- info: 'IxCC.X86.Encode.produced_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.produced_flags

/-- info: 'IxCC.X86.Encode.fused_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.fused_execution

/-- info: 'IxCC.X86.Encode.fused_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.fused_decode

/-- info: 'IxCC.X86.Stream.fused_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.fused_progress

/-- info: 'IxCC.X86.cutAt_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.cutAt_suffix

/-- info: 'IxCC.X86.Stream.FramesMapped.suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.FramesMapped.suffix

/-- info: 'IxCC.X86.executeInstr_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.executeInstr_unwind

/-- info: 'IxCC.X86.Stream.unwind_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.unwind_progress

/-- info: 'IxCC.X86.unwind_inFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.unwind_inFrame

/-- info: 'IxCC.X86.Straight.Segment.safe_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.safe_unwind

/-- info: 'IxCC.X86.ObjectEval.run_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.run_exit

/-- info: 'IxCC.X86.StreamExamples.unwind_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.StreamExamples.unwind_safe
