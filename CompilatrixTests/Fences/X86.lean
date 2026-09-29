import Compilatrix.X86.Basic
import Compilatrix.X86.Table.Index
import Compilatrix.X86.Table.Safe
import Compilatrix.X86.Constructors
import Compilatrix.X86.StreamEffects
import Compilatrix.X86.ByteBranch
import Compilatrix.X86.ByteCall
import Compilatrix.X86.ByteControl
import Compilatrix.X86.DecodeWindow
import Compilatrix.X86.ELFLink
import Compilatrix.X86.ELFValidate
import Compilatrix.X86.EncodeExecution
import Compilatrix.X86.EncodeForms
import Compilatrix.X86.EncodeLength
import Compilatrix.X86.EncodePatch
import Compilatrix.X86.Eval
import Compilatrix.X86.ExactNat
import Compilatrix.X86.Memory
import Compilatrix.X86.ObjectExecution
import Compilatrix.X86.SafeStepsObject
import Compilatrix.X86.StreamCalls
import Compilatrix.X86.StreamControl
import Compilatrix.X86.StreamExamples
import Compilatrix.X86.StreamIndexed
import Compilatrix.X86.StreamLayout
import Compilatrix.X86.StreamLinear
import Compilatrix.X86.StreamPermissions
import Compilatrix.X86.StreamRun
import Compilatrix.X86.StreamSpec
import Compilatrix.X86.StreamTrace

/-! Required axiom fences for X86; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.X86.Instr.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Instr.inV0

/-- info: 'Compilatrix.X86.Terminator.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Terminator.inV0

/-- info: 'Compilatrix.X86.Program.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Program.inV0

/-- info: 'Compilatrix.X86.Checked.inV0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Checked.inV0

/-- info: 'Compilatrix.X86.step_of_not_running' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.step_of_not_running

/-- info: 'Compilatrix.X86.Core.applyIntrinsicResult_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Core.applyIntrinsicResult_rsp

/-- info: 'Compilatrix.X86.Core.applyIntrinsicResult_calleeSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Core.applyIntrinsicResult_calleeSaved

/-- info: 'Compilatrix.X86.Memory.read64_write64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Memory.read64_write64

/-- info: 'Compilatrix.X86.Encode.instruction_decodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.instruction_decodeAt

/-- info: 'Compilatrix.X86.Encode.terminator_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.terminator_decode

/-- info: 'Compilatrix.X86.Encode.encoded_instruction_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.encoded_instruction_execution

/-- info: 'Compilatrix.X86.Encode.compare_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.compare_execution

/-- info: 'Compilatrix.X86.Encode.branch_bytes_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.branch_bytes_execution

/-- info: 'Compilatrix.X86.Encode.branch_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.branch_patch

/-- info: 'Compilatrix.X86.Encode.call_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.call_pair

/-- info: 'Compilatrix.X86.Encode.call_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.call_fault

/-- info: 'Compilatrix.X86.Encode.ret_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.ret_pair

/-- info: 'Compilatrix.X86.Encode.relative_resolves_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.relative_resolves_base

/-- info: 'Compilatrix.X86.Encode.patchSigned32_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.patchSigned32_splice

/-- info: 'Compilatrix.X86.Encode.signed32_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.signed32_checked

/-- info: 'Compilatrix.X86.Stream.pcOffset_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.pcOffset_injective

/-- info: 'Compilatrix.X86.Stream.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.check_sound

/-- info: 'Compilatrix.X86.Decode.decodeWindowAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Decode.decodeWindowAt_eq

/-- info: 'Compilatrix.X86.Stream.checkPrepared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.checkPrepared_eq

/-- info: 'Compilatrix.X86.Stream.checkIndexed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.checkIndexed_eq

/-- info: 'Compilatrix.X86.Stream.checkIndexed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.checkIndexed_sound

/-- info: 'Compilatrix.X86.Stream.linear_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.linear_step

/-- info: 'Compilatrix.X86.Stream.branch_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.branch_at

/-- info: 'Compilatrix.X86.Stream.call_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.call_progress

/-- info: 'Compilatrix.X86.Stream.ret_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.ret_progress

/-- info: 'Compilatrix.X86.Stream.run_to_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_to_return

/-- info: 'Compilatrix.X86.Stream.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_with_calls

/-- info: 'Compilatrix.X86.Stream.run_permissions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_permissions

/-- info: 'Compilatrix.X86.StreamExamples.reused_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.StreamExamples.reused_safe

/-- info: 'Compilatrix.X86.StreamExamples.nested_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.StreamExamples.nested_safe

/-- info: 'Compilatrix.X86.ELF.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELF.check_sound

/-- info: 'Compilatrix.X86.ELF.Valid.text' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ELF.Valid.text

/-- info: 'Compilatrix.X86.ELF.Valid.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELF.Valid.entry

/-- info: 'Compilatrix.X86.ELFLink.pc32_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELFLink.pc32_call

/-- info: 'Compilatrix.X86.ELFLink.Applied.resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELFLink.Applied.resolves

/-- info: 'Compilatrix.X86.ELFLink.runtime_call_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELFLink.runtime_call_transfer

/-- info: 'Compilatrix.X86.ObjectEval.run_from_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.run_from_typed

/-- info: 'Compilatrix.X86.ObjectEval.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.run_with_calls

/-- info: 'Compilatrix.X86.ExactNat.encode_some_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ExactNat.encode_some_iff

/-- info: 'Compilatrix.X86.ExactNat.add_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ExactNat.add_some_iff

/-- info: 'Compilatrix.X86.ExactNat.sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ExactNat.sub_toNat

/-- info: 'Compilatrix.X86.ObjectEval.run_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.run_safeSteps


/-! Instruction table (C2): kernel-decided table facts and the class-generic
E1/E2 laws. -/

/-- info: 'Compilatrix.X86.table_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.table_injective

/-- info: 'Compilatrix.X86.table_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.table_reachable

/-- info: 'Compilatrix.X86.table_shaped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.table_shaped

/-- info: 'Compilatrix.X86.table_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.table_bounded

/-- info: 'Compilatrix.X86.Encode.table_flagsFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.table_flagsFree

/-- info: 'Compilatrix.X86.Encode.row_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.row_decode

/-- info: 'Compilatrix.X86.Encode.instruction_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.instruction_decode

/-- info: 'Compilatrix.X86.Instr.mov_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Instr.mov_wellFormed

/-- info: 'Compilatrix.X86.Instr.alu_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Instr.alu_wellFormed

/-- info: 'Compilatrix.X86.Instr.allocFrame_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Instr.allocFrame_wellFormed

/-- info: 'Compilatrix.X86.Encode.row_execution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.row_execution

/-- info: 'Compilatrix.X86.Encode.instruction_execution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.instruction_execution

/-- info: 'Compilatrix.X86.Compare.holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Compare.holds_eq

/-- info: 'Compilatrix.X86.Decode.one_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Decode.one_stable

/-- info: 'Compilatrix.X86.Stream.run_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_pair

/-- info: 'Compilatrix.X86.Stream.operation_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.operation_pair

/-- info: 'Compilatrix.X86.executeInstr_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.executeInstr_alu

/-- info: 'Compilatrix.X86.executeInstr_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.executeInstr_load

/-! Phase 1 table rows (M1.B1): row safety, fused pairs, branch producers and the
failure exit. -/

/-- info: 'Compilatrix.X86.Op.safe_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Op.safe_ok
