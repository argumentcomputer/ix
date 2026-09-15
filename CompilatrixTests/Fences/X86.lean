import Compilatrix.X86.AllocatingCall
import Compilatrix.X86.AllocatingExecution
import Compilatrix.X86.AllocatingFirst
import Compilatrix.X86.AllocatingMemory
import Compilatrix.X86.ArenaSpace
import Compilatrix.X86.Basic
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
import Compilatrix.X86.HeapCalls
import Compilatrix.X86.HeapCopies
import Compilatrix.X86.HeapGraph
import Compilatrix.X86.HeapObject
import Compilatrix.X86.HeapReject
import Compilatrix.X86.HeapTarget
import Compilatrix.X86.Memory
import Compilatrix.X86.NatCallsCapture
import Compilatrix.X86.NatCallsCheck
import Compilatrix.X86.NatCallsSim
import Compilatrix.X86.ObjectExecution
import Compilatrix.X86.PhysicalHeapCallSimulation
import Compilatrix.X86.PhysicalHeapFunctions
import Compilatrix.X86.PhysicalHeapGraphSelect
import Compilatrix.X86.PhysicalHeapObject
import Compilatrix.X86.PhysicalHeapRoot
import Compilatrix.X86.PhysicalHeapSourceObject
import Compilatrix.X86.PhysicalScalarCapturedExport
import Compilatrix.X86.PhysicalScalarCapturedHeap
import Compilatrix.X86.PhysicalScalarCapturedInit
import Compilatrix.X86.PhysicalScalarCapturedSourceApply
import Compilatrix.X86.PhysicalScalarCapturedSourceObject
import Compilatrix.X86.PhysicalScalarContracts
import Compilatrix.X86.PhysicalScalarControl
import Compilatrix.X86.PhysicalScalarExport
import Compilatrix.X86.PhysicalScalarObject
import Compilatrix.X86.PhysicalScalarSim
import Compilatrix.X86.PhysicalScalarSourceApply
import Compilatrix.X86.PhysicalScalarSourceHeap
import Compilatrix.X86.PhysicalScalarSourceObject
import Compilatrix.X86.PhysicalScalarValues
import Compilatrix.X86.PipelineSim
import Compilatrix.X86.RuntimeExecution
import Compilatrix.X86.RuntimeInput
import Compilatrix.X86.RuntimeReject
import Compilatrix.X86.RuntimeScan
import Compilatrix.X86.RuntimeTarget
import Compilatrix.X86.SafeStepsObject
import Compilatrix.X86.ScalarApply
import Compilatrix.X86.ScalarBind
import Compilatrix.X86.ScalarCapacity
import Compilatrix.X86.ScalarObject
import Compilatrix.X86.ScalarSimulation
import Compilatrix.X86.ScalarSourceApply
import Compilatrix.X86.ScalarSourceObject
import Compilatrix.X86.ScalarSourceSelect
import Compilatrix.X86.ScalarSourceSim
import Compilatrix.X86.ScalarTotal
import Compilatrix.X86.Select
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
import Compilatrix.X86.UniqueCounterFold
import Compilatrix.X86.UniqueResult
import Compilatrix.X86.UniqueSafeControl
import Compilatrix.X86.UniqueSafeLoop

/-! Required axiom fences for X86; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.X86.Instr.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Instr.inV0

/-- info: 'Compilatrix.X86.Terminator.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Terminator.inV0

/-- info: 'Compilatrix.X86.Program.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Program.inV0

/-- info: 'Compilatrix.X86.Checked.inV0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.Checked.inV0

/-- info: 'Compilatrix.X86.step_of_not_running' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.step_of_not_running

/-- info: 'Compilatrix.X86.Core.applyIntrinsicResult_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Core.applyIntrinsicResult_rsp

/-- info: 'Compilatrix.X86.Core.applyIntrinsicResult_calleeSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Core.applyIntrinsicResult_calleeSaved

/-- info: 'Compilatrix.X86.Select.Output.sourceValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.Output.sourceValid

/-- info: 'Compilatrix.X86.Select.select_scalarMoveProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.select_scalarMoveProgram

/-- info: 'Compilatrix.X86.Select.scalarMoveRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.scalarMoveRefines

/-- info: 'Compilatrix.X86.Select.selectScalarMoveRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.selectScalarMoveRefines

/-- info: 'Compilatrix.X86.Select.ScalarApply.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.ScalarApply.runs

/-- info: 'Compilatrix.X86.Select.sourceWord?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.sourceWord?_sound

/-- info: 'Compilatrix.X86.Select.Output.refinesSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.Output.refinesSuccessfulRun

/-- info: 'Compilatrix.X86.Select.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.sourceRefines

/-- info: 'Compilatrix.X86.Select.sourceScalarRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.sourceScalarRefines

/-- info: 'Compilatrix.X86.Memory.read64_write64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Memory.read64_write64

/-- info: 'Compilatrix.X86.UniqueExecution.mainAndRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueExecution.mainAndRelease

/-- info: 'Compilatrix.X86.UniqueExecution.NativeList.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueExecution.NativeList.nodup

/-- info: 'Compilatrix.X86.RuntimeExecution.validationSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.validationSteps

/-- info: 'Compilatrix.X86.RuntimeExecution.executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.executes

/-- info: 'Compilatrix.X86.RuntimeExecution.canonical_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.canonical_executes

/-- info: 'Compilatrix.X86.RuntimeExecution.Execution.mainSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.Execution.mainSafe

/-- info: 'Compilatrix.X86.RuntimeExecution.Execution.releaseSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.Execution.releaseSafe

/-- info: 'Compilatrix.X86.RuntimeExecution.lengthRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.lengthRejects

/-- info: 'Compilatrix.X86.RuntimeExecution.capacityRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.capacityRejects

/-- info: 'Compilatrix.X86.RuntimeExecution.inputWordsStep_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.inputWordsStep_eq

/-- info: 'Compilatrix.X86.UniqueCounterFold.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueCounterFold.state_eq

/-- info: 'Compilatrix.X86.UniqueCounterFold.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueCounterFold.trace

/-- info: 'Compilatrix.X86.UniqueCounterFold.instruction_saving' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueCounterFold.instruction_saving

/-- info: 'Compilatrix.X86.RuntimeTarget.controlCost_saving' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeTarget.controlCost_saving

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

/-- info: 'Compilatrix.X86.Stream.run_permissions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'Compilatrix.X86.NatCalls.Output.refinesSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.Output.refinesSuccessfulRun

/-- info: 'Compilatrix.X86.NatCalls.Execution.objectReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.Execution.objectReturns

/-- info: 'Compilatrix.X86.NatCalls.sourceObjectRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.sourceObjectRefines

/-- info: 'Compilatrix.X86.NatCalls.Expr.closed_evaluate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.Expr.closed_evaluate

/-- info: 'Compilatrix.X86.NatCalls.checkCapture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.checkCapture

/-- info: 'Compilatrix.X86.NatCalls.StaticCapture.evaluates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.StaticCapture.evaluates

/-- info: 'Compilatrix.X86.NatCalls.Output.reclaimsSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.Output.reclaimsSuccessfulRun

/-- info: 'Compilatrix.X86.NatCalls.sourceObjectReclaims' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.sourceObjectReclaims

/-- info: 'Compilatrix.X86.ExactNat.encode_some_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ExactNat.encode_some_iff

/-- info: 'Compilatrix.X86.ExactNat.add_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ExactNat.add_some_iff

/-- info: 'Compilatrix.X86.ExactNat.sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ExactNat.sub_toNat

/-- info: 'Compilatrix.X86.Scalar.Evaluates.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Evaluates.native

/-- info: 'Compilatrix.X86.Scalar.Checked.function_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Checked.function_total

/-- info: 'Compilatrix.X86.Scalar.Stack.rank_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Stack.rank_capacity

/-- info: 'Compilatrix.X86.ObjectEval.run_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.run_safeSteps

/-- info: 'Compilatrix.X86.Scalar.RootRun.objectResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.RootRun.objectResult

/-- info: 'Compilatrix.X86.Scalar.Source.programMatches_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Source.programMatches_sound

/-- info: 'Compilatrix.X86.Scalar.Source.raw_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Source.raw_evaluates

/-- info: 'Compilatrix.X86.Scalar.Source.Selected.sourceApplies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Source.Selected.sourceApplies

/-- info: 'Compilatrix.X86.Scalar.Source.Compiled.nativeReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Source.Compiled.nativeReturns

/-- info: 'Compilatrix.X86.Scalar.Source.Compiled.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Source.Compiled.sourceReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.atom_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.atom_sound

/-- info: 'Compilatrix.X86.PhysicalScalar.edge_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.edge_transfer

/-- info: 'Compilatrix.X86.PhysicalScalar.Runs.call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Runs.call

/-- info: 'Compilatrix.X86.PhysicalScalar.Code.simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Code.simulate

/-- info: 'Compilatrix.X86.PhysicalScalar.Selected.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Selected.contract

/-- info: 'Compilatrix.X86.PhysicalScalar.Runs.agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Runs.agrees

/-- info: 'Compilatrix.X86.PhysicalScalar.ExportPath.runMain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.ExportPath.runMain

/-- info: 'Compilatrix.X86.PhysicalScalar.Compiled.nativeReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Compiled.nativeReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.Compiled.physicalReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Compiled.physicalReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.closureStore.applied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.closureStore.applied

/-- info: 'Compilatrix.X86.PhysicalScalar.Exported.sourceFunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Exported.sourceFunction

/-- info: 'Compilatrix.X86.PhysicalScalar.Exported.sourceRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Exported.sourceRun

/-- info: 'Compilatrix.X86.PhysicalScalar.Exported.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Exported.sourceReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.Exported.sourceNatReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Exported.sourceNatReturns

/-- info: 'Compilatrix.X86.Scalar.Bound.evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Scalar.Bound.evaluates

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Heap.owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Heap.owned

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Heap.spent_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Heap.spent_empty

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Heap.applied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Heap.applied

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.checkInitializer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.checkInitializer

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Initialized.reclaimed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Initialized.reclaimed

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Compiled.nativeReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Compiled.nativeReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Compiled.physicalReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Compiled.physicalReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceFunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceFunction

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceRun

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceReturns

/-- info: 'Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceNatReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalScalar.Captured.Compiled.sourceNatReturns

/-- info: 'Compilatrix.X86.UniqueABI.Layout.enough_bytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueABI.Layout.enough_bytes_iff

/-- info: 'Compilatrix.X86.UniqueABI.enough_cells_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueABI.enough_cells_iff

/-- info: 'Compilatrix.X86.UniqueABI.one_byte_short' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueABI.one_byte_short

/-- info: 'Compilatrix.X86.RuntimeExecution.executes_of_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.executes_of_bytes

/-- info: 'Compilatrix.X86.RuntimeExecution.capacityRejects_of_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.capacityRejects_of_bytes

/-- info: 'Compilatrix.X86.UniqueExecution.Trace.safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueExecution.Trace.safeSteps

/-- info: 'Compilatrix.X86.UniqueExecution.loopSafeStepsFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueExecution.loopSafeStepsFor

/-- info: 'Compilatrix.X86.UniqueABI.Realizes.writeOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueABI.Realizes.writeOutside

/-- info: 'Compilatrix.X86.Steps.rejecting_permissions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Steps.rejecting_permissions

/-- info: 'Compilatrix.X86.Allocating.Stack.callAligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Allocating.Stack.callAligned

/-- info: 'Compilatrix.X86.Allocating.Stack.returnClean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Allocating.Stack.returnClean

/-- info: 'Compilatrix.X86.Allocating.allocatorSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Allocating.allocatorSteps

/-- info: 'Compilatrix.X86.Allocating.firstState_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Allocating.firstState_words

/-- info: 'Compilatrix.X86.Allocating.firstState_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Allocating.firstState_invariant

/-- info: 'Compilatrix.X86.Allocating.mainSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Allocating.mainSteps

/-- info: 'Compilatrix.X86.RuntimeExecution.capacityRejectedSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.capacityRejectedSteps

/-- info: 'Compilatrix.X86.HeapCopies.execute_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapCopies.execute_trace

/-- info: 'Compilatrix.X86.HeapCopies.execute_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapCopies.execute_at

/-- info: 'Compilatrix.X86.HeapCopies.execute_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapCopies.execute_preserves

/-- info: 'Compilatrix.X86.HeapRuns.call_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapRuns.call_steps

/-- info: 'Compilatrix.X86.PhysicalHeap.Code.simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Code.simulate

/-- info: 'Compilatrix.X86.PhysicalHeap.Output.summaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Output.summaries

/-- info: 'Compilatrix.X86.PhysicalHeap.Output.physicalReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Output.physicalReturns

/-- info: 'Compilatrix.X86.HeapEntry.RootRun.object' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapEntry.RootRun.object

/-- info: 'Compilatrix.X86.PhysicalHeap.Compiled.policyReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Compiled.policyReturns

/-- info: 'Compilatrix.X86.PhysicalHeap.Compiled.physicalReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Compiled.physicalReturns

/-- info: 'Compilatrix.X86.HeapEntry.root_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapEntry.root_reject

/-- info: 'Compilatrix.X86.PhysicalHeap.Compiled.rejectsCapacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Compiled.rejectsCapacity

/-- info: 'Compilatrix.X86.PhysicalHeap.Exported.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Exported.sourceReturns

/-- info: 'Compilatrix.X86.PhysicalHeap.Exported.sourceNatReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Exported.sourceNatReturns

/-- info: 'Compilatrix.X86.HeapTarget.checkCandidate_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapTarget.checkCandidate_program

/-- info: 'Compilatrix.X86.PhysicalHeap.Graph.checkFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.PhysicalHeap.Graph.checkFunction

/-- info: 'Compilatrix.X86.HeapGraph.checkCandidate_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.HeapGraph.checkCandidate_program
