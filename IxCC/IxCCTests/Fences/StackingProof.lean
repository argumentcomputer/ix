import IxCC.Xv.Stacking.Proof.Shape
import IxCC.Xv.Stacking.Proof.Steps
import IxCC.Xv.Stacking.Proof.Exit
import IxCC.Xv.Stacking.Proof.Trunc
import IxCC.Xv.Stacking.Proof.RowRel
import IxCC.Xv.Stacking.Proof.RowXl
import IxCC.Xv.Stacking.Proof.InstXl
import IxCC.Xv.Stacking.Proof.Code
import IxCC.Xv.Stacking.Proof.Match
import IxCC.Xv.Stacking.Proof.Cells
import IxCC.Xv.Stacking.Proof.Chain
import IxCC.Xv.Stacking.Proof.Writes
import IxCC.Xv.Stacking.Proof.Body
import IxCC.Xv.Stacking.Proof.Machine
import IxCC.Xv.Stacking.Proof.StepBody
import IxCC.Xv.Stacking.Proof.StepTerm
import IxCC.Xv.Stacking.Proof.Call
import IxCC.Xv.Stacking.Proof.CallFacts
import IxCC.Xv.Stacking.Proof.StepCall
import IxCC.Xv.Stacking.Proof.CallMatch
import IxCC.Xv.Stacking.Proof.CallRun
import IxCC.Xv.Stacking.Proof.CallStep
import IxCC.Xv.Stacking.Proof.Return
import IxCC.Xv.Stacking.Proof.RetStep
import IxCC.Xv.Stacking.Proof.RetFacts
import IxCC.Xv.Stacking.Proof.RetMatch
import IxCC.Xv.Stacking.Proof.TailMatch
import IxCC.Xv.Stacking.Proof.TailStep
import IxCC.Xv.Stacking.Proof.WrapperExit
import IxCC.Xv.Stacking.Proof.Sim
import IxCC.Xv.Stacking.Proof.WrapperSteps
import IxCC.Xv.Stacking.Proof.WrapperProof
import IxCC.Xv.Stacking.Proof.WrapperHead
import IxCC.Xv.Stacking.Proof.WrapperCall
import IxCC.Xv.Stacking.Proof.WrapperEntry
import IxCC.Xv.Stacking.Proof.Ends

/-! Required axiom fences for the stacking and wrapper proofs (M2.6b
deliverables 2-3): the stacked program's shape and checks (`run_ok`,
`func_at`, `main_at`, `exit_at`), rows, fused pairs, moves and zeroing in
Xl and in the stacked code, the stacking invariant (`Match`) and its frame
cells, every Xl step as checked machine steps (`step_op`, `step_fused`,
`step_move`, `step_zero`, `step_jmp`, `step_jcc`, `step_fail`,
`step_call`, `step_ret`, `step_tail`, `step_done`, `step_sim`), the
failure exit (`Wrapper.fail_safe`), the simulation over clocked runs
(`sim`), the export wrapper's head, `Nat` check, marshalling and call
(`wrapper_head`, `wrapper_pre`, `wrapper_call`, `wrapper_entry`,
`wrapper_overflow`), its success exit (`success_exit`), and 05 §6.2's
conclusion at the stacked level (`stacked_ends`, `run_ends`). Generated
from the proof modules' public theorems; expected messages are preserved
verbatim. -/

/-- info: 'IxCC.Xv.Stacking.Proof.bind_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.bind_ok

/-- info: 'IxCC.Xv.Stacking.Proof.mapError_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mapError_ok

/-- info: 'IxCC.Xv.Stacking.Proof.mapM_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mapM_ok

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_place' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_place

/-- info: 'IxCC.Xv.Stacking.Proof.placeList_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.placeList_length

/-- info: 'IxCC.Xv.Stacking.Proof.placeList_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.placeList_get

/-- info: 'IxCC.Xv.Stacking.Proof.placeExports_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.placeExports_eq

/-- info: 'IxCC.Xv.Stacking.Proof.placeFuncs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.placeFuncs_eq

/-- info: 'IxCC.Xv.Stacking.Proof.withLayouts_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.withLayouts_length

/-- info: 'IxCC.Xv.Stacking.Proof.withLayouts_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.withLayouts_get

/-- info: 'IxCC.Xv.Stacking.Proof.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.run_ok

/-- info: 'IxCC.Xv.Stacking.Proof.flatten_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.flatten_getElem?

/-- info: 'IxCC.Xv.Stacking.Proof.take_sum_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.take_sum_eq

/-- info: 'IxCC.Xv.Stacking.Proof.flatten_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.flatten_length

/-- info: 'IxCC.Xv.Stacking.Proof.mapM_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mapM_lengths

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_insert_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_insert_get

/-- info: 'IxCC.Xv.Stacking.Proof.emitFunc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.emitFunc_ok

/-- info: 'IxCC.Xv.Stacking.Proof.emitFunc_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.emitFunc_length

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_length

/-- info: 'IxCC.Xv.Stacking.Proof.wrapperOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapperOf_ok

/-- info: 'IxCC.Xv.Stacking.Proof.placed_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.placed_get

/-- info: 'IxCC.Xv.Stacking.Proof.placed_fn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.placed_fn

/-- info: 'IxCC.Xv.Stacking.Proof.entries_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entries_get

/-- info: 'IxCC.Xv.Stacking.Proof.func_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.func_at

/-- info: 'IxCC.Xv.Stacking.Proof.exit_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.exit_at

/-- info: 'IxCC.Xv.Stacking.Proof.withLayouts_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.withLayouts_mem

/-- info: 'IxCC.Xv.Stacking.Proof.main_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.main_at

/-- info: 'IxCC.X86.inFrame_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.inFrame_eq

/-- info: 'IxCC.X86.Straight.Segment.safeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.safeAt

/-- info: 'IxCC.X86.Straight.Segment.safe_op' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.safe_op

/-- info: 'IxCC.X86.Straight.Segment.safe_fused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.safe_fused

/-- info: 'IxCC.X86.Straight.Segment.safe_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.safe_exec

/-- info: 'IxCC.X86.slotReads_noMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.slotReads_noMem

/-- info: 'IxCC.X86.slotWrites_noMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.slotWrites_noMem

/-- info: 'IxCC.X86.footprint_noMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.footprint_noMem

/-- info: 'IxCC.X86.Straight.Segment.of_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.of_block

/-- info: 'IxCC.X86.Straight.Segment.left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.left

/-- info: 'IxCC.X86.Straight.Segment.right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Straight.Segment.right

/-- info: 'IxCC.X86.OperationSafe.of_noMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.OperationSafe.of_noMemory

/-- info: 'IxCC.X86.BlockCode.safe_ret_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.BlockCode.safe_ret_top

/-- info: 'IxCC.Xv.Stacking.Proof.EntryFrame.cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.EntryFrame.cut

/-- info: 'IxCC.Xv.Stacking.Proof.signExtend32_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.signExtend32_ofNat

/-- info: 'IxCC.Xv.Stacking.Proof.signExtend32_ofInt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.signExtend32_ofInt_neg

/-- info: 'IxCC.Xv.Stacking.Proof.rspAt_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.rspAt_eval

/-- info: 'IxCC.Xv.Stacking.Proof.rspBelow_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.rspBelow_eval

/-- info: 'IxCC.Xv.Stacking.Proof.ctxAt_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ctxAt_eval

/-- info: 'IxCC.Xv.Stacking.Proof.entrySpCell_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entrySpCell_eval

/-- info: 'IxCC.Xv.Stacking.Proof.stackLimitCell_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.stackLimitCell_eval

/-- info: 'IxCC.Xv.Stacking.Proof.stackBudgetCell_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.stackBudgetCell_eval

/-- info: 'IxCC.Xv.Stacking.Proof.addRsp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.addRsp_eq

/-- info: 'IxCC.Xv.Stacking.Proof.subRsp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.subRsp_eq

/-- info: 'IxCC.Xv.Stacking.Proof.exec_addRsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.exec_addRsp

/-- info: 'IxCC.Xv.Stacking.Proof.exec_subRsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.exec_subRsp

/-- info: 'IxCC.Xv.Stacking.Proof.pop_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.pop_footprint

/-- info: 'IxCC.Xv.Stacking.Proof.readReg_setReg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readReg_setReg'

/-- info: 'IxCC.Xv.Stacking.Proof.pops_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.pops_safe

/-- info: 'IxCC.Xv.Stacking.Proof.addRsp_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.addRsp_footprint

/-- info: 'IxCC.Xv.Stacking.Proof.subRsp_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.subRsp_footprint

/-- info: 'IxCC.Xv.Stacking.Proof.seg_safe_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.seg_safe_reg

/-- info: 'IxCC.Xv.Stacking.Proof.wrapperEpilogue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapperEpilogue_eq

/-- info: 'IxCC.Xv.Stacking.Proof.epilogue_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.epilogue_safe

/-- info: 'IxCC.Xv.Stacking.Proof.ExitGroupAt.fail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ExitGroupAt.fail

/-- info: 'IxCC.Xv.Stacking.Proof.ExitGroupAt.failExit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ExitGroupAt.failExit

/-- info: 'IxCC.Xv.Stacking.Proof.Wrapper.fail_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Wrapper.fail_safe

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.length

/-- info: 'IxCC.Xv.Stacking.Proof.setWidth_of_truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.setWidth_of_truncate

/-- info: 'IxCC.Xv.Stacking.Proof.truncate_of_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.truncate_of_eq

/-- info: 'IxCC.Xv.Stacking.Proof.TruncEq.truncate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.TruncEq.truncate

/-- info: 'IxCC.Xv.Stacking.Proof.aluFlags_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.aluFlags_congr

/-- info: 'IxCC.Xv.Stacking.Proof.mulFlags_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mulFlags_congr

/-- info: 'IxCC.Xv.Stacking.Proof.shiftCount_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.shiftCount_congr

/-- info: 'IxCC.Xv.Stacking.Proof.ResW.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ResW.nil

/-- info: 'IxCC.Xv.Stacking.Proof.ResW.same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ResW.same

/-- info: 'IxCC.Xv.Stacking.Proof.ResW.one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ResW.one

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.two

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.one

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.three

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.nil'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.nil'

/-- info: 'IxCC.Xv.Stacking.Proof.aluSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.aluSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.cmpSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cmpSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.testSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.testSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.moveSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.moveSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.zeroExtendSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zeroExtendSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.mulSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mulSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.shiftSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.shiftSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.divSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.divSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.setccSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.setccSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.cmovSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cmovSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.controlSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.controlSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.jccSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.jccSem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.arith_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.arith_rel

/-- info: 'IxCC.Xv.Stacking.Proof.arithDesc_implicit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.arithDesc_implicit

/-- info: 'IxCC.Xv.Stacking.Proof.sem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.sem_rel

/-- info: 'IxCC.Xv.Stacking.Proof.rangeAllowed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.rangeAllowed_iff

/-- info: 'IxCC.Xv.Stacking.Proof.width_bits' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.width_bits

/-- info: 'IxCC.Xv.Stacking.Proof.width_bytes_le' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.width_bytes_le

/-- info: 'IxCC.Xv.Stacking.Proof.width_bytes_pos' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.width_bytes_pos

/-- info: 'IxCC.Xv.Stacking.Proof.readLittle_succ_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readLittle_succ_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.readLittle_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readLittle_lt

/-- info: 'IxCC.Xv.Stacking.Proof.readLittle_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readLittle_mod

/-- info: 'IxCC.Xv.Stacking.Proof.read_eq_truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.read_eq_truncate

/-- info: 'IxCC.Xv.Stacking.Proof.truncate_truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.truncate_truncate

/-- info: 'IxCC.Xv.Stacking.Proof.truncate_w64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.truncate_w64

/-- info: 'IxCC.Xv.Stacking.Proof.byte_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.byte_congr

/-- info: 'IxCC.Xv.Stacking.Proof.writeLittle_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeLittle_congr

/-- info: 'IxCC.Xv.Stacking.Proof.write_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write_congr

/-- info: 'IxCC.Xv.Stacking.Proof.writeReg_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeReg_congr

/-- info: 'IxCC.Xv.Stacking.Proof.mergeWrite_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mergeWrite_congr

/-- info: 'IxCC.Xv.Stacking.Proof.writeLittle_readable' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeLittle_readable

/-- info: 'IxCC.Xv.Stacking.Proof.writeLittle_writable' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeLittle_writable

/-- info: 'IxCC.Xv.Stacking.Proof.write_readable' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write_readable

/-- info: 'IxCC.Xv.Stacking.Proof.write_writable' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write_writable

/-- info: 'IxCC.Xv.Stacking.Proof.w64_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.w64_bytes

/-- info: 'IxCC.Xv.Stacking.Proof.Inside.read?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Inside.read?

/-- info: 'IxCC.Xv.Stacking.Proof.write_bytes_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write_bytes_inside

/-- info: 'IxCC.Xv.Stacking.Proof.Inside.write?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Inside.write?

/-- info: 'IxCC.Xv.Stacking.Proof.Inside.write_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Inside.write_cell

/-- info: 'IxCC.Xv.Stacking.Proof.Cell.read?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Cell.read?

/-- info: 'IxCC.Xv.Stacking.Proof.Cell.write?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Cell.write?

/-- info: 'IxCC.Xv.Stacking.Proof.Cell.perm' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Cell.perm

/-- info: 'IxCC.Xv.Stacking.Proof.write?_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write?_congr

/-- info: 'IxCC.Xv.Stacking.Proof.CellWrite.memCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.CellWrite.memCount

/-- info: 'IxCC.Xv.Stacking.Proof.memCount_cons_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.memCount_cons_le

/-- info: 'IxCC.Xv.Stacking.Proof.ArgsRel.slotWrites_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ArgsRel.slotWrites_sublist

/-- info: 'IxCC.Xv.Stacking.Proof.ArgRel.load_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ArgRel.load_read

/-- info: 'IxCC.Xv.Stacking.Proof.ArgRel.load_rw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ArgRel.load_rw

/-- info: 'IxCC.Xv.Stacking.Proof.ArgRel.address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ArgRel.address

/-- info: 'IxCC.Xv.Stacking.Proof.readSlots_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readSlots_rel

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.append

/-- info: 'IxCC.Xv.Stacking.Proof.RelW.implicits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.RelW.implicits

/-- info: 'IxCC.Xv.Stacking.Proof.ResW.head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ResW.head

/-- info: 'IxCC.Xv.Stacking.Proof.ResW.tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ResW.tail

/-- info: 'IxCC.Xv.Stacking.Proof.readReg_writeReg_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readReg_writeReg_other

/-- info: 'IxCC.Xv.Stacking.Proof.slotWrites_skip' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.slotWrites_skip

/-- info: 'IxCC.Xv.Stacking.Proof.writeSlots_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeSlots_rel

/-- info: 'IxCC.Xv.Stacking.Proof.writeImplicits_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeImplicits_rel

/-- info: 'IxCC.Xv.Stacking.Proof.CellWrite.mem_slotWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.CellWrite.mem_slotWrites

/-- info: 'IxCC.Xv.Stacking.Proof.reads_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.reads_rel

/-- info: 'IxCC.Xv.Stacking.Proof.writes_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writes_rel

/-- info: 'IxCC.Xv.Stacking.Proof.run_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.run_rel

/-- info: 'IxCC.Xv.Stacking.Proof.exec_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.exec_rel

/-- info: 'IxCC.Xv.Stacking.Proof.indexReg_gpr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.indexReg_gpr

/-- info: 'IxCC.Xv.Stacking.Proof.Amode.toMem_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Amode.toMem_congr

/-- info: 'IxCC.Xv.Stacking.Proof.amode_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.amode_eq

/-- info: 'IxCC.Xv.Stacking.Proof.toMem_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.toMem_spec

/-- info: 'IxCC.Xv.Stacking.Proof.toMem_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.toMem_eval

/-- info: 'IxCC.Xv.Stacking.Proof.arg_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.arg_reg

/-- info: 'IxCC.Xv.Stacking.Proof.arg_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.arg_cell

/-- info: 'IxCC.Xv.Stacking.Proof.bound_argRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.bound_argRel

/-- info: 'IxCC.Xv.Stacking.Proof.bounds_argsRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.bounds_argsRel

/-- info: 'IxCC.Xv.Stacking.Proof.zip4_of_mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip4_of_mapM

/-- info: 'IxCC.Xv.Stacking.Proof.Zip4.mem' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Zip4.mem

/-- info: 'IxCC.Xv.Stacking.Proof.pos_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.pos_cases

/-- info: 'IxCC.Xv.Stacking.Proof.zip_slotWrites₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_slotWrites₂

/-- info: 'IxCC.Xv.Stacking.Proof.zip_slotWrites₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_slotWrites₁

/-- info: 'IxCC.Xv.Stacking.Proof.zip_cellWrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_cellWrite

/-- info: 'IxCC.Xv.Stacking.Proof.zip_cellWrite_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_cellWrite_of

/-- info: 'IxCC.Xv.Stacking.Proof.zip_write_of_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_write_of_def

/-- info: 'IxCC.Xv.Stacking.Proof.zip_cellArg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_cellArg

/-- info: 'IxCC.Xv.Stacking.Proof.memCount_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.memCount_eq

/-- info: 'IxCC.Xv.Stacking.Proof.optGuard_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.optGuard_some

/-- info: 'IxCC.Xv.Stacking.Proof.readAll_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readAll_some

/-- info: 'IxCC.Xv.Stacking.Proof.filter_isSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.filter_isSlot

/-- info: 'IxCC.Xv.Stacking.Proof.implicit_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.implicit_bounds

/-- info: 'IxCC.Xv.Stacking.Proof.readback_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readback_loc

/-- info: 'IxCC.Xv.Stacking.Proof.writeBacks_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.writeBacks_of

/-- info: 'IxCC.Xv.Stacking.Proof.cell_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cell_rsp

/-- info: 'IxCC.Xv.Stacking.Proof.FrameCells.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FrameCells.keep

/-- info: 'IxCC.Xv.Stacking.Proof.read64_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.read64_congr

/-- info: 'IxCC.Xv.Stacking.Proof.distinctLocs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.distinctLocs_nodup

/-- info: 'IxCC.Xv.Stacking.Proof.zip_def_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zip_def_cell

/-- info: 'IxCC.Xv.Stacking.Proof.part_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.part_rel

/-- info: 'IxCC.Xv.Stacking.Proof.uses_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.uses_agree

/-- info: 'IxCC.Xv.Stacking.Proof.op_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.op_sim

/-- info: 'IxCC.Xv.Stacking.Proof.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.finish

/-- info: 'IxCC.Xv.Stacking.Proof.eval_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.eval_congr

/-- info: 'IxCC.Xv.Stacking.Proof.slotReads_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.slotReads_congr

/-- info: 'IxCC.Xv.Stacking.Proof.slotWrites_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.slotWrites_congr

/-- info: 'IxCC.Xv.Stacking.Proof.Foot.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Foot.congr

/-- info: 'IxCC.Xv.Stacking.Proof.LocAgree.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.LocAgree.keep

/-- info: 'IxCC.Xv.Stacking.Proof.fused_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.fused_sim

/-- info: 'IxCC.Xv.Stacking.Proof.jccTaken_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.jccTaken_eq

/-- info: 'IxCC.Xv.Stacking.Proof.after_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.after_reg

/-- info: 'IxCC.Xv.Stacking.Proof.after_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.after_cell

/-- info: 'IxCC.Xv.Stacking.Proof.after_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.after_same

/-- info: 'IxCC.Xv.Stacking.Proof.movRR_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.movRR_exec

/-- info: 'IxCC.Xv.Stacking.Proof.load64_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.load64_exec

/-- info: 'IxCC.Xv.Stacking.Proof.store64_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.store64_exec

/-- info: 'IxCC.Xv.Stacking.Proof.zero_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zero_exec

/-- info: 'IxCC.Xv.Stacking.Proof.movRR_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.movRR_foot

/-- info: 'IxCC.Xv.Stacking.Proof.load64_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.load64_foot

/-- info: 'IxCC.Xv.Stacking.Proof.store64_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.store64_foot

/-- info: 'IxCC.Xv.Stacking.Proof.zero_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zero_foot

/-- info: 'IxCC.Xv.Stacking.Proof.gpr_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.gpr_ok

/-- info: 'IxCC.Xv.Stacking.Proof.move_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.move_cases

/-- info: 'IxCC.Xv.Stacking.Proof.move_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.move_sim

/-- info: 'IxCC.Xv.Stacking.Proof.zero_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zero_sim

/-- info: 'IxCC.Xv.Stacking.Proof.block_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.block_at

/-- info: 'IxCC.Xv.Stacking.Proof.check_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.check_at

/-- info: 'IxCC.Xv.Stacking.Proof.entry_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entry_of

/-- info: 'IxCC.Xv.Stacking.Proof.block_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.block_ok

/-- info: 'IxCC.Xv.Stacking.Proof.FnAt.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FnAt.unique

/-- info: 'IxCC.Xv.Stacking.Proof.FnAt.checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FnAt.checks

/-- info: 'IxCC.Xv.Stacking.Proof.addr_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.addr_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.ranges_apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ranges_apart

/-- info: 'IxCC.Xv.Stacking.Proof.cell_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cell_off

/-- info: 'IxCC.Xv.Stacking.Proof.CellAt.range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.CellAt.range

/-- info: 'IxCC.Xv.Stacking.Proof.save_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.save_range

/-- info: 'IxCC.Xv.Stacking.Proof.nodup_getElem?_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.nodup_getElem?_inj

/-- info: 'IxCC.Xv.Stacking.Proof.CellAt.apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.CellAt.apart

/-- info: 'IxCC.Xv.Stacking.Proof.CellAt.apart_save' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.CellAt.apart_save

/-- info: 'IxCC.Xv.Stacking.Proof.ActFacts.span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ActFacts.span

/-- info: 'IxCC.Xv.Stacking.Proof.FrameSpan.byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FrameSpan.byte

/-- info: 'IxCC.Xv.Stacking.Proof.FrameSpan.cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FrameSpan.cell

/-- info: 'IxCC.Xv.Stacking.Proof.FrameSpan.cell.word_add_assoc_ofNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FrameSpan.cell.word_add_assoc_ofNat

/-- info: 'IxCC.Xv.Stacking.Proof.frameCells_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.frameCells_of

/-- info: 'IxCC.Xv.Stacking.Proof.read64_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.read64_keep

/-- info: 'IxCC.Xv.Stacking.Proof.ReadableData.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ReadableData.keep

/-- info: 'IxCC.Xv.Stacking.Proof.susp_cell_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.susp_cell_off

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.mono

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_keeps' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_keeps

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_gets' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_gets

/-- info: 'IxCC.Xv.Stacking.Proof.noteLoc_writes' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.noteLoc_writes

/-- info: 'IxCC.Xv.Stacking.Proof.noteDef_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.noteDef_mono

/-- info: 'IxCC.Xv.Stacking.Proof.noteDef_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.noteDef_reg

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_noteLoc_writes' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_noteLoc_writes

/-- info: 'IxCC.Xv.Stacking.Proof.inst_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.inst_mono

/-- info: 'IxCC.Xv.Stacking.Proof.inst_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.inst_def

/-- info: 'IxCC.Xv.Stacking.Proof.term_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.term_mono

/-- info: 'IxCC.Xv.Stacking.Proof.term_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.term_def

/-- info: 'IxCC.Xv.Stacking.Proof.block_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.block_mono

/-- info: 'IxCC.Xv.Stacking.Proof.facts_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_inst

/-- info: 'IxCC.Xv.Stacking.Proof.facts_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_term

/-- info: 'IxCC.Xv.Stacking.Proof.write_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.retop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.retop

/-- info: 'IxCC.Xv.Stacking.Proof.read64?_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.read64?_keep

/-- info: 'IxCC.Xv.Stacking.Proof.defCell_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.defCell_bytes

/-- info: 'IxCC.Xv.Stacking.Proof.Match.update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Match.update

/-- info: 'IxCC.Xv.Stacking.Proof.Match.body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Match.body

/-- info: 'IxCC.Xv.Stacking.Proof.clearAccesses_sub' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.clearAccesses_sub

/-- info: 'IxCC.Xv.Stacking.Proof.clearAccesses_clears' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.clearAccesses_clears

/-- info: 'IxCC.Xv.Stacking.Proof.block_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.block_fits

/-- info: 'IxCC.Xv.Stacking.Proof.flatten_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.flatten_split

/-- info: 'IxCC.Xv.Stacking.Proof.machine_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.machine_at

/-- info: 'IxCC.Xv.Stacking.Proof.XlPos.segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.XlPos.segment

/-- info: 'IxCC.Xv.Stacking.Proof.XlPos.blockCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.XlPos.blockCode

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.slots

/-- info: 'IxCC.Xv.Stacking.Proof.Match.slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Match.slot

/-- info: 'IxCC.Xv.Stacking.Proof.Foot.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Foot.safe

/-- info: 'IxCC.Xv.Stacking.Proof.offsetOf_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.offsetOf_succ

/-- info: 'IxCC.Xv.Stacking.Proof.machine_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.machine_next

/-- info: 'IxCC.Xv.Stacking.Proof.nextHoles_op_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.nextHoles_op_sub

/-- info: 'IxCC.Xv.Stacking.Proof.nextHoles_op_clears' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.nextHoles_op_clears

/-- info: 'IxCC.Xv.Stacking.Proof.step_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_op

/-- info: 'IxCC.Xv.Stacking.Proof.step_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_row

/-- info: 'IxCC.Xv.Stacking.Proof.step_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_move

/-- info: 'IxCC.Xv.Stacking.Proof.step_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_zero

/-- info: 'IxCC.Xv.Stacking.Proof.zeroAll_readReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zeroAll_readReg

/-- info: 'IxCC.Xv.Stacking.Proof.zeroAll_memory' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zeroAll_memory

/-- info: 'IxCC.Xv.Stacking.Proof.zero_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zero_steps

/-- info: 'IxCC.Xv.Stacking.Proof.zeroes_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.zeroes_regs

/-- info: 'IxCC.Xv.Stacking.Proof.step_fused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_fused

/-- info: 'IxCC.Xv.Stacking.Proof.FnAt.noEntryEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FnAt.noEntryEdge

/-- info: 'IxCC.Xv.Stacking.Proof.xlPos_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.xlPos_start

/-- info: 'IxCC.Xv.Stacking.Proof.After.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.After.refl

/-- info: 'IxCC.Xv.Stacking.Proof.takeEdge_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.takeEdge_empty

/-- info: 'IxCC.Xv.Stacking.Proof.edge_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.edge_ok

/-- info: 'IxCC.Xv.Stacking.Proof.Match.jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Match.jump

/-- info: 'IxCC.Xv.Stacking.Proof.step_jmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_jmp

/-- info: 'IxCC.Xv.Stacking.Proof.step_jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_jcc

/-- info: 'IxCC.Xv.Stacking.Proof.EntryFrame.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.EntryFrame.keep

/-- info: 'IxCC.Xv.Stacking.Proof.step_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_fail

/-- info: 'IxCC.Xv.Stacking.Proof.Straight.Segment.safe_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Straight.Segment.safe_call

/-- info: 'IxCC.Xv.Stacking.Proof.lea_foot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.lea_foot

/-- info: 'IxCC.Xv.Stacking.Proof.cmp_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cmp_exec

/-- info: 'IxCC.Xv.Stacking.Proof.cmp_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cmp_test

/-- info: 'IxCC.Xv.Stacking.Proof.cmp_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.cmp_foot

/-- info: 'IxCC.Xv.Stacking.Proof.check_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.check_steps

/-- info: 'IxCC.Xv.Stacking.Proof.store_exec_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.store_exec_ok

/-- info: 'IxCC.Xv.Stacking.Proof.stores_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.stores_steps

/-- info: 'IxCC.Xv.Stacking.Proof.inst_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.inst_keep

/-- info: 'IxCC.Xv.Stacking.Proof.term_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.term_keep

/-- info: 'IxCC.Xv.Stacking.Proof.block_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.block_keep

/-- info: 'IxCC.Xv.Stacking.Proof.facts_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_keep

/-- info: 'IxCC.Xv.Stacking.Proof.facts_gets' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_gets

/-- info: 'IxCC.Xv.Stacking.Proof.facts_inArgs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_inArgs

/-- info: 'IxCC.Xv.Stacking.Proof.facts_calls' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_calls

/-- info: 'IxCC.Xv.Stacking.Proof.noteLoc_outArgs_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.noteLoc_outArgs_le

/-- info: 'IxCC.Xv.Stacking.Proof.facts_outArgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.facts_outArgs

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_set_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_set_get

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_set_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_set_size

/-- info: 'IxCC.Xv.Stacking.Proof.entryRegs_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entryRegs_size

/-- info: 'IxCC.Xv.Stacking.Proof.entryRegs_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entryRegs_get

/-- info: 'IxCC.Xv.Stacking.Proof.readAll_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.readAll_get

/-- info: 'IxCC.Xv.Stacking.Proof.conventionArgs_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.conventionArgs_get

/-- info: 'IxCC.Xv.Stacking.Proof.argLoc_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argLoc_reg

/-- info: 'IxCC.Xv.Stacking.Proof.argLoc_out' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argLoc_out

/-- info: 'IxCC.Xv.Stacking.Proof.nArgRegs_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.nArgRegs_eq

/-- info: 'IxCC.Xv.Stacking.Proof.inst_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.inst_call

/-- info: 'IxCC.Xv.Stacking.Proof.disjoint_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.disjoint_below

/-- info: 'IxCC.Xv.Stacking.Proof.saved_ne_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.saved_ne_rsp

/-- info: 'IxCC.Xv.Stacking.Proof.saveOff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.saveOff_mem

/-- info: 'IxCC.Xv.Stacking.Proof.frameless_saveOff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.frameless_saveOff

/-- info: 'IxCC.Xv.Stacking.Proof.prologue_map' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.prologue_map

/-- info: 'IxCC.Xv.Stacking.Proof.setReg_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.setReg_self

/-- info: 'IxCC.Xv.Stacking.Proof.prologue_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.prologue_steps

/-- info: 'IxCC.Xv.Stacking.Proof.ActFacts.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ActFacts.mono

/-- info: 'IxCC.Xv.Stacking.Proof.entry_save_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entry_save_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.ctx_56' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ctx_56

/-- info: 'IxCC.Xv.Stacking.Proof.Global.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Global.mono

/-- info: 'IxCC.Xv.Stacking.Proof.sub_ofNat_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.sub_ofNat_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.sub8_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.sub8_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.word_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.word_eq

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.react' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.react

/-- info: 'IxCC.Xv.Stacking.Proof.call_inArgs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.call_inArgs_le

/-- info: 'IxCC.Xv.Stacking.Proof.call_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.call_match

/-- info: 'IxCC.Xv.Stacking.Proof.fnAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.fnAt_of

/-- info: 'IxCC.Xv.Stacking.Proof.hasBlock_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.hasBlock_of

/-- info: 'IxCC.Xv.Stacking.Proof.write64_bytes_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write64_bytes_off

/-- info: 'IxCC.Xv.Stacking.Proof.prologue_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.prologue_match

/-- info: 'IxCC.Xv.Stacking.Proof.r11_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.r11_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.unchecked_slack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.unchecked_slack

/-- info: 'IxCC.Xv.Stacking.Proof.first_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.first_block

/-- info: 'IxCC.Xv.Stacking.Proof.step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_call

/-- info: 'IxCC.Xv.Stacking.Proof.loads_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.loads_steps

/-- info: 'IxCC.Xv.Stacking.Proof.epilogue_map' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.epilogue_map

/-- info: 'IxCC.Xv.Stacking.Proof.epilogue_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.epilogue_steps

/-- info: 'IxCC.Xv.Stacking.Proof.clobber_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.clobber_fold

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_set_notin' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_set_notin

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_set_in' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_set_in

/-- info: 'IxCC.Xv.Stacking.Proof.mem_allGPRs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mem_allGPRs

/-- info: 'IxCC.Xv.Stacking.Proof.resultRegs_zip_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.resultRegs_zip_nodup

/-- info: 'IxCC.Xv.Stacking.Proof.returnRegs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.returnRegs_spec

/-- info: 'IxCC.Xv.Stacking.Proof.allowed_callerSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.allowed_callerSaved

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.allow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.allow

/-- info: 'IxCC.Xv.Stacking.Proof.calleeSaved_not_callerSaved' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.calleeSaved_not_callerSaved

/-- info: 'IxCC.Xv.Stacking.Proof.calleeSavedMatch_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.calleeSavedMatch_of

/-- info: 'IxCC.Xv.Stacking.Proof.ret_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ret_steps

/-- info: 'IxCC.Xv.Stacking.Proof.conventionResults_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.conventionResults_get

/-- info: 'IxCC.Xv.Stacking.Proof.FnAt.arities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.FnAt.arities

/-- info: 'IxCC.Xv.Stacking.Proof.resultsOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.resultsOf_eq

/-- info: 'IxCC.Xv.Stacking.Proof.call_arity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.call_arity

/-- info: 'IxCC.Xv.Stacking.Proof.mayChange_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mayChange_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.clobbers_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.clobbers_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.results_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.results_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.resultReg_not_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.resultReg_not_saved

/-- info: 'IxCC.Xv.Stacking.Proof.mem_take_zip_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.mem_take_zip_fst

/-- info: 'IxCC.Xv.Stacking.Proof.inst_call_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.inst_call_conv

/-- info: 'IxCC.Xv.Stacking.Proof.step_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_ret

/-- info: 'IxCC.Xv.Stacking.Proof.saved_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.saved_mem

/-- info: 'IxCC.Xv.Stacking.Proof.term_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.term_tail

/-- info: 'IxCC.Xv.Stacking.Proof.tail_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.tail_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.room

/-- info: 'IxCC.Xv.Stacking.Proof.Chain.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Chain.tail

/-- info: 'IxCC.Xv.Stacking.Proof.tail_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.tail_match

/-- info: 'IxCC.Xv.Stacking.Proof.tailCall_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.tailCall_safe

/-- info: 'IxCC.Xv.Stacking.Proof.epilogue_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.epilogue_at

/-- info: 'IxCC.Xv.Stacking.Proof.saved_not_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.saved_not_allowed

/-- info: 'IxCC.Xv.Stacking.Proof.tail_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.tail_prologue

/-- info: 'IxCC.Xv.Stacking.Proof.step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_tail

/-- info: 'IxCC.Xv.Stacking.Proof.success_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.success_exit

/-- info: 'IxCC.Xv.Stacking.Proof.step_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_done

/-- info: 'IxCC.Xv.Stacking.Proof.Outcome.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Outcome.mono

/-- info: 'IxCC.Xv.Stacking.Proof.Outcome.succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.Outcome.succ

/-- info: 'IxCC.Xv.Stacking.Proof.term_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.term_fail

/-- info: 'IxCC.Xv.Stacking.Proof.statusOf_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.statusOf_range

/-- info: 'IxCC.Xv.Stacking.Proof.step_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.step_sim

/-- info: 'IxCC.Xv.Stacking.Proof.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.sim

/-- info: 'IxCC.Xv.Stacking.Proof.bare_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.bare_step

/-- info: 'IxCC.Xv.Stacking.Proof.write64?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.write64?_ok

/-- info: 'IxCC.Xv.Stacking.Proof.read?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.read?_ok

/-- info: 'IxCC.Xv.Stacking.Proof.subRM_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.subRM_exec

/-- info: 'IxCC.Xv.Stacking.Proof.orMR_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.orMR_exec

/-- info: 'IxCC.Xv.Stacking.Proof.test_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.test_exec

/-- info: 'IxCC.Xv.Stacking.Proof.test_signedLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.test_signedLt

/-- info: 'IxCC.Xv.Stacking.Proof.word_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.word_big

/-- info: 'IxCC.Xv.Stacking.Proof.or_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.or_big

/-- info: 'IxCC.Xv.Stacking.Proof.foldl_or_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.foldl_or_big

/-- info: 'IxCC.Xv.Stacking.Proof.word_sub_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.word_sub_sub

/-- info: 'IxCC.Xv.Stacking.Proof.pushes_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.pushes_steps

/-- info: 'IxCC.Xv.Stacking.Proof.ors_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ors_steps

/-- info: 'IxCC.Xv.Stacking.Proof.marshalOne_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.marshalOne_exec

/-- info: 'IxCC.Xv.Stacking.Proof.marshal_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.marshal_steps

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_ok

/-- info: 'IxCC.Xv.Stacking.Proof.EntryBase.entrySp_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.EntryBase.entrySp_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.EntryBase.limit_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.EntryBase.limit_toNat

/-- info: 'IxCC.Xv.Stacking.Proof.EntryBase.inStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.EntryBase.inStack

/-- info: 'IxCC.Xv.Stacking.Proof.entry_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entry_match

/-- info: 'IxCC.Xv.Stacking.Proof.word_add_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.word_add_ne

/-- info: 'IxCC.Xv.Stacking.Proof.saves_popOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.saves_popOrder

/-- info: 'IxCC.Xv.Stacking.Proof.ctx_48' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.ctx_48

/-- info: 'IxCC.Xv.Stacking.Proof.store_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.store_exec

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_head

/-- info: 'IxCC.Xv.Stacking.Proof.main_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.main_start

/-- info: 'IxCC.Xv.Stacking.Proof.entry_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entry_prologue

/-- info: 'IxCC.Xv.Stacking.Proof.entryFrame_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.entryFrame_of

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_call

/-- info: 'IxCC.Xv.Stacking.Proof.argPairs_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argPairs_get

/-- info: 'IxCC.Xv.Stacking.Proof.argPairs_get'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argPairs_get'

/-- info: 'IxCC.Xv.Stacking.Proof.marshal_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.marshal_order

/-- info: 'IxCC.Xv.Stacking.Proof.argRegs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argRegs_nodup

/-- info: 'IxCC.Xv.Stacking.Proof.natSrcs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.natSrcs_mem

/-- info: 'IxCC.Xv.Stacking.Proof.argsFit_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argsFit_iff

/-- info: 'IxCC.Xv.Stacking.Proof.wrapperArgs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapperArgs_length

/-- info: 'IxCC.Xv.Stacking.Proof.sysvArgs_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.sysvArgs_ne

/-- info: 'IxCC.Xv.Stacking.Proof.argRegs_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argRegs_ne

/-- info: 'IxCC.Xv.Stacking.Proof.marshal_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.marshal_regs

/-- info: 'IxCC.Xv.Stacking.Proof.regsRel_entry_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.regsRel_entry_nil

/-- info: 'IxCC.Xv.Stacking.Proof.argPairs_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.argPairs_dst

/-- info: 'IxCC.Xv.Stacking.Proof.CallCore.regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.CallCore.regs

/-- info: 'IxCC.Xv.Stacking.Proof.marshal_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.marshal_call

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_pre

/-- info: 'IxCC.Xv.Stacking.Proof.main_fnAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.main_fnAt

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_entry

/-- info: 'IxCC.Xv.Stacking.Proof.wrapper_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.wrapper_overflow

/-- info: 'IxCC.Xv.Stacking.Proof.stacked_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.stacked_ends

/-- info: 'IxCC.Xv.Stacking.Proof.run_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Stacking.Proof.run_ends
