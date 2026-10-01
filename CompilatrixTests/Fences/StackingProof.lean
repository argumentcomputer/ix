import Compilatrix.Xv.Stacking.Proof.Shape
import Compilatrix.Xv.Stacking.Proof.Steps
import Compilatrix.Xv.Stacking.Proof.Exit
import Compilatrix.Xv.Stacking.Proof.Trunc
import Compilatrix.Xv.Stacking.Proof.RowRel
import Compilatrix.Xv.Stacking.Proof.RowXl
import Compilatrix.Xv.Stacking.Proof.InstXl
import Compilatrix.Xv.Stacking.Proof.Code
import Compilatrix.Xv.Stacking.Proof.Match
import Compilatrix.Xv.Stacking.Proof.Cells
import Compilatrix.Xv.Stacking.Proof.Chain
import Compilatrix.Xv.Stacking.Proof.Writes
import Compilatrix.Xv.Stacking.Proof.Body
import Compilatrix.Xv.Stacking.Proof.Machine
import Compilatrix.Xv.Stacking.Proof.StepBody
import Compilatrix.Xv.Stacking.Proof.StepTerm
import Compilatrix.Xv.Stacking.Proof.Call
import Compilatrix.Xv.Stacking.Proof.CallFacts
import Compilatrix.Xv.Stacking.Proof.StepCall
import Compilatrix.Xv.Stacking.Proof.CallMatch
import Compilatrix.Xv.Stacking.Proof.CallRun
import Compilatrix.Xv.Stacking.Proof.CallStep
import Compilatrix.Xv.Stacking.Proof.Return
import Compilatrix.Xv.Stacking.Proof.RetStep
import Compilatrix.Xv.Stacking.Proof.RetFacts
import Compilatrix.Xv.Stacking.Proof.RetMatch
import Compilatrix.Xv.Stacking.Proof.TailMatch
import Compilatrix.Xv.Stacking.Proof.TailStep
import Compilatrix.Xv.Stacking.Proof.WrapperExit
import Compilatrix.Xv.Stacking.Proof.Sim
import Compilatrix.Xv.Stacking.Proof.WrapperSteps
import Compilatrix.Xv.Stacking.Proof.WrapperProof
import Compilatrix.Xv.Stacking.Proof.WrapperHead
import Compilatrix.Xv.Stacking.Proof.WrapperCall
import Compilatrix.Xv.Stacking.Proof.WrapperEntry
import Compilatrix.Xv.Stacking.Proof.Ends

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

/-- info: 'Compilatrix.Xv.Stacking.Proof.bind_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.bind_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.mapError_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mapError_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.mapM_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mapM_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_place' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_place

/-- info: 'Compilatrix.Xv.Stacking.Proof.placeList_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.placeList_length

/-- info: 'Compilatrix.Xv.Stacking.Proof.placeList_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.placeList_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.placeExports_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.placeExports_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.placeFuncs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.placeFuncs_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.withLayouts_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.withLayouts_length

/-- info: 'Compilatrix.Xv.Stacking.Proof.withLayouts_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.withLayouts_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.run_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.flatten_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.flatten_getElem?

/-- info: 'Compilatrix.Xv.Stacking.Proof.take_sum_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.take_sum_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.flatten_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.flatten_length

/-- info: 'Compilatrix.Xv.Stacking.Proof.mapM_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mapM_lengths

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_insert_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_insert_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.emitFunc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.emitFunc_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.emitFunc_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.emitFunc_length

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_length

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapperOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapperOf_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.placed_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.placed_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.placed_fn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.placed_fn

/-- info: 'Compilatrix.Xv.Stacking.Proof.entries_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entries_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.func_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.func_at

/-- info: 'Compilatrix.Xv.Stacking.Proof.exit_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.exit_at

/-- info: 'Compilatrix.Xv.Stacking.Proof.withLayouts_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.withLayouts_mem

/-- info: 'Compilatrix.Xv.Stacking.Proof.main_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.main_at

/-- info: 'Compilatrix.X86.inFrame_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.inFrame_eq

/-- info: 'Compilatrix.X86.Straight.Segment.safeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.safeAt

/-- info: 'Compilatrix.X86.Straight.Segment.safe_op' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.safe_op

/-- info: 'Compilatrix.X86.Straight.Segment.safe_fused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.safe_fused

/-- info: 'Compilatrix.X86.Straight.Segment.safe_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.safe_exec

/-- info: 'Compilatrix.X86.slotReads_noMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.slotReads_noMem

/-- info: 'Compilatrix.X86.slotWrites_noMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.slotWrites_noMem

/-- info: 'Compilatrix.X86.footprint_noMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.footprint_noMem

/-- info: 'Compilatrix.X86.Straight.Segment.of_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.of_block

/-- info: 'Compilatrix.X86.Straight.Segment.left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.left

/-- info: 'Compilatrix.X86.Straight.Segment.right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Straight.Segment.right

/-- info: 'Compilatrix.X86.OperationSafe.of_noMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.OperationSafe.of_noMemory

/-- info: 'Compilatrix.X86.BlockCode.safe_ret_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.BlockCode.safe_ret_top

/-- info: 'Compilatrix.Xv.Stacking.Proof.EntryFrame.cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.EntryFrame.cut

/-- info: 'Compilatrix.Xv.Stacking.Proof.signExtend32_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.signExtend32_ofNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.signExtend32_ofInt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.signExtend32_ofInt_neg

/-- info: 'Compilatrix.Xv.Stacking.Proof.rspAt_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.rspAt_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.rspBelow_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.rspBelow_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.ctxAt_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ctxAt_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.entrySpCell_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entrySpCell_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.stackLimitCell_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.stackLimitCell_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.stackBudgetCell_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.stackBudgetCell_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.addRsp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.addRsp_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.subRsp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.subRsp_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.exec_addRsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.exec_addRsp

/-- info: 'Compilatrix.Xv.Stacking.Proof.exec_subRsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.exec_subRsp

/-- info: 'Compilatrix.Xv.Stacking.Proof.pop_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.pop_footprint

/-- info: 'Compilatrix.Xv.Stacking.Proof.readReg_setReg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readReg_setReg'

/-- info: 'Compilatrix.Xv.Stacking.Proof.pops_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.pops_safe

/-- info: 'Compilatrix.Xv.Stacking.Proof.addRsp_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.addRsp_footprint

/-- info: 'Compilatrix.Xv.Stacking.Proof.subRsp_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.subRsp_footprint

/-- info: 'Compilatrix.Xv.Stacking.Proof.seg_safe_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.seg_safe_reg

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapperEpilogue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapperEpilogue_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.epilogue_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.epilogue_safe

/-- info: 'Compilatrix.Xv.Stacking.Proof.ExitGroupAt.fail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ExitGroupAt.fail

/-- info: 'Compilatrix.Xv.Stacking.Proof.ExitGroupAt.failExit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ExitGroupAt.failExit

/-- info: 'Compilatrix.Xv.Stacking.Proof.Wrapper.fail_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Wrapper.fail_safe

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.length

/-- info: 'Compilatrix.Xv.Stacking.Proof.setWidth_of_truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.setWidth_of_truncate

/-- info: 'Compilatrix.Xv.Stacking.Proof.truncate_of_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.truncate_of_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.TruncEq.truncate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.TruncEq.truncate

/-- info: 'Compilatrix.Xv.Stacking.Proof.aluFlags_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.aluFlags_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.mulFlags_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mulFlags_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.shiftCount_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.shiftCount_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.ResW.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ResW.nil

/-- info: 'Compilatrix.Xv.Stacking.Proof.ResW.same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ResW.same

/-- info: 'Compilatrix.Xv.Stacking.Proof.ResW.one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ResW.one

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.two

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.one

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.three

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.nil'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.nil'

/-- info: 'Compilatrix.Xv.Stacking.Proof.aluSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.aluSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.cmpSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cmpSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.testSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.testSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.moveSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.moveSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.zeroExtendSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zeroExtendSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.mulSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mulSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.shiftSem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.shiftSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.divSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.divSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.setccSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.setccSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.cmovSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cmovSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.controlSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.controlSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.jccSem_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.jccSem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.arith_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.arith_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.arithDesc_implicit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.arithDesc_implicit

/-- info: 'Compilatrix.Xv.Stacking.Proof.sem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.sem_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.rangeAllowed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.rangeAllowed_iff

/-- info: 'Compilatrix.Xv.Stacking.Proof.width_bits' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.width_bits

/-- info: 'Compilatrix.Xv.Stacking.Proof.width_bytes_le' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.width_bytes_le

/-- info: 'Compilatrix.Xv.Stacking.Proof.width_bytes_pos' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.width_bytes_pos

/-- info: 'Compilatrix.Xv.Stacking.Proof.readLittle_succ_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readLittle_succ_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.readLittle_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readLittle_lt

/-- info: 'Compilatrix.Xv.Stacking.Proof.readLittle_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readLittle_mod

/-- info: 'Compilatrix.Xv.Stacking.Proof.read_eq_truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.read_eq_truncate

/-- info: 'Compilatrix.Xv.Stacking.Proof.truncate_truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.truncate_truncate

/-- info: 'Compilatrix.Xv.Stacking.Proof.truncate_w64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.truncate_w64

/-- info: 'Compilatrix.Xv.Stacking.Proof.byte_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.byte_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeLittle_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeLittle_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.write_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeReg_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeReg_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.mergeWrite_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mergeWrite_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeLittle_readable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeLittle_readable

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeLittle_writable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeLittle_writable

/-- info: 'Compilatrix.Xv.Stacking.Proof.write_readable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write_readable

/-- info: 'Compilatrix.Xv.Stacking.Proof.write_writable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write_writable

/-- info: 'Compilatrix.Xv.Stacking.Proof.w64_bytes' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.w64_bytes

/-- info: 'Compilatrix.Xv.Stacking.Proof.Inside.read?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Inside.read?

/-- info: 'Compilatrix.Xv.Stacking.Proof.write_bytes_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write_bytes_inside

/-- info: 'Compilatrix.Xv.Stacking.Proof.Inside.write?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Inside.write?

/-- info: 'Compilatrix.Xv.Stacking.Proof.Inside.write_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Inside.write_cell

/-- info: 'Compilatrix.Xv.Stacking.Proof.Cell.read?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Cell.read?

/-- info: 'Compilatrix.Xv.Stacking.Proof.Cell.write?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Cell.write?

/-- info: 'Compilatrix.Xv.Stacking.Proof.Cell.perm' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Cell.perm

/-- info: 'Compilatrix.Xv.Stacking.Proof.write?_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write?_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.CellWrite.memCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.CellWrite.memCount

/-- info: 'Compilatrix.Xv.Stacking.Proof.memCount_cons_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.memCount_cons_le

/-- info: 'Compilatrix.Xv.Stacking.Proof.ArgsRel.slotWrites_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ArgsRel.slotWrites_sublist

/-- info: 'Compilatrix.Xv.Stacking.Proof.ArgRel.load_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ArgRel.load_read

/-- info: 'Compilatrix.Xv.Stacking.Proof.ArgRel.load_rw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ArgRel.load_rw

/-- info: 'Compilatrix.Xv.Stacking.Proof.ArgRel.address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ArgRel.address

/-- info: 'Compilatrix.Xv.Stacking.Proof.readSlots_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readSlots_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.append

/-- info: 'Compilatrix.Xv.Stacking.Proof.RelW.implicits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.RelW.implicits

/-- info: 'Compilatrix.Xv.Stacking.Proof.ResW.head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ResW.head

/-- info: 'Compilatrix.Xv.Stacking.Proof.ResW.tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ResW.tail

/-- info: 'Compilatrix.Xv.Stacking.Proof.readReg_writeReg_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readReg_writeReg_other

/-- info: 'Compilatrix.Xv.Stacking.Proof.slotWrites_skip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.slotWrites_skip

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeSlots_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeSlots_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeImplicits_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeImplicits_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.CellWrite.mem_slotWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.CellWrite.mem_slotWrites

/-- info: 'Compilatrix.Xv.Stacking.Proof.reads_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.reads_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.writes_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writes_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.run_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.run_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.exec_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.exec_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.indexReg_gpr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.indexReg_gpr

/-- info: 'Compilatrix.Xv.Stacking.Proof.Amode.toMem_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Amode.toMem_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.amode_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.amode_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.toMem_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.toMem_spec

/-- info: 'Compilatrix.Xv.Stacking.Proof.toMem_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.toMem_eval

/-- info: 'Compilatrix.Xv.Stacking.Proof.arg_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.arg_reg

/-- info: 'Compilatrix.Xv.Stacking.Proof.arg_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.arg_cell

/-- info: 'Compilatrix.Xv.Stacking.Proof.bound_argRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.bound_argRel

/-- info: 'Compilatrix.Xv.Stacking.Proof.bounds_argsRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.bounds_argsRel

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip4_of_mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip4_of_mapM

/-- info: 'Compilatrix.Xv.Stacking.Proof.Zip4.mem' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Zip4.mem

/-- info: 'Compilatrix.Xv.Stacking.Proof.pos_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.pos_cases

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_slotWrites₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_slotWrites₂

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_slotWrites₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_slotWrites₁

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_cellWrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_cellWrite

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_cellWrite_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_cellWrite_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_write_of_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_write_of_def

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_cellArg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_cellArg

/-- info: 'Compilatrix.Xv.Stacking.Proof.memCount_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.memCount_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.optGuard_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.optGuard_some

/-- info: 'Compilatrix.Xv.Stacking.Proof.readAll_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readAll_some

/-- info: 'Compilatrix.Xv.Stacking.Proof.filter_isSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.filter_isSlot

/-- info: 'Compilatrix.Xv.Stacking.Proof.implicit_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.implicit_bounds

/-- info: 'Compilatrix.Xv.Stacking.Proof.readback_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readback_loc

/-- info: 'Compilatrix.Xv.Stacking.Proof.writeBacks_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.writeBacks_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.cell_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cell_rsp

/-- info: 'Compilatrix.Xv.Stacking.Proof.FrameCells.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FrameCells.keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.read64_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.read64_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.distinctLocs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.distinctLocs_nodup

/-- info: 'Compilatrix.Xv.Stacking.Proof.zip_def_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zip_def_cell

/-- info: 'Compilatrix.Xv.Stacking.Proof.part_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.part_rel

/-- info: 'Compilatrix.Xv.Stacking.Proof.uses_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.uses_agree

/-- info: 'Compilatrix.Xv.Stacking.Proof.op_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.op_sim

/-- info: 'Compilatrix.Xv.Stacking.Proof.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.finish

/-- info: 'Compilatrix.Xv.Stacking.Proof.eval_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.eval_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.slotReads_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.slotReads_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.slotWrites_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.slotWrites_congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.Foot.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Foot.congr

/-- info: 'Compilatrix.Xv.Stacking.Proof.LocAgree.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.LocAgree.keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.fused_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.fused_sim

/-- info: 'Compilatrix.Xv.Stacking.Proof.jccTaken_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.jccTaken_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.after_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.after_reg

/-- info: 'Compilatrix.Xv.Stacking.Proof.after_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.after_cell

/-- info: 'Compilatrix.Xv.Stacking.Proof.after_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.after_same

/-- info: 'Compilatrix.Xv.Stacking.Proof.movRR_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.movRR_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.load64_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.load64_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.store64_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.store64_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.zero_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zero_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.movRR_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.movRR_foot

/-- info: 'Compilatrix.Xv.Stacking.Proof.load64_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.load64_foot

/-- info: 'Compilatrix.Xv.Stacking.Proof.store64_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.store64_foot

/-- info: 'Compilatrix.Xv.Stacking.Proof.zero_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zero_foot

/-- info: 'Compilatrix.Xv.Stacking.Proof.gpr_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.gpr_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.move_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.move_cases

/-- info: 'Compilatrix.Xv.Stacking.Proof.move_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.move_sim

/-- info: 'Compilatrix.Xv.Stacking.Proof.zero_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zero_sim

/-- info: 'Compilatrix.Xv.Stacking.Proof.block_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.block_at

/-- info: 'Compilatrix.Xv.Stacking.Proof.check_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.check_at

/-- info: 'Compilatrix.Xv.Stacking.Proof.entry_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entry_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.block_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.block_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.FnAt.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FnAt.unique

/-- info: 'Compilatrix.Xv.Stacking.Proof.FnAt.checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FnAt.checks

/-- info: 'Compilatrix.Xv.Stacking.Proof.addr_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.addr_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.ranges_apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ranges_apart

/-- info: 'Compilatrix.Xv.Stacking.Proof.cell_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cell_off

/-- info: 'Compilatrix.Xv.Stacking.Proof.CellAt.range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.CellAt.range

/-- info: 'Compilatrix.Xv.Stacking.Proof.save_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.save_range

/-- info: 'Compilatrix.Xv.Stacking.Proof.nodup_getElem?_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.nodup_getElem?_inj

/-- info: 'Compilatrix.Xv.Stacking.Proof.CellAt.apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.CellAt.apart

/-- info: 'Compilatrix.Xv.Stacking.Proof.CellAt.apart_save' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.CellAt.apart_save

/-- info: 'Compilatrix.Xv.Stacking.Proof.ActFacts.span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ActFacts.span

/-- info: 'Compilatrix.Xv.Stacking.Proof.FrameSpan.byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FrameSpan.byte

/-- info: 'Compilatrix.Xv.Stacking.Proof.FrameSpan.cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FrameSpan.cell

/-- info: 'Compilatrix.Xv.Stacking.Proof.FrameSpan.cell.word_add_assoc_ofNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FrameSpan.cell.word_add_assoc_ofNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.frameCells_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.frameCells_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.read64_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.read64_keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.ReadableData.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ReadableData.keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.susp_cell_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.susp_cell_off

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_keeps' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_keeps

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_gets' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_gets

/-- info: 'Compilatrix.Xv.Stacking.Proof.noteLoc_writes' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.noteLoc_writes

/-- info: 'Compilatrix.Xv.Stacking.Proof.noteDef_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.noteDef_mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.noteDef_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.noteDef_reg

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_noteLoc_writes' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_noteLoc_writes

/-- info: 'Compilatrix.Xv.Stacking.Proof.inst_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.inst_mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.inst_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.inst_def

/-- info: 'Compilatrix.Xv.Stacking.Proof.term_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.term_mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.term_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.term_def

/-- info: 'Compilatrix.Xv.Stacking.Proof.block_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.block_mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_inst

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_term

/-- info: 'Compilatrix.Xv.Stacking.Proof.write_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.retop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.retop

/-- info: 'Compilatrix.Xv.Stacking.Proof.read64?_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.read64?_keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.defCell_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.defCell_bytes

/-- info: 'Compilatrix.Xv.Stacking.Proof.Match.update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Match.update

/-- info: 'Compilatrix.Xv.Stacking.Proof.Match.body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Match.body

/-- info: 'Compilatrix.Xv.Stacking.Proof.clearAccesses_sub' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.clearAccesses_sub

/-- info: 'Compilatrix.Xv.Stacking.Proof.clearAccesses_clears' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.clearAccesses_clears

/-- info: 'Compilatrix.Xv.Stacking.Proof.block_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.block_fits

/-- info: 'Compilatrix.Xv.Stacking.Proof.flatten_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.flatten_split

/-- info: 'Compilatrix.Xv.Stacking.Proof.machine_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.machine_at

/-- info: 'Compilatrix.Xv.Stacking.Proof.XlPos.segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.XlPos.segment

/-- info: 'Compilatrix.Xv.Stacking.Proof.XlPos.blockCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.XlPos.blockCode

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.slots

/-- info: 'Compilatrix.Xv.Stacking.Proof.Match.slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Match.slot

/-- info: 'Compilatrix.Xv.Stacking.Proof.Foot.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Foot.safe

/-- info: 'Compilatrix.Xv.Stacking.Proof.offsetOf_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.offsetOf_succ

/-- info: 'Compilatrix.Xv.Stacking.Proof.machine_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.machine_next

/-- info: 'Compilatrix.Xv.Stacking.Proof.nextHoles_op_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.nextHoles_op_sub

/-- info: 'Compilatrix.Xv.Stacking.Proof.nextHoles_op_clears' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.nextHoles_op_clears

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_op

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_row

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_move

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_zero

/-- info: 'Compilatrix.Xv.Stacking.Proof.zeroAll_readReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zeroAll_readReg

/-- info: 'Compilatrix.Xv.Stacking.Proof.zeroAll_memory' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zeroAll_memory

/-- info: 'Compilatrix.Xv.Stacking.Proof.zero_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zero_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.zeroes_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.zeroes_regs

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_fused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_fused

/-- info: 'Compilatrix.Xv.Stacking.Proof.FnAt.noEntryEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FnAt.noEntryEdge

/-- info: 'Compilatrix.Xv.Stacking.Proof.xlPos_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.xlPos_start

/-- info: 'Compilatrix.Xv.Stacking.Proof.After.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.After.refl

/-- info: 'Compilatrix.Xv.Stacking.Proof.takeEdge_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.takeEdge_empty

/-- info: 'Compilatrix.Xv.Stacking.Proof.edge_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.edge_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.Match.jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Match.jump

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_jmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_jmp

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_jcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_jcc

/-- info: 'Compilatrix.Xv.Stacking.Proof.EntryFrame.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.EntryFrame.keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_fail

/-- info: 'Compilatrix.Xv.Stacking.Proof.Straight.Segment.safe_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Straight.Segment.safe_call

/-- info: 'Compilatrix.Xv.Stacking.Proof.lea_foot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.lea_foot

/-- info: 'Compilatrix.Xv.Stacking.Proof.cmp_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cmp_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.cmp_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cmp_test

/-- info: 'Compilatrix.Xv.Stacking.Proof.cmp_foot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.cmp_foot

/-- info: 'Compilatrix.Xv.Stacking.Proof.check_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.check_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.store_exec_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.store_exec_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.stores_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.stores_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.inst_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.inst_keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.term_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.term_keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.block_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.block_keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_keep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_keep

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_gets' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_gets

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_inArgs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_inArgs

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_calls' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_calls

/-- info: 'Compilatrix.Xv.Stacking.Proof.noteLoc_outArgs_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.noteLoc_outArgs_le

/-- info: 'Compilatrix.Xv.Stacking.Proof.facts_outArgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.facts_outArgs

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_set_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_set_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_set_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_set_size

/-- info: 'Compilatrix.Xv.Stacking.Proof.entryRegs_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entryRegs_size

/-- info: 'Compilatrix.Xv.Stacking.Proof.entryRegs_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entryRegs_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.readAll_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.readAll_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.conventionArgs_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.conventionArgs_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.argLoc_reg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argLoc_reg

/-- info: 'Compilatrix.Xv.Stacking.Proof.argLoc_out' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argLoc_out

/-- info: 'Compilatrix.Xv.Stacking.Proof.nArgRegs_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.nArgRegs_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.inst_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.inst_call

/-- info: 'Compilatrix.Xv.Stacking.Proof.disjoint_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.disjoint_below

/-- info: 'Compilatrix.Xv.Stacking.Proof.saved_ne_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.saved_ne_rsp

/-- info: 'Compilatrix.Xv.Stacking.Proof.saveOff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.saveOff_mem

/-- info: 'Compilatrix.Xv.Stacking.Proof.frameless_saveOff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.frameless_saveOff

/-- info: 'Compilatrix.Xv.Stacking.Proof.prologue_map' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.prologue_map

/-- info: 'Compilatrix.Xv.Stacking.Proof.setReg_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.setReg_self

/-- info: 'Compilatrix.Xv.Stacking.Proof.prologue_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.prologue_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.ActFacts.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ActFacts.mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.entry_save_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entry_save_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.ctx_56' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ctx_56

/-- info: 'Compilatrix.Xv.Stacking.Proof.Global.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Global.mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.sub_ofNat_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.sub_ofNat_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.sub8_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.sub8_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.word_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.word_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.react' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.react

/-- info: 'Compilatrix.Xv.Stacking.Proof.call_inArgs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.call_inArgs_le

/-- info: 'Compilatrix.Xv.Stacking.Proof.call_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.call_match

/-- info: 'Compilatrix.Xv.Stacking.Proof.fnAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.fnAt_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.hasBlock_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.hasBlock_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.write64_bytes_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write64_bytes_off

/-- info: 'Compilatrix.Xv.Stacking.Proof.prologue_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.prologue_match

/-- info: 'Compilatrix.Xv.Stacking.Proof.r11_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.r11_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.unchecked_slack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.unchecked_slack

/-- info: 'Compilatrix.Xv.Stacking.Proof.first_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.first_block

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_call

/-- info: 'Compilatrix.Xv.Stacking.Proof.loads_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.loads_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.epilogue_map' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.epilogue_map

/-- info: 'Compilatrix.Xv.Stacking.Proof.epilogue_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.epilogue_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.clobber_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.clobber_fold

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_set_notin' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_set_notin

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_set_in' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_set_in

/-- info: 'Compilatrix.Xv.Stacking.Proof.mem_allGPRs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mem_allGPRs

/-- info: 'Compilatrix.Xv.Stacking.Proof.resultRegs_zip_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.resultRegs_zip_nodup

/-- info: 'Compilatrix.Xv.Stacking.Proof.returnRegs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.returnRegs_spec

/-- info: 'Compilatrix.Xv.Stacking.Proof.allowed_callerSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.allowed_callerSaved

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.allow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.allow

/-- info: 'Compilatrix.Xv.Stacking.Proof.calleeSaved_not_callerSaved' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.calleeSaved_not_callerSaved

/-- info: 'Compilatrix.Xv.Stacking.Proof.calleeSavedMatch_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.calleeSavedMatch_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.ret_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ret_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.conventionResults_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.conventionResults_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.FnAt.arities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.FnAt.arities

/-- info: 'Compilatrix.Xv.Stacking.Proof.resultsOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.resultsOf_eq

/-- info: 'Compilatrix.Xv.Stacking.Proof.call_arity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.call_arity

/-- info: 'Compilatrix.Xv.Stacking.Proof.mayChange_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mayChange_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.clobbers_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.clobbers_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.results_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.results_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.resultReg_not_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.resultReg_not_saved

/-- info: 'Compilatrix.Xv.Stacking.Proof.mem_take_zip_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.mem_take_zip_fst

/-- info: 'Compilatrix.Xv.Stacking.Proof.inst_call_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.inst_call_conv

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_ret

/-- info: 'Compilatrix.Xv.Stacking.Proof.saved_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.saved_mem

/-- info: 'Compilatrix.Xv.Stacking.Proof.term_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.term_tail

/-- info: 'Compilatrix.Xv.Stacking.Proof.tail_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.tail_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.room

/-- info: 'Compilatrix.Xv.Stacking.Proof.Chain.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Chain.tail

/-- info: 'Compilatrix.Xv.Stacking.Proof.tail_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.tail_match

/-- info: 'Compilatrix.Xv.Stacking.Proof.tailCall_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.tailCall_safe

/-- info: 'Compilatrix.Xv.Stacking.Proof.epilogue_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.epilogue_at

/-- info: 'Compilatrix.Xv.Stacking.Proof.saved_not_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.saved_not_allowed

/-- info: 'Compilatrix.Xv.Stacking.Proof.tail_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.tail_prologue

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_tail

/-- info: 'Compilatrix.Xv.Stacking.Proof.success_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.success_exit

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_done

/-- info: 'Compilatrix.Xv.Stacking.Proof.Outcome.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Outcome.mono

/-- info: 'Compilatrix.Xv.Stacking.Proof.Outcome.succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.Outcome.succ

/-- info: 'Compilatrix.Xv.Stacking.Proof.term_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.term_fail

/-- info: 'Compilatrix.Xv.Stacking.Proof.statusOf_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.statusOf_range

/-- info: 'Compilatrix.Xv.Stacking.Proof.step_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.step_sim

/-- info: 'Compilatrix.Xv.Stacking.Proof.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.sim

/-- info: 'Compilatrix.Xv.Stacking.Proof.bare_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.bare_step

/-- info: 'Compilatrix.Xv.Stacking.Proof.write64?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.write64?_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.read?_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.read?_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.subRM_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.subRM_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.orMR_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.orMR_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.test_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.test_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.test_signedLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.test_signedLt

/-- info: 'Compilatrix.Xv.Stacking.Proof.word_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.word_big

/-- info: 'Compilatrix.Xv.Stacking.Proof.or_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.or_big

/-- info: 'Compilatrix.Xv.Stacking.Proof.foldl_or_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.foldl_or_big

/-- info: 'Compilatrix.Xv.Stacking.Proof.word_sub_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.word_sub_sub

/-- info: 'Compilatrix.Xv.Stacking.Proof.pushes_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.pushes_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.ors_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ors_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.marshalOne_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.marshalOne_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.marshal_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.marshal_steps

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_ok

/-- info: 'Compilatrix.Xv.Stacking.Proof.EntryBase.entrySp_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.EntryBase.entrySp_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.EntryBase.limit_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.EntryBase.limit_toNat

/-- info: 'Compilatrix.Xv.Stacking.Proof.EntryBase.inStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.EntryBase.inStack

/-- info: 'Compilatrix.Xv.Stacking.Proof.entry_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entry_match

/-- info: 'Compilatrix.Xv.Stacking.Proof.word_add_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.word_add_ne

/-- info: 'Compilatrix.Xv.Stacking.Proof.saves_popOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.saves_popOrder

/-- info: 'Compilatrix.Xv.Stacking.Proof.ctx_48' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.ctx_48

/-- info: 'Compilatrix.Xv.Stacking.Proof.store_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.store_exec

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_head

/-- info: 'Compilatrix.Xv.Stacking.Proof.main_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.main_start

/-- info: 'Compilatrix.Xv.Stacking.Proof.entry_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entry_prologue

/-- info: 'Compilatrix.Xv.Stacking.Proof.entryFrame_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.entryFrame_of

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_call

/-- info: 'Compilatrix.Xv.Stacking.Proof.argPairs_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argPairs_get

/-- info: 'Compilatrix.Xv.Stacking.Proof.argPairs_get'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argPairs_get'

/-- info: 'Compilatrix.Xv.Stacking.Proof.marshal_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.marshal_order

/-- info: 'Compilatrix.Xv.Stacking.Proof.argRegs_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argRegs_nodup

/-- info: 'Compilatrix.Xv.Stacking.Proof.natSrcs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.natSrcs_mem

/-- info: 'Compilatrix.Xv.Stacking.Proof.argsFit_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argsFit_iff

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapperArgs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapperArgs_length

/-- info: 'Compilatrix.Xv.Stacking.Proof.sysvArgs_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.sysvArgs_ne

/-- info: 'Compilatrix.Xv.Stacking.Proof.argRegs_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argRegs_ne

/-- info: 'Compilatrix.Xv.Stacking.Proof.marshal_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.marshal_regs

/-- info: 'Compilatrix.Xv.Stacking.Proof.regsRel_entry_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.regsRel_entry_nil

/-- info: 'Compilatrix.Xv.Stacking.Proof.argPairs_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.argPairs_dst

/-- info: 'Compilatrix.Xv.Stacking.Proof.CallCore.regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.CallCore.regs

/-- info: 'Compilatrix.Xv.Stacking.Proof.marshal_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.marshal_call

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_pre

/-- info: 'Compilatrix.Xv.Stacking.Proof.main_fnAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.main_fnAt

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_entry

/-- info: 'Compilatrix.Xv.Stacking.Proof.wrapper_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.wrapper_overflow

/-- info: 'Compilatrix.Xv.Stacking.Proof.stacked_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.stacked_ends

/-- info: 'Compilatrix.Xv.Stacking.Proof.run_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Stacking.Proof.run_ends
