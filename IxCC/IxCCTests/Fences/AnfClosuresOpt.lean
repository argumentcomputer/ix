import IxCC.Anf.Proof.Pass.FirstOrder
import IxCC.Anf.Proof.Pass.DeadParam
import IxCC.Anf.Proof.Defun.Narrow
import IxCC.Anf.Proof.Pass.Closures

/-! Exact axiom fences for Wave 1 closures & dead-parameter optimization proofs:
known-dispatch shrinking (`WalkProof.Ctx.vdisp`, `Shrink.Proof.roundOr_disp`),
first-order preservation across post-P8 passes (`Anf.Proof.Pass.FirstOrder`),
P5 dead-parameter worker/wrapper stripping (`Anf.Proof.Pass.DeadParam`),
P9 flow-directed dispatch narrowing (`Anf.Proof.Defun.Narrow`), and
post-P8 pipeline composition (`Anf.Pipeline.Proof.postStep_*`, `postSteps_*`,
`runPost_*`). -/

/-! ## Headline theorems -/

/-- info: 'IxCC.Anf.WalkProof.Ctx.vdisp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.WalkProof.Ctx.vdisp

/-- info: 'IxCC.Anf.Shrink.Proof.roundOr_disp' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Shrink.Proof.roundOr_disp

/-- info: 'IxCC.Anf.PassProof.shrink_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.shrink_firstOrder

/-- info: 'IxCC.Anf.PassProof.inline_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.inline_firstOrder

/-- info: 'IxCC.Anf.PassProof.prune_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.prune_firstOrder

/-- info: 'IxCC.Anf.DeadParam.Proof.run_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.run_tables

/-- info: 'IxCC.Anf.DeadParam.Proof.run_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.run_wf

/-- info: 'IxCC.Anf.DeadParam.Proof.run_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.run_firstOrder

/-- info: 'IxCC.Anf.DeadParam.Proof.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.run_refines

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.run_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.run_tables

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.run_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.run_wf

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.run_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.run_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.run_refines

/-- info: 'IxCC.Anf.Pipeline.Proof.postStep_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.postStep_tables

/-- info: 'IxCC.Anf.Pipeline.Proof.postSteps_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.postSteps_tables

/-- info: 'IxCC.Anf.Pipeline.Proof.runPost_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.runPost_tables

/-- info: 'IxCC.Anf.Pipeline.Proof.postStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.postStep_correct

/-- info: 'IxCC.Anf.Pipeline.Proof.postSteps_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.postSteps_correct

/-- info: 'IxCC.Anf.Pipeline.Proof.runPost_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.runPost_firstOrder

/-- info: 'IxCC.Anf.Pipeline.Proof.runPost_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.runPost_correct

/-! ## Every other public theorem of `IxCC.Anf.Proof.Pass.FirstOrder` -/

/-- info: 'IxCC.Anf.PassProof.NoFnEnv.nil' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.NoFnEnv.nil

/-- info: 'IxCC.Anf.PassProof.NoFnEnv.cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.NoFnEnv.cons

/-- info: 'IxCC.Anf.PassProof.NoFnEnv.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.NoFnEnv.append

/-- info: 'IxCC.Anf.PassProof.NoFnEnv.entsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.NoFnEnv.entsOf

/-- info: 'IxCC.Anf.PassProof.FoJEnv.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.FoJEnv.get

/-- info: 'IxCC.Anf.PassProof.pass_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.pass_fo

/-- info: 'IxCC.Anf.PassProof.branch_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.branch_fo

/-- info: 'IxCC.Anf.PassProof.ticks_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.ticks_fo

/-- info: 'IxCC.Anf.PassProof.stripTicks_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.stripTicks_fo

/-- info: 'IxCC.Anf.PassProof.alts_fo_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.alts_fo_mem

/-- info: 'IxCC.Anf.PassProof.select_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.select_fo

/-- info: 'IxCC.Anf.PassProof.FoCfg.strip' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.FoCfg.strip

/-- info: 'IxCC.Anf.PassProof.sameArms_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.sameArms_fo

/-- info: 'IxCC.Anf.PassProof.walk_fo_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.walk_fo_all

/-- info: 'IxCC.Anf.PassProof.walk_global_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.walk_global_fo

/-- info: 'IxCC.Anf.PassProof.foCfg_of_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.foCfg_of_firstOrder

/-- info: 'IxCC.Anf.PassProof.prune_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.prune_tables

/-- info: 'IxCC.Anf.PassProof.prune_rename_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.prune_rename_firstOrder

/-- info: 'IxCC.Anf.PassProof.prune_renameBind_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.prune_renameBind_firstOrder

/-- info: 'IxCC.Anf.PassProof.prune_renameAlts_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.prune_renameAlts_firstOrder

/-- info: 'IxCC.Anf.PassProof.prune_renameOpt_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.PassProof.prune_renameOpt_firstOrder

/-! ## Every other public theorem of `IxCC.Anf.Proof.Pass.DeadParam` -/

/-- info: 'IxCC.Anf.DeadParam.Proof.filterMask_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.filterMask_length

/-- info: 'IxCC.Anf.DeadParam.Proof.countTrue_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.countTrue_append

/-- info: 'IxCC.Anf.DeadParam.Proof.countTrue_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.countTrue_reverse

/-- info: 'IxCC.Anf.DeadParam.Proof.filterMask_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.filterMask_append

/-- info: 'IxCC.Anf.DeadParam.Proof.filterMask_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.filterMask_reverse

/-- info: 'IxCC.Anf.DeadParam.Proof.filterMask_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.filterMask_map

/-- info: 'IxCC.Anf.DeadParam.Proof.filterMask_pw' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.filterMask_pw

/-- info: 'IxCC.Anf.DeadParam.Proof.getElem?_filterMask_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.getElem?_filterMask_true

/-- info: 'IxCC.Anf.DeadParam.Proof.remapAtoms_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.remapAtoms_length

/-- info: 'IxCC.Anf.DeadParam.Proof.keepMask_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.keepMask_length

/-- info: 'IxCC.Anf.DeadParam.Proof.keepMask_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.keepMask_dead

/-- info: 'IxCC.Anf.DeadParam.Proof.evalAtoms_filterMask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.evalAtoms_filterMask

/-- info: 'IxCC.Anf.DeadParam.Proof.evalAtoms_keptParamAtoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.evalAtoms_keptParamAtoms

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFree.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFree.bind

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFree.join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFree.join

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFree.jump' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFree.jump

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFree.case' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFree.case

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFree.ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFree.ret

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFree.tick' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFree.tick

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFreeBind.app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFreeBind.app

/-- info: 'IxCC.Anf.DeadParam.Proof.DeadFreeBind.fn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DeadFreeBind.fn

/-- info: 'IxCC.Anf.DeadParam.Proof.pw_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.pw_of

/-- info: 'IxCC.Anf.DeadParam.Proof.of_pw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.of_pw

/-- info: 'IxCC.Anf.DeadParam.Proof.base' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.base

/-- info: 'IxCC.Anf.DeadParam.Proof.dv_obs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.dv_obs

/-- info: 'IxCC.Anf.DeadParam.Proof.dvs_obs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.dvs_obs

/-- info: 'IxCC.Anf.DeadParam.Proof.EnvRel.push' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.EnvRel.push

/-- info: 'IxCC.Anf.DeadParam.Proof.EnvRel.pushList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.EnvRel.pushList

/-- info: 'IxCC.Anf.DeadParam.Proof.atom_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.atom_rel

/-- info: 'IxCC.Anf.DeadParam.Proof.atoms_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.atoms_rel

/-- info: 'IxCC.Anf.DeadParam.Proof.DJ.get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.DJ.get

/-- info: 'IxCC.Anf.DeadParam.Proof.worker_call_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.worker_call_sim

/-- info: 'IxCC.Anf.DeadParam.Proof.app_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.app_at

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteExp_none_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteExp_none_depth

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteBind_none_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteBind_none_depth

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteAlts_none_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteAlts_none_depth

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteOpt_none_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteOpt_none_depth

/-- info: 'IxCC.Anf.DeadParam.Proof.call_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.call_at

/-- info: 'IxCC.Anf.DeadParam.Proof.glob_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.glob_at

/-- info: 'IxCC.Anf.DeadParam.Proof.fund_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.fund_exp

/-- info: 'IxCC.Anf.DeadParam.Proof.fund_alts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.fund_alts

/-- info: 'IxCC.Anf.DeadParam.Proof.fund_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.fund_bind

/-- info: 'IxCC.Anf.DeadParam.Proof.levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.levels

/-- info: 'IxCC.Anf.DeadParam.Proof.pw_lits' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.pw_lits

/-- info: 'IxCC.Anf.DeadParam.Proof.setting_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.setting_refines

/-- info: 'IxCC.Anf.DeadParam.Proof.candidate_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.candidate_spec

/-- info: 'IxCC.Anf.DeadParam.Proof.buildPlan_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.buildPlan_wf

/-- info: 'IxCC.Anf.DeadParam.Proof.run_roots' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.run_roots

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteExp_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteExp_firstOrder

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteBind_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteBind_firstOrder

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteAlts_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteAlts_firstOrder

/-- info: 'IxCC.Anf.DeadParam.Proof.rewriteOpt_firstOrder' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.rewriteOpt_firstOrder

/-- info: 'IxCC.Anf.DeadParam.Proof.exp_firstOrder_congr_below' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.exp_firstOrder_congr_below

/-- info: 'IxCC.Anf.DeadParam.Proof.bind_firstOrder_congr_below' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.bind_firstOrder_congr_below

/-- info: 'IxCC.Anf.DeadParam.Proof.alts_firstOrder_congr_below' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.alts_firstOrder_congr_below

/-- info: 'IxCC.Anf.DeadParam.Proof.opt_firstOrder_congr_below' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.opt_firstOrder_congr_below

/-- info: 'IxCC.Anf.DeadParam.Proof.globalList_keys_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.globalList_keys_nodup

/-- info: 'IxCC.Anf.DeadParam.Proof.mem_globalList_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.mem_globalList_iff

/-- info: 'IxCC.Anf.DeadParam.Proof.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.DeadParam.Proof.run_spec

/-! ## Every other public theorem of `IxCC.Anf.Proof.Defun.Narrow` -/

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.ClosOk.none' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.ClosOk.none

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.ClosOk.lit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.ClosOk.lit

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.ClosOk.box' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.ClosOk.box

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.ClosOk.src' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.ClosOk.src

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.kabsSub_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.kabsSub_sound

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.kabsListSub_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.kabsListSub_length

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.kabsListSub_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.kabsListSub_get

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.ValOk.not_clos' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.ValOk.not_clos

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.nil

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.cons

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.append

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.reverse

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.sub

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.replicate_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.replicate_none

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.lits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.lits

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.atom

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.atomsFlow_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.atomsFlow_length

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.EnvOk.atoms' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.EnvOk.atoms

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.fieldFlows_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.fieldFlows_length

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.fieldFlows_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.fieldFlows_get

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.paramFlows_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.paramFlows_length

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.knownClosure_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.knownClosure_false

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.asCtor_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.asCtor_ok

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.primResult_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.primResult_ok

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.dedupKeysAux_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.dedupKeysAux_mem

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.dedupKeys_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.dedupKeys_mem

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.dedupKeysAux_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.dedupKeysAux_nodup

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.dedupKeys_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.dedupKeys_nodup

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.evalAlts_allClo_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.evalAlts_allClo_src

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.evalAlts_filter_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.evalAlts_filter_nil

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.evalAlts_filter_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.evalAlts_filter_singleton

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.narrowArms_keys_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.narrowArms_keys_mem

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.narrowArms_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.narrowArms_spec

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.evalAtoms_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.evalAtoms_get

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.shiftAtom_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.shiftAtom_eval

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instAtom_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instAtom_eval

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instAtoms_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instAtoms_eval

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instExp_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instExp_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instBind_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instBind_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instAlts_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instAlts_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instOpt_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instOpt_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.altsFirstOrder_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.altsFirstOrder_mem

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.narrowArms_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.narrowArms_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteExp_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteExp_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteAlts_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteAlts_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteOpt_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteOpt_firstOrder

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.natSet_contains_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.natSet_contains_insert

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.natSet_contains_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.natSet_contains_insert_self

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.natSet_contains_insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.natSet_contains_insert_ne

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkDisps_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkDisps_closed

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.rewriteGlobals_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.rewriteGlobals_spec

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.run_spec

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.CallOk.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.CallOk.mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.CallOk.zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.CallOk.zero

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.PlainJoinR.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.PlainJoinR.mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.PlainJEnv.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.PlainJEnv.nil

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.PlainJEnv.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.PlainJEnv.mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.PlainJEnv.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.PlainJEnv.cons

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkBindPlain_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkBindPlain_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkExpPlain_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkExpPlain_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkOptPlain_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkOptPlain_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkAltsPlain_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkAltsPlain_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.InstTarget_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.InstTarget_mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.InstJoinR.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.InstJoinR.mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.InstJEnv.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.InstJEnv.nil

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.InstJEnv.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.InstJEnv.mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.InstJEnv.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.InstJEnv.cons

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instBind_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instBind_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.result_bind_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.result_bind_assoc

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instExp_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instExp_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.instAlts_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.instAlts_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteExp_used_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteExp_used_mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteAlts_used_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteAlts_used_mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteOpt_used_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteOpt_used_mono

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.isTailRet_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.isTailRet_eq

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.narrowSite_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.narrowSite_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteExp_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteExp_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.checkRewriteAlts_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.checkRewriteAlts_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.callOk_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.callOk_all

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.applyN_valOk_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.applyN_valOk_sim

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.closed_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.closed_refines
