import IxCC.Lir.Proof.Opt.Arith
import IxCC.Lir.Proof.Opt.Mem
import IxCC.Lir.Proof.Opt.Seg
import IxCC.Lir.Proof.Opt.Inline
import IxCC.Lir.Proof.Opt.Unroll
import IxCC.Lir.Proof.Opt.IfConv
import IxCC.Lir.Proof.Opt.Sim
import IxCC.Lir.Proof.Opt.Backend

/-! Required axiom fences for the validated Lir SSA optimizer (`Lir.Opt`):
arithmetic/magic-multiplier soundness (`Arith`), byte-disjoint memory and
snapshot table soundness (`Mem`), straight-line segment and invariant soundness
(`Seg`), the directly proved structural passes with their forward diagrams
(`Inline`, `Unroll`, `IfConv`), end-to-end simulation and refinement with the
driver's bounded loops (`Sim`), and composed backend
Lir-to-ELF soundness (`Backend.compileOpt_*`, `Backend.compileWithOptCert_*`).
Every theorem depends strictly on a subset of `[propext, Classical.choice, Quot.sound]`. -/

/-! ## Arithmetic & magic-multiplier soundness (`Arith`) -/

/-- info: 'IxCC.Lir.Opt.isPow2_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.isPow2_mul

/-- info: 'IxCC.Lir.Opt.isPow2_udiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.isPow2_udiv

/-- info: 'IxCC.Lir.Opt.isPow2_urem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.isPow2_urem

/-- info: 'IxCC.Lir.Opt.findPow2_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.findPow2_sound

/-- info: 'IxCC.Lir.Opt.magic_nat_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.magic_nat_div

/-- info: 'IxCC.Lir.Opt.checkMagicSimple_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkMagicSimple_sound

/-- info: 'IxCC.Lir.Opt.checkMagicAddShift_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkMagicAddShift_sound

/-- info: 'IxCC.Lir.Opt.checkMagic32_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkMagic32_sound

/-- info: 'IxCC.Lir.Opt.checkMagic32AddShift_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkMagic32AddShift_sound

/-- info: 'IxCC.Lir.Opt.urem_sub_mul_udiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.urem_sub_mul_udiv

/-- info: 'IxCC.Lir.Opt.SymExpr.norm_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.SymExpr.norm_sound

/-- info: 'IxCC.Lir.Opt.checkDivMagicExpr_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkDivMagicExpr_sound

/-- info: 'IxCC.Lir.Opt.checkRemMagicExpr_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkRemMagicExpr_sound

/-- info: 'IxCC.Lir.Opt.exprEquiv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.exprEquiv_sound

/-- info: 'IxCC.Lir.Opt.rangeOf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.rangeOf_sound

/-- info: 'IxCC.Lir.Opt.condFromFacts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.condFromFacts_sound

/-- info: 'IxCC.Lir.Opt.ovfFromFacts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ovfFromFacts_sound

/-- info: 'IxCC.Lir.Opt.matchRotateOr_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.matchRotateOr_sound

/-- info: 'IxCC.Lir.Opt.matchRotateMasked32_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.matchRotateMasked32_sound

/-- info: 'IxCC.Lir.Opt.mkAdd64_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.mkAdd64_sound

/-- info: 'IxCC.Lir.Opt.parityOf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.parityOf_sound

/-- info: 'IxCC.Lir.Opt.exprEquivFacts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.exprEquivFacts_sound

/-- info: 'IxCC.Lir.Opt.unwrapSelectCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unwrapSelectCond_sound

/-- info: 'IxCC.Lir.Opt.unwrapOddBit2_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unwrapOddBit2_sound

/-- info: 'IxCC.Lir.Opt.addC_even_ovf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.addC_even_ovf_eq

/-! ## Memory & snapshot-table soundness (`Mem`) -/

/-- info: 'IxCC.Lir.Opt.dispWord_add_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.dispWord_add_ne

/-- info: 'IxCC.Lir.Opt.forwardVal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.forwardVal_sound

/-- info: 'IxCC.Lir.Opt.dropShadowed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.dropShadowed_sound

/-- info: 'IxCC.Lir.Opt.SymMem.readAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.SymMem.readAux_sound

/-- info: 'IxCC.Lir.Opt.writesEquiv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.writesEquiv_sound

/-- info: 'IxCC.Lir.Opt.SnapTable.intern_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.SnapTable.intern_sound

/-! ## Segment & invariant soundness (`Seg`) -/

/-- info: 'IxCC.Lir.Opt.checkSeg_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkSeg_sound

/-- info: 'IxCC.Lir.Opt.checkEntails_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkEntails_sound

/-- info: 'IxCC.Lir.Opt.checkAfterCall_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkAfterCall_sound

/-- info: 'IxCC.Lir.Opt.stepTotalTgtList_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.stepTotalTgtList_sound

/-! ## Directly-proved structural passes (`Inline`, `Unroll`, `IfConv`) -/

/-- info: 'IxCC.Lir.Opt.inlineCallSite_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineCallSite_forward

/-- info: 'IxCC.Lir.Opt.inlineCallSite_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineCallSite_sim

/-- info: 'IxCC.Lir.Opt.inlineCallSiteChecked_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineCallSiteChecked_wellFormed

/-- info: 'IxCC.Lir.Opt.inlineCallSiteChecked_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineCallSiteChecked_sim

/-- info: 'IxCC.Lir.Opt.inlineTailSite_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineTailSite_forward

/-- info: 'IxCC.Lir.Opt.inlineTailSite_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineTailSite_sim

/-- info: 'IxCC.Lir.Opt.inlineTailSiteChecked_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineTailSiteChecked_wellFormed

/-- info: 'IxCC.Lir.Opt.inlineTailSiteChecked_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineTailSiteChecked_sim

/-- info: 'IxCC.Lir.Opt.unrollLoopSite_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unrollLoopSite_forward

/-- info: 'IxCC.Lir.Opt.unrollLoopSite_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unrollLoopSite_sim

/-- info: 'IxCC.Lir.Opt.unrollLoopSiteChecked_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unrollLoopSiteChecked_wellFormed

/-- info: 'IxCC.Lir.Opt.unrollLoopSiteChecked_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unrollLoopSiteChecked_sim

/-- info: 'IxCC.Lir.Opt.versionOddLoopSite_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.versionOddLoopSite_forward

/-- info: 'IxCC.Lir.Opt.versionOddLoopSite_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.versionOddLoopSite_sim

/-- info: 'IxCC.Lir.Opt.versionOddLoopSiteChecked_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.versionOddLoopSiteChecked_wellFormed

/-- info: 'IxCC.Lir.Opt.versionOddLoopSiteChecked_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.versionOddLoopSiteChecked_sim

/-- info: 'IxCC.Lir.Opt.ifConvDiamondSite_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvDiamondSite_sim

/-- info: 'IxCC.Lir.Opt.ifConvDiamondSiteChecked_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvDiamondSiteChecked_wellFormed

/-- info: 'IxCC.Lir.Opt.ifConvDiamondSiteChecked_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvDiamondSiteChecked_sim

/-! ## End-to-end simulation & refinement (`Sim`) -/

/-- info: 'IxCC.Lir.Opt.checkProgramWithPlan_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkProgramWithPlan_forward

/-- info: 'IxCC.Lir.Opt.checkProgramWithPlan_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkProgramWithPlan_sim

/-- info: 'IxCC.Lir.Opt.check_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.check_sim

/-- info: 'IxCC.Lir.Opt.check_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.check_refines

/-- info: 'IxCC.Lir.Opt.runLocal_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.runLocal_wellFormed

/-- info: 'IxCC.Lir.Opt.runLocal_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.runLocal_sim

/-- info: 'IxCC.Lir.Opt.runLocalAt_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.runLocalAt_wellFormed

/-- info: 'IxCC.Lir.Opt.runLocalAt_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.runLocalAt_sim

/-- info: 'IxCC.Lir.Opt.inlineTailLoop_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineTailLoop_wellFormed

/-- info: 'IxCC.Lir.Opt.inlineTailLoop_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineTailLoop_sim

/-- info: 'IxCC.Lir.Opt.inlineHelpersLoop_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineHelpersLoop_wellFormed

/-- info: 'IxCC.Lir.Opt.inlineHelpersLoop_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineHelpersLoop_sim

/-- info: 'IxCC.Lir.Opt.versionOddLoop_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.versionOddLoop_wellFormed

/-- info: 'IxCC.Lir.Opt.versionOddLoop_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.versionOddLoop_sim

/-- info: 'IxCC.Lir.Opt.ifConvDiamondStep_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvDiamondStep_wellFormed

/-- info: 'IxCC.Lir.Opt.ifConvDiamondStep_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvDiamondStep_sim

/-- info: 'IxCC.Lir.Opt.ifConvLoop_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvLoop_wellFormed

/-- info: 'IxCC.Lir.Opt.ifConvLoop_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.ifConvLoop_sim

/-- info: 'IxCC.Lir.Opt.inlineSelfLoop_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineSelfLoop_wellFormed

/-- info: 'IxCC.Lir.Opt.inlineSelfLoop_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.inlineSelfLoop_sim

/-- info: 'IxCC.Lir.Opt.unrollLoop_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unrollLoop_wellFormed

/-- info: 'IxCC.Lir.Opt.unrollLoop_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.unrollLoop_sim

/-- info: 'IxCC.Lir.Opt.run_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.run_wellFormed

/-- info: 'IxCC.Lir.Opt.run_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.run_sim

/-- info: 'IxCC.Lir.Opt.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.run_refines

/-- info: 'IxCC.Lir.Opt.validateCert_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.validateCert_wellFormed

/-- info: 'IxCC.Lir.Opt.validateCert_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.validateCert_sim

/-- info: 'IxCC.Lir.Opt.validateCert_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.validateCert_refines

/-! ## Composed Lir-to-ELF backend soundness (`Backend`) -/

/-- info: 'IxCC.Backend.compileOpt_sim_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileOpt_sim_main

/-- info: 'IxCC.Backend.compileOpt_refines_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileOpt_refines_main

/-- info: 'IxCC.Backend.compileOpt_tsim_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileOpt_tsim_main

/-- info: 'IxCC.Backend.compileWithOptCert_sim_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileWithOptCert_sim_main

/-- info: 'IxCC.Backend.compileWithOptCert_refines_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileWithOptCert_refines_main

/-- info: 'IxCC.Backend.compileWithOptCert_tsim_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compileWithOptCert_tsim_main
