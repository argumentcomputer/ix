import IxCC.Lir.Proof.Opt.Arith
import IxCC.Lir.Proof.Opt.Mem
import IxCC.Lir.Proof.Opt.Seg
import IxCC.Lir.Proof.Opt.Sim
import IxCC.Lir.Proof.Opt.Backend

/-! Required axiom fences for the validated Lir SSA optimizer (`Lir.Opt`):
arithmetic/magic-multiplier soundness (`Arith`), byte-disjoint memory and
snapshot table soundness (`Mem`), straight-line segment and invariant soundness
(`Seg`), end-to-end simulation and refinement (`Sim`), and composed backend
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

/-! ## End-to-end simulation & refinement (`Sim`) -/

/-- info: 'IxCC.Lir.Opt.checkProgramWithPlan_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkProgramWithPlan_forward

/-- info: 'IxCC.Lir.Opt.checkProgramWithPlan_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.checkProgramWithPlan_sim

/-- info: 'IxCC.Lir.Opt.check_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.check_sim

/-- info: 'IxCC.Lir.Opt.check_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.check_refines

/-- info: 'IxCC.Lir.Opt.run_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.run_wellFormed

/-- info: 'IxCC.Lir.Opt.run_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.run_sim

/-- info: 'IxCC.Lir.Opt.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Opt.run_refines

/-- info: 'IxCC.Lir.Opt.validateCert_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
