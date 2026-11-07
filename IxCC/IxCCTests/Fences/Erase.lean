import IxCC.Src.Proof.Mono
import IxCC.Lam.Proof.Mono
import IxCC.Lam.Erase.Proof.Correct
import IxCC.Src.Relevance.Proof.Sound
import IxCC.Lam.Erase.Proof.ModesOk
import IxCC.Lam.Erase.Proof.WFProg

/-! Required axiom fences for the source-to-Lam theorems (M2.2): clock
monotonicity of SrcEval and Lam, erasure's correctness, and the relevance
checker's soundness. Expected messages are preserved verbatim. -/

/-- info: 'IxCC.Src.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.eval_mono

/-- info: 'IxCC.Src.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.apply_mono

/-- info: 'IxCC.Src.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.applyAll_mono

/-- info: 'IxCC.Src.fire_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.fire_mono

/-- info: 'IxCC.Src.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.force_mono

/-- info: 'IxCC.Src.forceAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.forceAll_mono

/-- info: 'IxCC.Src.evalConst_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.evalConst_mono

/-- info: 'IxCC.Src.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.run_mono

/-- info: 'IxCC.Lam.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.eval_mono

/-- info: 'IxCC.Lam.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.apply_mono

/-- info: 'IxCC.Lam.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.force_mono

/-- info: 'IxCC.Lam.evalList_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.evalList_mono

/-- info: 'IxCC.Lam.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.applyAll_mono

/-- info: 'IxCC.Lam.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.run_mono

/-! Erasure's simulation and correctness. -/

/-- info: 'IxCC.Lam.Erase.Proof.erase_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_correct

/-- info: 'IxCC.Lam.Erase.Proof.erase_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_refines

/-- info: 'IxCC.Lam.Erase.Proof.erase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_spec

/-- info: 'IxCC.Lam.Erase.Proof.readback_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.readback_erase

/-- info: 'IxCC.Lam.Erase.Proof.readback_erase_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.readback_erase_nat

/-- info: 'IxCC.Lam.Erase.Proof.vr_eraseVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.vr_eraseVal

/-- info: 'IxCC.Lam.Erase.Proof.vr_obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.vr_obs

/-- info: 'IxCC.Lam.Erase.Proof.Setting.level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.level

/-- info: 'IxCC.Lam.Erase.Proof.Setting.tr_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.tr_correct

/-- info: 'IxCC.Lam.Erase.Proof.Setting.apply_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.apply_correct

/-- info: 'IxCC.Lam.Erase.Proof.Setting.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.run_correct

/-- info: 'IxCC.Lam.Erase.Proof.sound_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.sound_term

/-- info: 'IxCC.Sem.SimUpTo.sim' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.SimUpTo.sim

/-! The relevance checker's soundness (tier S). -/

/-- info: 'IxCC.Src.Relevance.Proof.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.check_sound

/-- info: 'IxCC.Src.Relevance.Proof.loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.loop_spec

/-- info: 'IxCC.Src.Relevance.Proof.visit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.visit_spec

/-- info: 'IxCC.Src.Relevance.Proof.records_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.records_nil

/-- info: 'IxCC.Src.Relevance.Proof.term_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.term_nil

/-- info: 'IxCC.Src.Relevance.Proof.rest_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.rest_nil

/-- info: 'IxCC.Src.Relevance.Proof.subsingletonFields_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.subsingletonFields_nil

/-! Erasure decides the declarations' well-formedness (`progWF`), so
`erase_correct` and `erase_refines` need no premise about them. -/

/-- info: 'IxCC.Lam.Erase.Proof.progWF_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.progWF_iff

/-- info: 'IxCC.Lam.Erase.Proof.erase_progWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_progWF

/-- info: 'IxCC.Src.NatMap.mem_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.NatMap.mem_toList

/-! Erasure's constructor table has a row for every key it emits. -/

/-- info: 'IxCC.Lam.Erase.Proof.erase_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_reg

/-! Erasure's output is well formed. -/

/-- info: 'IxCC.Lam.Erase.Proof.erase_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_wellFormed

/-- info: 'IxCC.Lam.Erase.Proof.erase_spec_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_spec_run

/-- info: 'IxCC.Lam.Erase.Proof.tr_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.tr_wf

/-- info: 'IxCC.Lam.Erase.Proof.bodyR_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.bodyR_wf

/-! `ModesOk` as a proposition, its checker's soundness, and erasure's output
checked against it. -/

/-- info: 'IxCC.Lam.modesOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.modesOk_sound

/-- info: 'IxCC.Lam.ModesOk.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.ModesOk.check_sound

/-- info: 'IxCC.Lam.Erase.Proof.erase_modesOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_modesOk

/-- info: 'IxCC.Lam.Erase.Proof.erase_modesOkSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_modesOkSpec
