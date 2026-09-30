import Compilatrix.Src.Proof.Mono
import Compilatrix.Lam.Proof.Mono
import Compilatrix.Lam.Erase.Proof.Correct
import Compilatrix.Src.Relevance.Proof.Sound
import Compilatrix.Lam.Erase.Proof.ModesOk
import Compilatrix.Lam.Erase.Proof.RegBody

/-! Required axiom fences for the source-to-Lam theorems (M2.2): clock
monotonicity of SrcEval and Lam, erasure's correctness, and the relevance
checker's soundness. Expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Src.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.eval_mono

/-- info: 'Compilatrix.Src.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.apply_mono

/-- info: 'Compilatrix.Src.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.applyAll_mono

/-- info: 'Compilatrix.Src.fire_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.fire_mono

/-- info: 'Compilatrix.Src.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.force_mono

/-- info: 'Compilatrix.Src.forceAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.forceAll_mono

/-- info: 'Compilatrix.Src.evalConst_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.evalConst_mono

/-- info: 'Compilatrix.Src.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.run_mono

/-- info: 'Compilatrix.Lam.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.eval_mono

/-- info: 'Compilatrix.Lam.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.apply_mono

/-- info: 'Compilatrix.Lam.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.force_mono

/-- info: 'Compilatrix.Lam.evalList_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.evalList_mono

/-- info: 'Compilatrix.Lam.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.applyAll_mono

/-- info: 'Compilatrix.Lam.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.run_mono

/-! Erasure's simulation and correctness. -/

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_correct

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_refines

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_spec

/-- info: 'Compilatrix.Lam.Erase.Proof.readback_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.readback_erase

/-- info: 'Compilatrix.Lam.Erase.Proof.readback_erase_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.readback_erase_nat

/-- info: 'Compilatrix.Lam.Erase.Proof.vr_eraseVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.vr_eraseVal

/-- info: 'Compilatrix.Lam.Erase.Proof.vr_obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.vr_obs

/-- info: 'Compilatrix.Lam.Erase.Proof.Setting.level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.Setting.level

/-- info: 'Compilatrix.Lam.Erase.Proof.Setting.tr_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.Setting.tr_correct

/-- info: 'Compilatrix.Lam.Erase.Proof.Setting.apply_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.Setting.apply_correct

/-- info: 'Compilatrix.Lam.Erase.Proof.Setting.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.Setting.run_correct

/-- info: 'Compilatrix.Lam.Erase.Proof.sound_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.sound_term

/-- info: 'Compilatrix.Sem.SimUpTo.sim' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.SimUpTo.sim

/-! The relevance checker's soundness (tier S). -/

/-- info: 'Compilatrix.Src.Relevance.Proof.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.check_sound

/-- info: 'Compilatrix.Src.Relevance.Proof.loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.loop_spec

/-- info: 'Compilatrix.Src.Relevance.Proof.visit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.visit_spec

/-- info: 'Compilatrix.Src.Relevance.Proof.records_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.records_nil

/-- info: 'Compilatrix.Src.Relevance.Proof.term_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.term_nil

/-- info: 'Compilatrix.Src.Relevance.Proof.rest_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.rest_nil

/-- info: 'Compilatrix.Src.Relevance.Proof.subsingletonFields_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.Relevance.Proof.subsingletonFields_nil

/-! Erasure decides the declarations' well-formedness (`progWF`), so
`erase_correct` and `erase_refines` need no premise about them. -/

/-- info: 'Compilatrix.Lam.Erase.Proof.progWF_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.progWF_iff

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_progWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_progWF

/-- info: 'Compilatrix.Src.NatMap.mem_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.NatMap.mem_toList

/-! Erasure's constructor table has a row for every key it emits. -/

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_reg

/-! `ModesOk` as a proposition, its checker's soundness, and erasure's output
checked against it. -/

/-- info: 'Compilatrix.Lam.modesOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.modesOk_sound

/-- info: 'Compilatrix.Lam.ModesOk.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.ModesOk.check_sound

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_modesOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_modesOk

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_modesOkSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_modesOkSpec
