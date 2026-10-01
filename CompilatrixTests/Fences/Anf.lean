import Compilatrix.Anf.Proof.Mono
import Compilatrix.Sem.Dominance
import Compilatrix.Anf.Proof.Convert.Correct

/-! Required axiom fences for the Anf proofs (M2.3): clock monotonicity of
Anf evaluation; ANF conversion (P1, Lam → Anf); the Anf-to-Anf relation, its
fundamental lemma and adequacy; the rewriting passes P2 shrink, P3 inline,
P4 specialise and pruning; the pipeline's correctness for every certificate
its replay accepts; and their traced restatements (decision D-1). Generated
by `plans/x86-phase1/m2-3/GenFences.lean`; expected messages are preserved
verbatim. -/

/-! Clock monotonicity of Anf evaluation (`Anf.Proof.Mono`). -/

/-- info: 'Compilatrix.Anf.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.eval_mono

/-- info: 'Compilatrix.Anf.evalBind_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.evalBind_mono

/-- info: 'Compilatrix.Anf.applyN_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.applyN_mono

/-- info: 'Compilatrix.Anf.evalAlts_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.evalAlts_mono

/-- info: 'Compilatrix.Anf.globVal_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.globVal_mono

/-- info: 'Compilatrix.Anf.callVal_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.callVal_mono

/-- info: 'Compilatrix.Anf.jumpTo_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.jumpTo_mono

/-- info: 'Compilatrix.Anf.enter_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.enter_mono

/-- info: 'Compilatrix.Anf.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.run_mono

/-! Tick dominance under a charge (`Sem.Dominance`) and clock maps of simulations. -/

/-- info: 'Compilatrix.Sem.SimUpTo.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.SimUpTo.tick

/-- info: 'Compilatrix.Sem.SimUpTo.tickConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.SimUpTo.tickConst

/-- info: 'Compilatrix.Sem.SimUpTo.shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.SimUpTo.shift

/-- info: 'Compilatrix.Sem.Sim.succ_of_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.succ_of_id

/-- info: 'Compilatrix.Sem.Sim.congr' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.congr

/-! ANF conversion (P1, Lam → Anf): application, the conversion's simulation at every clock, runs from a root, refinement and the traced shape. -/

/-- info: 'Compilatrix.Anf.Convert.Proof.app_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.app_sim

/-- info: 'Compilatrix.Anf.Convert.Proof.convert_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.convert_spec

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.minor_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.minor_sim

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.force_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.force_sim

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.convAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.convAt

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.bodySim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.bodySim

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.appSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.appSim

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.run_simUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.run_simUpTo

/-- info: 'Compilatrix.Anf.Convert.Proof.Setting.run_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.Setting.run_sim

/-- info: 'Compilatrix.Anf.Convert.Proof.vr_obs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.vr_obs

/-- info: 'Compilatrix.Anf.Convert.Proof.convert_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.convert_correct

/-- info: 'Compilatrix.Anf.Convert.Proof.convert_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.convert_refines

/-- info: 'Compilatrix.Anf.Convert.Proof.convert_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.convert_correct_traced

/-- info: 'Compilatrix.Anf.Convert.Proof.convert_refines_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Convert.Proof.convert_refines_traced
