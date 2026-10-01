import Compilatrix.Anf.Proof.Mono
import Compilatrix.Sem.Dominance
import Compilatrix.Anf.Proof.Convert.Correct
import Compilatrix.Anf.Proof.Rel.Ident

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

/-! The Anf-to-Anf relation (`Anf.Proof.Rel`): compatibility per construct, the fundamental lemma, application of closures of the same code, adequacy, and the identity instance. -/

/-- info: 'Compilatrix.Anf.Rel.compat_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_atom

/-- info: 'Compilatrix.Anf.Rel.compat_con' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_con

/-- info: 'Compilatrix.Anf.Rel.compat_proj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_proj

/-- info: 'Compilatrix.Anf.Rel.compat_prim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_prim

/-- info: 'Compilatrix.Anf.Rel.compat_glob' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_glob

/-- info: 'Compilatrix.Anf.Rel.compat_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_call

/-- info: 'Compilatrix.Anf.Rel.compat_app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_app

/-- info: 'Compilatrix.Anf.Rel.compat_fn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_fn

/-- info: 'Compilatrix.Anf.Rel.compat_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_bind

/-- info: 'Compilatrix.Anf.Rel.compat_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_join

/-- info: 'Compilatrix.Anf.Rel.compat_jumpTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_jumpTo

/-- info: 'Compilatrix.Anf.Rel.compat_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_ret

/-- info: 'Compilatrix.Anf.Rel.compat_tick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_tick

/-- info: 'Compilatrix.Anf.Rel.compat_trap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.compat_trap

/-- info: 'Compilatrix.Anf.Rel.fund_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.fund_step

/-- info: 'Compilatrix.Anf.Rel.app_idc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.app_idc

/-- info: 'Compilatrix.Anf.Rel.run_simUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.run_simUpTo

/-- info: 'Compilatrix.Anf.Rel.refines_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.refines_of

/-- info: 'Compilatrix.Anf.Rel.Ident.structural' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.Ident.structural

/-- info: 'Compilatrix.Anf.Rel.Ident.level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.Ident.level

/-- info: 'Compilatrix.Anf.Rel.Ident.fund' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.Ident.fund

/-- info: 'Compilatrix.Anf.Rel.Ident.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Rel.Ident.refines
