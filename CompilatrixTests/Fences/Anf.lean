import Compilatrix.Anf.Proof.Mono
import Compilatrix.Sem.Dominance
import Compilatrix.Anf.Proof.Convert.Correct
import Compilatrix.Anf.Proof.Rel.Ident
import Compilatrix.Anf.Proof.Pass.Shrink
import Compilatrix.Anf.Proof.Pass.Inline

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

/-! The rewriting walk (`Anf.Proof.Walk`, shared by P2, P3 and P4's bodies): the walk relation is structural and keeps observations; one fuel level per walk function (returns, continuations, join points by Löb induction, jumps, case-of-case, case tests and alternatives, kept and skipped bindings, globals, calls, applications and β); application of walked closures; the simulation at every bound and adequacy. -/

/-- info: 'Compilatrix.Anf.WalkProof.structural' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.structural

/-- info: 'Compilatrix.Anf.WalkProof.obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.obs

/-- info: 'Compilatrix.Sem.SimUpTo.strengthen' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.SimUpTo.strengthen

/-- info: 'Compilatrix.Sem.SimUpTo.unmap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.SimUpTo.unmap

/-- info: 'Compilatrix.Anf.WalkProof.pass_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.pass_sim

/-- info: 'Compilatrix.Anf.WalkProof.branch_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.branch_sim

/-- info: 'Compilatrix.Anf.WalkProof.walk_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walk_step

/-- info: 'Compilatrix.Anf.WalkProof.after_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.after_step

/-- info: 'Compilatrix.Anf.WalkProof.joinR_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.joinR_emit

/-- info: 'Compilatrix.Anf.WalkProof.walkJoin_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkJoin_step

/-- info: 'Compilatrix.Anf.WalkProof.caseOfCase_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.caseOfCase_sim

/-- info: 'Compilatrix.Anf.WalkProof.walkJump_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkJump_step

/-- info: 'Compilatrix.Anf.WalkProof.identityTail_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.identityTail_spec

/-- info: 'Compilatrix.Anf.WalkProof.sameArms_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.sameArms_spec

/-- info: 'Compilatrix.Anf.WalkProof.walkAlts_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkAlts_step

/-- info: 'Compilatrix.Anf.WalkProof.case_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.case_general

/-- info: 'Compilatrix.Anf.WalkProof.walkCase_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkCase_step

/-- info: 'Compilatrix.Anf.WalkProof.emit_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.emit_sim

/-- info: 'Compilatrix.Anf.WalkProof.skip_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.skip_sim

/-- info: 'Compilatrix.Anf.WalkProof.skip_tick_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.skip_tick_sim

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_atom

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_con' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_con

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_proj

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_prim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_prim

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_fn

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_glob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_glob

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_call

/-- info: 'Compilatrix.Anf.WalkProof.app_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.app_known

/-- info: 'Compilatrix.Anf.WalkProof.beta_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.beta_tick

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_app

/-- info: 'Compilatrix.Anf.WalkProof.walkBind_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkBind_step

/-- info: 'Compilatrix.Anf.WalkProof.enter_walkc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.enter_walkc

/-- info: 'Compilatrix.Anf.WalkProof.app_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.app_at

/-- info: 'Compilatrix.Anf.WalkProof.walkAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkAt_succ

/-- info: 'Compilatrix.Anf.WalkProof.walkAt_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.walkAt_all

/-- info: 'Compilatrix.Anf.WalkProof.levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.levels

/-- info: 'Compilatrix.Anf.WalkProof.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.refines

/-- info: 'Compilatrix.Anf.WalkProof.WalkProg.hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.WalkProg.hyp

/-- info: 'Compilatrix.Anf.WalkProof.WalkProg.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.WalkProof.WalkProg.refines

/-! P2 shrink and P3 inline (`Anf.Proof.Pass`): every certificate and oracle the re-run accepts gives a refinement of the input; the traced shape. -/

/-- info: 'Compilatrix.Anf.PassProof.get?_ofList_globalList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.PassProof.get?_ofList_globalList

/-- info: 'Compilatrix.Anf.PassProof.refines_of_globals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.PassProof.refines_of_globals

/-- info: 'Compilatrix.Anf.Shrink.Proof.roundOn_walkProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Shrink.Proof.roundOn_walkProg

/-- info: 'Compilatrix.Anf.Shrink.Proof.stage_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Shrink.Proof.stage_refines

/-- info: 'Compilatrix.Anf.Shrink.Proof.stage_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Shrink.Proof.stage_global

/-- info: 'Compilatrix.Anf.Shrink.Proof.run_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Shrink.Proof.run_global

/-- info: 'Compilatrix.Anf.Shrink.Proof.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Shrink.Proof.run_refines

/-- info: 'Compilatrix.Anf.Shrink.Proof.run_refines_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Shrink.Proof.run_refines_traced

/-- info: 'Compilatrix.Anf.Inline.Proof.round_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Inline.Proof.round_global

/-- info: 'Compilatrix.Anf.Inline.Proof.round_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Inline.Proof.round_refines

/-- info: 'Compilatrix.Anf.Inline.Proof.round_refines_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.Inline.Proof.round_refines_traced
