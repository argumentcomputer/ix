import IxCC.Sem.Bind
import IxCC.Sem.TracedTransform
import IxCC.Lam.Erase.Proof.Traced
import IxCC.Xv.Validate.Proof.Traced
import IxCCTests.Sem.Toy.IO.Cases

/-! Required axiom fences for the traced statement shapes (decision D-1):
the bind-form kit for clocked results (`IxCC.Sem.Bind`), traced
outcomes, trace monotonicity and traced behaviours
(`IxCC.Sem.Traced`), the traced simulation with its forward,
timeout-prefix and progress clauses and its divergence lemma, backward
reading, safety and composition (`IxCC.Sem.TracedSim`), traced
languages, refinement and passes with the lifts from the pure framework
(`IxCC.Sem.TracedTransform`), and the Phase 1 restatements of
erasure's and the allocation validator's theorems through the lifts; then
the IO toy that checks the clause shapes (`IxCCTests.Sem.Toy.IO`).
Generated from the modules' public theorems; expected messages are
preserved verbatim. -/

/-- info: 'IxCC.Sem.ClockMono.dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.ClockMono.dom

/-- info: 'IxCC.Sem.Result.Agrees.dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Result.Agrees.dom

/-- info: 'IxCC.Sem.Result.Dom.bind' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Dom.bind

/-- info: 'IxCC.Sem.Result.Dom.eq_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Dom.eq_timeout

/-- info: 'IxCC.Sem.Result.Dom.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Dom.refl

/-- info: 'IxCC.Sem.Result.Dom.timeout' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Dom.timeout

/-- info: 'IxCC.Sem.Result.Dom.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Dom.trans

/-- info: 'IxCC.Sem.Result.bind_eq_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Result.bind_eq_ok_iff

/-- info: 'IxCC.Sem.Result.bind_eq_resource_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Result.bind_eq_resource_iff

/-- info: 'IxCC.Sem.Result.bind_eq_stuck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Result.bind_eq_stuck_iff

/-- info: 'IxCC.Sem.Result.bind_eq_timeout_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Result.bind_eq_timeout_iff

/-- info: 'IxCC.Sem.Result.bind_eq_trap_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Result.bind_eq_trap_iff

/-- info: 'IxCC.Sem.Result.Refines.ofBehaviour' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.ofBehaviour

/-- info: 'IxCC.Sem.TBehaviour.Performs.of_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Performs.of_prefix

/-- info: 'IxCC.Sem.TBehaviour.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.goesWrong

/-- info: 'IxCC.Sem.TBehaviour.Refines.live' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.live

/-- info: 'IxCC.Sem.TBehaviour.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.mono

/-- info: 'IxCC.Sem.TBehaviour.Refines.ofPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.ofPure

/-- info: 'IxCC.Sem.TBehaviour.Refines.performs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.performs

/-- info: 'IxCC.Sem.TBehaviour.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.refl

/-- info: 'IxCC.Sem.TBehaviour.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TBehaviour.Refines.trans

/-- info: 'IxCC.Sem.TraceMono.const' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TraceMono.const

/-- info: 'IxCC.Sem.TraceMono.eq_of_ne_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.TraceMono.eq_of_ne_timeout

/-- info: 'IxCC.Sem.TraceMono.ofPure' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TraceMono.ofPure

/-- info: 'IxCC.Sem.TraceMono.result' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.TraceMono.result

/-- info: 'IxCC.Sem.TraceMono.timeout_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TraceMono.timeout_of_le

/-- info: 'IxCC.Sem.TraceMono.trace_prefix_final' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TraceMono.trace_prefix_final

/-- info: 'IxCC.Sem.Traced.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.goesWrong

/-- info: 'IxCC.Sem.Traced.Refines.lift' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.lift

/-- info: 'IxCC.Sem.Traced.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.mono

/-- info: 'IxCC.Sem.Traced.Refines.of_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.of_ok

/-- info: 'IxCC.Sem.Traced.Refines.of_resource' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.of_resource

/-- info: 'IxCC.Sem.Traced.Refines.of_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.of_stuck

/-- info: 'IxCC.Sem.Traced.Refines.of_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.of_timeout

/-- info: 'IxCC.Sem.Traced.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.refl

/-- info: 'IxCC.Sem.Traced.Refines.toPure' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.toPure

/-- info: 'IxCC.Sem.Traced.Refines.trace_live' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.trace_live

/-- info: 'IxCC.Sem.Traced.Refines.trace_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.trace_prefix

/-- info: 'IxCC.Sem.Traced.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Traced.Refines.trans

/-- info: 'IxCC.Sem.Traced.lift_result' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.lift_result

/-- info: 'IxCC.Sem.Traced.lift_trace' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Traced.lift_trace

/-- info: 'IxCC.Sem.goesWrong_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.goesWrong_tbehaviour

/-- info: 'IxCC.Sem.performs_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.performs_tbehaviour

/-- info: 'IxCC.Sem.stuck_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.stuck_tbehaviour

/-- info: 'IxCC.Sem.tbehaviour_diverges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.tbehaviour_diverges_iff

/-- info: 'IxCC.Sem.tbehaviour_eq_ends_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.tbehaviour_eq_ends_iff

/-- info: 'IxCC.Sem.tbehaviour_of_forall_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.tbehaviour_of_forall_timeout

/-- info: 'IxCC.Sem.tbehaviour_of_ne_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.tbehaviour_of_ne_timeout

/-- info: 'IxCC.Sem.TSim.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.backward

/-- info: 'IxCC.Sem.TSim.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.comp

/-- info: 'IxCC.Sem.TSim.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.TSim.mono

/-- info: 'IxCC.Sem.TSim.ofPure' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.ofPure

/-- info: 'IxCC.Sem.TSim.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.refines

/-- info: 'IxCC.Sem.TSim.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.refl

/-- info: 'IxCC.Sem.TSim.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.safe

/-- info: 'IxCC.Sem.TSim.safe_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.safe_all

/-- info: 'IxCC.Sem.TSim.toPure' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.TSim.toPure

/-- info: 'IxCC.Sem.TSim.trace_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TSim.trace_prefix

/-- info: 'IxCC.Sem.Refines.ofPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.ofPure

/-- info: 'IxCC.Sem.TRefines.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.backward

/-- info: 'IxCC.Sem.TRefines.diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.diverges

/-- info: 'IxCC.Sem.TRefines.live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.live

/-- info: 'IxCC.Sem.TRefines.of_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.of_sim

/-- info: 'IxCC.Sem.TRefines.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.refl

/-- info: 'IxCC.Sem.TRefines.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.safe

/-- info: 'IxCC.Sem.TRefines.trace_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.trace_prefix

/-- info: 'IxCC.Sem.TRefines.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TRefines.trans

/-- info: 'IxCC.Sem.TTransform.comp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TTransform.comp_correct

/-- info: 'IxCC.Sem.TTransform.comp_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TTransform.comp_run

/-- info: 'IxCC.Sem.TTransform.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.TTransform.compile_correct

/-- info: 'IxCC.Sem.Transform.lift_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Transform.lift_run

/-- info: 'IxCC.Lam.Erase.Proof.erase_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_correct_traced

/-- info: 'IxCC.Lam.Erase.Proof.erase_refines_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_refines_traced

/-- info: 'IxCC.Xv.Validate.program_sim_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.program_sim_traced

/-- info: 'IxCC.Xv.Validate.program_sound_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Validate.program_sound_traced

/-! The IO toy (`IxCCTests.Sem.Toy.IO`). -/

/-- info: 'IxCCTests.Sem.Toy.IO.MAgrees.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.MAgrees.bind

/-- info: 'IxCCTests.Sem.Toy.IO.MDom.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.MDom.bind

/-- info: 'IxCCTests.Sem.Toy.IO.Big.evalAt_agree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Big.evalAt_agree

/-- info: 'IxCCTests.Sem.Toy.IO.Big.evalAt_dom' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Big.evalAt_dom

/-- info: 'IxCCTests.Sem.Toy.IO.Big.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Big.eval_mono

/-- info: 'IxCCTests.Sem.Toy.IO.Big.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Big.run_mono

/-- info: 'IxCCTests.Sem.Toy.IO.Tick.eval_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Tick.eval_dom

/-- info: 'IxCCTests.Sem.Toy.IO.Tick.eval_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Tick.eval_agree

/-- info: 'IxCCTests.Sem.Toy.IO.Tick.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Tick.sim

/-- info: 'IxCCTests.Sem.Toy.IO.ReachesT.det' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.ReachesT.det

/-- info: 'IxCCTests.Sem.Toy.IO.ReachesT.trace_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.ReachesT.trace_mono

/-- info: 'IxCCTests.Sem.Toy.IO.ReachesT.timeout_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.ReachesT.timeout_of_star

/-- info: 'IxCCTests.Sem.Toy.IO.ReachesT.passes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.ReachesT.passes

/-- info: 'IxCCTests.Sem.Toy.IO.reachesT_runT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.reachesT_runT

/-- info: 'IxCCTests.Sem.Toy.IO.RunsT.traceMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.RunsT.traceMono

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.step_grows' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.step_grows

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.potential_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.potential_ok

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.run_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.run_runs

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.run_mono

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.eval_fwd' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.eval_fwd

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.eval_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.eval_stop

/-- info: 'IxCCTests.Sem.Toy.IO.Stack.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Stack.sim

/-- info: 'IxCCTests.Sem.Toy.IO.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.pipeline_correct

/-- info: 'IxCCTests.Sem.Toy.IO.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.compile_sound

/-- info: 'IxCCTests.Sem.Toy.IO.compile_trace_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.compile_trace_prefix

/-- info: 'IxCCTests.Sem.Toy.IO.compile_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.compile_live

/-- info: 'IxCCTests.Sem.Toy.IO.compile_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.compile_safe

/-- info: 'IxCCTests.Sem.Toy.IO.compile_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.compile_diverges

/-- info: 'IxCCTests.Sem.Toy.IO.Cases.count_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Cases.count_run

/-- info: 'IxCCTests.Sem.Toy.IO.Cases.count_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Cases.count_tbehaviour

/-- info: 'IxCCTests.Sem.Toy.IO.Cases.count_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Cases.count_sim

/-- info: 'IxCCTests.Sem.Toy.IO.Cases.count_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Cases.count_refines

/-- info: 'IxCCTests.Sem.Toy.IO.Cases.count_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Cases.count_live

/-- info: 'IxCCTests.Sem.Toy.IO.Cases.count_never_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.IO.Cases.count_never_returns
