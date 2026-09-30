import Compilatrix.Sem.Bind
import Compilatrix.Sem.TracedTransform
import Compilatrix.Lam.Erase.Proof.Traced
import Compilatrix.Xv.Validate.Proof.Traced
import CompilatrixTests.Sem.Toy.IO.Cases

/-! Required axiom fences for the traced statement shapes (decision D-1):
the bind-form kit for clocked results (`Compilatrix.Sem.Bind`), traced
outcomes, trace monotonicity and traced behaviours
(`Compilatrix.Sem.Traced`), the traced simulation with its forward,
timeout-prefix and progress clauses and its divergence lemma, backward
reading, safety and composition (`Compilatrix.Sem.TracedSim`), traced
languages, refinement and passes with the lifts from the pure framework
(`Compilatrix.Sem.TracedTransform`), and the Phase 1 restatements of
erasure's and the allocation validator's theorems through the lifts; then
the IO toy that checks the clause shapes (`CompilatrixTests.Sem.Toy.IO`).
Generated from the modules' public theorems; expected messages are
preserved verbatim. -/

/-- info: 'Compilatrix.Sem.ClockMono.dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.ClockMono.dom

/-- info: 'Compilatrix.Sem.Result.Agrees.dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Agrees.dom

/-- info: 'Compilatrix.Sem.Result.Dom.bind' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Dom.bind

/-- info: 'Compilatrix.Sem.Result.Dom.eq_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Dom.eq_timeout

/-- info: 'Compilatrix.Sem.Result.Dom.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Dom.refl

/-- info: 'Compilatrix.Sem.Result.Dom.timeout' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Dom.timeout

/-- info: 'Compilatrix.Sem.Result.Dom.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Dom.trans

/-- info: 'Compilatrix.Sem.Result.bind_eq_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.bind_eq_ok_iff

/-- info: 'Compilatrix.Sem.Result.bind_eq_resource_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.bind_eq_resource_iff

/-- info: 'Compilatrix.Sem.Result.bind_eq_stuck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.bind_eq_stuck_iff

/-- info: 'Compilatrix.Sem.Result.bind_eq_timeout_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.bind_eq_timeout_iff

/-- info: 'Compilatrix.Sem.Result.bind_eq_trap_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.bind_eq_trap_iff

/-- info: 'Compilatrix.Sem.Result.Refines.ofBehaviour' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.ofBehaviour

/-- info: 'Compilatrix.Sem.TBehaviour.Performs.of_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Performs.of_prefix

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.goesWrong

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.live' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.live

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.mono

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.ofPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.ofPure

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.performs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.performs

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.refl

/-- info: 'Compilatrix.Sem.TBehaviour.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TBehaviour.Refines.trans

/-- info: 'Compilatrix.Sem.TraceMono.const' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TraceMono.const

/-- info: 'Compilatrix.Sem.TraceMono.eq_of_ne_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.TraceMono.eq_of_ne_timeout

/-- info: 'Compilatrix.Sem.TraceMono.ofPure' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TraceMono.ofPure

/-- info: 'Compilatrix.Sem.TraceMono.result' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.TraceMono.result

/-- info: 'Compilatrix.Sem.TraceMono.timeout_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TraceMono.timeout_of_le

/-- info: 'Compilatrix.Sem.TraceMono.trace_prefix_final' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TraceMono.trace_prefix_final

/-- info: 'Compilatrix.Sem.Traced.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.goesWrong

/-- info: 'Compilatrix.Sem.Traced.Refines.lift' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.lift

/-- info: 'Compilatrix.Sem.Traced.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.mono

/-- info: 'Compilatrix.Sem.Traced.Refines.of_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.of_ok

/-- info: 'Compilatrix.Sem.Traced.Refines.of_resource' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.of_resource

/-- info: 'Compilatrix.Sem.Traced.Refines.of_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.of_stuck

/-- info: 'Compilatrix.Sem.Traced.Refines.of_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.of_timeout

/-- info: 'Compilatrix.Sem.Traced.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.refl

/-- info: 'Compilatrix.Sem.Traced.Refines.toPure' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.toPure

/-- info: 'Compilatrix.Sem.Traced.Refines.trace_live' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.trace_live

/-- info: 'Compilatrix.Sem.Traced.Refines.trace_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.trace_prefix

/-- info: 'Compilatrix.Sem.Traced.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.Refines.trans

/-- info: 'Compilatrix.Sem.Traced.lift_result' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.lift_result

/-- info: 'Compilatrix.Sem.Traced.lift_trace' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Traced.lift_trace

/-- info: 'Compilatrix.Sem.goesWrong_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.goesWrong_tbehaviour

/-- info: 'Compilatrix.Sem.performs_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.performs_tbehaviour

/-- info: 'Compilatrix.Sem.stuck_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.stuck_tbehaviour

/-- info: 'Compilatrix.Sem.tbehaviour_diverges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.tbehaviour_diverges_iff

/-- info: 'Compilatrix.Sem.tbehaviour_eq_ends_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.tbehaviour_eq_ends_iff

/-- info: 'Compilatrix.Sem.tbehaviour_of_forall_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.tbehaviour_of_forall_timeout

/-- info: 'Compilatrix.Sem.tbehaviour_of_ne_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.tbehaviour_of_ne_timeout

/-- info: 'Compilatrix.Sem.TSim.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.backward

/-- info: 'Compilatrix.Sem.TSim.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.comp

/-- info: 'Compilatrix.Sem.TSim.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.mono

/-- info: 'Compilatrix.Sem.TSim.ofPure' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.ofPure

/-- info: 'Compilatrix.Sem.TSim.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.refines

/-- info: 'Compilatrix.Sem.TSim.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.refl

/-- info: 'Compilatrix.Sem.TSim.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.safe

/-- info: 'Compilatrix.Sem.TSim.safe_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.safe_all

/-- info: 'Compilatrix.Sem.TSim.toPure' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.toPure

/-- info: 'Compilatrix.Sem.TSim.trace_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TSim.trace_prefix

/-- info: 'Compilatrix.Sem.Refines.ofPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.ofPure

/-- info: 'Compilatrix.Sem.TRefines.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.backward

/-- info: 'Compilatrix.Sem.TRefines.diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.diverges

/-- info: 'Compilatrix.Sem.TRefines.live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.live

/-- info: 'Compilatrix.Sem.TRefines.of_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.of_sim

/-- info: 'Compilatrix.Sem.TRefines.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.refl

/-- info: 'Compilatrix.Sem.TRefines.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.safe

/-- info: 'Compilatrix.Sem.TRefines.trace_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.trace_prefix

/-- info: 'Compilatrix.Sem.TRefines.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TRefines.trans

/-- info: 'Compilatrix.Sem.TTransform.comp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TTransform.comp_correct

/-- info: 'Compilatrix.Sem.TTransform.comp_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TTransform.comp_run

/-- info: 'Compilatrix.Sem.TTransform.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.TTransform.compile_correct

/-- info: 'Compilatrix.Sem.Transform.lift_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Transform.lift_run

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_correct_traced

/-- info: 'Compilatrix.Lam.Erase.Proof.erase_refines_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.Erase.Proof.erase_refines_traced

/-- info: 'Compilatrix.Xv.Validate.program_sim_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.program_sim_traced

/-- info: 'Compilatrix.Xv.Validate.program_sound_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Validate.program_sound_traced

/-! The IO toy (`CompilatrixTests.Sem.Toy.IO`). -/

/-- info: 'CompilatrixTests.Sem.Toy.IO.MAgrees.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.MAgrees.bind

/-- info: 'CompilatrixTests.Sem.Toy.IO.MDom.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.MDom.bind

/-- info: 'CompilatrixTests.Sem.Toy.IO.Big.evalAt_agree' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Big.evalAt_agree

/-- info: 'CompilatrixTests.Sem.Toy.IO.Big.evalAt_dom' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Big.evalAt_dom

/-- info: 'CompilatrixTests.Sem.Toy.IO.Big.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Big.eval_mono

/-- info: 'CompilatrixTests.Sem.Toy.IO.Big.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Big.run_mono

/-- info: 'CompilatrixTests.Sem.Toy.IO.Tick.eval_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Tick.eval_dom

/-- info: 'CompilatrixTests.Sem.Toy.IO.Tick.eval_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Tick.eval_agree

/-- info: 'CompilatrixTests.Sem.Toy.IO.Tick.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Tick.sim

/-- info: 'CompilatrixTests.Sem.Toy.IO.ReachesT.det' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.ReachesT.det

/-- info: 'CompilatrixTests.Sem.Toy.IO.ReachesT.trace_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.ReachesT.trace_mono

/-- info: 'CompilatrixTests.Sem.Toy.IO.ReachesT.timeout_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.ReachesT.timeout_of_star

/-- info: 'CompilatrixTests.Sem.Toy.IO.ReachesT.passes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.ReachesT.passes

/-- info: 'CompilatrixTests.Sem.Toy.IO.reachesT_runT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.reachesT_runT

/-- info: 'CompilatrixTests.Sem.Toy.IO.RunsT.traceMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.RunsT.traceMono

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.step_grows' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.step_grows

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.potential_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.potential_ok

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.run_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.run_runs

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.run_mono

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.eval_fwd' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.eval_fwd

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.eval_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.eval_stop

/-- info: 'CompilatrixTests.Sem.Toy.IO.Stack.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Stack.sim

/-- info: 'CompilatrixTests.Sem.Toy.IO.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.pipeline_correct

/-- info: 'CompilatrixTests.Sem.Toy.IO.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.compile_sound

/-- info: 'CompilatrixTests.Sem.Toy.IO.compile_trace_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.compile_trace_prefix

/-- info: 'CompilatrixTests.Sem.Toy.IO.compile_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.compile_live

/-- info: 'CompilatrixTests.Sem.Toy.IO.compile_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.compile_safe

/-- info: 'CompilatrixTests.Sem.Toy.IO.compile_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.compile_diverges

/-- info: 'CompilatrixTests.Sem.Toy.IO.Cases.count_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Cases.count_run

/-- info: 'CompilatrixTests.Sem.Toy.IO.Cases.count_tbehaviour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Cases.count_tbehaviour

/-- info: 'CompilatrixTests.Sem.Toy.IO.Cases.count_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Cases.count_sim

/-- info: 'CompilatrixTests.Sem.Toy.IO.Cases.count_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Cases.count_refines

/-- info: 'CompilatrixTests.Sem.Toy.IO.Cases.count_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Cases.count_live

/-- info: 'CompilatrixTests.Sem.Toy.IO.Cases.count_never_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.IO.Cases.count_never_returns
