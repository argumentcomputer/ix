import Compilatrix.Sem.Smallstep
import Compilatrix.Sem.Transform
import CompilatrixTests.Sem.Toy.Cases

/-! Required axiom fences for the shared semantic framework (M2.1): clock
monotonicity and behaviours, clocked simulation and the divergence lemma,
refinement and certificate-taking passes, and the small-step core; then the
toy pipeline that exercises them end to end. Expected messages are preserved
verbatim. -/

/-- info: 'Compilatrix.Sem.Behaviour.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Behaviour.Refines.goesWrong

/-- info: 'Compilatrix.Sem.Behaviour.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Behaviour.Refines.mono

/-- info: 'Compilatrix.Sem.Behaviour.Refines.of_terminates' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Behaviour.Refines.of_terminates

/-- info: 'Compilatrix.Sem.Behaviour.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Behaviour.Refines.refl

/-- info: 'Compilatrix.Sem.Behaviour.Refines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Behaviour.Refines.trans

/-- info: 'Compilatrix.Sem.Behaviour.goesWrong_toBehaviour' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Behaviour.goesWrong_toBehaviour

/-- info: 'Compilatrix.Sem.ClockMono.const' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.ClockMono.const

/-- info: 'Compilatrix.Sem.ClockMono.ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.ClockMono.ok

/-- info: 'Compilatrix.Sem.ClockMono.timeout_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.ClockMono.timeout_of_le

/-- info: 'Compilatrix.Sem.Clocked.behaviour_of_ne_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Clocked.behaviour_of_ne_timeout

/-- info: 'Compilatrix.Sem.Diagram.forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Diagram.forward

/-- info: 'Compilatrix.Sem.Diagram.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Diagram.sim

/-- info: 'Compilatrix.Sem.Diagram.timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Diagram.timeout

/-- info: 'Compilatrix.Sem.Final.det' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Final.det

/-- info: 'Compilatrix.Sem.Final.iff_outcome' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Final.iff_outcome

/-- info: 'Compilatrix.Sem.Final.ne_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Final.ne_timeout

/-- info: 'Compilatrix.Sem.Final.not_next' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Final.not_next

/-- info: 'Compilatrix.Sem.Potential.clockMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Potential.clockMono

/-- info: 'Compilatrix.Sem.Potential.reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Potential.reaches

/-- info: 'Compilatrix.Sem.Potential.runClocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Potential.runClocked

/-- info: 'Compilatrix.Sem.Potential.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Potential.runs

/-- info: 'Compilatrix.Sem.Reaches.det' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.det

/-- info: 'Compilatrix.Sem.Reaches.down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.down

/-- info: 'Compilatrix.Sem.Reaches.iff_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.iff_final

/-- info: 'Compilatrix.Sem.Reaches.inv_charge' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.inv_charge

/-- info: 'Compilatrix.Sem.Reaches.inv_charge_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.inv_charge_zero

/-- info: 'Compilatrix.Sem.Reaches.inv_final' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.inv_final

/-- info: 'Compilatrix.Sem.Reaches.inv_free' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.inv_free

/-- info: 'Compilatrix.Sem.Reaches.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.mono

/-- info: 'Compilatrix.Sem.Reaches.of_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.of_final

/-- info: 'Compilatrix.Sem.Reaches.of_star' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.of_star

/-- info: 'Compilatrix.Sem.Reaches.star' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.star

/-- info: 'Compilatrix.Sem.Reaches.timeout_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.timeout_iff

/-- info: 'Compilatrix.Sem.Reaches.timeout_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.timeout_le

/-- info: 'Compilatrix.Sem.Reaches.timeout_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Reaches.timeout_of_star

/-- info: 'Compilatrix.Sem.Refines.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.backward

/-- info: 'Compilatrix.Sem.Refines.diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.diverges

/-- info: 'Compilatrix.Sem.Refines.of_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.of_sim

/-- info: 'Compilatrix.Sem.Refines.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.refl

/-- info: 'Compilatrix.Sem.Refines.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.safe

/-- info: 'Compilatrix.Sem.Refines.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Refines.trans

/-- info: 'Compilatrix.Sem.Result.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.goesWrong

/-- info: 'Compilatrix.Sem.Result.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.mono

/-- info: 'Compilatrix.Sem.Result.Refines.of_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.of_ok

/-- info: 'Compilatrix.Sem.Result.Refines.of_resource' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.of_resource

/-- info: 'Compilatrix.Sem.Result.Refines.of_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.of_stuck

/-- info: 'Compilatrix.Sem.Result.Refines.of_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.of_timeout

/-- info: 'Compilatrix.Sem.Result.Refines.of_trap' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.of_trap

/-- info: 'Compilatrix.Sem.Result.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.refl

/-- info: 'Compilatrix.Sem.Result.Refines.timeout_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.timeout_iff

/-- info: 'Compilatrix.Sem.Result.Refines.toBehaviour' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.toBehaviour

/-- info: 'Compilatrix.Sem.Result.Refines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.Refines.trans

/-- info: 'Compilatrix.Sem.Result.goesWrong_stuck' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.goesWrong_stuck

/-- info: 'Compilatrix.Sem.Result.goesWrong_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.goesWrong_trap

/-- info: 'Compilatrix.Sem.Result.not_goesWrong_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.not_goesWrong_ok

/-- info: 'Compilatrix.Sem.Result.not_goesWrong_resource' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.not_goesWrong_resource

/-- info: 'Compilatrix.Sem.Result.not_goesWrong_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.not_goesWrong_timeout

/-- info: 'Compilatrix.Sem.Result.toBehaviour_eq_diverges' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_eq_diverges

/-- info: 'Compilatrix.Sem.Result.toBehaviour_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_injective

/-- info: 'Compilatrix.Sem.Result.toBehaviour_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_ok

/-- info: 'Compilatrix.Sem.Result.toBehaviour_resource' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_resource

/-- info: 'Compilatrix.Sem.Result.toBehaviour_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_stuck

/-- info: 'Compilatrix.Sem.Result.toBehaviour_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_timeout

/-- info: 'Compilatrix.Sem.Result.toBehaviour_trap' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Result.toBehaviour_trap

/-- info: 'Compilatrix.Sem.Runs.clockMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Runs.clockMono

/-- info: 'Compilatrix.Sem.Runs.eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Sem.Runs.eq

/-- info: 'Compilatrix.Sem.Runs.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Runs.unique

/-- info: 'Compilatrix.Sem.Sim.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.backward

/-- info: 'Compilatrix.Sem.Sim.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.comp

/-- info: 'Compilatrix.Sem.Sim.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.mono

/-- info: 'Compilatrix.Sem.Sim.ofStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.ofStar

/-- info: 'Compilatrix.Sem.Sim.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.refines

/-- info: 'Compilatrix.Sem.Sim.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.refl

/-- info: 'Compilatrix.Sem.Sim.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.safe

/-- info: 'Compilatrix.Sem.Sim.safe_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Sim.safe_all

/-- info: 'Compilatrix.Sem.Star.head' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Star.head

/-- info: 'Compilatrix.Sem.Star.map' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Star.map

/-- info: 'Compilatrix.Sem.Star.single' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Star.single

/-- info: 'Compilatrix.Sem.Star.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.Star.trans

/-- info: 'Compilatrix.Sem.Transform.comp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Transform.comp_correct

/-- info: 'Compilatrix.Sem.Transform.comp_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Transform.comp_run

/-- info: 'Compilatrix.Sem.Transform.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Transform.compile_correct

/-- info: 'Compilatrix.Sem.behaviour_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_congr

/-- info: 'Compilatrix.Sem.behaviour_eq_diverges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_eq_diverges_iff

/-- info: 'Compilatrix.Sem.behaviour_eq_iff_of_ne_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_eq_iff_of_ne_diverges

/-- info: 'Compilatrix.Sem.behaviour_eq_resource_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_eq_resource_iff

/-- info: 'Compilatrix.Sem.behaviour_eq_stuck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_eq_stuck_iff

/-- info: 'Compilatrix.Sem.behaviour_eq_terminates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_eq_terminates_iff

/-- info: 'Compilatrix.Sem.behaviour_eq_trap_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_eq_trap_iff

/-- info: 'Compilatrix.Sem.behaviour_of_forall_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_of_forall_timeout

/-- info: 'Compilatrix.Sem.behaviour_of_ne_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.behaviour_of_ne_timeout

/-- info: 'Compilatrix.Sem.runClocked_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.runClocked_complete

/-- info: 'Compilatrix.Sem.runClocked_fuel_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.runClocked_fuel_mono

/-- info: 'Compilatrix.Sem.runClocked_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.runClocked_sound

/-- info: 'Compilatrix.Sem.runClocked_timeout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.runClocked_timeout

/-! The toy pipeline (`CompilatrixTests.Sem.Toy`). -/

/-- info: 'CompilatrixTests.Sem.Toy.Big.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Big.run_mono

/-- info: 'CompilatrixTests.Sem.Toy.Tick.eval_dom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Tick.eval_dom

/-- info: 'CompilatrixTests.Sem.Toy.Tick.eval_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Tick.eval_agree

/-- info: 'CompilatrixTests.Sem.Toy.Tick.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Tick.sim

/-- info: 'CompilatrixTests.Sem.Toy.Stack.potential_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Stack.potential_ok

/-- info: 'CompilatrixTests.Sem.Toy.Stack.run_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Stack.run_runs

/-- info: 'CompilatrixTests.Sem.Toy.Stack.eval_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Stack.eval_fwd

/-- info: 'CompilatrixTests.Sem.Toy.Stack.eval_timeout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Stack.eval_timeout

/-- info: 'CompilatrixTests.Sem.Toy.Stack.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Stack.sim

/-- info: 'CompilatrixTests.Sem.Toy.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.pipeline_correct

/-- info: 'CompilatrixTests.Sem.Toy.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.compile_sound

/-- info: 'CompilatrixTests.Sem.Toy.compile_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.compile_safe

/-- info: 'CompilatrixTests.Sem.Toy.compile_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.compile_diverges

/-- info: 'CompilatrixTests.Sem.Toy.Cases.loop_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Sem.Toy.Cases.loop_target
