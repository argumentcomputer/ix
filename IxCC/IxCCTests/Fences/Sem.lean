import IxCC.Sem.Smallstep
import IxCC.Sem.Transform
import IxCCTests.Sem.Toy.Cases

/-! Required axiom fences for the shared semantic framework (M2.1): clock
monotonicity and behaviours, clocked simulation and the divergence lemma,
refinement and certificate-taking passes, and the small-step core; then the
toy pipeline that exercises them end to end. Expected messages are preserved
verbatim. -/

/-- info: 'IxCC.Sem.Behaviour.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Behaviour.Refines.goesWrong

/-- info: 'IxCC.Sem.Behaviour.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Behaviour.Refines.mono

/-- info: 'IxCC.Sem.Behaviour.Refines.of_terminates' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Behaviour.Refines.of_terminates

/-- info: 'IxCC.Sem.Behaviour.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Behaviour.Refines.refl

/-- info: 'IxCC.Sem.Behaviour.Refines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Behaviour.Refines.trans

/-- info: 'IxCC.Sem.Behaviour.goesWrong_toBehaviour' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Behaviour.goesWrong_toBehaviour

/-- info: 'IxCC.Sem.ClockMono.const' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.ClockMono.const

/-- info: 'IxCC.Sem.ClockMono.ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.ClockMono.ok

/-- info: 'IxCC.Sem.ClockMono.timeout_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.ClockMono.timeout_of_le

/-- info: 'IxCC.Sem.Clocked.behaviour_of_ne_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Clocked.behaviour_of_ne_timeout

/-- info: 'IxCC.Sem.Diagram.forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Diagram.forward

/-- info: 'IxCC.Sem.Diagram.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Diagram.sim

/-- info: 'IxCC.Sem.Diagram.timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Diagram.timeout

/-- info: 'IxCC.Sem.Final.det' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Final.det

/-- info: 'IxCC.Sem.Final.iff_outcome' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Final.iff_outcome

/-- info: 'IxCC.Sem.Final.ne_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Final.ne_timeout

/-- info: 'IxCC.Sem.Final.not_next' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Final.not_next

/-- info: 'IxCC.Sem.Potential.clockMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Potential.clockMono

/-- info: 'IxCC.Sem.Potential.reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Potential.reaches

/-- info: 'IxCC.Sem.Potential.runClocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Potential.runClocked

/-- info: 'IxCC.Sem.Potential.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Potential.runs

/-- info: 'IxCC.Sem.Reaches.det' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.det

/-- info: 'IxCC.Sem.Reaches.down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.down

/-- info: 'IxCC.Sem.Reaches.iff_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.iff_final

/-- info: 'IxCC.Sem.Reaches.inv_charge' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.inv_charge

/-- info: 'IxCC.Sem.Reaches.inv_charge_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.inv_charge_zero

/-- info: 'IxCC.Sem.Reaches.inv_final' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.inv_final

/-- info: 'IxCC.Sem.Reaches.inv_free' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.inv_free

/-- info: 'IxCC.Sem.Reaches.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.mono

/-- info: 'IxCC.Sem.Reaches.of_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.of_final

/-- info: 'IxCC.Sem.Reaches.of_star' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.of_star

/-- info: 'IxCC.Sem.Reaches.star' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.star

/-- info: 'IxCC.Sem.Reaches.timeout_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.timeout_iff

/-- info: 'IxCC.Sem.Reaches.timeout_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.timeout_le

/-- info: 'IxCC.Sem.Reaches.timeout_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Reaches.timeout_of_star

/-- info: 'IxCC.Sem.Refines.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.backward

/-- info: 'IxCC.Sem.Refines.diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.diverges

/-- info: 'IxCC.Sem.Refines.of_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.of_sim

/-- info: 'IxCC.Sem.Refines.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.refl

/-- info: 'IxCC.Sem.Refines.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.safe

/-- info: 'IxCC.Sem.Refines.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.trans

/-- info: 'IxCC.Sem.Result.Refines.goesWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.goesWrong

/-- info: 'IxCC.Sem.Result.Refines.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.mono

/-- info: 'IxCC.Sem.Result.Refines.of_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.of_ok

/-- info: 'IxCC.Sem.Result.Refines.of_resource' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.of_resource

/-- info: 'IxCC.Sem.Result.Refines.of_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.of_stuck

/-- info: 'IxCC.Sem.Result.Refines.of_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.of_timeout

/-- info: 'IxCC.Sem.Result.Refines.of_trap' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.of_trap

/-- info: 'IxCC.Sem.Result.Refines.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.refl

/-- info: 'IxCC.Sem.Result.Refines.timeout_iff' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.timeout_iff

/-- info: 'IxCC.Sem.Result.Refines.toBehaviour' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.toBehaviour

/-- info: 'IxCC.Sem.Result.Refines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.Refines.trans

/-- info: 'IxCC.Sem.Result.goesWrong_stuck' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.goesWrong_stuck

/-- info: 'IxCC.Sem.Result.goesWrong_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.goesWrong_trap

/-- info: 'IxCC.Sem.Result.not_goesWrong_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.not_goesWrong_ok

/-- info: 'IxCC.Sem.Result.not_goesWrong_resource' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.not_goesWrong_resource

/-- info: 'IxCC.Sem.Result.not_goesWrong_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.not_goesWrong_timeout

/-- info: 'IxCC.Sem.Result.toBehaviour_eq_diverges' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_eq_diverges

/-- info: 'IxCC.Sem.Result.toBehaviour_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_injective

/-- info: 'IxCC.Sem.Result.toBehaviour_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_ok

/-- info: 'IxCC.Sem.Result.toBehaviour_resource' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_resource

/-- info: 'IxCC.Sem.Result.toBehaviour_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_stuck

/-- info: 'IxCC.Sem.Result.toBehaviour_timeout' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_timeout

/-- info: 'IxCC.Sem.Result.toBehaviour_trap' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Result.toBehaviour_trap

/-- info: 'IxCC.Sem.Runs.clockMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Runs.clockMono

/-- info: 'IxCC.Sem.Runs.eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Runs.eq

/-- info: 'IxCC.Sem.Runs.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Runs.unique

/-- info: 'IxCC.Sem.Sim.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Sim.backward

/-- info: 'IxCC.Sem.Sim.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Sim.comp

/-- info: 'IxCC.Sem.Sim.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Sim.mono

/-- info: 'IxCC.Sem.Sim.ofStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Sim.ofStar

/-- info: 'IxCC.Sem.Sim.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Sim.refines

/-- info: 'IxCC.Sem.Sim.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Sim.refl

/-- info: 'IxCC.Sem.Sim.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Sim.safe

/-- info: 'IxCC.Sem.Sim.safe_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Sim.safe_all

/-- info: 'IxCC.Sem.Star.head' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Star.head

/-- info: 'IxCC.Sem.Star.map' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Star.map

/-- info: 'IxCC.Sem.Star.single' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Star.single

/-- info: 'IxCC.Sem.Star.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Star.trans

/-- info: 'IxCC.Sem.Transform.comp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Transform.comp_correct

/-- info: 'IxCC.Sem.Transform.comp_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Transform.comp_run

/-- info: 'IxCC.Sem.Transform.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Transform.compile_correct

/-- info: 'IxCC.Sem.behaviour_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_congr

/-- info: 'IxCC.Sem.behaviour_eq_diverges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_eq_diverges_iff

/-- info: 'IxCC.Sem.behaviour_eq_iff_of_ne_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_eq_iff_of_ne_diverges

/-- info: 'IxCC.Sem.behaviour_eq_resource_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_eq_resource_iff

/-- info: 'IxCC.Sem.behaviour_eq_stuck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_eq_stuck_iff

/-- info: 'IxCC.Sem.behaviour_eq_terminates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_eq_terminates_iff

/-- info: 'IxCC.Sem.behaviour_eq_trap_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_eq_trap_iff

/-- info: 'IxCC.Sem.behaviour_of_forall_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_of_forall_timeout

/-- info: 'IxCC.Sem.behaviour_of_ne_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.behaviour_of_ne_timeout

/-- info: 'IxCC.Sem.runClocked_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.runClocked_complete

/-- info: 'IxCC.Sem.runClocked_fuel_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.runClocked_fuel_mono

/-- info: 'IxCC.Sem.runClocked_sound' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.runClocked_sound

/-- info: 'IxCC.Sem.runClocked_timeout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.runClocked_timeout

/-! The toy pipeline (`IxCCTests.Sem.Toy`). -/

/-- info: 'IxCCTests.Sem.Toy.Big.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Big.run_mono

/-- info: 'IxCCTests.Sem.Toy.Tick.eval_dom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Tick.eval_dom

/-- info: 'IxCCTests.Sem.Toy.Tick.eval_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Tick.eval_agree

/-- info: 'IxCCTests.Sem.Toy.Tick.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Tick.sim

/-- info: 'IxCCTests.Sem.Toy.Stack.potential_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Stack.potential_ok

/-- info: 'IxCCTests.Sem.Toy.Stack.run_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Stack.run_runs

/-- info: 'IxCCTests.Sem.Toy.Stack.eval_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Stack.eval_fwd

/-- info: 'IxCCTests.Sem.Toy.Stack.eval_timeout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Stack.eval_timeout

/-- info: 'IxCCTests.Sem.Toy.Stack.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Stack.sim

/-- info: 'IxCCTests.Sem.Toy.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.pipeline_correct

/-- info: 'IxCCTests.Sem.Toy.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.compile_sound

/-- info: 'IxCCTests.Sem.Toy.compile_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.compile_safe

/-- info: 'IxCCTests.Sem.Toy.compile_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.compile_diverges

/-- info: 'IxCCTests.Sem.Toy.Cases.loop_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Sem.Toy.Cases.loop_target
