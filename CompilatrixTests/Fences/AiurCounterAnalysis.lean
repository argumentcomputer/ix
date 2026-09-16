import CompilatrixTests.Aiur.CounterAnalysis.Proofs

/-! Exact axiom cones for the universal pinned-analyzer proof and its
kernel regressions. All use the existing ordinary logical basis. -/

/-- info: 'Compilatrix.Aiur.CounterAnalysis.add_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.add_assoc

/-- info: 'Compilatrix.Aiur.CounterAnalysis.mul_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.mul_one

/-- info: 'Compilatrix.Aiur.CounterAnalysis.one_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.one_mul

/-- info: 'Compilatrix.Aiur.CounterAnalysis.sub_eq_add_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.sub_eq_add_neg

/-- info: 'Compilatrix.Aiur.CounterAnalysis.add_sub_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.add_sub_assoc

/-- info: 'Compilatrix.Aiur.CounterAnalysis.affine_beq_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.affine_beq_eq

/-- info: 'Compilatrix.Aiur.CounterAnalysis.add_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.add_sound

/-- info: 'Compilatrix.Aiur.CounterAnalysis.sub_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.sub_sound

/-- info: 'Compilatrix.Aiur.CounterAnalysis.mul_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.mul_sound

/-- info: 'Compilatrix.Aiur.CounterAnalysis.Registers.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.Registers.initial

/-- info: 'Compilatrix.Aiur.CounterAnalysis.Registers.marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.Registers.marker

/-- info: 'Compilatrix.Aiur.CounterAnalysis.evalOp_effect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.evalOp_effect

/-- info: 'Compilatrix.Aiur.CounterAnalysis.Invariant.inputCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.Invariant.inputCall

/-- info: 'Compilatrix.Aiur.CounterAnalysis.Invariant.outputCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.Invariant.outputCall

/-- info: 'Compilatrix.Aiur.CounterAnalysis.stepOp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.stepOp_sound

/-- info: 'Compilatrix.Aiur.CounterAnalysis.check_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.check_accepted

/-- info: 'Compilatrix.Aiur.CounterAnalysis.selectBranch_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.selectBranch_checked

/-- info: 'Compilatrix.Aiur.CounterAnalysis.return_relation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.return_relation

/-- info: 'Compilatrix.Aiur.CounterAnalysis.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.run_sound

/-- info: 'Compilatrix.Aiur.CounterAnalysis.check_runFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.check_runFunction

/-- info: 'Compilatrix.Aiur.CounterAnalysis.check_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.check_body

/-- info: 'Compilatrix.Aiur.CounterAnalysis.forIn_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.forIn_invariant

/-- info: 'Compilatrix.Aiur.CounterAnalysis.forIn_range_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.forIn_range_invariant

/-- info: 'Compilatrix.Aiur.CounterAnalysis.find_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.find_spec

/-- info: 'Compilatrix.Aiur.CounterAnalysis.find_runFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.find_runFunction

/-- info: 'Compilatrix.Aiur.CounterAnalysis.find_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.find_body

/-- info: 'Compilatrix.Aiur.CounterAnalysis.find_body_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.find_body_normalized

/-- info: 'Compilatrix.Aiur.CounterAnalysis.find_body_counter_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.find_body_counter_ne

/-- info: 'Compilatrix.Aiur.CounterAnalysis.find_body_no_short_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.CounterAnalysis.find_body_no_short_cycle

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.input_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.input_increment

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.input_decrement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.input_decrement

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.output_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.output_increment

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.output_decrement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.output_decrement

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.algebra_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.algebra_found

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.algebra_all_self_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.algebra_all_self_calls

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.marker_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.marker_found

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.marker_all_self_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.marker_all_self_calls

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.short_leaf_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.short_leaf_found

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.short_leaf_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.short_leaf_body

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.hints_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.hints_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.nonlinear_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.nonlinear_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.repeated_outputs_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.repeated_outputs_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.missing_argument_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.missing_argument_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.missing_register_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.missing_register_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.no_outputs_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.no_outputs_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.bad_branch_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.bad_branch_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.yield_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.yield_rejected

/-- info: 'CompilatrixTests.Aiur.CounterAnalysis.continuation_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.CounterAnalysis.continuation_rejected
