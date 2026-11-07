import IxCCTests.Aiur.CounterAnalysis.Proofs

/-! Exact axiom cones for the universal pinned-analyzer proof and its
kernel regressions. All use the existing ordinary logical basis. -/

/-- info: 'IxCC.Aiur.CounterAnalysis.add_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.add_assoc

/-- info: 'IxCC.Aiur.CounterAnalysis.mul_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.mul_one

/-- info: 'IxCC.Aiur.CounterAnalysis.one_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.one_mul

/-- info: 'IxCC.Aiur.CounterAnalysis.sub_eq_add_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.sub_eq_add_neg

/-- info: 'IxCC.Aiur.CounterAnalysis.add_sub_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.add_sub_assoc

/-- info: 'IxCC.Aiur.CounterAnalysis.affine_beq_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.affine_beq_eq

/-- info: 'IxCC.Aiur.CounterAnalysis.add_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.add_sound

/-- info: 'IxCC.Aiur.CounterAnalysis.sub_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.sub_sound

/-- info: 'IxCC.Aiur.CounterAnalysis.mul_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.mul_sound

/-- info: 'IxCC.Aiur.CounterAnalysis.Registers.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.Registers.initial

/-- info: 'IxCC.Aiur.CounterAnalysis.Registers.marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.Registers.marker

/-- info: 'IxCC.Aiur.CounterAnalysis.evalOp_effect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.evalOp_effect

/-- info: 'IxCC.Aiur.CounterAnalysis.Invariant.inputCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.Invariant.inputCall

/-- info: 'IxCC.Aiur.CounterAnalysis.Invariant.outputCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.Invariant.outputCall

/-- info: 'IxCC.Aiur.CounterAnalysis.stepOp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.stepOp_sound

/-- info: 'IxCC.Aiur.CounterAnalysis.check_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.check_accepted

/-- info: 'IxCC.Aiur.CounterAnalysis.selectBranch_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.selectBranch_checked

/-- info: 'IxCC.Aiur.CounterAnalysis.return_relation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.return_relation

/-- info: 'IxCC.Aiur.CounterAnalysis.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.run_sound

/-- info: 'IxCC.Aiur.CounterAnalysis.check_runFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.check_runFunction

/-- info: 'IxCC.Aiur.CounterAnalysis.check_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.check_body

/-- info: 'IxCC.Aiur.CounterAnalysis.forIn_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.forIn_invariant

/-- info: 'IxCC.Aiur.CounterAnalysis.forIn_range_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.forIn_range_invariant

/-- info: 'IxCC.Aiur.CounterAnalysis.find_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.find_spec

/-- info: 'IxCC.Aiur.CounterAnalysis.find_runFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.find_runFunction

/-- info: 'IxCC.Aiur.CounterAnalysis.find_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.find_body

/-- info: 'IxCC.Aiur.CounterAnalysis.find_body_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.find_body_normalized

/-- info: 'IxCC.Aiur.CounterAnalysis.find_body_counter_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.find_body_counter_ne

/-- info: 'IxCC.Aiur.CounterAnalysis.find_body_no_short_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.CounterAnalysis.find_body_no_short_cycle

/-- info: 'IxCCTests.Aiur.CounterAnalysis.input_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.input_increment

/-- info: 'IxCCTests.Aiur.CounterAnalysis.input_decrement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.input_decrement

/-- info: 'IxCCTests.Aiur.CounterAnalysis.output_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.output_increment

/-- info: 'IxCCTests.Aiur.CounterAnalysis.output_decrement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.output_decrement

/-- info: 'IxCCTests.Aiur.CounterAnalysis.algebra_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.algebra_found

/-- info: 'IxCCTests.Aiur.CounterAnalysis.algebra_all_self_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.algebra_all_self_calls

/-- info: 'IxCCTests.Aiur.CounterAnalysis.marker_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.marker_found

/-- info: 'IxCCTests.Aiur.CounterAnalysis.marker_all_self_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.marker_all_self_calls

/-- info: 'IxCCTests.Aiur.CounterAnalysis.short_leaf_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.short_leaf_found

/-- info: 'IxCCTests.Aiur.CounterAnalysis.short_leaf_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.short_leaf_body

/-- info: 'IxCCTests.Aiur.CounterAnalysis.hints_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.hints_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.nonlinear_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.nonlinear_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.repeated_outputs_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.repeated_outputs_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.missing_argument_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.missing_argument_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.missing_register_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.missing_register_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.no_outputs_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.no_outputs_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.bad_branch_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.bad_branch_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.yield_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.yield_rejected

/-- info: 'IxCCTests.Aiur.CounterAnalysis.continuation_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.CounterAnalysis.continuation_rejected
