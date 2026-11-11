import IxCC.Aiur.Static.CounterProofs
import IxCC.Aiur.Static.OrderProofs
import IxCCTests.Aiur.Static.Proofs

/-! Exact static-assignment cones, on ordinary logic (the addressed ingress
adapter's hash is pure BLAKE3). -/

/-- info: 'IxCC.Aiur.Static.Program.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.Program.accepted

/-- info: 'IxCC.Aiur.Static.prepareChecked_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.prepareChecked_ok

/-- info: 'IxCC.Aiur.Static.checkDependencies_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.checkDependencies_sound

/-- info: 'IxCC.Aiur.Static.Assignment.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.Assignment.certificate

/-- info: 'IxCC.Aiur.Static.Assignment.wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.Assignment.wellFounded

/-- info: 'IxCC.Aiur.Static.CheckedTrace.public_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.CheckedTrace.public_message

/-- info: 'IxCC.Aiur.Static.CheckedTrace.public_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.CheckedTrace.public_bytecode

/-- info: 'IxCC.Aiur.Static.CheckedTrace.wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.CheckedTrace.wellFounded

/-- info: 'IxCC.Aiur.Static.CheckedTrace.noShortCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.CheckedTrace.noShortCycle

/-- info: 'IxCC.Aiur.Static.neg_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.neg_add_one

/-- info: 'IxCC.Aiur.Static.neg_sub_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.neg_sub_one

/-- info: 'IxCC.Aiur.Static.normalizeCounter_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.normalizeCounter_step

/-- info: 'IxCC.Aiur.Static.normalizedCounter_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.normalizedCounter_step

/-- info: 'IxCC.Aiur.Static.FunctionPlan.order_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.FunctionPlan.order_positive

/-- info: 'IxCC.Aiur.Static.FunctionPlan.ranked_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.FunctionPlan.ranked_order

/-- info: 'IxCC.Aiur.Static.FunctionPlan.order_lt_of_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.FunctionPlan.order_lt_of_component

/-- info: 'IxCC.Aiur.Static.FunctionPlan.order_lt_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.FunctionPlan.order_lt_leaf

/-- info: 'IxCC.Aiur.Static.FunctionPlan.same_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.FunctionPlan.same_order

/-- info: 'IxCC.Aiur.Static.checkAssignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.checkAssignment

/-- info: 'IxCC.Aiur.Static.prepareChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.prepareChecked

/-- info: 'IxCC.Aiur.Static.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.prepare

/-- info: 'IxCC.Aiur.Static.validatePrepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.validatePrepared

/-- info: 'IxCC.Aiur.Static.validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Static.validate

/-- info: 'IxCC.Aiur.Wire.Ingress.validateTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Ingress.validateTrace

/-- info: 'IxCCTests.Aiur.Static.input_decrement_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.input_decrement_exec

/-- info: 'IxCCTests.Aiur.Static.input_increment_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.input_increment_exec

/-- info: 'IxCCTests.Aiur.Static.output_increment_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.output_increment_exec

/-- info: 'IxCCTests.Aiur.Static.output_decrement_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.output_decrement_exec

/-- info: 'IxCCTests.Aiur.Static.mixed_ranked_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.mixed_ranked_exec

/-- info: 'IxCCTests.Aiur.Static.mixed_counter_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.mixed_counter_exec

/-- info: 'IxCCTests.Aiur.Static.duplicate_providers_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.duplicate_providers_exec

/-- info: 'IxCCTests.Aiur.Static.zero_weight_parent_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.zero_weight_parent_exec

/-- info: 'IxCCTests.Aiur.Static.ranked_mutual_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.ranked_mutual_exec

/-- info: 'IxCCTests.Aiur.Static.ordered_call_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.ordered_call_exec

/-- info: 'IxCCTests.Aiur.Static.pointer_seven_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.pointer_seven_exec

/-- info: 'IxCCTests.Aiur.Static.self_loop_no_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.self_loop_no_checked

/-- info: 'IxCCTests.Aiur.Static.mutual_loop_no_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.mutual_loop_no_checked

/-- info: 'IxCCTests.Aiur.Static.self_loop_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.self_loop_rejected

/-- info: 'IxCCTests.Aiur.Static.mutual_loop_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Static.mutual_loop_rejected
