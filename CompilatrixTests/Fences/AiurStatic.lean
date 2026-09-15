import Compilatrix.Aiur.Static.CounterProofs
import Compilatrix.Aiur.Static.OrderProofs
import CompilatrixTests.Aiur.Static.Proofs

/-! Exact static-assignment cones. The addressed ingress adapter inherits
only the existing native BLAKE3 exception; all other cones use ordinary logic. -/

/-- info: 'Compilatrix.Aiur.Static.Program.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.Program.accepted

/-- info: 'Compilatrix.Aiur.Static.prepareChecked_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.prepareChecked_ok

/-- info: 'Compilatrix.Aiur.Static.checkDependencies_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.checkDependencies_sound

/-- info: 'Compilatrix.Aiur.Static.Assignment.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.Assignment.certificate

/-- info: 'Compilatrix.Aiur.Static.Assignment.wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.Assignment.wellFounded

/-- info: 'Compilatrix.Aiur.Static.CheckedTrace.public_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.CheckedTrace.public_message

/-- info: 'Compilatrix.Aiur.Static.CheckedTrace.public_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.CheckedTrace.public_bytecode

/-- info: 'Compilatrix.Aiur.Static.CheckedTrace.wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.CheckedTrace.wellFounded

/-- info: 'Compilatrix.Aiur.Static.CheckedTrace.noShortCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.CheckedTrace.noShortCycle

/-- info: 'Compilatrix.Aiur.Static.neg_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.neg_add_one

/-- info: 'Compilatrix.Aiur.Static.neg_sub_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.neg_sub_one

/-- info: 'Compilatrix.Aiur.Static.normalizeCounter_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.normalizeCounter_step

/-- info: 'Compilatrix.Aiur.Static.normalizedCounter_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.normalizedCounter_step

/-- info: 'Compilatrix.Aiur.Static.FunctionPlan.order_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.FunctionPlan.order_positive

/-- info: 'Compilatrix.Aiur.Static.FunctionPlan.ranked_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.FunctionPlan.ranked_order

/-- info: 'Compilatrix.Aiur.Static.FunctionPlan.order_lt_of_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.FunctionPlan.order_lt_of_component

/-- info: 'Compilatrix.Aiur.Static.FunctionPlan.order_lt_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.FunctionPlan.order_lt_leaf

/-- info: 'Compilatrix.Aiur.Static.FunctionPlan.same_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.FunctionPlan.same_order

/-- info: 'Compilatrix.Aiur.Static.checkAssignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.checkAssignment

/-- info: 'Compilatrix.Aiur.Static.prepareChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.prepareChecked

/-- info: 'Compilatrix.Aiur.Static.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.prepare

/-- info: 'Compilatrix.Aiur.Static.validatePrepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.validatePrepared

/-- info: 'Compilatrix.Aiur.Static.validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Static.validate

/-- info: 'Compilatrix.Aiur.Wire.Ingress.validateTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Ingress.validateTrace

/-- info: 'CompilatrixTests.Aiur.Static.input_decrement_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.input_decrement_exec

/-- info: 'CompilatrixTests.Aiur.Static.input_increment_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.input_increment_exec

/-- info: 'CompilatrixTests.Aiur.Static.output_increment_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.output_increment_exec

/-- info: 'CompilatrixTests.Aiur.Static.output_decrement_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.output_decrement_exec

/-- info: 'CompilatrixTests.Aiur.Static.mixed_ranked_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.mixed_ranked_exec

/-- info: 'CompilatrixTests.Aiur.Static.mixed_counter_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.mixed_counter_exec

/-- info: 'CompilatrixTests.Aiur.Static.duplicate_providers_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.duplicate_providers_exec

/-- info: 'CompilatrixTests.Aiur.Static.zero_weight_parent_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.zero_weight_parent_exec

/-- info: 'CompilatrixTests.Aiur.Static.ranked_mutual_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.ranked_mutual_exec

/-- info: 'CompilatrixTests.Aiur.Static.ordered_call_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.ordered_call_exec

/-- info: 'CompilatrixTests.Aiur.Static.pointer_seven_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.pointer_seven_exec

/-- info: 'CompilatrixTests.Aiur.Static.self_loop_no_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.self_loop_no_checked

/-- info: 'CompilatrixTests.Aiur.Static.mutual_loop_no_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.mutual_loop_no_checked

/-- info: 'CompilatrixTests.Aiur.Static.self_loop_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.self_loop_rejected

/-- info: 'CompilatrixTests.Aiur.Static.mutual_loop_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Static.mutual_loop_rejected
