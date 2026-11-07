import IxCC.Aiur.OracleEval.MachineProofs
import IxCCTests.Aiur.Execution.Proofs

/-! Exact axiom sets for witness-heap execution. Every new cone uses only
ordinary logic; no native reflection or new trusted interface is admitted. -/

/-- info: 'IxCC.Aiur.OracleEval.Gadget.ofTag_tag' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.Gadget.ofTag_tag

/-- info: 'IxCC.Aiur.OracleEval.Gadget.check_message' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.Gadget.check_message

/-- info: 'IxCC.Aiur.OracleEval.two32_mul_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.two32_mul_inv

/-- info: 'IxCC.Aiur.OracleEval.run_add_fuel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.run_add_fuel

/-- info: 'IxCC.Aiur.OracleEval.runFunction_add_fuel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.runFunction_add_fuel

/-- info: 'IxCC.Aiur.OracleEval.adviceAllowed_unrestricted' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.adviceAllowed_unrestricted

/-- info: 'IxCC.Aiur.OracleEval.adviceAllowed_mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.adviceAllowed_mono

/-- info: 'IxCC.Aiur.OracleEval.check' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.check

/-- info: 'IxCC.Aiur.OracleEval.checkRow_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.checkRow_sound

/-- info: 'IxCC.Aiur.OracleEval.checkRows_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.checkRows_sound

/-- info: 'IxCC.Aiur.OracleEval.validateRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.validateRows

/-- info: 'IxCC.Aiur.OracleEval.Checked.sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.Checked.sound

/-- info: 'IxCC.Aiur.MessageEval.memory_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.MessageEval.memory_iff

/-- info: 'IxCC.Aiur.MessageEval.gadget_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.MessageEval.gadget_iff

/-- info: 'IxCC.Aiur.BytecodeEvalW.body' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.BytecodeEvalW.body

/-- info: 'IxCC.Aiur.MessageEval.advice_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.MessageEval.advice_mono

/-- info: 'IxCC.Aiur.MessageEval.heap_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.MessageEval.heap_congr

/-- info: 'IxCC.Aiur.Trace.Derivation.bytecode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.Derivation.bytecode

/-- info: 'IxCC.Aiur.Trace.Validated.public_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.Validated.public_bytecode

/-- info: 'IxCC.Aiur.OracleEval.CheckedRows.public_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.OracleEval.CheckedRows.public_bytecode

/-- info: 'IxCCTests.Aiur.Execution.counter_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.counter_exec

/-- info: 'IxCCTests.Aiur.Execution.ranked_mutual_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.ranked_mutual_exec

/-- info: 'IxCCTests.Aiur.Execution.store_at_seven_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.store_at_seven_exec

/-- info: 'IxCCTests.Aiur.Execution.load_without_store_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.load_without_store_exec

/-- info: 'IxCCTests.Aiur.Execution.self_pointer_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.self_pointer_exec

/-- info: 'IxCCTests.Aiur.Execution.distinct_store_pointers_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.distinct_store_pointers_exec

/-- info: 'IxCCTests.Aiur.Execution.gadget_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.gadget_exec

/-- info: 'IxCCTests.Aiur.Execution.constrained_call_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.constrained_call_exec

/-- info: 'IxCCTests.Aiur.Execution.unconstrained_call_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.unconstrained_call_exec

/-- info: 'IxCCTests.Aiur.Execution.repeated_advice_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.repeated_advice_exec

/-- info: 'IxCCTests.Aiur.Execution.continuation_scope_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.continuation_scope_body

/-- info: 'IxCCTests.Aiur.Execution.nested_return_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.nested_return_body

/-- info: 'IxCCTests.Aiur.Execution.continuation_scope_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.continuation_scope_exec

/-- info: 'IxCCTests.Aiur.Execution.nested_return_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.nested_return_exec

/-- info: 'IxCCTests.Aiur.Execution.self_loop_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.self_loop_rows

/-- info: 'IxCCTests.Aiur.Execution.self_loop_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.self_loop_no_static

/-- info: 'IxCCTests.Aiur.Execution.mutual_loop_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.mutual_loop_rows

/-- info: 'IxCCTests.Aiur.Execution.mutual_loop_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.mutual_loop_no_static

/-- info: 'IxCCTests.Aiur.Execution.false_gadget_has_no_meaning' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCCTests.Aiur.Execution.false_gadget_has_no_meaning
