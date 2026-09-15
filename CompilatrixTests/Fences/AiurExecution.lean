import Compilatrix.Aiur.OracleEval.MachineProofs
import CompilatrixTests.Aiur.Execution.Proofs

/-! Exact axiom sets for witness-heap execution. Every new cone uses only
ordinary logic; no native reflection or new trusted interface is admitted. -/

/-- info: 'Compilatrix.Aiur.OracleEval.Gadget.ofTag_tag' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.Gadget.ofTag_tag

/-- info: 'Compilatrix.Aiur.OracleEval.Gadget.check_message' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.Gadget.check_message

/-- info: 'Compilatrix.Aiur.OracleEval.two32_mul_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.two32_mul_inv

/-- info: 'Compilatrix.Aiur.OracleEval.run_add_fuel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.run_add_fuel

/-- info: 'Compilatrix.Aiur.OracleEval.runFunction_add_fuel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.runFunction_add_fuel

/-- info: 'Compilatrix.Aiur.OracleEval.adviceAllowed_unrestricted' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.adviceAllowed_unrestricted

/-- info: 'Compilatrix.Aiur.OracleEval.adviceAllowed_mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.adviceAllowed_mono

/-- info: 'Compilatrix.Aiur.OracleEval.check' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.check

/-- info: 'Compilatrix.Aiur.OracleEval.checkRow_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.checkRow_sound

/-- info: 'Compilatrix.Aiur.OracleEval.checkRows_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.checkRows_sound

/-- info: 'Compilatrix.Aiur.OracleEval.validateRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.validateRows

/-- info: 'Compilatrix.Aiur.OracleEval.Checked.sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.Checked.sound

/-- info: 'Compilatrix.Aiur.MessageEval.memory_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.MessageEval.memory_iff

/-- info: 'Compilatrix.Aiur.MessageEval.gadget_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.MessageEval.gadget_iff

/-- info: 'Compilatrix.Aiur.BytecodeEvalW.body' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.BytecodeEvalW.body

/-- info: 'Compilatrix.Aiur.MessageEval.advice_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.MessageEval.advice_mono

/-- info: 'Compilatrix.Aiur.MessageEval.heap_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.MessageEval.heap_congr

/-- info: 'Compilatrix.Aiur.Trace.Derivation.bytecode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.Derivation.bytecode

/-- info: 'Compilatrix.Aiur.Trace.Validated.public_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.Validated.public_bytecode

/-- info: 'Compilatrix.Aiur.OracleEval.CheckedRows.public_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.OracleEval.CheckedRows.public_bytecode

/-- info: 'CompilatrixTests.Aiur.Execution.counter_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.counter_exec

/-- info: 'CompilatrixTests.Aiur.Execution.ranked_mutual_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.ranked_mutual_exec

/-- info: 'CompilatrixTests.Aiur.Execution.store_at_seven_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.store_at_seven_exec

/-- info: 'CompilatrixTests.Aiur.Execution.load_without_store_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.load_without_store_exec

/-- info: 'CompilatrixTests.Aiur.Execution.self_pointer_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.self_pointer_exec

/-- info: 'CompilatrixTests.Aiur.Execution.distinct_store_pointers_exec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.distinct_store_pointers_exec

/-- info: 'CompilatrixTests.Aiur.Execution.gadget_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.gadget_exec

/-- info: 'CompilatrixTests.Aiur.Execution.constrained_call_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.constrained_call_exec

/-- info: 'CompilatrixTests.Aiur.Execution.unconstrained_call_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.unconstrained_call_exec

/-- info: 'CompilatrixTests.Aiur.Execution.repeated_advice_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.repeated_advice_exec

/-- info: 'CompilatrixTests.Aiur.Execution.continuation_scope_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.continuation_scope_body

/-- info: 'CompilatrixTests.Aiur.Execution.nested_return_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.nested_return_body

/-- info: 'CompilatrixTests.Aiur.Execution.continuation_scope_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.continuation_scope_exec

/-- info: 'CompilatrixTests.Aiur.Execution.nested_return_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.nested_return_exec

/-- info: 'CompilatrixTests.Aiur.Execution.self_loop_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.self_loop_rows

/-- info: 'CompilatrixTests.Aiur.Execution.self_loop_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.self_loop_no_static

/-- info: 'CompilatrixTests.Aiur.Execution.mutual_loop_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.mutual_loop_rows

/-- info: 'CompilatrixTests.Aiur.Execution.mutual_loop_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.mutual_loop_no_static

/-- info: 'CompilatrixTests.Aiur.Execution.false_gadget_has_no_meaning' depends on axioms: [propext] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.Execution.false_gadget_has_no_meaning
