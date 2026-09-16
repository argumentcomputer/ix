import CompilatrixTests.Aiur.MemoryAIR.Proofs

/-! Exact axiom sets for memory AIR extraction and its kernel regressions.
No primality, native reflection, or new native interface is admitted. -/

/-- info: 'Compilatrix.Aiur.AIR.Circuit.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Circuit.check_sound

/-- info: 'Compilatrix.Aiur.AIR.Memory.mul_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.mul_one

/-- info: 'Compilatrix.Aiur.AIR.Memory.one_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.one_mul

/-- info: 'Compilatrix.Aiur.AIR.Memory.mul_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.mul_zero

/-- info: 'Compilatrix.Aiur.AIR.Memory.sub_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.sub_eq_zero

/-- info: 'Compilatrix.Aiur.AIR.Memory.satisfied_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.satisfied_iff

/-- info: 'Compilatrix.Aiur.AIR.Memory.selected_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.selected_predecessor

/-- info: 'Compilatrix.Aiur.AIR.Memory.row_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.row_activity

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.consecutive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.consecutive

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.selected_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.selected_prefix

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.pointer_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.pointer_ne

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.pointer_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.pointer_injective

/-- info: 'Compilatrix.Aiur.AIR.Memory.eval_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.eval_scale

/-- info: 'Compilatrix.Aiur.AIR.Memory.pull_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.pull_weight

/-- info: 'Compilatrix.Aiur.AIR.Memory.pull_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.pull_arguments

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.row_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.row_mem

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.mem_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.mem_rows

/-- info: 'Compilatrix.Aiur.AIR.Memory.mem_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.mem_cells

/-- info: 'Compilatrix.Aiur.AIR.Memory.unique_bucket_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.unique_bucket_eq

/-- info: 'Compilatrix.Aiur.AIR.Memory.coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.coherent

/-- info: 'Compilatrix.Aiur.AIR.Memory.heap_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.heap_agrees

/-- info: 'Compilatrix.Aiur.AIR.Memory.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.activity

/-- info: 'Compilatrix.Aiur.AIR.Memory.Table.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Table.check_sound

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.unique

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.table

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.coherent

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.activity

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.heap_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.heap_agrees

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.row_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.row_shape

/-- info: 'Compilatrix.Aiur.AIR.Memory.Checked.message_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.AIR.Memory.Checked.message_eval

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.arbitrary_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.arbitrary_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.wrapped_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.wrapped_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.signed_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.signed_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.self_pointer_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.self_pointer_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.repeated_contents_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.repeated_contents_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.distinct_buckets_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.distinct_buckets_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.zero_width_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.zero_width_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.padding_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.padding_checked

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.duplicate_bucket_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.duplicate_bucket_rejected

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.inactive_provider_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.inactive_provider_rejected

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.invalid_selector_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.invalid_selector_rejected

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.repeated_pointer_impossible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.repeated_pointer_impossible

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.padding_restart_impossible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.padding_restart_impossible

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.wrapped_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.wrapped_heap

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.self_pointer_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.self_pointer_message

/-- info: 'CompilatrixTests.Aiur.MemoryAIR.signed_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.MemoryAIR.signed_activity
