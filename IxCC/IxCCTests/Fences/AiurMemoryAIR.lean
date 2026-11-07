import IxCCTests.Aiur.MemoryAIR.Proofs

/-! Exact axiom sets for memory AIR extraction and its kernel regressions.
No primality, native reflection, or new native interface is admitted. -/

/-- info: 'IxCC.Aiur.AIR.Circuit.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Circuit.check_sound

/-- info: 'IxCC.Aiur.AIR.Memory.mul_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.mul_one

/-- info: 'IxCC.Aiur.AIR.Memory.one_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.one_mul

/-- info: 'IxCC.Aiur.AIR.Memory.mul_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.mul_zero

/-- info: 'IxCC.Aiur.AIR.Memory.sub_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.sub_eq_zero

/-- info: 'IxCC.Aiur.AIR.Memory.satisfied_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.satisfied_iff

/-- info: 'IxCC.Aiur.AIR.Memory.selected_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.selected_predecessor

/-- info: 'IxCC.Aiur.AIR.Memory.row_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.row_activity

/-- info: 'IxCC.Aiur.AIR.Memory.Table.consecutive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.consecutive

/-- info: 'IxCC.Aiur.AIR.Memory.Table.selected_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.selected_prefix

/-- info: 'IxCC.Aiur.AIR.Memory.Table.pointer_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.pointer_ne

/-- info: 'IxCC.Aiur.AIR.Memory.Table.pointer_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.pointer_injective

/-- info: 'IxCC.Aiur.AIR.Memory.eval_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.eval_scale

/-- info: 'IxCC.Aiur.AIR.Memory.pull_weight' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.pull_weight

/-- info: 'IxCC.Aiur.AIR.Memory.pull_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.pull_arguments

/-- info: 'IxCC.Aiur.AIR.Memory.Table.row_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.row_mem

/-- info: 'IxCC.Aiur.AIR.Memory.Table.mem_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.mem_rows

/-- info: 'IxCC.Aiur.AIR.Memory.mem_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.mem_cells

/-- info: 'IxCC.Aiur.AIR.Memory.unique_bucket_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.unique_bucket_eq

/-- info: 'IxCC.Aiur.AIR.Memory.coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.coherent

/-- info: 'IxCC.Aiur.AIR.Memory.heap_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.heap_agrees

/-- info: 'IxCC.Aiur.AIR.Memory.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.activity

/-- info: 'IxCC.Aiur.AIR.Memory.Table.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Table.check_sound

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.unique

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.table

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.coherent

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.activity

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.heap_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.heap_agrees

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.row_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.row_shape

/-- info: 'IxCC.Aiur.AIR.Memory.Checked.message_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.AIR.Memory.Checked.message_eval

/-- info: 'IxCCTests.Aiur.MemoryAIR.arbitrary_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.arbitrary_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.wrapped_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.wrapped_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.signed_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.signed_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.self_pointer_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.self_pointer_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.repeated_contents_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.repeated_contents_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.distinct_buckets_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.distinct_buckets_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.zero_width_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.zero_width_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.padding_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.padding_checked

/-- info: 'IxCCTests.Aiur.MemoryAIR.duplicate_bucket_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.duplicate_bucket_rejected

/-- info: 'IxCCTests.Aiur.MemoryAIR.inactive_provider_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.inactive_provider_rejected

/-- info: 'IxCCTests.Aiur.MemoryAIR.invalid_selector_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.invalid_selector_rejected

/-- info: 'IxCCTests.Aiur.MemoryAIR.repeated_pointer_impossible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.repeated_pointer_impossible

/-- info: 'IxCCTests.Aiur.MemoryAIR.padding_restart_impossible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.padding_restart_impossible

/-- info: 'IxCCTests.Aiur.MemoryAIR.wrapped_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.wrapped_heap

/-- info: 'IxCCTests.Aiur.MemoryAIR.self_pointer_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.self_pointer_message

/-- info: 'IxCCTests.Aiur.MemoryAIR.signed_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.MemoryAIR.signed_activity
