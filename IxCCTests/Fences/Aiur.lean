import IxCC.Aiur
import IxCC.Vendor.Ix.Aiur.Compiler.CallOrder
import IxCCTests.Aiur.Proofs

/-! Exact axiom sets for the initial Aiur trace boundary and pinned reference lemmas. -/

/-- info: 'IxCC.Aiur.Field.ext' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Aiur.Field.ext

/-- info: 'IxCC.Aiur.Field.zero_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Field.zero_add

/-- info: 'IxCC.Aiur.Field.ofNat_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Field.ofNat_ne_zero

/-- info: 'IxCC.Aiur.Trace.rows_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.rows_lt

/-- info: 'IxCC.Aiur.Trace.provider_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.provider_exists

/-- info: 'IxCC.Aiur.Memory.heap_of_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Aiur.Memory.heap_of_mem

/-- info: 'IxCC.Aiur.Memory.row_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Memory.row_agrees

/-- info: 'IxCC.Aiur.Memory.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Memory.check_sound

/-- info: 'IxCC.Aiur.Trace.checkActivity_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.checkActivity_sound

/-- info: 'IxCC.Aiur.Trace.checkBalance_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.checkBalance_sound

/-- info: 'IxCC.Aiur.Trace.validate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.validate

/-- info: 'IxCC.Aiur.Finite.exists_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Finite.exists_repeat

/-- info: 'IxCC.Aiur.Finite.wellFounded_of_noChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Finite.wellFounded_of_noChain

/-- info: 'IxCC.Aiur.Finite.wellFounded_of_noShortCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Finite.wellFounded_of_noShortCycle

/-- info: 'IxCC.Aiur.StaticCertificate.noShortCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.StaticCertificate.noShortCycle

/-- info: 'IxCC.Aiur.StaticCertificate.wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.StaticCertificate.wellFounded

/-- info: 'IxCC.Aiur.Trace.static_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.static_wellFounded

/-- info: 'IxCC.Aiur.Trace.row_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.row_derivation

/-- info: 'IxCC.Aiur.Trace.public_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.public_derivation

/-- info: 'IxCC.Aiur.Trace.Derivation.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.Derivation.sound

/-- info: 'IxCC.Aiur.Trace.Validated.public_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.Validated.public_derivation

/-- info: 'IxCC.Aiur.Trace.Validated.memory_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Trace.Validated.memory_agrees

/-- info: 'Aiur.Bytecode.CallComponent.wellFounded_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.CallComponent.wellFounded_calls

/-- info: 'Aiur.Bytecode.UnitCounter.Proofs.no_short_unit_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.UnitCounter.Proofs.no_short_unit_cycle

/-- info: 'Aiur.Bytecode.UnitCounter.Proofs.no_short_reverse_unit_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.UnitCounter.Proofs.no_short_reverse_unit_cycle

/-- info: 'Aiur.Bytecode.UnitCounter.Proofs.no_short_field_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.UnitCounter.Proofs.no_short_field_cycle

/-- info: 'Aiur.Bytecode.UnitCounter.Proofs.no_short_reverse_field_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.UnitCounter.Proofs.no_short_reverse_field_cycle

/-- info: 'Aiur.Bytecode.UnitCounter.Proofs.no_short_decrement_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.UnitCounter.Proofs.no_short_decrement_cycle

/-- info: 'Aiur.Bytecode.UnitCounter.Proofs.no_short_negative_field_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aiur.Bytecode.UnitCounter.Proofs.no_short_negative_field_cycle

/-- info: 'IxCCTests.Aiur.mixed_derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.mixed_derives

/-- info: 'IxCCTests.Aiur.memory_at_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.memory_at_seven

/-- info: 'IxCCTests.Aiur.selfCall_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.selfCall_no_static

/-- info: 'IxCCTests.Aiur.mutualCall_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.mutualCall_no_static
