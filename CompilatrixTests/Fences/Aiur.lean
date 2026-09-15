import Compilatrix.Aiur
import Ix.Aiur.Compiler.CallOrder
import CompilatrixTests.Aiur.Proofs

/-! Exact axiom sets for the initial Aiur trace boundary and pinned reference lemmas. -/

/-- info: 'Compilatrix.Aiur.Field.ext' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Aiur.Field.ext

/-- info: 'Compilatrix.Aiur.Field.zero_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Field.zero_add

/-- info: 'Compilatrix.Aiur.Field.ofNat_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Field.ofNat_ne_zero

/-- info: 'Compilatrix.Aiur.Trace.rows_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.rows_lt

/-- info: 'Compilatrix.Aiur.Trace.provider_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.provider_exists

/-- info: 'Compilatrix.Aiur.Memory.heap_of_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Memory.heap_of_mem

/-- info: 'Compilatrix.Aiur.Memory.row_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Memory.row_agrees

/-- info: 'Compilatrix.Aiur.Memory.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Memory.check_sound

/-- info: 'Compilatrix.Aiur.Trace.checkActivity_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.checkActivity_sound

/-- info: 'Compilatrix.Aiur.Trace.checkBalance_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.checkBalance_sound

/-- info: 'Compilatrix.Aiur.Trace.validate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.validate

/-- info: 'Compilatrix.Aiur.Finite.exists_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Finite.exists_repeat

/-- info: 'Compilatrix.Aiur.Finite.wellFounded_of_noChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Finite.wellFounded_of_noChain

/-- info: 'Compilatrix.Aiur.Finite.wellFounded_of_noShortCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Finite.wellFounded_of_noShortCycle

/-- info: 'Compilatrix.Aiur.StaticCertificate.noShortCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.StaticCertificate.noShortCycle

/-- info: 'Compilatrix.Aiur.StaticCertificate.wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.StaticCertificate.wellFounded

/-- info: 'Compilatrix.Aiur.Trace.static_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.static_wellFounded

/-- info: 'Compilatrix.Aiur.Trace.row_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.row_derivation

/-- info: 'Compilatrix.Aiur.Trace.public_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.public_derivation

/-- info: 'Compilatrix.Aiur.Trace.Derivation.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.Derivation.sound

/-- info: 'Compilatrix.Aiur.Trace.Validated.public_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.Validated.public_derivation

/-- info: 'Compilatrix.Aiur.Trace.Validated.memory_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Trace.Validated.memory_agrees

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

/-- info: 'CompilatrixTests.Aiur.mixed_derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.mixed_derives

/-- info: 'CompilatrixTests.Aiur.memory_at_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.memory_at_seven

/-- info: 'CompilatrixTests.Aiur.selfCall_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.selfCall_no_static

/-- info: 'CompilatrixTests.Aiur.mutualCall_no_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.mutualCall_no_static
