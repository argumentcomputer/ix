import Compilatrix.Ixon.V3.Resource.StateProofs
import Compilatrix.Ixon.V3.Source

/-! Contract/state fences retain ordinary logic. The addressed input equations
retain the already ledgered BLAKE3 compiler boundary. -/

/-- info: 'Compilatrix.Ixon.V3.Locality.ofBits?_toBits' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Locality.ofBits?_toBits

/-- info: 'Compilatrix.Ixon.V3.ValueContract.ofBits?_toBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValueContract.ofBits?_toBits

/-- info: 'Compilatrix.Ixon.V3.BinderContract.ofBits?_toBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.BinderContract.ofBits?_toBits

/-- info: 'Compilatrix.Ixon.V3.unpackAllContract?_packAllContract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.unpackAllContract?_packAllContract

/-- info: 'Compilatrix.Ixon.V3.LetContract.ofFlags?_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.LetContract.ofFlags?_flags

/-- info: 'Compilatrix.Ixon.Uses.covers_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Uses.covers_sound

/-- info: 'Compilatrix.Ixon.Uses.join_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Uses.join_left

/-- info: 'Compilatrix.Ixon.Uses.join_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Uses.join_right

/-- info: 'Compilatrix.Ixon.Uses.add_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Uses.add_sound

/-- info: 'Compilatrix.Ixon.Uses.mul_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Uses.mul_sound

/-- info: 'Compilatrix.Ixon.V3.Resource.root_scopeTree' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.root_scopeTree

/-- info: 'Compilatrix.Ixon.V3.Resource.push_scopeTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.push_scopeTree

/-- info: 'Compilatrix.Ixon.V3.Resource.ancestor_older' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.ancestor_older

/-- info: 'Compilatrix.Ixon.V3.Resource.outlivesAux_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.outlivesAux_sound

/-- info: 'Compilatrix.Ixon.V3.Resource.outlives_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.outlives_sound

/-- info: 'Compilatrix.Ixon.V3.Resource.fresh_scope_cannot_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.fresh_scope_cannot_escape

/-- info: 'Compilatrix.Ixon.V3.Resource.checkOrigins_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.checkOrigins_sound

/-- info: 'Compilatrix.Ixon.V3.Resource.endLoan_live' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.endLoan_live

/-- info: 'Compilatrix.Ixon.V3.Resource.endLoan_unique' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.endLoan_unique

/-- info: 'Compilatrix.Ixon.V3.Resource.moveOwner_requires' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.moveOwner_requires

/-- info: 'Compilatrix.Ixon.V3.Resource.shareOwner_permanent' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.shareOwner_permanent

/-- info: 'Compilatrix.Ixon.V3.Resource.checkUnrestricted_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.checkUnrestricted_sound

/-- info: 'Compilatrix.Ixon.V3.Resource.joinOwner_live' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.joinOwner_live

/-- info: 'Compilatrix.Ixon.V3.Resource.joinOwner_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.joinOwner_unique

/-- info: 'Compilatrix.Ixon.V3.Resource.checkDemand_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.Resource.checkDemand_sound

/-- info: 'Compilatrix.Ixon.V3.ResourceInput.resources_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ResourceInput.resources_checked

/-- info: 'Compilatrix.Ixon.V3.ResourceInput.source_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ResourceInput.source_decoded
