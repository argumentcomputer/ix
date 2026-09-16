import Compilatrix.Ixon.V3.Validate

/-! Combined admission retains the existing logical and BLAKE3 axiom basis. -/

/-- info: 'Compilatrix.Ixon.V3.literalPinAllowed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.literalPinAllowed_sound

/-- info: 'Compilatrix.Ixon.V3.checkLiteralProfile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.checkLiteralProfile_sound

/-- info: 'Compilatrix.Ixon.V3.ValidatedInput.typing_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValidatedInput.typing_checked

/-- info: 'Compilatrix.Ixon.V3.ValidatedInput.literal_profile_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValidatedInput.literal_profile_checked

/-- info: 'Compilatrix.Ixon.V3.ValidatedInput.resources_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValidatedInput.resources_checked

/-- info: 'Compilatrix.Ixon.V3.ValidatedInput.source_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValidatedInput.source_decoded

/-- info: 'Compilatrix.Ixon.V3.ValidatedInput.profile_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValidatedInput.profile_decoded

/-- info: 'Compilatrix.Ixon.V3.ValidatedInput.literal_types' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.V3.ValidatedInput.literal_types
