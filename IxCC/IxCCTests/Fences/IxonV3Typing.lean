import IxCC.Ixon.V3.Validate

/-! Combined admission retains the existing logical and BLAKE3 axiom basis. -/

/-- info: 'IxCC.Ixon.V3.literalPinAllowed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.literalPinAllowed_sound

/-- info: 'IxCC.Ixon.V3.checkLiteralProfile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.checkLiteralProfile_sound

/-- info: 'IxCC.Ixon.V3.ValidatedInput.typing_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.typing_checked

/-- info: 'IxCC.Ixon.V3.ValidatedInput.literal_profile_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.literal_profile_checked

/-- info: 'IxCC.Ixon.V3.ValidatedInput.resources_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.resources_checked

/-- info: 'IxCC.Ixon.V3.ValidatedInput.source_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.source_decoded

/-- info: 'IxCC.Ixon.V3.ValidatedInput.profile_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.profile_decoded

/-- info: 'IxCC.Ixon.V3.ValidatedInput.literal_types' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.literal_types
