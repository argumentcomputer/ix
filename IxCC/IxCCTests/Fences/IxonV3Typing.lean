import IxCC.Ixon.V3.Validate

/-! The resource-validation API (resource admission and the literal pins)
rests on the standard axioms (pure BLAKE3). -/

/-- info: 'IxCC.Ixon.V3.literalPinAllowed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.literalPinAllowed_sound

/-- info: 'IxCC.Ixon.V3.checkLiteralProfile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.checkLiteralProfile_sound

/-- info: 'IxCC.Ixon.V3.ValidatedInput.literal_profile_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.literal_profile_checked

/-- info: 'IxCC.Ixon.V3.ValidatedInput.resources_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.resources_checked

/-- info: 'IxCC.Ixon.V3.ValidatedInput.source_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.source_decoded

/-- info: 'IxCC.Ixon.V3.ValidatedInput.profile_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.profile_decoded

/-- info: 'IxCC.Ixon.V3.ValidatedInput.literal_types' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.ValidatedInput.literal_types
