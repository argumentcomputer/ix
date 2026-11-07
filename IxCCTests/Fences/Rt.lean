import IxCC.Rt.Readback

/-! Required axiom fences for the Phase 1 runtime (M1.F6): the word and
header encodings (immediates are odd and halve back, the immortal header's
scan and tag fields decode, the first object is aligned past the context
block) and the readback of immediates and cells. `Rt.lower_correct` and
`Rt.readback_sound` (M2.5) will join them. Expected messages are preserved
verbatim. -/

/-- info: 'IxCC.Rt.natWord_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.natWord_toNat

/-- info: 'IxCC.Rt.ctor0Word_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.ctor0Word_toNat

/-- info: 'IxCC.Rt.odd_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.odd_word

/-- info: 'IxCC.Rt.immortalHeader_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.immortalHeader_toNat

/-- info: 'IxCC.Rt.immortalHeader_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.immortalHeader_scan

/-- info: 'IxCC.Rt.immortalHeader_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.immortalHeader_tag

/-- info: 'IxCC.Rt.objectsStart_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.objectsStart_aligned

/-- info: 'IxCC.Rt.objectsStart_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.objectsStart_bounds

/-- info: 'IxCC.Rt.readback_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readback_nat

/-- info: 'IxCC.Rt.readback_ctor0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readback_ctor0

/-- info: 'IxCC.Rt.readback_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readback_cell
