import Compilatrix.Rt.Readback

/-! Required axiom fences for the Phase 1 runtime (M1.F6): the word and
header encodings (immediates are odd and halve back, the immortal header's
scan and tag fields decode, the first object is aligned past the context
block) and the readback of immediates and cells. `Rt.lower_correct` and
`Rt.readback_sound` (M2.5) will join them. Expected messages are preserved
verbatim. -/

/-- info: 'Compilatrix.Rt.natWord_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.natWord_toNat

/-- info: 'Compilatrix.Rt.ctor0Word_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.ctor0Word_toNat

/-- info: 'Compilatrix.Rt.odd_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.odd_word

/-- info: 'Compilatrix.Rt.immortalHeader_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.immortalHeader_toNat

/-- info: 'Compilatrix.Rt.immortalHeader_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.immortalHeader_scan

/-- info: 'Compilatrix.Rt.immortalHeader_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.immortalHeader_tag

/-- info: 'Compilatrix.Rt.objectsStart_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.objectsStart_aligned

/-- info: 'Compilatrix.Rt.objectsStart_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.objectsStart_bounds

/-- info: 'Compilatrix.Rt.readback_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.readback_nat

/-- info: 'Compilatrix.Rt.readback_ctor0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.readback_ctor0

/-- info: 'Compilatrix.Rt.readback_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.readback_cell
