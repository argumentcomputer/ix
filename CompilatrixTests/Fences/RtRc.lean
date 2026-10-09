import Compilatrix.Rt.Rc.Readback

/-! Exact fences for dynamic header encoding and constructor observation.
These preserve the Phase 1 fences and do not certify reclamation by themselves. -/

/-- info: 'Compilatrix.Rt.Rc.header_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.header_toNat

/-- info: 'Compilatrix.Rt.Rc.header_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.header_scan

/-- info: 'Compilatrix.Rt.Rc.header_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.header_class

/-- info: 'Compilatrix.Rt.Rc.header_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.header_tag

/-- info: 'Compilatrix.Rt.Rc.header_rc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.header_rc

/-- info: 'Compilatrix.Rt.Rc.dynamicHeader_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.dynamicHeader_count

/-- info: 'Compilatrix.Rt.Rc.dynamicHeader_unique' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.dynamicHeader_unique

/-- info: 'Compilatrix.Rt.Rc.smallClass_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.smallClass_bounds

/-- info: 'Compilatrix.Rt.Rc.smallClass_bytes' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.smallClass_bytes

/-- info: 'Compilatrix.Rt.Rc.readback_cell_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.readback_cell_header
