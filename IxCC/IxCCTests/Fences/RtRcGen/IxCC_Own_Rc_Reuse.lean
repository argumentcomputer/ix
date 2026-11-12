import IxCC.Own.Rc.Reuse

/-! Exact axiom inventory of the general-layout heap: in-place reuse. -/

/-- info: 'IxCC.Own.Rc.reuseCell_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuseCell_some

/-- info: 'IxCC.Own.Rc.reuseCell_of_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuseCell_of_some

/-- info: 'IxCC.Own.Rc.reusedHeap_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reusedHeap_size

/-- info: 'IxCC.Own.Rc.reusedHeap_new' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reusedHeap_new

/-- info: 'IxCC.Own.Rc.reusedHeap_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reusedHeap_cell

/-- info: 'IxCC.Own.Rc.refsIn_fields_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.refsIn_fields_le

/-- info: 'IxCC.Own.Rc.lt_size_of_dynCount' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.lt_size_of_dynCount

/-- info: 'IxCC.Own.Rc.refsIn_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.refsIn_eq_zero

/-- info: 'IxCC.Own.Rc.reuse_exclusive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuse_exclusive

/-- info: 'IxCC.Own.Rc.reuse_mass_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuse_mass_avoid

/-- info: 'IxCC.Own.Rc.reuse_mass_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuse_mass_live

/-- info: 'IxCC.Own.Rc.reuseCell_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuseCell_balance

/-- info: 'IxCC.Own.Rc.reuseCell_heapOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuseCell_heapOk

/-- info: 'IxCC.Own.Rc.toFir_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.toFir_alloc

/-- info: 'IxCC.Own.Rc.toFir_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.toFir_stable

/-- info: 'IxCC.Own.Rc.toFirList_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.toFirList_mapM

/-- info: 'IxCC.Own.Rc.reuseCell_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.reuseCell_readback
