import IxCC.Rt.Rc.Gen.Proof.CountHeap

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.HeapLive.update_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.HeapLive.update_count

/-- info: 'IxCC.Rt.Rc.Gen.count_live_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.count_live_iff
