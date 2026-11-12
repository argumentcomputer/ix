import IxCC.Rt.Rc.Gen.Proof.DetachHeap

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.HeapLive.detach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.HeapLive.detach

/-- info: 'IxCC.Rt.Rc.Gen.HeapLive.kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.HeapLive.kill
