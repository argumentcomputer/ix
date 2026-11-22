import IxCC.Rt.Rc.Proof.CountHeap

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.HeapLive.update_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.HeapLive.update_count

/-- info: 'IxCC.Rt.Rc.Procs.count_live_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.count_live_iff
