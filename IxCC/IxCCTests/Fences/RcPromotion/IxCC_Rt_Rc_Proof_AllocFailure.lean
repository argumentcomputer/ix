import IxCC.Rt.Rc.Proof.AllocFailure

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.reserve_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.reserve_short

/-- info: 'IxCC.Rt.Rc.Procs.alloc_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.alloc_short
