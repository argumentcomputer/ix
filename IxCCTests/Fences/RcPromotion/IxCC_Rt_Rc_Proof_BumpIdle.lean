import IxCC.Rt.Rc.Proof.BumpIdle

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.bump_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.bump_idle

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.bump_not_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.bump_not_free
