import IxCC.Rt.Rc.Proof.BumpMetadata

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.after_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.after_bump

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.limit_address_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.limit_address_nat
