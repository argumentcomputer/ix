import Compilatrix.Rt.Rc.Proof.BumpMetadata

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.AllocatorReady.after_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.AllocatorReady.after_bump

/-- info: 'Compilatrix.Rt.Rc.Procs.AllocatorReady.limit_address_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.AllocatorReady.limit_address_nat
