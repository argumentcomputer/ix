import IxCC.Rt.Rc.Proof.AllocatorMetadata

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.after_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.after_protected

/-- info: 'IxCC.Rt.Rc.Procs.bumpAddress_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.bumpAddress_eq

/-- info: 'IxCC.Rt.Rc.Procs.headAddress_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.headAddress_eq

/-- info: 'IxCC.Rt.Rc.Procs.limitAddress_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.limitAddress_eq
