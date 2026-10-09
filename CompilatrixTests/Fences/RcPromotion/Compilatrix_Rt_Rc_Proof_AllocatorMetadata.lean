import Compilatrix.Rt.Rc.Proof.AllocatorMetadata

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.AllocatorReady.after_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.AllocatorReady.after_protected

/-- info: 'Compilatrix.Rt.Rc.Procs.bumpAddress_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.bumpAddress_eq

/-- info: 'Compilatrix.Rt.Rc.Procs.headAddress_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.headAddress_eq

/-- info: 'Compilatrix.Rt.Rc.Procs.limitAddress_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.limitAddress_eq
