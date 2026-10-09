import Compilatrix.Rt.Rc.Proof.ReserveFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.reserve_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.reserve_live

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.reserve_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.reserve_protected

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.reserve_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.reserve_slot_frame
