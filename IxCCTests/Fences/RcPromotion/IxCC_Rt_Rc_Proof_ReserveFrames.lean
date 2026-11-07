import IxCC.Rt.Rc.Proof.ReserveFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_live

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_protected

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_slot_frame
