import IxCC.Rt.Rc.Gen.Proof.ProtectedOps

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_protected

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.count_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.count_protected

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_protected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_protected

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_protected
