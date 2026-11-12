import IxCC.Rt.Rc.Gen.Proof.ProtectedFrame

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ProtectedFrame.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ProtectedFrame.refl

/-- info: 'IxCC.Rt.Rc.Gen.ProtectedFrame.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ProtectedFrame.trans

/-- info: 'IxCC.Rt.Rc.Gen.ProtectedFrame.word' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ProtectedFrame.word

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.head_store_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.head_store_frame

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.object_store_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.object_store_frame

/-- info: 'IxCC.Rt.Rc.Gen.protected_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.protected_write
