import Compilatrix.Rt.Rc.Proof.ProtectedFrame

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ProtectedFrame.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ProtectedFrame.refl

/-- info: 'Compilatrix.Rt.Rc.Procs.ProtectedFrame.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ProtectedFrame.trans

/-- info: 'Compilatrix.Rt.Rc.Procs.ProtectedFrame.word' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ProtectedFrame.word

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.head_store_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.head_store_frame

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.object_store_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.object_store_frame

/-- info: 'Compilatrix.Rt.Rc.Procs.protected_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.protected_write
