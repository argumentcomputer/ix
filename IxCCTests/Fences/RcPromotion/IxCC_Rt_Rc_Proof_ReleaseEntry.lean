import IxCC.Rt.Rc.Proof.ReleaseEntry

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.begin_release' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.begin_release

/-- info: 'IxCC.Rt.Rc.Procs.release_entry_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.release_entry_complete
