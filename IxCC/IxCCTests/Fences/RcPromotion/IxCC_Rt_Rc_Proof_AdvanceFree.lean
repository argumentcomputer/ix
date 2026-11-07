import IxCC.Rt.Rc.Proof.AdvanceFree

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.FreeChain.write_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.FreeChain.write_frame

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.advance_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.advance_chains

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.advance_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.advance_heads
