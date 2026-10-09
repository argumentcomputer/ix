import Compilatrix.Rt.Rc.Proof.AdvanceFree

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.FreeChain.write_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.FreeChain.write_frame

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_chains

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_heads
