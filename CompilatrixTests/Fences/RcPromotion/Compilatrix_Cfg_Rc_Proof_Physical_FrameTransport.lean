import Compilatrix.Cfg.Rc.Proof.Physical.FrameTransport

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.action_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.action_size

/-- info: 'Compilatrix.Cfg.Rc.Native.actions_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.actions_size

/-- info: 'Compilatrix.Cfg.Rc.Native.dropAll_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.dropAll_size

/-- info: 'Compilatrix.Cfg.Rc.Native.frame_allocation_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.frame_allocation_transport

/-- info: 'Compilatrix.Cfg.Rc.Native.frame_marker_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.frame_marker_transport
