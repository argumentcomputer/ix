import IxCC.Cfg.Rc.Proof.Physical.FrameTransport

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.action_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.action_size

/-- info: 'IxCC.Cfg.Rc.Native.actions_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.actions_size

/-- info: 'IxCC.Cfg.Rc.Native.dropAll_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.dropAll_size

/-- info: 'IxCC.Cfg.Rc.Native.frame_allocation_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.frame_allocation_transport

/-- info: 'IxCC.Cfg.Rc.Native.frame_marker_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.frame_marker_transport
