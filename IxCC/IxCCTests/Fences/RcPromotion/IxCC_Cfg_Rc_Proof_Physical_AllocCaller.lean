import IxCC.Cfg.Rc.Proof.Physical.AllocCaller

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.allocator_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocator_call_free

/-- info: 'IxCC.Cfg.Rc.Native.allocator_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocator_caller
