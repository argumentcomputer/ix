import Compilatrix.Cfg.Rc.Proof.Physical.AllocCaller

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.allocator_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocator_call_free

/-- info: 'Compilatrix.Cfg.Rc.Native.allocator_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocator_caller
