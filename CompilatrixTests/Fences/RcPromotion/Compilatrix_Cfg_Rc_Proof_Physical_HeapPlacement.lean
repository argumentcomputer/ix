import Compilatrix.Cfg.Rc.Proof.Physical.HeapPlacement

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.heapLive_fieldBounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.heapLive_fieldBounded

/-- info: 'Compilatrix.Cfg.Rc.Native.heapLive_placeFresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.heapLive_placeFresh
