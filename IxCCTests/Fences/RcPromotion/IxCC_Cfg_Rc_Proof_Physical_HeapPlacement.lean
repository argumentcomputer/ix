import IxCC.Cfg.Rc.Proof.Physical.HeapPlacement

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.heapLive_fieldBounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.heapLive_fieldBounded

/-- info: 'IxCC.Cfg.Rc.Native.heapLive_placeFresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.heapLive_placeFresh
