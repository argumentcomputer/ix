import IxCC.Cfg.Rc.Proof.Physical.HeapAppend

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.allocated_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocated_cell

/-- info: 'IxCC.Cfg.Rc.Native.allocated_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocated_old

/-- info: 'IxCC.Cfg.Rc.Native.heapLive_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.heapLive_append
