import Compilatrix.Cfg.Rc.Proof.Physical.HeapAppend

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.allocated_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocated_cell

/-- info: 'Compilatrix.Cfg.Rc.Native.allocated_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocated_old

/-- info: 'Compilatrix.Cfg.Rc.Native.heapLive_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.heapLive_append
