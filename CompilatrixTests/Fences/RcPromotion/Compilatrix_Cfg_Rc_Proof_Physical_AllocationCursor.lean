import Compilatrix.Cfg.Rc.Proof.Physical.AllocationCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_cursor_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_cursor_cases

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_lowering_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_lowering_cases

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_overflow_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_overflow_cursor

/-- info: 'Compilatrix.Cfg.Rc.Native.lower_allocation_overflow' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.lower_allocation_overflow
