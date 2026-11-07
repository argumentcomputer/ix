import IxCC.Cfg.Rc.Proof.Physical.AllocationCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.allocation_cursor_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_cursor_cases

/-- info: 'IxCC.Cfg.Rc.Native.allocation_lowering_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_lowering_cases

/-- info: 'IxCC.Cfg.Rc.Native.allocation_overflow_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_overflow_cursor

/-- info: 'IxCC.Cfg.Rc.Native.lower_allocation_overflow' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.lower_allocation_overflow
