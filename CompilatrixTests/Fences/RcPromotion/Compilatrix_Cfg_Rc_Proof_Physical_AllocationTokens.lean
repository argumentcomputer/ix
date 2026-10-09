import Compilatrix.Cfg.Rc.Proof.Physical.AllocationTokens

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_field_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_field_balance

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_tokens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_tokens
