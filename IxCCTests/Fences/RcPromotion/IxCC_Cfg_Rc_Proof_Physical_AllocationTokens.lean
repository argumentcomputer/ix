import IxCC.Cfg.Rc.Proof.Physical.AllocationTokens

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.allocation_field_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_field_balance

/-- info: 'IxCC.Cfg.Rc.Native.allocation_tokens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_tokens
