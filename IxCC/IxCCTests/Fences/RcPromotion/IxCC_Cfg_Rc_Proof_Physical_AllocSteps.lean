import IxCC.Cfg.Rc.Proof.Physical.AllocSteps

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.allocation_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_call

/-- info: 'IxCC.Cfg.Rc.Native.allocation_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_return
