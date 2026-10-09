import Compilatrix.Cfg.Rc.Proof.Physical.AllocSteps

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_call

/-- info: 'Compilatrix.Cfg.Rc.Native.allocation_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.allocation_return
