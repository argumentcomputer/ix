import IxCC.Cfg.Rc.Proof.Native.HeapInit

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapState.initialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapState.initialize
