import Compilatrix.Cfg.Rc.Proof.Native.HeapInit

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapState.initialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapState.initialize
