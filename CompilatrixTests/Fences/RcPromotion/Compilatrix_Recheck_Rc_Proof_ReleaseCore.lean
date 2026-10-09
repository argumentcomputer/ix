import Compilatrix.Recheck.Rc.Proof.ReleaseCore

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapState.reclaimed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapState.reclaimed

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.drop_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.drop_top
