import Compilatrix.Recheck.Rc.Proof.Reentry

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapState.numeric_reentry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapState.numeric_reentry

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.recycled_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.recycled_entry
