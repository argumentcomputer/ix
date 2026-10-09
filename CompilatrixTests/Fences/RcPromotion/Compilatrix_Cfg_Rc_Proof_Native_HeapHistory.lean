import Compilatrix.Cfg.Rc.Proof.Native.HeapHistory

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.allocate' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.allocate

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.frame

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.refl

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.resume

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.trans

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.value' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.value

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapHistory.words
