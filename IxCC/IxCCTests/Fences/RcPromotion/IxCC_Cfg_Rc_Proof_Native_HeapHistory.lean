import IxCC.Cfg.Rc.Proof.Native.HeapHistory

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.allocate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.allocate

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.frame

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.refl

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.resume

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.trans

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.value' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.value

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapHistory.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapHistory.words
