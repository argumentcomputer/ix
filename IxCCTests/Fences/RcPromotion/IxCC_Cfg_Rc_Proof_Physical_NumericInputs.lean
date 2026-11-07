import IxCC.Cfg.Rc.Proof.Physical.NumericInputs

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapState.numeric_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapState.numeric_roots

/-- info: 'IxCC.Cfg.Rc.Native.Spec.numeric_balance' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.numeric_balance

/-- info: 'IxCC.Cfg.Rc.Native.Spec.numeric_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.numeric_compatible

/-- info: 'IxCC.Cfg.Rc.Native.Spec.numeric_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.numeric_inputs

/-- info: 'IxCC.Cfg.Rc.Native.Spec.numeric_refs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.numeric_refs

/-- info: 'IxCC.Cfg.Rc.Native.Spec.numeric_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.numeric_words
