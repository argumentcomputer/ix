import Compilatrix.Cfg.Rc.Proof.Physical.NumericInputs

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.HeapState.numeric_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.HeapState.numeric_roots

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.numeric_balance' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.numeric_balance

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.numeric_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.numeric_compatible

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.numeric_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.numeric_inputs

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.numeric_refs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.numeric_refs

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.numeric_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.numeric_words
