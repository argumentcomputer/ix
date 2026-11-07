import IxCC.Recheck.Rc.Proof.Reentry

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapState.numeric_reentry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapState.numeric_reentry

/-- info: 'IxCC.Cfg.Rc.Native.Spec.recycled_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.recycled_entry
