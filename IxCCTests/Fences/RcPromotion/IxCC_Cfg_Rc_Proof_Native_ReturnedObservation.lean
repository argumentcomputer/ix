import IxCC.Cfg.Rc.Proof.Native.ReturnedObservation

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Returned.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Returned.finish

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Returned.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Returned.observe
