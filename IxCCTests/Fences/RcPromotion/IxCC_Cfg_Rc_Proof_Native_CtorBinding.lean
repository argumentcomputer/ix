import IxCC.Cfg.Rc.Proof.Native.CtorBinding

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.consume_allocation_runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.consume_allocation_runtime

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ctorIndex_binding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ctorIndex_binding

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ctorIndex_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ctorIndex_row

/-- info: 'IxCC.Cfg.Rc.Native.Spec.table_row' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.table_row
