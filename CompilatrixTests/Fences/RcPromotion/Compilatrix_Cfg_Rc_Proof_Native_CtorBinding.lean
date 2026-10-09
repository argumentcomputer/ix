import Compilatrix.Cfg.Rc.Proof.Native.CtorBinding

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.consume_allocation_runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.consume_allocation_runtime

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ctorIndex_binding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ctorIndex_binding

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ctorIndex_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ctorIndex_row

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.table_row' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.table_row
