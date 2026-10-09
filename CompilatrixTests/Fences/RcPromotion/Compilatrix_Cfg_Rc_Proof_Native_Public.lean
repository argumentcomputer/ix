import Compilatrix.Cfg.Rc.Proof.Native.Public

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.accepted_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.accepted_drop

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.assemble_drop' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.assemble_drop

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.assemble_existing' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.assemble_existing

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.lower_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.lower_parts
