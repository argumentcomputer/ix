import Compilatrix.Cfg.Rc.Proof.Native.Split

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.accepted_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.accepted_split

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.assemble_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.assemble_split

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.drop_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.drop_split

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.program_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.program_split
