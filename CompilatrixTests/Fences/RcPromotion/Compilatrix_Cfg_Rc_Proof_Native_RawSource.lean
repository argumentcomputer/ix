import Compilatrix.Cfg.Rc.Proof.Native.RawSource

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.public_functions' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.public_functions

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.public_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.public_get

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.raw_blocks_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.raw_blocks_nonempty

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.sourceStage_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.sourceStage_get

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.source_pruned_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.source_pruned_split

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.source_raw_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.source_raw_layout

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.source_raw_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.source_raw_pruned
