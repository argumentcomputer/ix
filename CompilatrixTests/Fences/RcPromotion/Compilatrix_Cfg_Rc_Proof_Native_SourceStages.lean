import Compilatrix.Cfg.Rc.Proof.Native.SourceStages

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.accepted_source_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.accepted_source_stages

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.sourceStageRel_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.sourceStageRel_memory
