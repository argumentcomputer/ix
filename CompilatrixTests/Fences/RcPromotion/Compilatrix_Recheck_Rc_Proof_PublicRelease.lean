import Compilatrix.Recheck.Rc.Proof.PublicRelease

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Returned.release_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Returned.release_public

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.accepted_drop_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.accepted_drop_index

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.source_stage_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.source_stage_drop
