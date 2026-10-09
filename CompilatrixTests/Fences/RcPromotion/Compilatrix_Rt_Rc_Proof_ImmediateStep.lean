import Compilatrix.Rt.Rc.Proof.ImmediateStep

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.consume_immediate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.consume_immediate

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.immediate_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.immediate_step

/-- info: 'Compilatrix.Rt.Rc.Procs.valueWord_immediate_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.valueWord_immediate_tag
