import IxCC.Rt.Rc.Proof.ImmediateStep

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.consume_immediate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.consume_immediate

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.immediate_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.immediate_step

/-- info: 'IxCC.Rt.Rc.Procs.valueWord_immediate_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.valueWord_immediate_tag
