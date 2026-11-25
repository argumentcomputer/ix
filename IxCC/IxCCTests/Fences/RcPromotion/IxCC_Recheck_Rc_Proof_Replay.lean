import IxCC.Recheck.Rc.Proof.Replay

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Recheck.RcReplay.runFront_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.runFront_spec

/-- info: 'IxCC.Recheck.RcReplay.source_refines_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_refines_cfg

/-- info: 'IxCC.Own.Plain.Sink.run_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Sink.run_sim

/-- info: 'IxCC.Own.Plain.Sink.run_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Sink.run_retained

/-- info: 'IxCC.Own.Plain.Sink.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Sink.run_refines
