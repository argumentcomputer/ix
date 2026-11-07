import IxCC.Recheck.Rc.Proof.SourceFir

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Recheck.RcReplay.SourceFirWitness.observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.SourceFirWitness.observations

/-- info: 'IxCC.Recheck.RcReplay.SourceFirWitness.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.SourceFirWitness.observe

/-- info: 'IxCC.Recheck.RcReplay.SourceFirWitness.value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.SourceFirWitness.value

/-- info: 'IxCC.Recheck.RcReplay.source_fir_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_fir_retained

/-- info: 'IxCC.Recheck.RcReplay.source_fir_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_fir_success
