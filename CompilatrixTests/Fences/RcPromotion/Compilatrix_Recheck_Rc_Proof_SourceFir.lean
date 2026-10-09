import Compilatrix.Recheck.Rc.Proof.SourceFir

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Recheck.RcReplay.SourceFirWitness.observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.SourceFirWitness.observations

/-- info: 'Compilatrix.Recheck.RcReplay.SourceFirWitness.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.SourceFirWitness.observe

/-- info: 'Compilatrix.Recheck.RcReplay.SourceFirWitness.value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.SourceFirWitness.value

/-- info: 'Compilatrix.Recheck.RcReplay.source_fir_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_fir_retained

/-- info: 'Compilatrix.Recheck.RcReplay.source_fir_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_fir_success
