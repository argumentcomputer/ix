import IxCC.Fir.Proof.Retained

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Fir.Proof.FirWitness.observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.FirWitness.observations

/-- info: 'IxCC.Fir.Proof.lower_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.lower_retained
