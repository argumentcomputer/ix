import Compilatrix.Fir.Proof.Retained

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Fir.Proof.FirWitness.observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Fir.Proof.FirWitness.observations

/-- info: 'Compilatrix.Fir.Proof.lower_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Fir.Proof.lower_retained
