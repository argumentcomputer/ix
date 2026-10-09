import Compilatrix.Recheck.Rc.Proof.LoadedCalls

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Recheck.RcReplay.erased_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.erased_view

/-- info: 'Compilatrix.Recheck.RcReplay.loaded_call_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.loaded_call_sim
