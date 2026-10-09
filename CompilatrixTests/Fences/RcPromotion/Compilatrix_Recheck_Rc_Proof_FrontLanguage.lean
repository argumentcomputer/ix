import Compilatrix.Recheck.Rc.Proof.FrontLanguage

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Recheck.RcReplay.returned_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.returned_view

/-- info: 'Compilatrix.Recheck.RcReplay.source_view_refines_of_fir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_view_refines_of_fir
