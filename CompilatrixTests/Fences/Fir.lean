import Compilatrix.Fir.Semantics

/-! Required axiom fences for Fir (M1.F5): the size and join-stack facts the
well-founded Fir semantics terminates by. `Fir.convert_correct` (M2.4) will
join them. Expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Fir.Code.size_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Fir.Code.size_pos

/-- info: 'Compilatrix.Fir.lookupJ_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Fir.lookupJ_weight

/-- info: 'Compilatrix.Fir.JEntry.jweight_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Fir.JEntry.jweight_after
