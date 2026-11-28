import IxCC.Fir.Semantics

/-! Required axiom fences for Fir: the size and join-stack facts the
well-founded Fir semantics terminates by. `Fir.convert_correct` will
join them. Expected messages are preserved verbatim. -/

/-- info: 'IxCC.Fir.Code.size_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Code.size_pos

/-- info: 'IxCC.Fir.lookupJ_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.lookupJ_weight

/-- info: 'IxCC.Fir.JEntry.jweight_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.JEntry.jweight_after
