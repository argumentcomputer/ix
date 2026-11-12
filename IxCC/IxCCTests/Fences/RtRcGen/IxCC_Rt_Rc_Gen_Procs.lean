import IxCC.Rt.Rc.Gen.Procs

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.alloc_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.alloc_eq

/-- info: 'IxCC.Rt.Rc.Gen.alloc_ofFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.alloc_ofFields
