import Compilatrix.Rt.Rc.Proof.InitHeads

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.Init.head_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Init.head_address

/-- info: 'Compilatrix.Rt.Rc.Procs.Init.head_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Init.head_nat

/-- info: 'Compilatrix.Rt.Rc.Procs.Init.initMemory_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Init.initMemory_head

/-- info: 'Compilatrix.Rt.Rc.Procs.Init.zeroed_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Init.zeroed_head

/-- info: 'Compilatrix.Rt.Rc.Procs.Init.zeros_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Init.zeros_word
