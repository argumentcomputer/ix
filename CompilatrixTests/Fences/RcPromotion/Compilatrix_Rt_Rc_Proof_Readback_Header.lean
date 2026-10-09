import Compilatrix.Rt.Rc.Proof.Readback.Header

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.Readback.halves_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Readback.halves_word

/-- info: 'Compilatrix.Rt.Rc.Procs.Readback.live_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Readback.live_header

/-- info: 'Compilatrix.Rt.Rc.Procs.Readback.read64_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.Readback.read64_halves
