import Compilatrix.Xv.Select.Lemmas

/-! Required axiom fences for Xv selection: the branch producers decide the
Lir condition, carry or borrow, and selected immediates keep the Lir
constant's low bits. Expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Xv.Select.condX86_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.condX86_holds

/-- info: 'Compilatrix.Xv.Select.swapCond_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.swapCond_holds

/-- info: 'Compilatrix.Xv.Select.cmp_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.cmp_test

/-- info: 'Compilatrix.Xv.Select.sub_borrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.sub_borrow

/-- info: 'Compilatrix.Xv.Select.add_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.add_carry

/-- info: 'Compilatrix.Xv.Select.and_test_tz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.and_test_tz

/-- info: 'Compilatrix.Xv.Select.and_test_tnz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.and_test_tnz

/-- info: 'Compilatrix.Xv.Select.imm8?_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.imm8?_low

/-- info: 'Compilatrix.Xv.Select.immFull?_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Xv.Select.immFull?_low
