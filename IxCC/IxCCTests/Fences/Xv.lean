import IxCC.Xv.Select.Lemmas

/-! Required axiom fences for Xv selection: the branch producers (`test a, a`
included) decide the Lir condition, carry or borrow, and selected
immediates keep the Lir constant's low bits. Expected messages are
preserved verbatim. -/

/-- info: 'IxCC.Xv.Select.condX86_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.condX86_holds

/-- info: 'IxCC.Xv.Select.swapCond_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.swapCond_holds

/-- info: 'IxCC.Xv.Select.cmp_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.cmp_test

/-- info: 'IxCC.Xv.Select.sub_borrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.sub_borrow

/-- info: 'IxCC.Xv.Select.add_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.add_carry

/-- info: 'IxCC.Xv.Select.and_test_tz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.and_test_tz

/-- info: 'IxCC.Xv.Select.and_test_tnz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.and_test_tnz

/-- info: 'IxCC.Xv.Select.imm8?_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.imm8?_low

/-- info: 'IxCC.Xv.Select.immFull?_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.immFull?_low

/-- info: 'IxCC.Xv.Select.test_self_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.test_self_flags

/-- info: 'IxCC.Xv.Select.test_self_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Xv.Select.test_self_test
