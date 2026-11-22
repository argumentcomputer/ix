import IxCC.Ixon.V3.Contracts

/-! Ixon v5 mode-code bijections and usage algebra fences retain ordinary logic. -/

/-- info: 'Ixon.BinderMode.ofCode?_toCode' does not depend on any axioms -/
#guard_msgs in #print axioms Ixon.BinderMode.ofCode?_toCode

/-- info: 'Ixon.ResultMode.ofCode?_toCode' does not depend on any axioms -/
#guard_msgs in #print axioms Ixon.ResultMode.ofCode?_toCode

/-- info: 'Ixon.AllMode.ofCode?_toCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ixon.AllMode.ofCode?_toCode

/-- info: 'Ixon.LetMode.ofCode?_toCode' does not depend on any axioms -/
#guard_msgs in #print axioms Ixon.LetMode.ofCode?_toCode

/-- info: 'Ixon.LetMode.ofHeader?_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ixon.LetMode.ofHeader?_header

/-- info: 'Ixon.FieldMode.ofCode?_toCode' does not depend on any axioms -/
#guard_msgs in #print axioms Ixon.FieldMode.ofCode?_toCode

/-- info: 'Ixon.AllocAssert.ofCode?_toCode' does not depend on any axioms -/
#guard_msgs in #print axioms Ixon.AllocAssert.ofCode?_toCode

/-- info: 'Ixon.DefAsserts.ofCode?_toCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ixon.DefAsserts.ofCode?_toCode

/-- info: 'Ixon.Usage.covers_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ixon.Usage.covers_sound

/-- info: 'Ixon.Usage.join_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ixon.Usage.join_left

/-- info: 'Ixon.Usage.join_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ixon.Usage.join_right

/-- info: 'Ixon.Usage.add_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ixon.Usage.add_sound

/-- info: 'Ixon.Usage.mul_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ixon.Usage.mul_sound
