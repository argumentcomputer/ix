import IxCC.X86.Proof.DriverSession

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.X86.DriverSession.Session.continuation_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.continuation_bytes

/-- info: 'IxCC.X86.DriverSession.Session.dropCall_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.dropCall_exact

/-- info: 'IxCC.X86.DriverSession.Session.dropCall_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.dropCall_mono

/-- info: 'IxCC.X86.DriverSession.Session.one_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.one_mono

/-- info: 'IxCC.X86.DriverSession.Session.rawWord_argument' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.rawWord_argument

/-- info: 'IxCC.X86.DriverSession.Session.runCalls_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.runCalls_mono

/-- info: 'IxCC.X86.DriverSession.Session.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.run_mono

/-- info: 'IxCC.X86.DriverSession.Session.setup_bytes_outside_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.setup_bytes_outside_return

/-- info: 'IxCC.X86.DriverSession.Session.validTrace_nil' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.validTrace_nil

/-- info: 'IxCC.X86.DriverSession.Session.validTrace_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.validTrace_cons

/-- info: 'IxCC.X86.DriverSession.Session.validTrace_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.validTrace_append

/-- info: 'IxCC.X86.DriverSession.Session.one_ok_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.one_ok_parts

/-- info: 'IxCC.X86.DriverSession.Session.runCalls_ok_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.runCalls_ok_cons

/-- info: 'IxCC.X86.DriverSession.Session.runCalls_ok_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.runCalls_ok_inputs

/-- info: 'IxCC.X86.DriverSession.Session.runCalls_validTrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.runCalls_validTrace

/-- info: 'IxCC.X86.DriverSession.Session.runCalls_validTrace_of_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.runCalls_validTrace_of_one

/-- info: 'IxCC.X86.DriverSession.Session.run_validTrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.DriverSession.Session.run_validTrace
