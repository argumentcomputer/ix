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
