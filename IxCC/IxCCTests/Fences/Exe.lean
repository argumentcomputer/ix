import IxCC.Exe

/-! Standalone executables: the layout's driver contract and the written
file's structural check use only the standard logical axioms. -/

/-- info: 'IxCC.X86.Exe.Layout.driver_canonicalOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Layout.driver_canonicalOk

/-- info: 'IxCC.X86.Exe.Layout.default_check' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Layout.default_check

/-- info: 'IxCC.X86.Exe.checkWith_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.checkWith_sound

/-- info: 'IxCC.X86.Exe.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.check_sound

/-- info: 'IxCC.X86.Exe.Certified.valid'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Certified.valid'
