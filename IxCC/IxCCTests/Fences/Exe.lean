import IxCC.Exe
import IxCC.Exe.Machine.Sound

/-! Standalone executables: the layout's driver contract and the written
file's structural check (for the production frame and for any frame) use only
the standard logical axioms. -/

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

/-- info: 'IxCC.X86.Exe.checkFor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.checkFor_sound

/-! Numeric state machines: the generic shell's driver contract and segments,
and the request interface. -/

/-- info: 'IxCC.X86.Exe.Machine.Layout.driver_canonicalOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Machine.Layout.driver_canonicalOk

/-- info: 'IxCC.X86.Exe.Machine.Layout.segmentsOk_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Machine.Layout.segmentsOk_of_check

/-- info: 'IxCC.X86.Exe.Machine.Layout.default_check' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Machine.Layout.default_check

/-- info: 'IxCC.Exe.Machine.Request.decode_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Request.decode_encode

/-- info: 'IxCC.Exe.Machine.Request.encode_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Request.encode_lt

/-- info: 'IxCC.Exe.Machine.Request.decode_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Request.decode_valid

/-! Numeric state machines: the session model and the session theorem. -/

/-- info: 'IxCC.Exe.Machine.Reaches.refines' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Reaches.refines

/-- info: 'IxCC.Exe.Machine.Performs.refines' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Performs.refines

/-- info: 'IxCC.Exe.Machine.runFor_performs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.runFor_performs

/-- info: 'IxCC.Exe.Machine.MachineRoot.exact' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.MachineRoot.exact

/-- info: 'IxCC.Exe.Machine.srcCallOf_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.srcCallOf_functional

/-- info: 'IxCC.Exe.Machine.callRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.callRefines

/-- info: 'IxCC.Exe.Machine.session_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.session_sound

/-- info: 'IxCC.Exe.Machine.machine_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.machine_root

/-- info: 'IxCC.Exe.Machine.machine_session_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.machine_session_sound

/-- info: 'IxCC.Exe.Machine.Rc.callRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Rc.callRefines

/-- info: 'IxCC.Exe.Machine.Rc.session_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Rc.session_sound

/-! X0-P, first part: a call site per call, and the session theorem from two sites. -/

/-- info: 'IxCC.X86.Driver.Ok.withSite' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Driver.Ok.withSite

/-- info: 'IxCC.X86.LinkedAt.call_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.LinkedAt.call_mono

/-- info: 'IxCC.X86.LinkedAt.run_site' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.LinkedAt.run_site

/-- info: 'IxCC.Exe.Machine.Reaches.refines_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Reaches.refines_prefix

/-- info: 'IxCC.Exe.Machine.Performs.refines_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Performs.refines_prefix

/-- info: 'IxCC.Exe.Machine.Reaches.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Reaches.mono

/-- info: 'IxCC.Exe.Machine.Last.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Last.mono

/-- info: 'IxCC.Exe.Machine.Performs.mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Performs.mono

/-- info: 'IxCC.Exe.Machine.objCall_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.objCall_le

/-- info: 'IxCC.Exe.Machine.callRefines_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.callRefines_at

/-- info: 'IxCC.Exe.Machine.session_sound_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.session_sound_at

/-- info: 'IxCC.Exe.Machine.machine_session_sound_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.machine_session_sound_at

/-- info: 'IxCC.Exe.Machine.Rc.objCall_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Rc.objCall_le

/-- info: 'IxCC.Exe.Machine.Rc.callRefines_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Rc.callRefines_at

/-- info: 'IxCC.Exe.Machine.Rc.session_sound_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Machine.Rc.session_sound_at
