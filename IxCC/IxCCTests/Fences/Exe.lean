import IxCC.Exe
import IxCC.Exe.Machine.Sound
import IxCC.X86.Exe.Process
import IxCC.X86.Exe.Machine.Proof.Call

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

/-! The shell proof's second part (X0-P): the shell's text check that
`Machine.writeChecked` runs, and the process's runs and what its traces denote. -/

/-- info: 'IxCC.X86.Exe.Shell.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.check_sound

/-- info: 'IxCC.X86.Exe.Process.Shows.refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Shows.refines

/-- info: 'IxCC.X86.Exe.Process.DenotesAll.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.DenotesAll.append

/-- info: 'IxCC.X86.Exe.Process.DenotesAll.split' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.DenotesAll.split

/-- info: 'IxCC.X86.Exe.Process.DenotesAll.prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.DenotesAll.prefix

/-- info: 'IxCC.X86.Exe.Process.Run.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Run.trans

/-- info: 'IxCC.X86.Exe.Process.Run.ofByteRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Run.ofByteRun

/-! The shell proof's second part (X0-P): a call into the object on the process
(`call_lifts`), the two calls of an iteration (`two_calls`), and a fault ending
the trace (`Trace.nil_of_faults`, `Trace.through`), with their lemmas. -/

/-- info: 'IxCC.X86.Exe.Process.call_lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.call_lifts

/-- info: 'IxCC.X86.Exe.Process.AtCall.lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.AtCall.lifts

/-- info: 'IxCC.X86.Exe.Process.two_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.two_calls

/-- info: 'IxCC.X86.Exe.Process.Trace.nil_of_faults' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Trace.nil_of_faults

/-- info: 'IxCC.X86.Exe.Process.Trace.through' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Trace.through

/-- info: 'IxCC.X86.Exe.Process.Run.through' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Run.through

/-- info: 'IxCC.X86.Exe.Process.Step.of_decodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Step.of_decodes

/-- info: 'IxCC.X86.Exe.Process.decodes_of_step_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.decodes_of_step_ok

/-- info: 'IxCC.X86.Exe.Process.decodes_of_fault' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.decodes_of_fault

/-- info: 'IxCC.X86.Exe.Process.run_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_add

/-- info: 'IxCC.X86.Exe.Process.run_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_comp

/-- info: 'IxCC.X86.Exe.Process.run_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_prefix

/-- info: 'IxCC.X86.Exe.Process.FaultsWithin.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.FaultsWithin.mono

/-- info: 'IxCC.X86.Exe.Process.FaultsWithin.shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.FaultsWithin.shift

/-- info: 'IxCC.X86.Exe.Process.Lifts.of_faults' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Lifts.of_faults

/-- info: 'IxCC.X86.Exe.Process.CallsLift.of_faults' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.CallsLift.of_faults

/-- info: 'IxCC.X86.Exe.Process.step_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.step_window

/-- info: 'IxCC.X86.Exe.Process.run_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_window

/-- info: 'IxCC.X86.Exe.Process.drop_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.drop_window

/-- info: 'IxCC.X86.Exe.Process.decodeAt_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.decodeAt_lt

/-- info: 'IxCC.X86.Exe.Process.run_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_error

/-- info: 'IxCC.X86.Exe.Process.run_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_succ

/-- info: 'IxCC.X86.Exe.Process.runTo_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.runTo_run

/-- info: 'IxCC.X86.Exe.Process.sp_addr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.sp_addr

/-- info: 'IxCC.X86.Exe.Process.slot_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.slot_mapped

/-- info: 'IxCC.X86.Exe.Process.mem_writable' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mem_writable

/-- info: 'IxCC.X86.Exe.Process.mem_readable' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mem_readable

/-- info: 'IxCC.X86.Exe.Process.mem_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mem_slot

/-- info: 'IxCC.X86.Exe.Process.mem_unmapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mem_unmapped

/-- info: 'IxCC.X86.Exe.Process.call_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.call_step

/-- info: 'IxCC.X86.Exe.Process.regs_calleeSaved' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.regs_calleeSaved

/-- info: 'IxCC.X86.Exe.Process.restored_saved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.restored_saved
