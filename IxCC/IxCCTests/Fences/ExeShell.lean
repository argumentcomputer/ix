import IxCC.Exe.Machine.Exe
import IxCC.X86.Exe.Machine.Proof.Loaded

/-! The shell proof's third part (X0-P): the shell's instructions on the byte
machine, a checked machine executable's placement, a checked shell's steps and
traces counted in steps, the machine shell's blocks, the glue between an
iteration's two calls, the failure report, the loop's paths, the loop
(`from_loop`), start-up (`start`), the shell theorem (`shell_sound`) and the
executable theorems (`machine_exe_sound`, `Rc.machine_exe_sound`) with their
corollaries for states where `Process.Step` promises nothing (`shell_unspecified`,
`machine_exe_unspecified`, `Rc.machine_exe_unspecified`), and the loader
specification satisfiable (`loaded_exists`). Every
theorem's axiom set, exactly. -/

/-- info: 'IxCC.X86.Exe.Process.probe_core' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.probe_core

/-- info: 'IxCC.X86.Exe.Process.probe_advance' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.probe_advance

/-- info: 'IxCC.X86.Exe.Process.execute_rip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.execute_rip

/-- info: 'IxCC.X86.Exe.Process.execute_of_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.execute_of_advance

/-- info: 'IxCC.X86.Exe.Process.execute_of_trap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.execute_of_trap

/-- info: 'IxCC.X86.Exe.Process.merge_unchanged' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.merge_unchanged

/-- info: 'IxCC.X86.Exe.Process.execute_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.execute_flags

/-- info: 'IxCC.X86.Exe.Process.exec_mov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_mov

/-- info: 'IxCC.X86.Exe.Process.exec_lea' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_lea

/-- info: 'IxCC.X86.Exe.Process.exec_load64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_load64

/-- info: 'IxCC.X86.Exe.Process.exec_store64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_store64

/-- info: 'IxCC.X86.Exe.Process.exec_store8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_store8

/-- info: 'IxCC.X86.Exe.Process.exec_load8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_load8

/-- info: 'IxCC.X86.Exe.Process.exec_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_alu

/-- info: 'IxCC.X86.Exe.Process.exec_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_test

/-- info: 'IxCC.X86.Exe.Process.test_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.test_ne_self

/-- info: 'IxCC.X86.Exe.Process.exec_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_compare

/-- info: 'IxCC.X86.Exe.Process.compare_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.compare_test

/-- info: 'IxCC.X86.Exe.Process.ne_call_of_op' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.ne_call_of_op

/-- info: 'IxCC.X86.Exe.Process.fetch_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.fetch_index

/-- info: 'IxCC.X86.Exe.Process.instrOffset_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.instrOffset_zero

/-- info: 'IxCC.X86.Exe.Process.instrOffset_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.instrOffset_succ

/-- info: 'IxCC.X86.Exe.Process.next_addr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.next_addr

/-- info: 'IxCC.X86.Exe.Process.decodes_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.decodes_some

/-- info: 'IxCC.X86.Exe.Shell.Valid.step_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.step_instr

/-- info: 'IxCC.X86.Exe.Shell.Valid.step_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.step_ok

/-- info: 'IxCC.X86.Exe.Shell.Valid.step_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.step_fault

/-- info: 'IxCC.X86.Exe.Process.addr_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.addr_add

/-- info: 'IxCC.X86.Exe.Process.targets_lands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.targets_lands

/-- info: 'IxCC.X86.Exe.Shell.Valid.run_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.run_branch

/-- info: 'IxCC.X86.Exe.Shell.Valid.step_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.step_jump

/-- info: 'IxCC.X86.Exe.Shell.Valid.step_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.step_ret

/-- info: 'IxCC.X86.Exe.Shell.Valid.step_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.step_call

/-- info: 'IxCC.X86.Exe.Shell.Valid.callsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.callsTo

/-- info: 'IxCC.X86.Exe.Shell.Valid.syscall_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Shell.Valid.syscall_at

/-- info: 'IxCC.X86.Exe.Process.Run.toN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Run.toN

/-- info: 'IxCC.X86.Exe.Process.RunN.toRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.RunN.toRun

/-- info: 'IxCC.X86.Exe.Process.Trace.toN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Trace.toN

/-- info: 'IxCC.X86.Exe.Process.TraceN.toTrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.toTrace

/-- info: 'IxCC.X86.Exe.Process.TraceN.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.mono

/-- info: 'IxCC.X86.Exe.Process.TraceN.through' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.through

/-- info: 'IxCC.X86.Exe.Process.TraceN.nil_of_faults' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.nil_of_faults

/-- info: 'IxCC.X86.Exe.Process.TraceN.sys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.sys

/-- info: 'IxCC.X86.Exe.Process.blocks_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.blocks_get

/-- info: 'IxCC.X86.Exe.Process.shell_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shell_size

/-- info: 'IxCC.X86.Exe.Process.shellAddr_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shellAddr_zero

/-- info: 'IxCC.X86.Exe.Process.shell_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shell_get

/-- info: 'IxCC.X86.Exe.Process.shell_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shell_valid

/-- info: 'IxCC.X86.Exe.Process.file_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.file_fit

/-- info: 'IxCC.X86.Exe.Process.shellAddr_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shellAddr_lt

/-- info: 'IxCC.X86.Exe.Process.mstep_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_ok

/-- info: 'IxCC.X86.Exe.Process.mstep_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_fault

/-- info: 'IxCC.X86.Exe.Process.mrun_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mrun_branch

/-- info: 'IxCC.X86.Exe.Process.mstep_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_jump

/-- info: 'IxCC.X86.Exe.Process.mstep_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_ret

/-- info: 'IxCC.X86.Exe.Process.mstep_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_call

/-- info: 'IxCC.X86.Exe.Process.mcallsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mcallsTo

/-- info: 'IxCC.X86.Exe.Process.msyscall_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.msyscall_at

/-- info: 'IxCC.X86.Exe.Process.block_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_start

/-- info: 'IxCC.X86.Exe.Process.block_seccomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_seccomp

/-- info: 'IxCC.X86.Exe.Process.block_args' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_args

/-- info: 'IxCC.X86.Exe.Process.block_argsNone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_argsNone

/-- info: 'IxCC.X86.Exe.Process.block_argsSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_argsSome

/-- info: 'IxCC.X86.Exe.Process.block_setup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_setup

/-- info: 'IxCC.X86.Exe.Process.block_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_loop

/-- info: 'IxCC.X86.Exe.Process.block_initBack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_initBack

/-- info: 'IxCC.X86.Exe.Process.block_callStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_callStep

/-- info: 'IxCC.X86.Exe.Process.block_stepBack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_stepBack

/-- info: 'IxCC.X86.Exe.Process.block_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_decode

/-- info: 'IxCC.X86.Exe.Process.block_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_split

/-- info: 'IxCC.X86.Exe.Process.block_kindArg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_kindArg

/-- info: 'IxCC.X86.Exe.Process.block_kind1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_kind1

/-- info: 'IxCC.X86.Exe.Process.block_kind2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_kind2

/-- info: 'IxCC.X86.Exe.Process.block_kind3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_kind3

/-- info: 'IxCC.X86.Exe.Process.block_arg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_arg

/-- info: 'IxCC.X86.Exe.Process.block_noMore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_noMore

/-- info: 'IxCC.X86.Exe.Process.block_argByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_argByte

/-- info: 'IxCC.X86.Exe.Process.block_argNext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_argNext

/-- info: 'IxCC.X86.Exe.Process.block_argEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_argEnd

/-- info: 'IxCC.X86.Exe.Process.block_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_out

/-- info: 'IxCC.X86.Exe.Process.block_err' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_err

/-- info: 'IxCC.X86.Exe.Process.block_write1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_write1

/-- info: 'IxCC.X86.Exe.Process.block_written' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_written

/-- info: 'IxCC.X86.Exe.Process.block_notWritten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_notWritten

/-- info: 'IxCC.X86.Exe.Process.block_exitCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_exitCode

/-- info: 'IxCC.X86.Exe.Process.block_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_exit

/-- info: 'IxCC.X86.Exe.Process.block_fail1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_fail1

/-- info: 'IxCC.X86.Exe.Process.block_fail2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_fail2

/-- info: 'IxCC.X86.Exe.Process.block_fail3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_fail3

/-- info: 'IxCC.X86.Exe.Process.block_fail4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_fail4

/-- info: 'IxCC.X86.Exe.Process.block_report' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_report

/-- info: 'IxCC.X86.Exe.Process.block_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_write

/-- info: 'IxCC.X86.Exe.Process.block_writeSys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_writeSys

/-- info: 'IxCC.X86.Exe.Process.block_writeAdv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_writeAdv

/-- info: 'IxCC.X86.Exe.Process.block_writeRet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_writeRet

/-- info: 'IxCC.X86.Exe.Process.block_writeErr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_writeErr

/-- info: 'IxCC.X86.Exe.Process.block_heap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_heap

/-- info: 'IxCC.X86.Exe.Process.block_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_stack

/-- info: 'IxCC.X86.Exe.Process.block_natOverflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_natOverflow

/-- info: 'IxCC.X86.Exe.Process.block_trap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_trap

/-- info: 'IxCC.X86.Exe.Process.block_abi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_abi

/-- info: 'IxCC.X86.Exe.Process.block_notValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_notValue

/-- info: 'IxCC.X86.Exe.Process.block_request' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_request

/-- info: 'IxCC.X86.Exe.Process.block_confine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_confine

/-- info: 'IxCC.X86.Exe.Process.message_index' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.message_index

/-- info: 'IxCC.X86.Exe.Process.block_message' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.block_message

/-- info: 'IxCC.X86.Exe.Process.run_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.run_one

/-- info: 'IxCC.X86.Exe.Process.read64?_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.read64?_value

/-- info: 'IxCC.X86.Exe.Process.layout_numbers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.layout_numbers

/-- info: 'IxCC.X86.Exe.Process.toNat_small' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.toNat_small

/-- info: 'IxCC.X86.Exe.Process.sp_add8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.sp_add8

/-- info: 'IxCC.X86.Exe.Process.scratch_unmapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.scratch_unmapped

/-- info: 'IxCC.X86.Exe.Process.driver_ok_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.driver_ok_at

/-- info: 'IxCC.X86.Exe.Process.shellAddr_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shellAddr_in

/-- info: 'IxCC.X86.Exe.Process.shellAddr_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shellAddr_below

/-- info: 'IxCC.X86.Exe.Process.file_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.file_text

/-- info: 'IxCC.X86.Exe.Process.loop_ret_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.loop_ret_in

/-- info: 'IxCC.X86.Exe.Process.step_ret_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.step_ret_in

/-- info: 'IxCC.X86.Exe.Process.initDriver_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.initDriver_ok

/-- info: 'IxCC.X86.Exe.Process.stepDriver_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.stepDriver_ok

/-- info: 'IxCC.X86.Exe.Process.glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.glue

/-- info: 'IxCC.X86.Exe.Process.iteration_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.iteration_calls

/-- info: 'IxCC.X86.Exe.planFor_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.planFor_facts

/-- info: 'IxCC.X86.Exe.byteArray_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.byteArray_getElem?

/-- info: 'IxCC.X86.Exe.slice_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.slice_getElem?

/-- info: 'IxCC.X86.Exe.le_alignUp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.le_alignUp

/-- info: 'IxCC.X86.Exe.Machine.fileFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Machine.fileFacts

/-! ### The failure report, the loop's paths and the loop -/

/-- info: 'IxCC.X86.Exe.Process.syscall_write' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.syscall_write

/-- info: 'IxCC.X86.Exe.Process.syscall_exit' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.syscall_exit

/-- info: 'IxCC.X86.Exe.Process.syscall_prctl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.syscall_prctl

/-- info: 'IxCC.X86.Exe.Process.syscall_seccomp' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.syscall_seccomp

/-- info: 'IxCC.X86.Exe.Process.TraceN.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.write

/-- info: 'IxCC.X86.Exe.Process.TraceN.exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.exit

/-- info: 'IxCC.X86.Exe.Process.TraceN.prctl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.prctl

/-- info: 'IxCC.X86.Exe.Process.TraceN.seccomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.seccomp

/-- info: 'IxCC.X86.Exe.Process.TraceN.nil_of_step_fault' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.TraceN.nil_of_step_fault

/-- info: 'IxCC.X86.Exe.Process.slice_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.slice_drop

/-- info: 'IxCC.X86.Exe.Process.slice_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.slice_length

/-- info: 'IxCC.X86.Exe.Process.ByteArray.toList_eq_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.ByteArray.toList_eq_data

/-- info: 'IxCC.X86.Exe.Process.text_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.text_length

/-- info: 'IxCC.X86.Exe.Process.messageOf_status' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.messageOf_status

/-- info: 'IxCC.X86.Exe.Process.failure_split' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.failure_split

/-- info: 'IxCC.X86.Exe.Process.flatMap_text_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.flatMap_text_length

/-- info: 'IxCC.X86.Exe.Process.filter_prefix_length' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.filter_prefix_length

/-- info: 'IxCC.X86.Exe.Process.messageAt_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.messageAt_fst

/-- info: 'IxCC.X86.Exe.Process.message_end_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.message_end_le

/-- info: 'IxCC.X86.Exe.Process.dataBytes_message' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.dataBytes_message

/-- info: 'IxCC.X86.Exe.Process.getElem!_of_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.getElem!_of_getElem?

/-- info: 'IxCC.X86.Exe.Process.message_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.message_slice

/-- info: 'IxCC.X86.Exe.Process.message_length_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.message_length_lt

/-- info: 'IxCC.X86.Exe.Process.exit_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exit_path

/-- info: 'IxCC.X86.Exe.Process.truncate64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.truncate64

/-- info: 'IxCC.X86.Exe.Process.signedValue_w64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.signedValue_w64

/-- info: 'IxCC.X86.Exe.Process.signedLe_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.signedLe_zero

/-- info: 'IxCC.X86.Exe.Process.report_nil' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.report_nil

/-- info: 'IxCC.X86.Exe.Process.write_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write_loop

/-- info: 'IxCC.X86.Exe.Process.report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.report

/-- info: 'IxCC.X86.Exe.Process.toNat_add_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.toNat_add_small

/-- info: 'IxCC.X86.Exe.Process.ne_of_toNat' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.ne_of_toNat

/-- info: 'IxCC.X86.Exe.Process.eval_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.eval_at

/-- info: 'IxCC.X86.Exe.Process.exec_shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exec_shr

/-- info: 'IxCC.X86.Exe.Process.shr_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shr_toNat

/-- info: 'IxCC.X86.Exe.Process.and_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.and_toNat

/-- info: 'IxCC.X86.Exe.Process.odd_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.odd_test

/-- info: 'IxCC.X86.Exe.Process.load8_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.load8_toNat

/-- info: 'IxCC.X86.Exe.Process.read64_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.read64_congr

/-- info: 'IxCC.X86.Exe.Process.write_bytes_apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write_bytes_apart

/-- info: 'IxCC.X86.Exe.Process.write_read64_apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write_read64_apart

/-- info: 'IxCC.X86.Exe.Process.write_read64_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write_read64_same

/-- info: 'IxCC.X86.Exe.Process.write?_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write?_ok

/-- info: 'IxCC.X86.Exe.Process.write_twice_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write_twice_bytes

/-- info: 'IxCC.X86.Exe.Process.inside_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.inside_stack

/-- info: 'IxCC.X86.Exe.Process.inside_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.inside_region

/-- info: 'IxCC.X86.Exe.Process.Kept.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Kept.refl

/-- info: 'IxCC.X86.Exe.Process.Kept.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Kept.write

/-- info: 'IxCC.X86.Exe.Process.numbers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.numbers

/-- info: 'IxCC.X86.Exe.Process.cTop_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.cTop_add

/-- info: 'IxCC.X86.Exe.Process.cTop_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.cTop_toNat

/-- info: 'IxCC.X86.Exe.Process.region_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.region_add

/-- info: 'IxCC.X86.Exe.Process.notKept_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.notKept_low

/-- info: 'IxCC.X86.Exe.Process.notKept_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.notKept_high

/-- info: 'IxCC.X86.Exe.Process.notKept_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.notKept_region

/-- info: 'IxCC.X86.Exe.Process.kept_unmapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.kept_unmapped

/-- info: 'IxCC.X86.Exe.Process.Kept.read64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Kept.read64

/-- info: 'IxCC.X86.Exe.Process.store_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.store_low

/-- info: 'IxCC.X86.Exe.Process.store_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.store_out

/-- info: 'IxCC.X86.Exe.Process.store_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.store_region

/-- info: 'IxCC.X86.Exe.Process.cword_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.cword_apart

/-- info: 'IxCC.X86.Exe.Process.regionStart_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.regionStart_toNat

/-- info: 'IxCC.X86.Exe.Process.ctx_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.ctx_sub

/-- info: 'IxCC.X86.Exe.Process.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.head

/-- info: 'IxCC.X86.Exe.Process.back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.back

/-- info: 'IxCC.X86.Exe.Process.back_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.back_nonzero

/-- info: 'IxCC.X86.Exe.Process.back_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.back_zero

/-- info: 'IxCC.X86.Exe.Process.fail_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.fail_step

/-- info: 'IxCC.X86.Exe.Process.fail_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.fail_dispatch

/-- info: 'IxCC.X86.Exe.Process.mstep_movI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_movI

/-- info: 'IxCC.X86.Exe.Process.mstep_movR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_movR

/-- info: 'IxCC.X86.Exe.Process.mstep_alu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_alu

/-- info: 'IxCC.X86.Exe.Process.mstep_shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_shr

/-- info: 'IxCC.X86.Exe.Process.mstep_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_load

/-- info: 'IxCC.X86.Exe.Process.mstep_load8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_load8

/-- info: 'IxCC.X86.Exe.Process.mstep_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_store

/-- info: 'IxCC.X86.Exe.Process.mstep_jmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mstep_jmp

/-- info: 'IxCC.X86.Exe.Process.mrun_cmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mrun_cmp

/-- info: 'IxCC.X86.Exe.Process.holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.holds_eq

/-- info: 'IxCC.X86.Exe.Process.holds_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.holds_ne

/-- info: 'IxCC.X86.Exe.Process.byte_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.byte_of

/-- info: 'IxCC.X86.Exe.Process.add_zero'' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.add_zero'

/-- info: 'IxCC.X86.Exe.Process.decode_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.decode_run

/-- info: 'IxCC.X86.Exe.Process.split_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.split_run

/-- info: 'IxCC.X86.Exe.Process.kinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.kinds

/-- info: 'IxCC.X86.Exe.Process.exitCode_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.exitCode_path

/-- info: 'IxCC.X86.Exe.Process.answer_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.answer_run

/-- info: 'IxCC.X86.Exe.Process.write_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.write_path

/-- info: 'IxCC.X86.Exe.Process.arg_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.arg_head

/-- info: 'IxCC.X86.Exe.Process.noMore_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.noMore_run

/-- info: 'IxCC.X86.Exe.Process.argByte_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.argByte_run

/-- info: 'IxCC.X86.Exe.Process.argNext_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.argNext_run

/-- info: 'IxCC.X86.Exe.Process.argEnd_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.argEnd_run

/-- info: 'IxCC.X86.Exe.Process.LoopGoal.nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.LoopGoal.nil

/-- info: 'IxCC.X86.Exe.Process.LoopGoal.stuck' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.LoopGoal.stuck

/-- info: 'IxCC.X86.Exe.Process.LoopGoal.last' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.LoopGoal.last

/-- info: 'IxCC.X86.Exe.Process.LoopGoal.fail' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.LoopGoal.fail

/-- info: 'IxCC.X86.Exe.Process.LoopGoal.arg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.LoopGoal.arg

/-- info: 'IxCC.X86.Exe.Process.LoopGoal.write' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.LoopGoal.write

/-- info: 'IxCC.X86.Exe.Process.Cursor.slot_apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Cursor.slot_apart

/-- info: 'IxCC.X86.Exe.Process.Cursor.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Cursor.congr

/-- info: 'IxCC.X86.Exe.Process.file_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.file_outside

/-- info: 'IxCC.X86.Exe.Process.region_store_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.region_store_read

/-- info: 'IxCC.X86.Exe.Process.kept_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.kept_calls

/-- info: 'IxCC.X86.Exe.Process.fail_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.fail_report

/-- info: 'IxCC.X86.Exe.Process.returned_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.returned_fail

/-- info: 'IxCC.X86.Exe.Process.atLoop_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.atLoop_parts

/-- info: 'IxCC.X86.Exe.Process.atLoop_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.atLoop_next

/-- info: 'IxCC.X86.Exe.Process.cword0_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.cword0_apart

/-- info: 'IxCC.X86.Exe.Process.cursor_store_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.cursor_store_out

/-- info: 'IxCC.X86.Exe.Process.value_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.value_exit

/-- info: 'IxCC.X86.Exe.Process.value_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.value_request

/-- info: 'IxCC.X86.Exe.Process.value_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.value_write

/-- info: 'IxCC.X86.Exe.Process.arg_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.arg_done

/-- info: 'IxCC.X86.Exe.Process.arg_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.arg_next

/-- info: 'IxCC.X86.Exe.Process.arg_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.arg_end

/-- info: 'IxCC.X86.Exe.Process.value_arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.value_arg

/-- info: 'IxCC.X86.Exe.Process.decode_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.decode_none

/-- info: 'IxCC.X86.Exe.Process.after_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.after_split

/-- info: 'IxCC.X86.Exe.Process.observe_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.observe_value

/-- info: 'IxCC.X86.Exe.Process.iter_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.iter_value

/-- info: 'IxCC.X86.Exe.Process.iteration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.iteration

/-- info: 'IxCC.X86.Exe.Process.from_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.from_loop

/-- info: 'IxCC.X86.Exe.Process.glue_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.glue_at

/-- info: 'IxCC.X86.Exe.Process.iteration_calls_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.iteration_calls_at

/-! ### Start-up, the shell theorem and the executable theorems -/

/-- info: 'IxCC.X86.Exe.Process.slot_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.slot_add

/-- info: 'IxCC.X86.Exe.Process.cursor_of_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.cursor_of_block

/-- info: 'IxCC.X86.Exe.Process.entry_addr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.entry_addr

/-- info: 'IxCC.X86.Exe.Process.mrun_ifNz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.mrun_ifNz

/-- info: 'IxCC.X86.Exe.Process.confine_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.confine_run

/-- info: 'IxCC.X86.Exe.Process.out_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.out_low

/-- info: 'IxCC.X86.Exe.Process.setup_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.setup_run

/-- info: 'IxCC.X86.Exe.Process.args_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.args_run

/-- info: 'IxCC.X86.Exe.Process.start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.start

/-- info: 'IxCC.X86.Exe.Process.shell_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shell_sound

/-- info: 'IxCC.X86.Exe.Process.shell_unspecified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.shell_unspecified

/-- info: 'IxCC.X86.Exe.Process.map_fst_zipIdx' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.map_fst_zipIdx

/-- info: 'IxCC.X86.Exe.Process.lower_roots_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.lower_roots_fst

/-- info: 'IxCC.X86.Exe.Process.machine_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.machine_spec

/-- info: 'IxCC.X86.Exe.Process.head_linkedRoot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.head_linkedRoot

/-- info: 'IxCC.X86.Exe.Process.textSize_of_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.textSize_of_emit

/-- info: 'IxCC.X86.Exe.Process.textSize_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.textSize_eq

/-- info: 'IxCC.X86.Exe.Process.machine_linkedRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.machine_linkedRoot

/-- info: 'IxCC.X86.Exe.Process.machine_exe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.machine_exe_sound

/-- info: 'IxCC.X86.Exe.Process.toRecheck_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.toRecheck_spec

/-- info: 'IxCC.X86.Exe.Process.Rc.machine_exe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Rc.machine_exe_sound

/-- info: 'IxCC.X86.Exe.Process.machine_exe_unspecified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.machine_exe_unspecified

/-- info: 'IxCC.X86.Exe.Process.Rc.machine_exe_unspecified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.Rc.machine_exe_unspecified

/-! ### The loader specification, satisfiable -/

/-- info: 'IxCC.X86.Exe.Process.le_bootSlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.le_bootSlot

/-- info: 'IxCC.X86.Exe.Process.bootSlot_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.bootSlot_le

/-- info: 'IxCC.X86.Exe.Process.read64_of_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.read64_of_bytes

/-- info: 'IxCC.X86.Exe.Process.outside_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.outside_high

/-- info: 'IxCC.X86.Exe.Process.loaded_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Process.loaded_exists
