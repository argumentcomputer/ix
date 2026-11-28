import IxCC.Exe.Plain.Exe

/-! Exact axiom fences for:
1. Hardened `.ix.cert` v1 ELF64 trailer invariants (`X86.Exe.Cert.*`);
2. Certified executable verification (`Exe.Cert.verifyExeBytes_sound`);
3. Plain `--exe` unified shell & process theorems (`X86.Exe.Plain.*`, `Exe.Plain.*`);
4. Unified `verify-exe` → x86-64 process execution theorems
   (`verifyExeBytes_plain_sound`, `verifyExeBytes_machine_sound`). -/

/-- info: 'IxCC.X86.Exe.Cert.checkTrailer_attachTrailer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Cert.checkTrailer_attachTrailer

/-- info: 'IxCC.X86.Exe.Cert.checkTrailer_core_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Cert.checkTrailer_core_eq

/-- info: 'IxCC.X86.Exe.Cert.checkTrailer_sled_int3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Cert.checkTrailer_sled_int3

/-- info: 'IxCC.X86.Exe.Cert.checkTrailer_payload_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Cert.checkTrailer_payload_eq

/-- info: 'IxCC.X86.Exe.Cert.checkTrailer_flush_eof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Cert.checkTrailer_flush_eof

/-- info: 'IxCC.Exe.Cert.verifyExeBytes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Cert.verifyExeBytes_sound

/-- info: 'IxCC.X86.Exe.Plain.plain_shell_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Plain.plain_shell_sound

/-- info: 'IxCC.X86.Exe.Plain.plain_shell_unspecified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Exe.Plain.plain_shell_unspecified

/-- info: 'IxCC.Exe.Plain.plain_exe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Plain.plain_exe_sound

/-- info: 'IxCC.Exe.Plain.plain_exe_unspecified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Plain.plain_exe_unspecified

/-- info: 'IxCC.Exe.Plain.Rc.plain_exe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Plain.Rc.plain_exe_sound

/-- info: 'IxCC.Exe.Plain.Rc.plain_exe_unspecified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Plain.Rc.plain_exe_unspecified

/-- info: 'IxCC.Exe.Plain.verifyExeBytes_plain_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Plain.verifyExeBytes_plain_sound

/-- info: 'IxCC.Exe.Plain.verifyExeBytes_machine_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Exe.Plain.verifyExeBytes_machine_sound
