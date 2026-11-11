import IxCC.X86.Exe.Process.Syscall
import IxCC.X86.Exe.Layout

/-!
# The processor (a specification)

One of the three hypotheses of the shell theorem (with `Process.Loaded` and
`Process.Syscall`): what one instruction of the process does. It is the byte
machine (`ByteEval.step`: the instruction table's rows through `Op.exec` and
the control rows, the semantics the trust ledger records as
`x86-v0-local-semantics` and the `x86-hardware` gate compares with the
processor), fetching from the executable file, which the loader maps at
`fileBase` (its one read-and-execute `PT_LOAD`, at file offset 0), plus one
rule the table does not have:

- **`syscall`** (`0F 05`, Intel SDM Vol. 2B, `SYSCALL`) where the byte
  decoder decodes nothing: the platform's system call (`Process.Syscall`).
  Since the rule applies only where the decoder decodes nothing, a decodable
  instruction is never taken for a system call.

**A fault ends the process, silently.** Where the byte machine faults (a
memory access its permissions refuse, bytes it does not decode that are not
`0F 05`, a condition on an undefined flag, a division error) there is no step:
the processor raises an exception and the kernel sends the matching signal
(`SIGSEGV`, `SIGILL`, `SIGFPE`), whose default action (`signal(7)`) ends the
process with no further system call. "A fault is no step" assumes exactly
this: that no handler for those signals is installed, so the default action
applies. The process starts with no handler (`execve(2)` resets handled
signals to their default; a fault's signal that the parent left ignored or
blocked is forced back to its default action by the kernel, Linux
`force_sig_fault`), and only a system call could install one
(`rt_sigaction`, a `Sys.other`). That the shell makes none is part of what the
shell theorem proves (X0-P's third part): every system call of a trace it
allows is `prctl`, `seccomp`, `write` or `exit` (`Process.Shows`); after a
call the model shows stuck it claims nothing of the trace anyway. With the
shell check's soundness and the call lemma (part two), a fault inside a call
ends the trace there (`Trace.nil_of_faults`).

**Not assumed**: that the object stays inside its text, or that the shell's
bytes decode as the shell's instructions; the shell theorem proves both (the
second from the check `Machine.writeChecked` runs on the written file). That
the process fetches from the file, not from its memory, is sound for the
executables the shell theorem covers because it also proves the file's bytes
in memory are never changed; outside the file nothing decodes, so a jump
there ends the trace.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

/-- Where the file is mapped (its read-and-execute `PT_LOAD`). -/
def fetchBase : Word := UInt64.ofNat fileBase

/-- `syscall` (`0F 05`) at `rip` in the file. -/
def syscallAt (image : ByteArray) (rip : Word) : Prop :=
  image[(rip - fetchBase).toNat]? = some 0x0f ∧ image[(rip - fetchBase).toNat + 1]? = some 0x05

/-- **The processor**: the byte machine fetching from the file `image`, and
`syscall` where the byte decoder decodes nothing and the bytes are `0F 05`.
From a state, the system call it makes (if any) and the state after it
(`none`: the process ended). A fault is no step. -/
inductive Step (image : ByteArray) : ByteEval.State → Option Sys → Option ByteEval.State → Prop
  /-- An instruction of the byte machine. -/
  | byte {s s' : ByteEval.State} (h : ByteEval.step image fetchBase s = .ok s') : Step image s none (some s')
  /-- A system call. -/
  | sys {s : ByteEval.State} {ev : Sys} {after : Option ByteEval.State}
      (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
      (h : Syscall s ev after) : Step image s (some ev) after

end IxCC.X86.Exe.Process
