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
`fileBase` (its one read-and-execute `PT_LOAD`, at file offset 0), plus two
rules the table does not have:

- **`syscall`** (`0F 05`, Intel SDM Vol. 2B, `SYSCALL`) where the byte
  decoder decodes nothing: the platform's system call (`Process.Syscall`).
  Since the rule applies only where the decoder decodes nothing, a decodable
  instruction is never taken for a system call.
- **Nothing promised** (`unknown`) where the byte machine does not say what
  the processor does (`Unspecified`): where the byte decoder decodes nothing
  and the bytes are not that `syscall`, which includes every `rip` outside the
  file, and where the byte machine stops on a condition over a flag it leaves
  undefined. There the process may step to any state, with any system call or
  none, or end; so from such a state every list of system calls is a trace
  (`Trace.of_unspecified`). None of these is a fault of the processor: the
  decoder reads a subset of x86-64, and bytes it does not decode are in
  general instructions the processor runs; a branch on a flag the byte machine
  leaves undefined (`IMUL`'s `SF` and `ZF`, a shift's `OF`) does not fault,
  the flag has some value and the branch goes one way; and at a `rip` outside
  the file the processor runs whatever is mapped there (the zero tail of the
  file's last page, the vDSO, the vsyscall page) or faults.

**A memory fault or a divide error ends the process, silently.** Where the
byte machine faults on a memory access its permissions refuse, or on a
division (`#DE`), there is no step: the processor raises an exception (a page
or general-protection fault for the access) and the kernel sends the matching
signal (`SIGSEGV` or `SIGBUS`, `SIGFPE`), whose default action (`signal(7)`)
ends the process with no further system call. "No step" assumes exactly this:
that no handler for those signals is installed, so the default action
applies. The process starts with no handler (`execve(2)` resets handled
signals to their default; a fault's signal that the parent left ignored or
blocked is forced back to its default action by the kernel, Linux
`force_sig_fault`), and only a system call could install one (`rt_sigaction`,
a `Sys.other`). That the shell makes none is part of what the shell theorem
proves: every system call of a trace it allows is `prctl`, `seccomp`, `write`
or `exit` (`Process.Shows`), up to a call the model shows stuck, after which
it claims nothing of the trace anyway.

**Fetching from the file.** The processor fetches from memory; this
specification fetches from the file. The two agree while the memory at the
file's addresses holds the file: the loader maps it read-and-execute, so a
store of the process there faults (and a fault ends the process), and no
other process writes it (the environment, below). The shell proof also
carries this inside the model, for every permission assignment: `from_loop`'s
invariant `AtLoop` (`X86/Exe/Machine/Proof/Loop.lean`) includes that the
memory holds the file at every arrival at the loop before a call the model
shows stuck, since the shell's stores lie inside the zero-filled segments and
a call changes no byte outside its mapping (`Proof/Paths.lean`, `Kept`;
`Returned.frame`). That is a step of the proof, not part of any theorem's
statement.

**What the shell proof shows of the instructions run**, and where; none of it
is assumed here:
- the shell's bytes in the file decode as the shell's instructions: the check
  `Machine.writeChecked` runs on the written file (`Shell.check_sound`,
  carried in `CertifiedFor.shell`; used through `Shell.Valid` in
  `Proof/Steps.lean`);
- a call into the object that the per-call model does not show stuck runs
  only the byte machine's steps on the object's text, up to its return, its
  clock or a memory fault (`call_lifts`, `two_calls`, `Proof/Call.lean`); of a
  call the model shows stuck nothing is shown, and the theorems claim nothing
  after one;
- so the process reaches a state where this specification promises nothing,
  if at all, only after the system calls of a trace reaching a call the model
  shows stuck (`shell_unspecified`), that is, past the point where the source
  step goes wrong (`machine_exe_unspecified`); both are corollaries of the
  theorems' statements.

**The environment** this specification and `Process.Syscall` describe is a
process nothing outside it interferes with, the four assumptions
`Process.Syscall` lists. For instructions: no tracer is attached (a `ptrace`
tracer can change registers and memory between instructions and suppress a
fault's signal, so a memory fault need not end the process); no other process
writes this process's memory or the file it is mapped from (otherwise the
processor runs, and the shell reads, bytes this specification does not have);
and the process has one thread (`execve` leaves one and the shell creates
none; another thread would change the memory between instructions). The
fourth, no seccomp filter or supervisor installed by an ancestor changing the
shell's four system calls, concerns `Process.Syscall` only.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

/-- Where the file is mapped (its read-and-execute `PT_LOAD`). -/
def fetchBase : Word := UInt64.ofNat fileBase

/-- `syscall` (`0F 05`) at `rip` in the file. -/
def syscallAt (image : ByteArray) (rip : Word) : Prop :=
  image[(rip - fetchBase).toNat]? = some 0x0f ∧ image[(rip - fetchBase).toNat + 1]? = some 0x05

/-- **Where this specification promises nothing** (see the module note): the
byte decoder decodes nothing at `rip` and the bytes there are not the
`syscall` the `sys` rule covers (every `rip` outside the file is such a state,
`Unspecified.outside`), or the byte machine stops on a condition over a flag
it leaves undefined. None of these is a fault of the processor. -/
def Unspecified (image : ByteArray) (s : ByteEval.State) : Prop :=
  (Decode.decodeAt image (s.rip - fetchBase).toNat = none ∧ ¬ syscallAt image s.rip) ∨
  ∃ c, ByteEval.step image fetchBase s = .error (.undefinedCondition c)

/-- **The processor**: the byte machine fetching from the file `image`,
`syscall` where the byte decoder decodes nothing and the bytes are `0F 05`,
and anything where the byte machine does not say what the processor does.
From a state, the system call it makes (if any) and the state after it
(`none`: the process ended). A memory fault or a divide error is no step. -/
inductive Step (image : ByteArray) : ByteEval.State → Option Sys → Option ByteEval.State → Prop
  /-- An instruction of the byte machine. -/
  | byte {s s' : ByteEval.State} (h : ByteEval.step image fetchBase s = .ok s') : Step image s none (some s')
  /-- A system call. -/
  | sys {s : ByteEval.State} {ev : Sys} {after : Option ByteEval.State}
      (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
      (h : Syscall s ev after) : Step image s (some ev) after
  /-- Where the byte machine does not say what the processor does: any step,
  with any system call or none, to any state or to the end of the process. -/
  | unknown {s : ByteEval.State} {e : Option Sys} {after : Option ByteEval.State}
      (h : Unspecified image s) : Step image s e after

end IxCC.X86.Exe.Process
