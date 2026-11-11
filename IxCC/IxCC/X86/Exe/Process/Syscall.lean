import IxCC.X86.ByteEval

/-!
# The platform's system calls (a specification)

One of the three hypotheses of the shell theorem (with `Process.Loaded` and
`Process.Step`): what a Linux x86-64 system call does to the process, as a
relation from the state at a `syscall` instruction to the event it records and
the state after it. It transcribes:

- **the calling convention** (`syscall(2)`, "Architecture calling
  conventions", x86-64): the number in `rax`, the arguments in `rdi`, `rsi`,
  `rdx`, `r10`, `r8`, `r9`, the result in `rax`; the instruction itself
  writes `rcx` and `r11` (Intel SDM Vol. 2B, `SYSCALL`), and the kernel
  returns with every other register and the memory as they were, past the
  two-byte instruction;
- **the four calls the shell makes**, each with only what its manual page
  documents for the arguments the shell passes:
  - `prctl(PR_SET_NO_NEW_PRIVS, 1, …)` (`prctl(2)`; number 157, option 38)
    and `seccomp(SECCOMP_SET_MODE_FILTER, 0, prog)` (`seccomp(2)`; number 317,
    operation 1): any result, and nothing else changed (neither writes the
    caller's memory);
  - `write(fd, buf, count)` (`write(2)`; number 1): the `count` bytes at
    `buf` recorded, and a result that is a byte count no larger than `count`
    when it is non-negative as a signed word (a negative one is `-errno`);
  - `exit(status)` (`_exit(2)`; number 60): the process ends;
- **anything else**: any other number, or `prctl` and `seccomp` with other
  arguments, may do anything, including end the process (`other`).

**Not assumed**: that the confinement works (the theorem never relies on the
filter), that a write succeeds or writes all its bytes, that the flags
survive a call, or anything of a call the shell does not make. A signal that
ends the process (the filter's kill, `SIGPIPE`) ends its trace, which the
traces of `IxCC/X86/Exe/Process.lean` already allow: every prefix of a trace
is a trace.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

/-- `PR_SET_NO_NEW_PRIVS` (`prctl(2)`; `<linux/prctl.h>`). -/
def prSetNoNewPrivs : Word := 38

/-- `SECCOMP_SET_MODE_FILTER` (`seccomp(2)`; `<linux/seccomp.h>`). -/
def seccompSetModeFilter : Word := 1

/-- A system call the process makes, with its arguments and the platform's
answer. -/
inductive Sys where
  /-- `prctl(option, arg2, …)` (`prctl(2)`) and its result. -/
  | prctl (option arg2 result : Word)
  /-- `seccomp(operation, flags, args)` (`seccomp(2)`) and its result. -/
  | seccomp (operation flags args result : Word)
  /-- `write(fd, buf, count)` (`write(2)`): the `count` bytes at `buf`, and
  the result (how many of them it wrote, or `-errno`). -/
  | write (fd : Word) (bytes : List UInt8) (result : Word)
  /-- `exit(status)` (`_exit(2)`): the process ends with `status & 0xff`. -/
  | exit (status : Word)
  /-- Any other system call, by its number (the theorem shows none occurs). -/
  | other (number : Word)
  deriving DecidableEq, Repr

/-- The bytes `[a, a + n)` of a memory. -/
def slice (m : Memory) (a : Word) (n : Nat) : List UInt8 := (List.range n).map fun i => m.bytes (a + UInt64.ofNat i)

/-- After a system call that returns (Intel SDM, `SYSCALL`; `syscall(2)`):
`rax` the result, `rcx` and `r11` whatever the instruction and the kernel
leave there, the flags anything, every other register and the memory
unchanged, `rip` past the two-byte instruction. -/
def returned (s : ByteEval.State) (result rcx r11 : Word) (flags : ByteEval.Flags) : ByteEval.State :=
  { core := ((s.core.setReg .rax result).setReg .rcx rcx).setReg .r11 r11
    rip := s.rip + 2
    flags }

/-- The calls this specification describes (the shell's four, with the
arguments the shell passes to `prctl` and `seccomp`); every other is
`Syscall.other`. -/
def Documented (s : ByteEval.State) : Prop :=
  (s.core.readReg .rax = 157 ∧ s.core.readReg .rdi = prSetNoNewPrivs) ∨
  (s.core.readReg .rax = 317 ∧ s.core.readReg .rdi = seccompSetModeFilter ∧ s.core.readReg .rsi = 0) ∨
  s.core.readReg .rax = 1 ∨ s.core.readReg .rax = 60

/-- **The platform's system calls** (Linux x86-64; see the module note): from
the state at a `syscall`, the event and the state after it (`none`: the
process ended). The results are unconstrained but for `write`'s, whose
non-negative value is at most its count. -/
inductive Syscall : ByteEval.State → Sys → Option ByteEval.State → Prop
  /-- `prctl(PR_SET_NO_NEW_PRIVS, arg2, …)`: any result. -/
  | prctl {s : ByteEval.State} {result rcx r11 : Word} {flags : ByteEval.Flags}
      (h : s.core.readReg .rax = 157) (hopt : s.core.readReg .rdi = prSetNoNewPrivs) :
      Syscall s (.prctl (s.core.readReg .rdi) (s.core.readReg .rsi) result) (some (returned s result rcx r11 flags))
  /-- `seccomp(SECCOMP_SET_MODE_FILTER, 0, args)`: any result. -/
  | seccomp {s : ByteEval.State} {result rcx r11 : Word} {flags : ByteEval.Flags}
      (h : s.core.readReg .rax = 317) (hop : s.core.readReg .rdi = seccompSetModeFilter)
      (hflags : s.core.readReg .rsi = 0) :
      Syscall s (.seccomp (s.core.readReg .rdi) (s.core.readReg .rsi) (s.core.readReg .rdx) result)
        (some (returned s result rcx r11 flags))
  /-- `write(fd, buf, count)`: the bytes at `buf` recorded; a non-negative
  result is at most `count`. -/
  | write {s : ByteEval.State} {result rcx r11 : Word} {flags : ByteEval.Flags}
      (h : s.core.readReg .rax = 1)
      (hcount : result.toNat < 2 ^ 63 → result.toNat ≤ (s.core.readReg .rdx).toNat) :
      Syscall s (.write (s.core.readReg .rdi) (slice s.core.memory (s.core.readReg .rsi) (s.core.readReg .rdx).toNat)
        result) (some (returned s result rcx r11 flags))
  /-- `exit(status)`: the process ends. -/
  | exit {s : ByteEval.State} (h : s.core.readReg .rax = 60) : Syscall s (.exit (s.core.readReg .rdi)) none
  /-- Any other call: anything. -/
  | other {s : ByteEval.State} {after : Option ByteEval.State} (h : ¬ Documented s) :
      Syscall s (.other (s.core.readReg .rax)) after

end IxCC.X86.Exe.Process
