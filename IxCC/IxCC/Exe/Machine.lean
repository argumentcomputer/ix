import IxCC.Sem.Result

/-!
# Numeric state machines: the platform interface, version 0

A *numeric state machine* is a root `step : Nat → Nat → Nat` of a state and an
event, run by the generic shell that `ixcc compile --exe FILE --machine`
writes (`IxCC/X86/Exe/Machine.lean`). Its result word `w` is
`state * requestSpan + request`: the next state in the high bits (below
`2^52`, since a `Nat` word is below `2^63`), and the request field in the low
eleven, its kind in the low three bits and a byte above them:

| field | request | the next call's event |
| --- | --- | --- |
| `0` | `arg`: the next byte of the argument block (the arguments after the program's name, one after another) | the byte (1 to 255); `endOfArgument` (256) at the end of an argument, after which the next one starts; `endOfArguments` (257) when none is left |
| `1 + 8 b` | `write 1 b`: the byte `b` on standard output | `written` (0), or `notWritten` (1) if the platform refused it |
| `2 + 8 b` | `write 2 b`: the byte `b` on standard error | the same |
| `3 + 8 c` | `exit c`: the end of the process with status `c` | none |
| anything else | outside version 0 (kinds 4 to 7 are kept for `read` and the clock) | none: the shell ends the run with `statusRequest` |

The first call gets state 0 and, as its event, the number of arguments.

Between calls nothing of the program lives on: the shell calls `cx_init`
before every call, so a state is a number and never a heap value (heap states
and byte arrays are later stages; `docs/standalone-executables-design.md`).
The parsing and rendering a program needs are Lean, compiled with it
(`IxCC/lib/IxccExe.lean`).
-/

namespace IxCC.Exe.Machine

open IxCC.Sem (Resource)

/-- A step's result word is `state * requestSpan + request`. -/
def requestSpan : Nat := 2048

/-- What a step asks the platform for. -/
inductive Request where
  /-- The next byte of the argument block. -/
  | arg
  /-- One byte on standard output (`fd = 1`) or standard error (`fd = 2`). -/
  | write (fd byte : Nat)
  /-- The end of the process with this status. -/
  | exit (code : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The request a field `r` (below `requestSpan`) asks for, if it is one of
version 0's (see the module note). -/
def Request.decode (r : Nat) : Option Request :=
  match r % 8 with
  | 0 => if r / 8 = 0 then some .arg else none
  | 1 => some (.write 1 (r / 8))
  | 2 => some (.write 2 (r / 8))
  | 3 => some (.exit (r / 8))
  | _ => none

/-- The field of a request. -/
def Request.encode : Request → Nat
  | .arg => 0
  | .write fd b => (if fd = 2 then 2 else 1) + 8 * b
  | .exit c => 3 + 8 * c

/-- A request version 0 can make: a write to 1 or 2 of a byte, an exit status
below 256. -/
def Request.Valid : Request → Prop
  | .arg => True
  | .write fd b => (fd = 1 ∨ fd = 2) ∧ b < 256
  | .exit c => c < 256

theorem Request.decode_encode {q : Request} (hq : q.Valid) : Request.decode q.encode = some q := by
  cases q with
  | arg => rfl
  | write fd b =>
    obtain ⟨hfd | hfd, -⟩ := hq <;> subst hfd <;> simp [encode, decode] <;> omega
  | exit c => simp [encode, decode]; omega

theorem Request.encode_lt {q : Request} (hq : q.Valid) : q.encode < requestSpan := by
  cases q with
  | arg => decide
  | write fd b =>
    obtain ⟨hfd | hfd, hb⟩ := hq <;> subst hfd <;> simp [encode, requestSpan] <;> omega
  | exit c => simp only [encode, requestSpan]; simp only [Valid] at hq; omega

theorem Request.decode_valid {r : Nat} {q : Request} (hr : r < requestSpan)
    (h : Request.decode r = some q) : q.Valid := by
  unfold decode at h
  unfold requestSpan at hr
  split at h
  · split at h <;> cases h; trivial
  all_goals (try (cases h; exact ⟨by simp, by omega⟩))
  · cases h; show r / 8 < 256; omega
  · cases h

/-- The next state and the request field of a result word. -/
def split (w : Nat) : Nat × Nat := (w / requestSpan, w % requestSpan)

/-! ## Events -/

/-- The answer to `arg` at the end of an argument. -/
def endOfArgument : Nat := 256
/-- The answer to `arg` when no argument is left. -/
def endOfArguments : Nat := 257
/-- The answer to a write the platform made. -/
def written : Nat := 0
/-- The answer to a write the platform refused. -/
def notWritten : Nat := 1

/-! ## The shell's own exit statuses

As `ixcc compile --exe`'s shell has them, with one more (`statusRequest`). A
program's own exit (`Request.exit`) can be any status from 0 to 255. -/

/-- A resource failure of `cx_init` or the step: `64 +` the wrapper's status. -/
def statusOf : Resource → Nat
  | .heap => 65
  | .stack => 66
  | .natOverflow => 67
/-- The step trapped (the wrapper's status 4). -/
def statusTrap : Nat := 68
/-- A call returned with its stack pointer moved, or an unknown status. -/
def statusAbi : Nat := 70
/-- The result word is not a `Nat`'s. -/
def statusNotValue : Nat := 71
/-- The request is outside version 0. -/
def statusRequest : Nat := 72
/-- A failure message could not be written. -/
def statusWriteFailed : Nat := 74
/-- The process could not be confined. -/
def statusConfine : Nat := 75

end IxCC.Exe.Machine
