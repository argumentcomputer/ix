import IxCC.Sem.Result
import IxCC.Sem.Simulation

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

Below the interface: the session model (`Config`, `Event`, `Reaches`, `Last`,
`Performs`), its refinement from a per-call refinement (`Performs.refines`,
and `Performs.refines_prefix`, which ties the source's going wrong to a prefix
of the trace), its monotonicity in the calls (`Performs.mono`), and the model
as a function for tests (`runFor`, `runFor_performs`). The
session theorem over the linked object is `IxCC/Exe/Machine/Sound.lean`'s.
-/

set_option autoImplicit false

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


/-! ## The session model

What a machine's process does, as finite traces of platform events with the
environment's answers, for any relation `call s e r` that gives the step's
possible outcomes on state `s` and event `e`. `IxCC/Exe/Machine/Sound.lean`
instantiates `call` with the linked object's calls and with the source's,
and proves the first refines the second (`session_sound`). -/

open IxCC.Sem (Result Obs)

/-- What the process does at one call, seen from outside: the platform event
with the environment's answer. -/
inductive Event where
  /-- An `arg` request and its answer (a byte, `endOfArgument` or
  `endOfArguments`). -/
  | arg (answer : Nat)
  /-- A one-byte write and whether the platform wrote it. -/
  | write (fd byte : Nat) (ok : Bool)
  /-- The program's exit with this status. -/
  | exit (code : Nat)
  /-- The shell's report of a failure: its message to standard error, then an
  exit with `status` (74 if the platform refused the message). -/
  | fail (status : Nat) (reported : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Between two calls: the state, the next call's event, and what is left of
the argument block (the current argument's remaining bytes first). -/
structure Config where
  state : Nat
  event : Nat
  args : List (List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The first call: state 0, the event the number of arguments. -/
def Config.initial (args : List (List Nat)) : Config := ⟨0, args.length, args⟩

/-- The answer to `arg`, and what is left of the block. -/
def nextArg : List (List Nat) → Nat × List (List Nat)
  | [] => (endOfArguments, [])
  | [] :: rest => (endOfArgument, rest)
  | (b :: bs) :: rest => (b, bs :: rest)

/-- The calls a session may make: `call s e r` when a call of the step on
state `s` and event `e` can have outcome `r`. -/
abbrev Call := Nat → Nat → Result (Option Obs) → Prop

/-- `Reaches call c t c'`: from `c` the process makes calls that return a
`Nat` whose request is `arg` or a write, performs them with events `t`, and is
about to call again at `c'`. -/
inductive Reaches (call : Call) : Config → List Event → Config → Prop
  | refl (c : Config) : Reaches call c [] c
  | arg {c c' : Config} {w : Nat} {rest : List Event}
      (hc : call c.state c.event (.ok (some (.nat w))))
      (hq : Request.decode (split w).2 = some .arg)
      (hr : Reaches call ⟨(split w).1, (nextArg c.args).1, (nextArg c.args).2⟩ rest c') :
      Reaches call c (.arg (nextArg c.args).1 :: rest) c'
  | write {c c' : Config} {w fd b : Nat} {ok : Bool} {rest : List Event}
      (hc : call c.state c.event (.ok (some (.nat w))))
      (hq : Request.decode (split w).2 = some (.write fd b))
      (hr : Reaches call ⟨(split w).1, if ok then written else notWritten, c.args⟩ rest c') :
      Reaches call c (.write fd b ok :: rest) c'

/-- `Last call c ev`: the call at `c` ends the process with event `ev`. -/
inductive Last (call : Call) (c : Config) : Event → Prop
  | exit {w code : Nat} (hc : call c.state c.event (.ok (some (.nat w))))
      (hq : Request.decode (split w).2 = some (.exit code)) : Last call c (.exit code)
  | request {w : Nat} {b : Bool} (hc : call c.state c.event (.ok (some (.nat w))))
      (hq : Request.decode (split w).2 = none) : Last call c (.fail statusRequest b)
  | notValue {o : Option Obs} {b : Bool} (hc : call c.state c.event (.ok o))
      (ho : ∀ w, o ≠ some (.nat w)) : Last call c (.fail statusNotValue b)
  | resource {f : Sem.Resource} {b : Bool} (hc : call c.state c.event (.resource f)) :
      Last call c (.fail (statusOf f) b)
  | trap {b : Bool} (hc : call c.state c.event .trap) : Last call c (.fail statusTrap b)

/-- A finite trace the process performs from `c`: it is still running after
`t`, or `t` ends with the event of the call that ended it. -/
def Performs (call : Call) (c : Config) (t : List Event) : Prop :=
  (∃ c', Reaches call c t c') ∨ ∃ t₀ c' ev, t = t₀ ++ [ev] ∧ Reaches call c t₀ c' ∧ Last call c' ev

/-- What a per-call correctness theorem gives: a value the object's call
returns is one the source's call returns, or the source goes wrong (`bad`)
there; an object call that goes wrong is one where the source goes wrong. -/
structure CallRefines (obj src : Call) (bad : Nat → Nat → Prop) : Prop where
  ok : ∀ {s e : Nat} {o : Option Obs}, obj s e (.ok o) → src s e (.ok o) ∨ bad s e
  wrong : ∀ {s e : Nat} {r : Result (Option Obs)}, obj s e r → r.GoesWrong → bad s e

theorem Reaches.refines {obj src : Call} {bad : Nat → Nat → Prop} (h : CallRefines obj src bad)
    {c c' : Config} {t : List Event} (ho : Reaches obj c t c') :
    Reaches src c t c' ∨ ∃ t₀ c₀, Reaches src c t₀ c₀ ∧ bad c₀.state c₀.event := by
  induction ho with
  | refl c => exact .inl (.refl c)
  | arg hc hq _ ih =>
    rcases h.ok hc with hs | hb
    · rcases ih with hr | ⟨t₀, c₀, hr, hb⟩
      · exact .inl (.arg hs hq hr)
      · exact .inr ⟨_, c₀, .arg hs hq hr, hb⟩
    · exact .inr ⟨[], _, .refl _, hb⟩
  | write hc hq _ ih =>
    rcases h.ok hc with hs | hb
    · rcases ih with hr | ⟨t₀, c₀, hr, hb⟩
      · exact .inl (.write hs hq hr)
      · exact .inr ⟨_, c₀, .write hs hq hr, hb⟩
    · exact .inr ⟨[], _, .refl _, hb⟩

/-- **The session refines** (for any per-call relation): every trace the
object's session performs is one the source's session performs on the same
answers; or it is a prefix the source performs followed by a resource
failure; or the source goes wrong at a call its own session reaches. -/
theorem Performs.refines {obj src : Call} {bad : Nat → Nat → Prop} (h : CallRefines obj src bad)
    {c : Config} {t : List Event} (ho : Performs obj c t) :
    Performs src c t ∨
    (∃ t₀ c' f b, t = t₀ ++ [.fail (statusOf f) b] ∧ Reaches src c t₀ c') ∨
    ∃ t₀ c', Reaches src c t₀ c' ∧ bad c'.state c'.event := by
  rcases ho with ⟨c', hr⟩ | ⟨t₀, c', ev, rfl, hr, hl⟩
  · rcases hr.refines h with hs | hb
    · exact .inl (.inl ⟨c', hs⟩)
    · exact .inr (.inr hb)
  · rcases hr.refines h with hs | hb
    · cases hl with
      | exit hc hq =>
        rcases h.ok hc with hc' | hb
        · exact .inl (.inr ⟨t₀, c', _, rfl, hs, .exit hc' hq⟩)
        · exact .inr (.inr ⟨t₀, c', hs, hb⟩)
      | request hc hq =>
        rcases h.ok hc with hc' | hb
        · exact .inl (.inr ⟨t₀, c', _, rfl, hs, .request hc' hq⟩)
        · exact .inr (.inr ⟨t₀, c', hs, hb⟩)
      | notValue hc hv =>
        rcases h.ok hc with hc' | hb
        · exact .inl (.inr ⟨t₀, c', _, rfl, hs, .notValue hc' hv⟩)
        · exact .inr (.inr ⟨t₀, c', hs, hb⟩)
      | resource _ => exact .inr (.inl ⟨t₀, c', _, _, rfl, hs⟩)
      | trap hc => exact .inr (.inr ⟨t₀, c', hs, h.wrong hc trivial⟩)
    · exact .inr (.inr hb)

/-- `Reaches.refines`, with the prefix of the trace along which the source
reaches the call where it goes wrong. -/
theorem Reaches.refines_prefix {obj src : Call} {bad : Nat → Nat → Prop} (h : CallRefines obj src bad)
    {c c' : Config} {t : List Event} (ho : Reaches obj c t c') :
    Reaches src c t c' ∨ ∃ t₀ c₀, t₀ <+: t ∧ Reaches src c t₀ c₀ ∧ bad c₀.state c₀.event := by
  induction ho with
  | refl c => exact .inl (.refl c)
  | arg hc hq _ ih =>
    rcases h.ok hc with hs | hb
    · rcases ih with hr | ⟨t₀, c₀, hp, hr, hb⟩
      · exact .inl (.arg hs hq hr)
      · exact .inr ⟨_, c₀, List.cons_prefix_cons.2 ⟨rfl, hp⟩, .arg hs hq hr, hb⟩
    · exact .inr ⟨[], _, List.nil_prefix, .refl _, hb⟩
  | write hc hq _ ih =>
    rcases h.ok hc with hs | hb
    · rcases ih with hr | ⟨t₀, c₀, hp, hr, hb⟩
      · exact .inl (.write hs hq hr)
      · exact .inr ⟨_, c₀, List.cons_prefix_cons.2 ⟨rfl, hp⟩, .write hs hq hr, hb⟩
    · exact .inr ⟨[], _, List.nil_prefix, .refl _, hb⟩

/-- **The session refines, with the prefix**: `Performs.refines` whose third
outcome says the source goes wrong at a call it reaches on the answers of a
prefix of this trace (`t₀ <+: t`), not of some trace. -/
theorem Performs.refines_prefix {obj src : Call} {bad : Nat → Nat → Prop} (h : CallRefines obj src bad)
    {c : Config} {t : List Event} (ho : Performs obj c t) :
    Performs src c t ∨
    (∃ t₀ c' f b, t = t₀ ++ [.fail (statusOf f) b] ∧ Reaches src c t₀ c') ∨
    ∃ t₀ c', t₀ <+: t ∧ Reaches src c t₀ c' ∧ bad c'.state c'.event := by
  rcases ho with ⟨c', hr⟩ | ⟨t₀, c', ev, rfl, hr, hl⟩
  · rcases hr.refines_prefix h with hs | hb
    · exact .inl (.inl ⟨c', hs⟩)
    · exact .inr (.inr hb)
  · rcases hr.refines_prefix h with hs | ⟨t₁, c₁, hp, hr₁, hb⟩
    · have hpre : t₀ <+: t₀ ++ [ev] := List.prefix_append _ _
      cases hl with
      | exit hc hq =>
        rcases h.ok hc with hc' | hb
        · exact .inl (.inr ⟨t₀, c', _, rfl, hs, .exit hc' hq⟩)
        · exact .inr (.inr ⟨t₀, c', hpre, hs, hb⟩)
      | request hc hq =>
        rcases h.ok hc with hc' | hb
        · exact .inl (.inr ⟨t₀, c', _, rfl, hs, .request hc' hq⟩)
        · exact .inr (.inr ⟨t₀, c', hpre, hs, hb⟩)
      | notValue hc hv =>
        rcases h.ok hc with hc' | hb
        · exact .inl (.inr ⟨t₀, c', _, rfl, hs, .notValue hc' hv⟩)
        · exact .inr (.inr ⟨t₀, c', hpre, hs, hb⟩)
      | resource _ => exact .inr (.inl ⟨t₀, c', _, _, rfl, hs⟩)
      | trap hc => exact .inr (.inr ⟨t₀, c', hpre, hs, h.wrong hc trivial⟩)
    · exact .inr (.inr ⟨t₁, c₁, hp.trans (List.prefix_append _ _), hr₁, hb⟩)

/-! ## More calls

A session over calls `c₁` is one over any calls that include them. -/

theorem Reaches.mono {c₁ c₂ : Call} (h : ∀ s e r, c₁ s e r → c₂ s e r) {c c' : Config} {t : List Event}
    (hr : Reaches c₁ c t c') : Reaches c₂ c t c' := by
  induction hr with
  | refl c => exact .refl c
  | arg hc hq _ ih => exact .arg (h _ _ _ hc) hq ih
  | write hc hq _ ih => exact .write (h _ _ _ hc) hq ih

theorem Last.mono {c₁ c₂ : Call} (h : ∀ s e r, c₁ s e r → c₂ s e r) {c : Config} {ev : Event}
    (hl : Last c₁ c ev) : Last c₂ c ev := by
  cases hl with
  | exit hc hq => exact .exit (h _ _ _ hc) hq
  | request hc hq => exact .request (h _ _ _ hc) hq
  | notValue hc hv => exact .notValue (h _ _ _ hc) hv
  | resource hc => exact .resource (h _ _ _ hc)
  | trap hc => exact .trap (h _ _ _ hc)

theorem Performs.mono {c₁ c₂ : Call} (h : ∀ s e r, c₁ s e r → c₂ s e r) {c : Config} {t : List Event}
    (hp : Performs c₁ c t) : Performs c₂ c t := by
  rcases hp with ⟨c', hr⟩ | ⟨t₀, c', ev, rfl, hr, hl⟩
  · exact .inl ⟨c', hr.mono h⟩
  · exact .inr ⟨t₀, c', ev, rfl, hr.mono h, hl.mono h⟩

/-! ## The model as a function

`runFor` runs the model for a function of the calls, so a test can compare
the model's trace with the executable's and with Lean's transcript;
`runFor_performs` says the trace it gives is one the model allows. -/

/-- The `Nat` of a result, if it is one. -/
def natOf : Option Obs → Option Nat
  | some (.nat w) => some w
  | _ => none

theorem natOf_some {o : Option Obs} {w : Nat} (h : natOf o = some w) : o = some (.nat w) := by
  unfold natOf at h
  split at h <;> simp_all

theorem natOf_none {o : Option Obs} (h : natOf o = none) : ∀ w, o ≠ some (.nat w) := by
  intro w hw
  subst hw
  simp [natOf] at h

/-- At most `n` calls of `call` from `c`, the platform answering every write
with `ok` and writing every failure message: the events, one per call. A call
that times out or is stuck ends the list without an event. -/
def runFor (call : Nat → Nat → Result (Option Obs)) (ok : Bool) : Nat → Config → List Event
  | 0, _ => []
  | n + 1, c =>
    match call c.state c.event with
    | .ok o =>
      match natOf o with
      | some w =>
        match Request.decode (split w).2 with
        | some .arg =>
          .arg (nextArg c.args).1 :: runFor call ok n ⟨(split w).1, (nextArg c.args).1, (nextArg c.args).2⟩
        | some (.write fd b) =>
          .write fd b ok :: runFor call ok n ⟨(split w).1, if ok then written else notWritten, c.args⟩
        | some (.exit code) => [.exit code]
        | none => [.fail statusRequest true]
      | none => [.fail statusNotValue true]
    | .resource f => [.fail (statusOf f) true]
    | .trap => [.fail statusTrap true]
    | .timeout => []
    | .stuck => []

theorem Performs.cons {call : Call} {c c' : Config} {ev : Event} {t : List Event}
    (step : ∀ t' c'', Reaches call c' t' c'' → Reaches call c (ev :: t') c'')
    (h : Performs call c' t) : Performs call c (ev :: t) := by
  rcases h with ⟨c'', hr⟩ | ⟨t₀, c'', e, rfl, hr, hl⟩
  · exact .inl ⟨c'', step _ _ hr⟩
  · exact .inr ⟨ev :: t₀, c'', e, rfl, step _ _ hr, hl⟩

theorem Performs.last {call : Call} {c : Config} {ev : Event} (h : Last call c ev) :
    Performs call c [ev] :=
  .inr ⟨[], c, ev, rfl, .refl c, h⟩

/-- The trace `runFor` gives is one the model performs, for the calls of
`call`. -/
theorem runFor_performs (call : Nat → Nat → Result (Option Obs)) (ok : Bool) :
    ∀ n c, Performs (fun s e r => call s e = r) c (runFor call ok n c) := by
  intro n
  induction n with
  | zero => intro c; exact .inl ⟨c, .refl c⟩
  | succ n ih =>
    intro c
    unfold runFor
    split
    · rename_i o hc
      split
      · rename_i w hw
        have hc' : call c.state c.event = .ok (some (.nat w)) := by rw [hc, natOf_some hw]
        split
        · rename_i hq
          exact (ih _).cons fun _ _ hr => .arg hc' hq hr
        · rename_i fd b hq
          exact (ih _).cons fun _ _ hr => .write hc' hq hr
        · rename_i code hq
          exact .last (.exit hc' hq)
        · rename_i hq
          exact .last (.request hc' hq)
      · rename_i hw
        exact .last (.notValue hc (natOf_none hw))
    · rename_i f hc
      exact .last (.resource hc)
    · rename_i hc
      exact .last (.trap hc)
    · exact .inl ⟨c, .refl c⟩
    · exact .inl ⟨c, .refl c⟩

end IxCC.Exe.Machine
