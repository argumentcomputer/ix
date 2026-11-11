import IxCC.X86.Exe.Process.Loaded
import IxCC.X86.Exe.Process.Step
import IxCC.X86.Exe.Machine
import IxCC.X86.Linked
import IxCC.Rt.Procs.Entry

/-!
# The process of a machine executable, and what its trace denotes

The shell theorem (X0-P) is a statement about the process
`ixcc compile --exe FILE --machine` starts: its finite traces of system calls,
from the loader's post-state, under the platform's system calls. This module
holds its vocabulary; the platform itself is the three specification modules
beside it:

- `Process.Loaded` (`Process/Loaded.lean`): the loader's post-state, from the
  System V gABI and x86-64 psABI;
- `Process.Syscall` (`Process/Syscall.lean`): the system calls, from
  `syscall(2)` and the manual pages of the four calls the shell makes;
- `Process.Step` (`Process/Step.lean`): the processor, the byte machine
  fetching from the file with the `syscall` rule.

**Runs and traces.** `Run image s σ s'`: from `s` the process steps to `s'`,
making the system calls `σ` (with the platform's answers). `Trace image s σ`:
`σ` is the system calls of a run so far, or of a run whose last call ended
the process. A fault is no step, so it ends a trace; every prefix of a trace
is a trace.

**What a session event is, in system calls** (`Denotes`, for the session model
of `IxCC/Exe/Machine.lean`): `arg` is none (the shell answers it from the
argument block); `write fd b ok` is one `write(fd, [b])` whose result is 1
exactly when `ok`; `exit c` is `exit(c)`; `fail s b` is the failure's message
written to standard error in parts, then `exit(s)`, or `exit(74)` after a part
the platform refused (`Report`). Before the first event the shell confines
the process (`started`: `prctl` and `seccomp` returning 0); a refusal is its
own outcome (`Refused`).

**What the theorems say of a trace.** `Shows call` (for the object's calls)
and `Outcome src bad` (for the source's, where it goes wrong at `bad`), each
a disjunction stated in its docstring. `Shows.refines`: a per-call refinement
of the object's calls by the source's (`CallRefines`) turns `Shows` into
`Outcome`, through `Performs.refines_prefix`.

**Safety only**: nothing here says that a trace goes on.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Exe.Machine (Event Config Performs Reaches CallRefines statusConfine statusWriteFailed statusOf)

/-- The session model's calls (`X86.Exe.Call` is the writer's call site). -/
abbrev SessionCall := IxCC.Exe.Machine.Call

/-- The object `object` with roots `roots`: `cx_init` under `D`, the roots
from `site` (as `Recheck.Artifact.linkedAt` builds it). -/
def linkedOf (object : ByteArray) (roots : List Linked.Root) (D : Driver) (site : Driver.Site) : LinkedAt :=
  ⟨{ object, init := Rt.Procs.initSymbol, roots, driver := D }, site⟩

/-! ## Runs and traces -/

/-- A finite run of the process on file `image`: the system calls it makes,
and where it is. -/
inductive Run (image : ByteArray) : ByteEval.State → List Sys → ByteEval.State → Prop
  | refl (s : ByteEval.State) : Run image s [] s
  | step {s s₁ s' : ByteEval.State} {e : Option Sys} {σ : List Sys}
      (h : Step image s e (some s₁)) (r : Run image s₁ σ s') : Run image s (e.toList ++ σ) s'

/-- **The process's finite traces** from `s`: a run so far, or a run that
ended the process. -/
def Trace (image : ByteArray) (s : ByteEval.State) (σ : List Sys) : Prop :=
  (∃ s', Run image s σ s') ∨ ∃ σ₀ s' ev, σ = σ₀ ++ [ev] ∧ Run image s σ₀ s' ∧ Step image s' (some ev) none

theorem Run.trans {image : ByteArray} {s s₁ s₂ : ByteEval.State} {σ₁ σ₂ : List Sys}
    (h₁ : Run image s σ₁ s₁) (h₂ : Run image s₁ σ₂ s₂) : Run image s (σ₁ ++ σ₂) s₂ := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => rw [List.append_assoc]; exact .step h (ih h₂)

/-- A run of the byte machine is a run of the process with no system call. -/
theorem Run.ofByteRun {image : ByteArray} :
    ∀ (n : Nat) {s s' : ByteEval.State}, ByteEval.run image fetchBase n s = .ok s' → Run image s [] s'
  | 0, s, s', h => by cases h; exact .refl s
  | n + 1, s, s', h => by
    simp only [ByteEval.run, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      exact .step (.byte h₁) (Run.ofByteRun n h)

/-! ## What a session event is, in system calls -/

/-- A shell failure's message (`Machine.Failure.text`; none for a status no
failure has). -/
def messageOf (status : Nat) : List UInt8 :=
  match Machine.Failure.all.find? (fun f => f.status == status) with
  | some f => f.text.toUTF8.toList
  | none => []

/-- The system calls of a failure report: the message written to standard
error in parts (each `write(2, rest, n)` returning how many bytes it wrote),
then `exit(status)`; a part refused (zero or `-errno`) ends it with
`exit(74)` instead. The flag says whether the whole message was written. -/
inductive Report (status : Nat) : List UInt8 → Bool → List Sys → Prop
  | done : Report status [] true [.exit (UInt64.ofNat status)]
  | part {m : List UInt8} {r : Word} {b : Bool} {σ : List Sys} (hne : m ≠ [])
      (hr : 0 < r.toNat ∧ r.toNat ≤ m.length) (rest : Report status (m.drop r.toNat) b σ) :
      Report status m b (.write 2 m r :: σ)
  | refused {m : List UInt8} {r : Word} (hne : m ≠ []) (hr : r.toNat = 0 ∨ 2 ^ 63 ≤ r.toNat) :
      Report status m false [.write 2 m r, .exit (UInt64.ofNat statusWriteFailed)]

/-- **What a session event is, in system calls.** -/
inductive Denotes : Event → List Sys → Prop
  | arg (answer : Nat) : Denotes (.arg answer) []
  | write {fd b : Nat} {ok : Bool} {r : Word} (hr : r = 1 ↔ ok = true) :
      Denotes (.write fd b ok) [.write (UInt64.ofNat fd) [UInt8.ofNat b] r]
  | exit (code : Nat) : Denotes (.exit code) [.exit (UInt64.ofNat code)]
  | fail {s : Nat} {b : Bool} {σ : List Sys} (h : Report s (messageOf s) b σ) : Denotes (.fail s b) σ

/-- The system calls of a list of events, one after another. -/
inductive DenotesAll : List Event → List Sys → Prop
  | nil : DenotesAll [] []
  | cons {e : Event} {t : List Event} {σ ρ : List Sys} (he : Denotes e σ) (ht : DenotesAll t ρ) :
      DenotesAll (e :: t) (σ ++ ρ)

theorem DenotesAll.append {t₁ t₂ : List Event} {ρ₁ ρ₂ : List Sys} (h₁ : DenotesAll t₁ ρ₁)
    (h₂ : DenotesAll t₂ ρ₂) : DenotesAll (t₁ ++ t₂) (ρ₁ ++ ρ₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons he _ ih => rw [List.cons_append, List.append_assoc]; exact .cons he ih

theorem DenotesAll.split : ∀ {t₁ t₂ : List Event} {ρ : List Sys}, DenotesAll (t₁ ++ t₂) ρ →
    ∃ ρ₁ ρ₂, ρ = ρ₁ ++ ρ₂ ∧ DenotesAll t₁ ρ₁ ∧ DenotesAll t₂ ρ₂
  | [], _, ρ, h => ⟨[], ρ, rfl, .nil, h⟩
  | _ :: _, _, _, h => by
    cases h with
    | cons he ht =>
      obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := DenotesAll.split ht
      exact ⟨_ ++ ρ₁, ρ₂, (List.append_assoc _ _ _).symm, .cons he h₁, h₂⟩

/-- The system calls of a prefix of the events are a prefix of theirs. -/
theorem DenotesAll.prefix {t₀ t : List Event} {ρ : List Sys} (hp : t₀ <+: t) (h : DenotesAll t ρ) :
    ∃ ρ₀, ρ₀ <+: ρ ∧ DenotesAll t₀ ρ₀ := by
  obtain ⟨t₁, rfl⟩ := hp
  obtain ⟨ρ₀, ρ₁, rfl, h₀, -⟩ := h.split
  exact ⟨ρ₀, List.prefix_append _ _, h₀⟩

/-! ## What the theorems say of a trace -/

/-- The confinement, made: `prctl(PR_SET_NO_NEW_PRIVS, 1)` and
`seccomp(SECCOMP_SET_MODE_FILTER, 0, &prog)` both returning 0 (`data` the
read-only data's address; `prog` is `fprogAddr data`). -/
def started (data : Nat) : List Sys :=
  [.prctl prSetNoNewPrivs 1 0, .seccomp seccompSetModeFilter 0 (UInt64.ofNat (fprogAddr data)) 0]

/-- The confinement, refused: a prefix of `prctl` or `seccomp` returning
nonzero, then the report with status 75. -/
def Refused (data : Nat) (σ : List Sys) : Prop :=
  ∃ ρ b, Report statusConfine (messageOf statusConfine) b ρ ∧
    ((∃ r : Word, r ≠ 0 ∧ σ <+: .prctl prSetNoNewPrivs 1 r :: ρ) ∨
     (∃ r : Word, r ≠ 0 ∧
       σ <+: .prctl prSetNoNewPrivs 1 0 :: .seccomp seccompSetModeFilter 0 (UInt64.ofNat (fprogAddr data)) r :: ρ))

/-- **What the shell theorem says of a trace** `σ`, for the calls `call` of
the object: it is a prefix of the system calls of a trace the session model
performs on the same answers; or it has passed the system calls of a trace
that reaches a call the model shows stuck (after which the process is
unconstrained: the object went wrong); or the confinement was refused. -/
def Shows (call : SessionCall) (data : Nat) (args : List (List Nat)) (σ : List Sys) : Prop :=
  (∃ t ρ, Performs call (Config.initial args) t ∧ DenotesAll t ρ ∧ σ <+: started data ++ ρ) ∨
  (∃ t₀ c' ρ₀, Reaches call (Config.initial args) t₀ c' ∧ call c'.state c'.event .stuck ∧
    DenotesAll t₀ ρ₀ ∧ started data ++ ρ₀ <+: σ) ∨
  Refused data σ

/-- **What the executable theorem says of a trace**, for the source's calls
`src` and where it goes wrong (`bad`): a prefix of what the source step's
iteration does on the same answers; or of that followed by a resource
failure's report; or it has passed the system calls of a trace along which the
source's iteration reaches a call where the source goes wrong; or the
confinement was refused. -/
def Outcome (src : SessionCall) (bad : Nat → Nat → Prop) (data : Nat) (args : List (List Nat))
    (σ : List Sys) : Prop :=
  (∃ t ρ, Performs src (Config.initial args) t ∧ DenotesAll t ρ ∧ σ <+: started data ++ ρ) ∨
  (∃ t₀ c' f b ρ, Reaches src (Config.initial args) t₀ c' ∧
    DenotesAll (t₀ ++ [.fail (statusOf f) b]) ρ ∧ σ <+: started data ++ ρ) ∨
  (∃ t₀ c' ρ₀, Reaches src (Config.initial args) t₀ c' ∧ bad c'.state c'.event ∧
    DenotesAll t₀ ρ₀ ∧ started data ++ ρ₀ <+: σ) ∨
  Refused data σ

/-- **`Shows` for the object's calls gives `Outcome` for the source's**, from
a per-call refinement (`Performs.refines_prefix`; a trace that has not yet
passed the point where the source goes wrong is a prefix of what the source
does up to there). -/
theorem Shows.refines {obj src : SessionCall} {bad : Nat → Nat → Prop} (h : CallRefines obj src bad)
    {data : Nat} {args : List (List Nat)} {σ : List Sys} (hs : Shows obj data args σ) :
    Outcome src bad data args σ := by
  rcases hs with ⟨t, ρ, hp, hd, hσ⟩ | ⟨t₀, c', ρ₀, hr, hstuck, hd, hσ⟩ | hrefused
  · rcases hp.refines_prefix h with hp' | ⟨t₀, c', f, b, rfl, hr⟩ | ⟨t₀, c', hpre, hr, hb⟩
    · exact .inl ⟨t, ρ, hp', hd, hσ⟩
    · exact .inr (.inl ⟨t₀, c', f, b, ρ, hr, hd, hσ⟩)
    · obtain ⟨ρ₀, hρ, hd₀⟩ := hd.prefix hpre
      have h₁ : started data ++ ρ₀ <+: started data ++ ρ := (List.prefix_append_right_inj _).2 hρ
      rcases List.prefix_or_prefix_of_prefix hσ h₁ with hle | hge
      · exact .inl ⟨t₀, ρ₀, .inl ⟨c', hr⟩, hd₀, hle⟩
      · exact .inr (.inr (.inl ⟨t₀, c', ρ₀, hr, hb, hd₀, hge⟩))
  · rcases hr.refines_prefix h with hr' | ⟨t₁, c₁, hpre, hr₁, hb⟩
    · exact .inr (.inr (.inl ⟨t₀, c', ρ₀, hr', h.wrong hstuck trivial, hd, hσ⟩))
    · obtain ⟨ρ₁, hρ, hd₁⟩ := hd.prefix hpre
      exact .inr (.inr (.inl ⟨t₁, c₁, ρ₁, hr₁, hb, hd₁, ((List.prefix_append_right_inj _).2 hρ).trans hσ⟩))
  · exact .inr (.inr (.inr hrefused))

end IxCC.X86.Exe.Process
