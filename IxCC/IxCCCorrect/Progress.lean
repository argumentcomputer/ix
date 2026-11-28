import IxCC.Shape.Progress
import IxCK.Kernel.Denotes

/-!
# Source progress: the targets (`IxCCCorrect.Progress`)

The statements `NeverStuck`, `NeverWrong` and the lemmas by which each discharges the
"source goes wrong" disjunct of the compiler's theorems are in production,
`IxCC.Shape.Progress` (namespace `IxCC.Progress`), and are re-exported here under their
names in `IxCC.Correct`. What stays is what quantifies over the kernel's model or states a
target: `Accepted`, `NatInput`, `SafetyProgress`, `SafetyProgressGiven`, `FunctionalProgress`.
-/

set_option autoImplicit false

namespace IxCC.Correct

export IxCC.Progress (
  Source NeverStuck NeverWrong NeverWrong.neverStuck viewed_stuck_iff neverStuck_iff
  neverWrong_iff not_goesWrong_iff rc_not_goesWrong_iff not_stuck_of_refinesOn
  recheck_sound_of_neverWrong recheck_not_stuck recheck_not_stuck_at
  rc_sound_of_neverWrong rc_not_stuck rc_not_stuck_at plainExeOutcome_mono
  plain_exe_sound_of_neverWrong rc_plain_exe_sound_of_neverWrong
  plain_exe_specified_of_neverStuck rc_plain_exe_specified_of_neverStuck)

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.X86.Exe.Plain
open IxCC.Sem (Lang Obs Result)
open IxCC.Lam.Erase.Proof (CheckedProgram)


/-! ## The targets -/

/-- **What a checker has established when it accepts.** Ingress: the bytes decode, and
the certified kernel accepts the whole environment at `limits`
(`Recheck.ingress`, through `Src.KernelFront.accept`), giving the program keyed to
the kernel's reading. The front half: under some certificate, the table, the
annotation, lazification, erasure and the passes down to Lir accept the program
(`Recheck.runLir`). Both are decisions of functions the checker runs; the
certificate and the sidecar are bound existentially, as in `CorrectToday`. -/
structure Accepted (limits : Ix.Kernel.Admission.Limits) (inp : Recheck.Input)
    (f : Recheck.Front) : Prop where
  ingress : ∃ (envBytes : ByteArray) (equations : Lean.Json) (roots : List String),
    Recheck.ingress envBytes equations roots limits = .ok inp
  front : ∃ (cfg : Recheck.Config) (c : Recheck.Cert),
    Recheck.runLir (cfg.forInput inp) inp.program c = .ok f

/-- **The inputs progress is stated on**: root `i.1` of the checked source, declared
without universe parameters, applied to exactly as many `Nat` literals as it declares
parameters, each of which it declares of type `Nat` (`Recheck.natDomain`, what
`CompileClaim.rootParamsAllNat` decides). On any other input the literals SrcEval is
handed are not of the parameters' types, and nothing is claimed. -/
def NatInput (src : Src.Program) (i : Nat × List Nat) : Prop :=
  ∃ (addr : Ixon.Address) (c : Src.CId) (d : Src.Decl), src.roots[i.1]? = some (addr, c) ∧
    src.decl? c = some d ∧ d.lvls = 0 ∧ d.type.pis.1.length = i.2.length ∧
    (d.type.pis.1.all fun b => Recheck.natDomain src b.2) = true

/-- **Source progress, safety strength, for a checker decision `ok`** (target, not
proved): on everything the checker accepts and `ok` accepts, the viewed source is
never stuck on the inputs of its roots. With it, `recheck_not_stuck` and
`plain_exe_specified_of_neverStuck` hold of every accepted program with no hypothesis
about the source. No model of the environment is assumed. That is right for a
decision that admits no fixed-width word entry: every other stuck point of SrcEval is
a matter of the shapes of values. F6w is stuck on a tower whose number is out of
range, which only a false proof builds, so a decision that admits word entries can be
discharged only where the erased proofs are true: `SafetyProgressGiven`
(`plans/PROGRESS.md`, 2 and 3). -/
def SafetyProgress (ok : Recheck.Input → Recheck.Front → Bool) : Prop :=
  ∀ (limits : Ix.Kernel.Admission.Limits) (inp : Recheck.Input) (f : Recheck.Front),
    Accepted limits inp f → ok inp f = true →
    ∀ i, NatInput f.src i → NeverStuck f.source i

/-- **Source progress, safety strength, where a set theory exists** (target, not
proved): `SafetyProgress` under the hypothesis `FunctionalProgress` carries. It is the
form for a decision that admits a construct whose stuck point depends on the truth of
an erased proof (F6w, a word's range). -/
def SafetyProgressGiven.{w} (ok : Recheck.Input → Recheck.Front → Bool) : Prop :=
  (∃ V : Type w, Nonempty (Ix.Kernel.SetTheory V)) → SafetyProgress ok

/-- **A canonical form of a root's declared result type**: at a root declared to return the
pinned `Nat`, a literal; at a root declared to return another constant `D`, a value of a
constructor of `D` without parameters and fields. What `Tier1` needs SrcEval to return, beyond
not going wrong: the compiler's view also accepts values that are not of the root's type
(`IxCCCorrect.Compose`, link G1). -/
def CanonValue (src : Src.Program) (c : Src.CId) (v : Src.Value) : Prop :=
  match src.decl? c with
  | some d =>
    match (Src.Term.pis d.type).2 with
    | .const r [] =>
      if some r = src.known.nat then ∃ n : Nat, v = .lit n
      else ∃ (c' : Src.CId) (ls : Src.Levels) (ps : List Src.Slot) (s : Bool) (lv i : Nat)
          (ty : Src.Term), v = .con c' ls ps [] ∧ src.decl? c' = some (.ctor s lv r i 0 0 ty)
    | _ => False
  | none => False

/-- **SrcEval returns canonical forms at root `i.1`** on the literals `i.2`. -/
def ReturnsCanonAt (src : Src.Program) (i : Nat × List Nat) : Prop :=
  ∀ (addr : Ixon.Address) (c : Src.CId) (k : Nat) (v : Src.Value),
    src.roots[i.1]? = some (addr, c) → Src.run src k c (i.2.map Src.Value.lit) = .ok v →
      CanonValue src c v

/-- **Source progress, functional strength, for a checker decision `ok`** (target, not
proved): as `SafetyProgress`, with "never traps" added, and SrcEval returning canonical forms
(owner-approved P1: `NeverWrong` alone does not give `Tier1`, the view being lossy). A trap is an
empty recursor reached with a relevant major premise, so excluding it is the statement that no
member of an empty family's denotation exists, which a proof through the model can
conclude only if a model exists: the hypothesis that some set theory with the
kernel's universes exists is explicit here (it is `VSet.OmegaUniverses` for the
standard carrier, `IxCK/Kernel/SetTheory/FiniteChain.lean`). -/
def FunctionalProgress.{w} (ok : Recheck.Input → Recheck.Front → Bool) : Prop :=
  (∃ V : Type w, Nonempty (Ix.Kernel.SetTheory V)) →
  ∀ (limits : Ix.Kernel.Admission.Limits) (inp : Recheck.Input) (f : Recheck.Front),
    Accepted limits inp f → ok inp f = true →
    ∀ i, NatInput f.src i → NeverWrong f.source i ∧ ReturnsCanonAt f.src i

/-- The functional strength gives the safety strength, where a set theory exists. -/
theorem FunctionalProgress.safety.{w} {ok : Recheck.Input → Recheck.Front → Bool}
    (h : FunctionalProgress.{w} ok) : SafetyProgressGiven.{w} ok :=
  fun hV limits inp f hacc hok i hi => (h hV limits inp f hacc hok i hi).1.neverStuck

/-- A decision that needs no model has the conditional form too. -/
theorem SafetyProgress.given.{w} {ok : Recheck.Input → Recheck.Front → Bool}
    (h : SafetyProgress ok) : SafetyProgressGiven.{w} ok :=
  fun _ => h

end IxCC.Correct
