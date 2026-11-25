import IxCC.Exe.Plain.Exe
import IxCC.Recheck.Produce

/-!
# Source progress: the statements, and what they discharge (`IxCC.Shape.Progress`)

The model-free half of the progress statements, in production so that the shape check
(`IxCC.Shape.Src`) and `compile` can use them; the targets that quantify over the kernel's
model (`SafetyProgress`, `FunctionalProgress`) stay in `IxCCCorrect.Progress`, which re-exports
everything here under `IxCC.Correct`.

Every top-level theorem of the compiler carries a disjunct `Front.GoesWrong`
(`IxCC.Recheck.Proof.Sound`): the checked source is stuck or traps at some clock,
or returns a value its root's view rejects. Under it the object is unconstrained.
This module states what removes it, in the two strengths the tiers of
`IxCC.Correct.Correct` (in `IxCCCorrect`) need, and proves that each strength discharges the disjunct
in the existing theorems.

* `NeverStuck s i` (safety strength, tier 2): the **viewed** source is stuck at no
  clock. A trap is allowed: every pass keeps a trap (`Sem.Result.Refines.trap`), and
  the shell reports one inside the system-call envelope. Because a result the root's
  view rejects is `stuck` in the viewed source (`Sem.viewResult`), this already
  includes that every returned value reads back at the root's type
  (`neverStuck_iff`).
* `NeverWrong s i` (functional strength, tier 1): the viewed source neither is
  stuck nor traps at any clock. It is `¬ Front.GoesWrong` (`not_goesWrong_iff`).

What they give, with no hypothesis left about the source:

| Theorem | From | Conclusion |
| --- | --- | --- |
| `recheck_sound_of_neverWrong`, `rc_sound_of_neverWrong` | `Recheck.sound`, `RcReplay.sound` | a value the object returns is the view of a value SrcEval returns; the object goes wrong at no clock |
| `recheck_not_stuck`, `rc_not_stuck` (and `_at`) | `Recheck.object_refines`, `RcReplay.object_refines` | the object is stuck at no clock |
| `plain_exe_sound_of_neverWrong`, `rc_plain_exe_sound_of_neverWrong` | `plain_exe_sound`, `Rc.plain_exe_sound` | `PlainExeOutcome` with `fun _ => False` for its escape |
| `plain_exe_specified_of_neverStuck`, `rc_plain_exe_specified_of_neverStuck` | `plain_shell_unspecified` | no reachable state of the process is `Unspecified` |

The targets `SafetyProgress` (with its conditional form `SafetyProgressGiven`) and
`FunctionalProgress` are definitions, stated over
what a checker establishes (`Accepted`: ingress, which is the kernel's acceptance of
the whole environment, and the front half under some certificate, which is the
table, the annotation, lazification and erasure) and one further decision `ok` of
the checker on those data. `plans/PROGRESS.md` explains why a further decision is
needed (kernel acceptance and the present front half do not determine the shapes of
SrcEval's values), and `IxCCCorrect.Shape` proves the first instance.
-/

set_option autoImplicit false

namespace IxCC.Progress

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.X86.Exe.Plain
open IxCC.Sem (Lang Obs Result)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- The source the end-to-end theorems speak about: the checked program, its results
observed through the roots' view. -/
abbrev Source := Sem.Viewed CheckedProgram

/-! ## The two strengths -/

/-- **Progress, safety strength.** The viewed source is stuck at no clock: SrcEval is
never stuck, and every value it returns is one the root's view reads back. -/
def NeverStuck (s : Source) (i : Nat × List Nat) : Prop :=
  ∀ k, Lang.run s i k ≠ .stuck

/-- **Progress, functional strength.** The viewed source goes wrong at no clock: it is
never stuck, never traps, and every value it returns is one the root's view reads
back. -/
def NeverWrong (s : Source) (i : Nat × List Nat) : Prop :=
  ∀ k, ¬ (Lang.run s i k).GoesWrong

theorem NeverWrong.neverStuck {s : Source} {i : Nat × List Nat} (h : NeverWrong s i) :
    NeverStuck s i :=
  fun k hk => h k (by rw [hk]; trivial)

/-- A viewed run is stuck exactly where the program's run is, or where the view
rejects its result. -/
theorem viewed_stuck_iff {s : Source} {i : Nat × List Nat} {k : Nat} :
    Lang.run s i k = .stuck ↔ Lang.run s.prog i k = .stuck ∨
      ∃ v, Lang.run s.prog i k = .ok v ∧ s.view i.1 (Lang.obs v) = none := by
  change (Lang.run s.prog i k).bind (fun v => Sem.viewResult s.view i.1 (Lang.obs v)) = .stuck ↔ _
  cases hr : Lang.run s.prog i k with
  | ok v =>
    constructor
    · intro h
      exact .inr ⟨v, rfl, Sem.viewResult_eq_stuck.1 h⟩
    · rintro (h | ⟨v', hv', hn⟩)
      · cases h
      · cases hv'
        exact Sem.viewResult_eq_stuck.2 hn
  | timeout =>
    constructor
    · intro h; cases h
    · rintro (h | ⟨v', hv', -⟩)
      · cases h
      · cases hv'
  | resource r =>
    constructor
    · intro h; cases h
    · rintro (h | ⟨v', hv', -⟩)
      · cases h
      · cases hv'
  | trap =>
    constructor
    · intro h; cases h
    · rintro (h | ⟨v', hv', -⟩)
      · cases h
      · cases hv'
  | stuck => exact ⟨fun _ => .inl rfl, fun _ => rfl⟩

/-- `NeverStuck`, read on the program's own runs. -/
theorem neverStuck_iff {s : Source} {i : Nat × List Nat} :
    NeverStuck s i ↔ ∀ k, Lang.run s.prog i k ≠ .stuck ∧
      ∀ v, Lang.run s.prog i k = .ok v → s.view i.1 (Lang.obs v) ≠ none := by
  constructor
  · intro h k
    exact ⟨fun hs => h k (viewed_stuck_iff.2 (.inl hs)),
      fun v hv hn => h k (viewed_stuck_iff.2 (.inr ⟨v, hv, hn⟩))⟩
  · intro h k hk
    rcases viewed_stuck_iff.1 hk with hs | ⟨v, hv, hn⟩
    · exact (h k).1 hs
    · exact (h k).2 v hv hn

/-- `NeverWrong`, read on the program's own runs. -/
theorem neverWrong_iff {s : Source} {i : Nat × List Nat} :
    NeverWrong s i ↔ ∀ k, ¬ (Lang.run s.prog i k).GoesWrong ∧
      ∀ v, Lang.run s.prog i k = .ok v → s.view i.1 (Lang.obs v) ≠ none := by
  constructor
  · intro h k
    exact ⟨fun hw => h k (Sem.Viewed.run_goesWrong.2 (.inl hw)),
      fun v hv hn => h k (Sem.Viewed.run_goesWrong.2 (.inr ⟨v, hv, hn⟩))⟩
  · intro h k hk
    rcases Sem.Viewed.run_goesWrong.1 hk with hw | ⟨v, hv, hn⟩
    · exact (h k).1 hw
    · exact (h k).2 v hv hn

/-! ## `NeverWrong` is the negation of the theorems' disjunct -/

/-- On the immortal and zero-RC path, `NeverWrong` of the front half's source is the
negation of `Recheck.Front.GoesWrong`. -/
theorem not_goesWrong_iff {f : Recheck.Front} {i : Nat × List Nat} :
    ¬ f.GoesWrong i ↔ NeverWrong f.source i := by
  constructor
  · intro h k hk
    exact h (Recheck.source_goesWrong hk)
  · rintro h ⟨k, hk⟩
    exact h k (Sem.Viewed.run_goesWrong.2 hk)

/-- On the plain-RC path, likewise for `RcReplay.Front.GoesWrong`. -/
theorem rc_not_goesWrong_iff {f : Recheck.RcReplay.Front} {i : Nat × List Nat} :
    ¬ f.GoesWrong i ↔ NeverWrong f.source i := by
  constructor
  · intro h k hk
    exact h (Recheck.RcReplay.source_goesWrong hk)
  · rintro h ⟨k, hk⟩
    exact h k (Sem.Viewed.run_goesWrong.2 hk)

/-! ## A refinement keeps "never stuck" -/

/-- **A stuck target has a stuck source.** `Sem.Refines.safe` is the same statement for
"goes wrong" (stuck or a trap); this is the half the safety tier needs, where a trap
is a reported outcome. -/
theorem not_stuck_of_refinesOn {I S T : Type} [Lang I S] [Lang I T] {D : I → Prop} {s : S} {t : T}
    (h : Sem.RefinesOn D s t) {i : I} (hi : D i) (hs : ∀ k, Lang.run s i k ≠ .stuck) (k : Nat) :
    Lang.run t i k ≠ .stuck := by
  intro ht
  have hb : Lang.behaviour t i = .stuck :=
    (Sem.behaviour_eq_stuck_iff (Lang.mono t i)).2 ⟨k, ht⟩
  have href := h i hi
  rw [hb] at href
  have hsb : Lang.behaviour s i = .stuck := by
    generalize Lang.behaviour s i = b at href
    cases href with
    | stuck => rfl
  obtain ⟨k', hk'⟩ := (Sem.behaviour_eq_stuck_iff (Lang.mono s i)).1 hsb
  exact hs k' hk'

/-! ## The object theorems without the disjunct -/

section Object

variable {cfg : Recheck.Config} {P : Src.Program}

/-- **`Recheck.sound` under functional progress**: every value the object returns is
the view of a value SrcEval returns, and the object goes wrong at no clock. -/
theorem recheck_sound_of_neverWrong {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (i : Nat × List Nat) (hi : a.front.Covered c i) (hp : NeverWrong a.front.source i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      ∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) := by
  have hs := Recheck.sound h D hD i hi
  have hn : ¬ a.front.GoesWrong i := not_goesWrong_iff.2 hp
  refine ⟨fun k w hw => ?_, hs.2.1 hn⟩
  rcases hs.1 k w hw with h' | h'
  · exact h'
  · exact absurd h' hn

/-- **`Recheck.sound` under safety progress**: the object is stuck at no clock (it
returns, runs, fails for a resource, or traps). -/
theorem recheck_not_stuck {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (i : Nat × List Nat) (hi : a.front.Covered c i) (hp : NeverStuck a.front.source i) (k : Nat) :
    Lang.run (a.linked D) i k ≠ .stuck :=
  not_stuck_of_refinesOn (Recheck.object_refines h D hD) hi hp k

/-- `recheck_not_stuck` from two call sites (the standalone executable's shell). -/
theorem recheck_not_stuck_at {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (s : X86.Driver.Site) (hs : (D.withSite s).Ok a.backend.encoded.text.size)
    (i : Nat × List Nat) (hi : a.front.Covered c i) (hp : NeverStuck a.front.source i) (k : Nat) :
    Lang.run (a.linkedAt D s) i k ≠ .stuck :=
  not_stuck_of_refinesOn (Recheck.object_refines_at h D hD s hs) hi hp k

/-- **`RcReplay.sound` under functional progress.** -/
theorem rc_sound_of_neverWrong {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i)
    (hp : NeverWrong a.front.source i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      ∃ k' v, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) := by
  have hs := Recheck.RcReplay.sound h D hD i hi
  have hn : ¬ a.front.GoesWrong i := rc_not_goesWrong_iff.2 hp
  refine ⟨fun k w hw => ?_, hs.2.1 hn⟩
  rcases hs.1 k w hw with h' | h'
  · exact h'
  · exact absurd h' hn

/-- **`RcReplay.sound` under safety progress.** -/
theorem rc_not_stuck {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i)
    (hp : NeverStuck a.front.source i) (k : Nat) :
    Lang.run (a.linked D) i k ≠ .stuck :=
  not_stuck_of_refinesOn (Recheck.RcReplay.object_refines h D hD) hi hp k

/-- `rc_not_stuck` from two call sites. -/
theorem rc_not_stuck_at {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (s : X86.Driver.Site)
    (hs : (D.withSite s).Ok a.backend.encoded.text.size) (i : Nat × List Nat)
    (hi : a.front.Covered c i) (hp : NeverStuck a.front.source i) (k : Nat) :
    Lang.run (a.linkedAt D s) i k ≠ .stuck :=
  not_stuck_of_refinesOn (Recheck.RcReplay.object_refines_at h D hD s hs) hi hp k

end Object

/-! ## The plain executable without the disjunct -/

/-- `PlainExeOutcome` is monotone in its escape, on the inputs of the root's arity. -/
theorem plainExeOutcome_mono {srcEval : List Nat → Option Obs → Prop} {g g' : List Nat → Prop}
    {arity : Nat} {result : ResultKind} {D : Nat} {args : List (List Nat)} {σ : List Sys}
    (hg : ∀ ns, ns.length = arity → g ns → g' ns)
    (h : IxCC.Exe.Plain.PlainExeOutcome srcEval g arity result D args σ) :
    IxCC.Exe.Plain.PlainExeOutcome srcEval g' arity result D args σ := by
  rcases h with h | h | ⟨ρ, heq, hbody⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨ρ, heq, ?_⟩)
    rcases hbody with hc | ⟨hlen, hparse⟩
    · exact .inl hc
    · refine .inr ⟨hlen, ?_⟩
      cases hp : parseArgsList args with
      | overflow => rw [hp] at hparse; exact hparse
      | bad => rw [hp] at hparse; exact hparse
      | ok ns =>
        rw [hp] at hparse
        rcases hparse with h1 | h2 | h3 | h4 | h5
        · exact .inl h1
        · exact .inr (.inl h2)
        · exact .inr (.inr (.inl h3))
        · exact .inr (.inr (.inr (.inl h4)))
        · exact .inr (.inr (.inr (.inr (hg ns ((parseArgsList_ok_length hp).trans hlen) h5))))

section Plain

variable {cfg : Recheck.Config} {P : Src.Program}

/-- **`plain_exe_sound` under functional progress** (immortal and zero-RC objects):
every finite trace of the checked executable satisfies `PlainExeOutcome` with no
escape. What is left of the disjuncts is the shell's own reports, the resource
reports, and a silent stop. -/
theorem plain_exe_sound_of_neverWrong {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp, ce⟩)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverWrong a.front.source (0, ns))
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (IxCC.X86.Exe.Plain.Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    IxCC.Exe.Plain.PlainExeOutcome (IxCC.Exe.Plain.srcPlainEval a.src a.checked a.front.view)
      (fun _ => False) inp.arity inp.result (fileBase + ce.plan.placement.dataOffset) args σ :=
  plainExeOutcome_mono (fun ns hlen hgw => not_goesWrong_iff.2 (hp ns hlen) hgw)
    (IxCC.Exe.Plain.plain_exe_sound h hb hargs hload hσ)

/-- **`Rc.plain_exe_sound` under functional progress** (plain-RC objects). -/
theorem rc_plain_exe_sound_of_neverWrong {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a)
    {a' : Recheck.Artifact} (h' : a.toRecheckArtifact c = .ok a')
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a' layout = .ok ⟨inp, ce⟩)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverWrong a.front.source (0, ns))
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (IxCC.X86.Exe.Plain.Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    IxCC.Exe.Plain.PlainExeOutcome
      (IxCC.Exe.Plain.srcPlainEval a.front.src a.front.checked a.front.view)
      (fun _ => False) inp.arity inp.result (fileBase + ce.plan.placement.dataOffset) args σ :=
  plainExeOutcome_mono (fun ns hlen hgw => rc_not_goesWrong_iff.2 (hp ns hlen) hgw)
    (IxCC.Exe.Plain.Rc.plain_exe_sound h h' hb hargs hload hσ)

/-- **The plain executable under safety progress** (immortal and zero-RC objects): no
state the process reaches is one where the processor specification promises nothing
(`Process.Unspecified`). A trap of the source is not excluded here and need not be:
the shell reports it (`PlainShows`, the `fail trap` case). -/
theorem plain_exe_specified_of_neverStuck {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp, ce⟩)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverStuck a.front.source (0, ns))
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (IxCC.X86.Exe.Plain.Certified.checked ce) args s₀)
    {σ : List Sys} {s : ByteEval.State} (hr : Run ce.bytes s₀ σ s) :
    ¬ Unspecified ce.bytes s := by
  intro hu
  obtain ⟨r, hf, hinp⟩ := IxCC.Exe.Plain.build_spec hb
  obtain ⟨hahead, _, hnatParams, htySpec⟩ := IxCC.Exe.Plain.fragment_spec hf
  have hroot0 := IxCC.Exe.Plain.plain_linkedRoot h hf
  have hrm : PlainRootMatches inp { symbol := r.symbol, params := r.params, ty := r.ty } := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hinp]
    · rw [hinp]
    · exact htySpec
  obtain ⟨hlen, ns, hparse, hstuck, -⟩ := plain_shell_unspecified ce hroot0 hrm hargs hload hr hu
  obtain ⟨-, xv, -, -, hemit, -⟩ := Recheck.run_parts h
  have hts : ce.plan.placement.textSize = a.backend.encoded.text.size :=
    IxCC.Exe.Plain.plain_textSize_of_emit hemit (by rw [hinp]; rfl) ce
  have hobjEq : inp.object = a.object := by rw [hinp]
  have hrp : ({ symbol := r.symbol, params := r.params, ty := r.ty } : Linked.Root).params =
      inp.arity := by
    rw [hinp]
  rw [hobjEq, hts] at hstuck
  obtain ⟨Drv, site, r', k, hr0, hD, hR, hcm⟩ := hstuck
  have hnsLen : ns.length = inp.arity := (parseArgsList_ok_length hparse).trans hlen
  have hrEq : r' = { symbol := r.symbol, params := r.params, ty := r.ty } :=
    Option.some.inj (hr0.symm.trans hroot0)
  subst hrEq
  have hcall : Lang.run (linkedOf a.object a.linkedRoots Drv site) (0, ns) k =
      (linkedOf a.object a.linkedRoots Drv site).call
        { symbol := r.symbol, params := r.params, ty := r.ty } ns k := by
    show LinkedAt.run (linkedOf a.object a.linkedRoots Drv site) (0, ns) k = _
    unfold LinkedAt.run
    rw [hr0]
    exact Sem.entryRun_exact (hnsLen.trans hrp.symm) k
  have hcov : a.front.Covered c (0, ns) :=
    Recheck.Artifact.covered_head h hahead hnatParams (hnsLen.trans hrp.symm)
  exact recheck_not_stuck_at h Drv hD site hR (0, ns) hcov (hp ns hnsLen) k (hcall.trans hcm)

/-- **The plain executable under safety progress** (plain-RC objects): no state the
process reaches is one where the processor specification promises nothing. -/
theorem rc_plain_exe_specified_of_neverStuck {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a)
    {a' : Recheck.Artifact} (h' : a.toRecheckArtifact c = .ok a')
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a' layout = .ok ⟨inp, ce⟩)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverStuck a.front.source (0, ns))
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (IxCC.X86.Exe.Plain.Certified.checked ce) args s₀)
    {σ : List Sys} {s : ByteEval.State} (hr : Run ce.bytes s₀ σ s) :
    ¬ Unspecified ce.bytes s := by
  intro hu
  obtain ⟨xv', xl', rfl⟩ := toRecheck_spec h'
  obtain ⟨r, hf, hinp⟩ := IxCC.Exe.Plain.build_spec hb
  obtain ⟨hahead, _, hnatParams, htySpec⟩ := IxCC.Exe.Plain.fragment_spec hf
  have hhead' : a.roots.head? = some r := hahead
  rw [Recheck.RcReplay.run_roots h] at hhead'
  have hfst : a.front.lowered.roots.map Prod.fst = a.front.cfg.base.exports :=
    Recheck.RcReplay.public_roots
      (Recheck.RcReplay.runFront_native (Recheck.RcReplay.run_parts h).1).2
  have hroot0 : a.linkedRoots[0]? =
      some { symbol := r.symbol, params := r.params, ty := r.ty } :=
    head_linkedRoot hfst hhead'
  have hrm : PlainRootMatches inp { symbol := r.symbol, params := r.params, ty := r.ty } := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hinp]
    · rw [hinp]
    · exact htySpec
  obtain ⟨hlen, ns, hparse, hstuck, -⟩ := plain_shell_unspecified ce hroot0 hrm hargs hload hr hu
  obtain ⟨-, xv, xl, -, -, hemit, -⟩ := Recheck.RcReplay.run_parts h
  have hts : ce.plan.placement.textSize = a.backend.encoded.text.size :=
    IxCC.Exe.Plain.plain_textSize_of_emit hemit (by rw [hinp]; rfl) ce
  have hobjEq : inp.object = a.backend.object := by rw [hinp]; rfl
  have hrp : ({ symbol := r.symbol, params := r.params, ty := r.ty } : Linked.Root).params =
      inp.arity := by
    rw [hinp]
  rw [hobjEq, hts] at hstuck
  obtain ⟨Drv, site, r', k, hr0, hD, hR, hcm⟩ := hstuck
  have hnsLen : ns.length = inp.arity := (parseArgsList_ok_length hparse).trans hlen
  have hrEq : r' = { symbol := r.symbol, params := r.params, ty := r.ty } :=
    Option.some.inj (hr0.symm.trans hroot0)
  subst hrEq
  have hcall : Lang.run (linkedOf a.backend.object a.linkedRoots Drv site) (0, ns) k =
      (linkedOf a.backend.object a.linkedRoots Drv site).call
        { symbol := r.symbol, params := r.params, ty := r.ty } ns k := by
    show LinkedAt.run (linkedOf a.backend.object a.linkedRoots Drv site) (0, ns) k = _
    unfold LinkedAt.run
    rw [hr0]
    exact Sem.entryRun_exact (hnsLen.trans hrp.symm) k
  have hcov : a.front.Covered c (0, ns) :=
    Recheck.RcReplay.Artifact.covered_head h hahead hnatParams (hnsLen.trans hrp.symm)
  exact rc_not_stuck_at h Drv hD site hR (0, ns) hcov (hp ns hnsLen) k (hcall.trans hcm)

end Plain

end IxCC.Progress
