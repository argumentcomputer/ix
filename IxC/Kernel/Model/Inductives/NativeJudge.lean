module

public import IxC.Kernel.Model.Inductives.StructBits
public import IxC.Kernel.Model.Inductives.StructRows
public import IxC.Kernel.Model.JudgeSound
public import IxC.Kernel.Verify.ProjSlots
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Verify.Mono
import IxC.Kernel.Verify.BinderLoop
import IxC.Kernel.Model.Tiers

public section

/-!
# What the native route's model proofs read of a judgement package

The native install's model proofs (`Model/Inductives/*`) read the checker's runs
through more than the claims `JudgeSound` names: they invert inference at the
shapes the stages type (a sort, a `∀`, a constant-headed spine), they read a sort
check of a sort, they use that a subject typed at a sort lies in that universe, and
that an annotated type checked before a structure's table is stored mentions none
of the table's slots. This module names those facts:

* `JudgeInv J`, model-free: the inversions, the sort check of a sort, and the
  projection slots of an accepted annotation;
* `SortClaimJ J m φ`, at a model: a subject inferred at a type that checks as the
  sort `u` is graded and lies in `univ u`;

and gives the package forms of the rows and the Π-prefix walk the stages read
(`inferRowJ`, `sortRowJ`, `defEqRowJ`, `piBitsJ`). The kernel's runs satisfy both
(`judgeInv_runJ`, `sortClaim_runJ`); the rules tier's derivations satisfy them by
inversion (`Model/Inductives/NativeRules.lean`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta
  openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The interface -/

/-- **The shapes a package's judgements take**, as the native route's model proofs
read them: inference at a sort and at a `∀`, the type of a constant-headed spine
whose head's type is a telescope ending in a sort, a sort check of a sort, and an
accepted closed annotation's projection slots. -/
structure JudgeInv (J : Judgements md) : Prop where
  /-- a sort infers its successor -/
  infer_sort : ∀ {env : Env md} {d : Nat} {u : Level} {t : Expr md},
    J.infer env d (.sort u) t → t = .sort (.succ u)
  /-- a sort checks as itself -/
  sort_sort : ∀ {env : Env md} {d : Nat} {u v : Level}, J.sort env d (.sort u) v → v = u
  /-- a `∀` infers through its domain and its opened body, whose sort's zero-ness is
  the binder's datum -/
  infer_forallE : ∀ {env : Env md} {d : Nat} {ty body t : Expr md} {mb : BinderMeta},
    J.infer env d (.forallE ty body mb) t →
    ∃ (s : Expr md) (u : Level) (bs : Expr md) (v : Level),
      J.infer env d ty s ∧ J.sort env d s u ∧
      J.infer env (d + 1) (body.instantiate1 (.fvar d ty)) bs ∧ J.sort env (d + 1) bs v ∧
      Level.zeronessOf v = mb.pw ∧ t = .sort (.imax u v)
  /-- a constant-headed spine whose head's type peels to a sort after the spine's
  length infers that sort -/
  infer_spine_sort : ∀ {env : Env md} {d : Nat} {n : Key md} {us : List Level}
    {as : List (Expr md)} {t : Expr md} {ci : ConstantInfo md}
    {bs : List (Expr md × BinderMeta)} {s : Level},
    J.infer env d (Expr.mkAppN (.const n us) as) t → env.find? n = some ci →
    (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us).stripPis
      as.length = some (bs, .sort s) →
    t = .sort s
  /-- an accepted closed annotation has no node at an empty projection slot -/
  annot_noProjAt : ∀ {env : Env md} {e e' : Expr md} {T : Key md} {i : Nat},
    J.annot env 0 e e' → (∃ t, J.infer env 0 e' t) → e.hasFvar = false →
    env.findProj? T i = none → Expr.NoProjAt T i e'

/-- **A subject typed at a sort lies in that universe**, at a model. -/
@[expose] def SortClaimJ (J : Judgements md) {env : Env md} (m : EnvModel V env)
    (φ : LevelParam → Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr md} {u : Level} {Δa : List AnnotTerm} {ea : AnnotTerm},
    J.infer env d e t → J.sort env d t u →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
    CtxOk m φ d Δa e → denoteMeta m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-! ## The rows, over a package -/

section Rows

variable {J : Judgements md} {env : Env md} {m : EnvModel V env} {φ : LevelParam → Nat}

/-- An inference at a context: the type reads, both readings are graded, and the
subject inhabits the type. -/
theorem inferRowJ (hJ : JudgeSound J m) {d : Nat} {e t : Expr md}
    {Δ : List AnnotTerm} {ea : AnnotTerm}
    (hi : J.infer env d e t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) (hC : CtxOk m φ d Δ e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
      (∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨ta, hta⟩ := hJ.reads φ hi hws hb hL hC hea
  obtain ⟨h1, h2, h3⟩ := hJ.infer φ hi hws hb hL hC hea hta
  exact ⟨ta, hta, h1, h2, h3⟩

/-- An inference whose type checks as a sort: the subject is graded and lies in
that universe. -/
theorem sortRowJ (hS : SortClaimJ J m φ) {d : Nat} {e t : Expr md} {u : Level}
    {Δ : List AnnotTerm} {ea : AnnotTerm}
    (hi : J.infer env d e t) (hens : J.sort env d t u)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) (hC : CtxOk m φ d Δ e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∀ ρ : Nat → V, Sat V Δ ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) :=
  hS hi hens hws hb hL hC hea

/-- A conversion at a context: the readings interpret alike. -/
theorem defEqRowJ (hJ : JudgeSound J m) {d : Nat} {a b : Expr md}
    {Δ : List AnnotTerm} {aa ba : AnnotTerm}
    (h : J.defeq env d a b)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hCa : CtxOk m φ d Δ a) (hCb : CtxOk m φ d Δ b)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (hbA : denoteMeta m.acval env φ d b = some ba)
    (hoka : ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ aa)
    (hokb : ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ba) :
    ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ aa = interp V ρ ba :=
  hJ.defeq φ h hwa hba hLa hwb hbb hLb hCa hCb haa hbA hoka hokb

end Rows

/-! ## The Π-prefix walk, over a package -/

/-- **The Π-prefix walk** (`piBits_of_infer` over a package): the first `n`
binders' data of an inferred type are exact against the innermost opened body's
sort, and the whole type's sort is zero exactly when that one is. -/
theorem piBitsJ {J : Judgements md} (hI : JudgeInv J) {env : Env md} :
    ∀ (n : Nat) {d : Nat} {e t : Expr md} {v₀ : Level} {fvs : List (Expr md)}
      {opened : Expr md},
      openPisAtFvars n e d = some (fvs, opened) →
      J.infer env d e t → J.sort env d t v₀ →
      ∃ (tb : Expr md) (vb : Level),
        J.infer env (d + n) opened tb ∧ J.sort env (d + n) tb vb ∧
        (∀ φ, Level.eval φ v₀ = 0 ↔ Level.eval φ vb = 0) ∧
        ∀ φ, PiBitsOpen φ (Level.eval φ vb = 0) n d e
  | 0, d, e, t, v₀, fvs, opened, hop, h, hens => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    exact ⟨t, v₀, h, hens, fun _ => Iff.rfl, fun _ => trivial⟩
  | n + 1, d, e, t, v₀, fvs, opened, hop, h, hens => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      obtain ⟨tty, u, bt, v, -, -, hbt, hensb, hz, rfl⟩ := hI.infer_forallE h
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' e' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨-, rfl⟩ := hop
        obtain ⟨tb, vb, hrun, hensb', hv, hbits⟩ := piBitsJ hI n hop' hbt hensb
        refine ⟨tb, vb, ?_, ?_, ?_, ?_⟩
        · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hrun
        · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hensb'
        · intro φ
          rw [hI.sort_sort hens, eval_imax_eq_zero_iff]
          exact hv φ
        · intro φ
          refine ⟨?_, hbits φ⟩
          rw [← hz]
          exact (pwBit_zeronessOf φ _).trans (hv φ)
      · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The kernel's runs satisfy the interface -/

section RunInstance

variable {μ : CheckMode}

/-- **The kernel's runs have the shapes** (verified mode, any fuel). -/
theorem judgeInv_runJ (hμ : μ.verifiedChecks = true) (F : Nat) :
    JudgeInv (md := md) (runJ μ F) where
  infer_sort := fun h => inferTypeCore_sort_inv h
  sort_sort := fun h => ensureSortCore_sort_eq h
  infer_forallE := by
    intro env d ty body t mb h
    have h' : Ix.Kernel.inferTypeCore μ env F d (.forallE ty body mb) = .ok t := h
    cases F with
    | zero => rw [Ix.Kernel.inferTypeCore_zero] at h'; exact nomatch h'
    | succ F' =>
      obtain ⟨tty, u, bt, v, hty, hwh, hbt, hens, hz, rfl⟩ :=
        Ix.Kernel.inferTypeCore_forall_inv h'
      have h1 : Ix.Kernel.ensureSortCore μ env F' d tty = .ok u := by
        rw [Ix.Kernel.ensureSortCore_eq, hwh]; rfl
      exact ⟨tty, u, bt, v, Ix.Kernel.inferTypeCore_mono (Nat.le_succ F') hty,
        Ix.Kernel.ensureSortCore_mono (Nat.le_succ F') h1,
        Ix.Kernel.inferTypeCore_mono (Nat.le_succ F') hbt,
        Ix.Kernel.ensureSortCore_mono (Nat.le_succ F') hens, hz hμ, rfl⟩
  infer_spine_sort := by
    intro env d n us as t ci bs s h hf hst
    have h' : Ix.Kernel.inferTypeCore μ env F d (Expr.mkAppN (.const n us) as) = .ok t := h
    obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv as h'
    obtain ⟨ci', hfci, -, rfl⟩ := Ix.Kernel.inferTypeCore_const_inv htf
    obtain rfl : ci' = ci := Option.some.inj (hfci.symm.trans hf)
    exact inferTypeCore_mkAppN_sort as htf hst h'
  annot_noProjAt := fun hann _ hnf hslot => Ix.Kernel.annotateCore_noProjAt μ hann hnf hslot

/-- **The kernel's sort claim**, at the fold's invariant. -/
theorem sortClaim_runJ (hμ : μ.verifiedChecks = true) {env : Env md}
    (mp : EnvModelM V μ env) (F : Nat) (φ : LevelParam → Nat) :
    SortClaimJ (runJ μ F) mp.base2 φ := by
  intro d e t u Δa ea hi hs hws hb hL hC hea
  exact (claimsAt_of hμ mp φ F).sort hC hws hb hL hi (Ix.Kernel.ensureSortCore_inv hs) hea

end RunInstance

end Ix.Kernel.Model
