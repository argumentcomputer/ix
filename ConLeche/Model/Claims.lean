module

public import ConLeche.Verify.InferLeaves
public import ConLeche.Semantics.Skeleton
import ConLeche.Model.Annot.Valid
import ConLeche.Model.Annot.EnvModel
public import ConLeche.Model.Currency

public section

/-!
# The P-generation claims: the ladder over `denoteMeta` (task #161, P3.3)

The generation-six claims (`Claims2E.lean`) state the soundness ladder
over `denoteAnnot` — the canonical reading, whose binder numerals are
checker runs.  This file states the same ladder over **`denoteMeta`**,
the validated-annotation reading.  The deltas, uniformly:

* `denoteAnnot μ m.acval env φ F d e` becomes `denoteMeta m.acval env φ d e`
  — the annotation fuels `F`/`F'` vanish (there is no run to pay
  for), taking with them the whole fuel-mediation surface
  (`denote2_fuelMono`, the `∃ F' ≥ F` slack, `CtxOk2`'s fuel
  parameter);
* the truthfulness currency is `WellDenotedV := WellDenoted ∧ AnnotValid`:
  the hereditary invariant plus bit validity — the claims *establish*
  the regime bits they dispatch on, clause by clause, from the run
  inversions (never from a validity metatheorem — the refuted
  `ValidInfer` shape stays off the table);
* the context discipline is `CtxOk`, `CtxOk2D`'s package with the
  historical `CtxOk2`/`CtxOk2Ann` split merged (fresh file, no
  compatibility constraint) and the leaf truthfulness upgraded to
  `WellDenotedV`.

The **dual-success** shape is kept verbatim: every `denoteMeta` sits in
a premise, never a conclusion, so the smallest-fuel refutation rule
has nothing to bite on — same structural reasoning as the E-tier's
frozen-text check.  (`denoteMeta` is *more* total than `denoteAnnot` — no
sort runs can fail — so success premises may later be dischargeable
outright; that is an upgrade path, not a statement change.)

`checkSound` closes the induction generically, exactly as
`checkSound2E`: the zero case is the checker's own zero-fuel throw,
untouched by the currency swap.

**Residue transformation (the P3.3 ledger, to be paid clause by
clause in the step proof):** where the E-tier step assembly consumes
sort-run residues, the P-tier consumes the P2 validation sites'
run-inversion conjuncts instead —

| E-tier residue | P-tier replacement |
|---|---|
| `BinderSortAgree2` (residue 9) | the `(defeq-forall)`/`(defeq-lam)` arm inversions: `==` ⇒ equal data ⇒ equal bits, and bits are canonical in `{0,1}` |
| `LamCodSort2` | the λ front door: leaf case delivered by `inferTypeCore_lam_inv`'s conjunct + `pwBit_zero_mem_univZero`; chain case by `piR_zero_mem_univZero` (impredicativity, no run) |
| `SortOfEInstLevels`/`LamSortEInstLevels` | `denotePInstLevels` — proved, unconditional, exact |
| `SortAgree` (env crossing) | dropped: `denoteMeta_envExtend` needs `FindPreserved`/`LitGuardsAgree` only |
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Head normalisation, dual success, P currency. -/
@[expose] def WhnfCoreClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AnnotTerm},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea = interp V ρ ea'

/-- The reduction loop, dual success, P currency. -/
@[expose] def WhnfClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AnnotTerm},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea = interp V ρ ea'

/-- Definitional equality, P currency. -/
@[expose] def DefEqClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a →
      CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa = interp V ρ ba

/-- Inference, dual success, P currency: the subject's and the
type's truthfulness — bit validity included — are *conclusions*. -/
@[expose] def InferClaim (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

/-- The P-generation step. -/
@[expose] def CheckStep (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaim μ m φ fuel → WhnfClaim μ m φ fuel →
    DefEqClaim μ m φ fuel → InferClaim μ m φ fuel →
    WhnfCoreClaim μ m φ (fuel + 1) ∧ WhnfClaim μ m φ (fuel + 1) ∧
      DefEqClaim μ m φ (fuel + 1) ∧ InferClaim μ m φ (fuel + 1)

/-- The P-generation induction: generic in the step, zero case from
the checker's own zero-fuel throws (currency-independent). -/
theorem checkSound {μ : CheckMode} {env : Env}
    (hstep : CheckStep μ V) (m : EnvModel V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δa h
      rw [ConLeche.whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δa h
      rw [ConLeche.whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δa h
      rw [ConLeche.isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δa h
      rw [ConLeche.inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

end ConLeche.Model
