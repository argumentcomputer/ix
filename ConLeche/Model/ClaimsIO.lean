module

public import ConLeche.Model.Claims
import ConLeche.Kernel.CoreIO
public section

/-!
# The io claims family, PREMISE FORM (task #161, stage 2 — the freeze)

The fifth family of the P ladder: the same soundness statement as
`InferClaim`, about the **io lane** (`inferTypeCoreIO`,
`Kernel/CoreIO.lean`), with one deliberate change of species.

## The species: premise form, and why it must be

`InferClaim` is an **establishment** statement — the subject's
truthfulness `WellDenotedV ea` is a *conclusion*, derived from the run.
The io lane cannot establish it at the application clause: with the
argument's certificate skipped there is nothing connecting `⟦tya⟧` to
`⟦Aa⟧`, which is exactly the proof-theoretic receipt for keeping the
front door ungated (the round-D study's refutation item 4).  What the
io lane *can* do is **consume**: given the subject's truthfulness, it
returns the type's truthfulness and the membership.  So

* `WellDenotedV ea` moves from the conclusion to the **premises**;
* the conclusions are `WellDenotedV ta` and `⟦ea⟧ ∈ ⟦ta⟧` — membership in
  the **io-computed** type, never identity with "the" type (which is
  why the old unique-typing and Π-domain-injectivity refutations do
  not bite: they refute an identity the statement never asserts).

This is the establishment/consumption asymmetry, in one statement.
Every consumer the campaign switches to the io lane already holds the
premise (`Steps/Irrel.lean:187-188` is the canonical witness:
`ProofIrrelPQ` takes `WellDenotedV` of both sides).

## The licensed fragment, and the wall

The only new mathematics is the application clause, and it splits:

* **graph regime** (`pw = .never`, where the gate fires): the skipped
  membership is recovered from the subject's own hereditary app slot
  by `io_domain_transfer` + `piR_dom_unique`, with **no** nonemptiness
  and **no** freshness side condition;
* **squash regime**: the certificate runs, and the clause reuses
  today's `ihd` route verbatim.

The split is not an engineering convenience.  `io_membership_fails_at_
squash` exhibits closed `V`-values satisfying every premise of the
premise-form claim at a squash binder with `app ⟦f⟧ ⟦a⟧ ∉ ⟦B'⟧⟦a⟧`:
truth values do not remember domains, so **no** proof-irrelevant set
model can license official's full inferOnly.  `pw = .never` is the
whole licensed fragment, forever.

## The five-way step

The io lane is a *leaf* lane (`Kernel/CoreIO.lean`): its reduction and
definitional equality are the full lane's, so the assembly grows by
one slot and nothing else moves —

    {WhnfCore, Whnf, DefEq, Infer, InferIO} at fuel
      ⟹ {WhnfCore, Whnf, DefEq, Infer, InferIO} at fuel + 1

with the io slot at `fuel + 1` consuming `Whnf`, `DefEq` and `InferIO`
at `fuel` (and, at the kept-check branch of the app clause, nothing
else).  `checkSound5` closes that induction generically; the step
itself is PAID since the io-license batch —
`checkStep2P5_of_quarters` / `checkSoundP5_of_inputs`
(`Steps/AssemblyP.lean`), modulo the routed `InferInputsIO`.

**Mode provenance (binding).**  An io conclusion must never feed a
site that needs establishment form.  The knot boundary is the
enforcement: the full lane's bodies never mention `coreKnotIO`, so no
full-lane claim can be discharged from an io claim by construction.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name inferTypeCoreIO)

universe w

variable {V : Type w} [SetTheory V]

/-- **The io inference family, premise form** (the frozen shape).
Compare `InferClaim`: the subject's `WellDenotedV` is a *premise* here,
and the run is the io lane's. -/
@[expose] def InferClaimIO (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    inferTypeCoreIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

/-! ## The slot family (task #172 B4)

The executable's internal inference call sites run the knot's io
*slot* (`inferTypeIO`, `Kernel/TypeChecker.lean`): the io lane at the
gated mode, full inference everywhere else.  The slot's claim is the
premise-form statement at that function, and it is DERIVED, not
proved by a walk: at a gate-off mode the slot is `inferTypeCore`
(`inferTypeIO_off`) and the full establishment claim is stronger than
the premise form; at the gated mode the slot is `inferTypeCoreIO`
(`inferTypeIO_on`) and the io claim is exactly it.  Every converted
call site's `of_claims` supplier consumes this one family. -/

/-- Premise form at the io slot. -/
@[expose] def InferClaimIOS (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    ConLeche.inferTypeIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

/-- **The slot claim, from the two lanes' claims** — one `Bool` case
on the mode's gate bit, one lane equation each way.  (The gate-off arm
drops the establishment conclusion's first conjunct; the premise is
unused there.) -/
theorem inferClaimIOS_of {μ : CheckMode} {env : Env}
    {m : EnvModel V env} {φ : Name → Nat} {fuel : Nat}
    (hfull : InferClaim μ m φ fuel) (hio : InferClaimIO μ m φ fuel) :
    InferClaimIOS μ m φ fuel := by
  intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
  cases hg : μ.betaGate with
  | false =>
    rw [ConLeche.inferTypeIO_off hg] at hrun
    obtain ⟨-, hokta, hmem⟩ := hfull hrun hws hb hLb hC hea hta
    exact ⟨hokta, hmem⟩
  | true =>
    rw [ConLeche.inferTypeIO_on hg] at hrun
    exact hio hrun hws hb hLb hC hea hta hok

/-- **The five-way step** (statement only; the assembly proof is the
campaign's B4).  The four sealed families and the io family, all at
`fuel`, give the same five at `fuel + 1`. -/
@[expose] def CheckStep5 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaim μ m φ fuel → WhnfClaim μ m φ fuel →
    DefEqClaim μ m φ fuel → InferClaim μ m φ fuel →
    InferClaimIO μ m φ fuel →
    WhnfCoreClaim μ m φ (fuel + 1) ∧ WhnfClaim μ m φ (fuel + 1) ∧
      DefEqClaim μ m φ (fuel + 1) ∧ InferClaim μ m φ (fuel + 1) ∧
        InferClaimIO μ m φ (fuel + 1)

/-- The five-way induction: generic in the step, zero case from the
checker's own zero-fuel throws — the io lane's zero level throws the
same `internal` error as the full one (`inferTypeCoreIO_zero`), so the
currency swap costs nothing here either. -/
theorem checkSound5 {μ : CheckMode} {env : Env}
    (hstep : CheckStep5 μ V) (m : EnvModel V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel ∧
          InferClaimIO μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
    · intro d e t Δa h
      rw [ConLeche.inferTypeCoreIO_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi, ihio⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi ihio

end ConLeche.Model
