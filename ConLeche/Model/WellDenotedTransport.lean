module

public import ConLeche.Model.Currency
public import ConLeche.Semantics.DenoteClosed
public section

/-!
# `WellDenotedV`'s substitution metatheory (task #161, P3 batch 2)

`WellDenotedV := WellDenoted ∧ AnnotValid` is the P-tier truthfulness
currency (`Claims.lean`), and every threading clause that crosses a
binder needs it to survive the same two moves the halves survive
separately: lifting (`WellDenoted_liftN` / `AnnotValid_liftN`) and
instantiation (`WellDenoted_inst0` / `AnnotValid_inst0`).

The file exists for a *layering* reason rather than a mathematical
one.  `WellDenotedV` is defined in `Claims.lean`, which imports
`Annot/ValidV.lean`; so the conjunction's transport laws cannot live
beside the halves they are assembled from.  Nothing here is new
content — each lemma is `⟨half₁ …, half₂ …⟩`.

**The premises are paid per half.**  `AnnotValid_inst` takes bit
validity of the substituted term, `WellDenoted_inst` takes hereditary
truthfulness of it, and the conjunction takes exactly their
conjunction — no half is charged for the other's premise.  See
`Annot/ValidV.lean`'s note on why the `bvar` clause forces this.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

/-- Splitting the currency. -/
theorem WellDenotedV.wellDenoted {ρ : Nat → V} {e : AnnotTerm} (h : WellDenotedV V ρ e) :
    WellDenoted V ρ e := h.1

/-- …and its other half. -/
theorem WellDenotedV.validV {ρ : Nat → V} {e : AnnotTerm}
    (h : WellDenotedV V ρ e) : AnnotValid V ρ e := h.2

/-- Assembling it. -/
theorem WellDenotedV.mk {ρ : Nat → V} {e : AnnotTerm} (h1 : WellDenoted V ρ e)
    (h2 : AnnotValid V ρ e) : WellDenotedV V ρ e := ⟨h1, h2⟩

variable (V)

/-- **The currency through lifting** — both halves at the same
rewrite. -/
theorem WellDenotedV_liftN (n : Nat) (e : AnnotTerm) (k : Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (e.liftN n k) ↔ WellDenotedV V (shiftE n k ρ) e :=
  and_congr (WellDenoted_liftN V n e k ρ) (AnnotValid_liftN V n e k ρ)

variable {V}

/-- **The currency through outermost substitution** — the β/ζ
transport form, the shape every reduction clause consumes. -/
theorem WellDenotedV_inst0 {e a : AnnotTerm} {ρ : Nat → V}
    (ha : WellDenotedV V ρ a) :
    WellDenotedV V ρ (e.inst a) ↔
      WellDenotedV V (cons (interp V ρ a) ρ) e :=
  and_congr (WellDenoted_inst0 V ha.1) (AnnotValid_inst0 V ha.2)

/-- **Weakening a hoisted fact under one more binder**, in the P
currency: `WellDenoted.hoist_lift`'s mirror, and what `CtxOk.weakenTop`
uses to move a leaf's fourth conjunct across the new head. -/
theorem WellDenotedV.hoist_lift {Δa : List AnnotTerm} {X e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ e) :
    ∀ ρ : Nat → V, Sat V (X :: Δa) ρ → WellDenotedV V ρ e.lift := by
  intro ρ hρ
  refine (WellDenotedV_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat_tail hρ)

/-- **The stored leaves are `inst`-invariant** — `denoteMeta_beta`'s
second leaf premise, discharged from the erasure link and the
collapse-lane closedness field.  (Shared home: both the infer and the
whnf quarters proved this independently at their batches; deduplicated
here at the merge.) -/
theorem acval_inst_self {env : ConLeche.Env}
    (m : EnvModel V env) (n : ConLeche.Name)
    (ψ : ConLeche.Name → Nat) (y : AnnotTerm) (k : Nat) :
    (m.acval n ψ).inst y k = m.acval n ψ :=
  AnnotTerm.inst_eq_self _
    (by rw [m.acval_erase]
        exact Term.bvarsBelow.mono (Nat.zero_le k)
          (m.cval_closed n ψ)) y

end ConLeche.Model
