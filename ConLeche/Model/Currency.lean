module

public import ConLeche.Model.Annot.Valid
public import ConLeche.Model.Annot.EnvModel
public import ConLeche.Semantics.Sat
public import ConLeche.Verify.Shift

public section

/-!
# The P currency — the truthfulness predicate and the context discipline

the P currency — the truthfulness predicate and the context discipline —
in a module whose imports are what the two definitions need and nothing
else, so that the rules tier (`Model/Rules/*`) can state its motives
without importing the run-stated claims (task #305 closing)
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- The P-tier truthfulness currency: hereditary truthfulness plus
bit validity.  (from `Model/Claims.lean`, task #305 closing) -/
@[expose] def WellDenotedV (V : Type w) [SetTheory V] (ρ : Nat → V) (e : AnnotTerm) :
    Prop :=
  WellDenoted V ρ e ∧ AnnotValid V ρ e

/-- The P-tier context discipline: `CtxOk2D`'s package over `denoteMeta`
— scope bound, leaf types annotate, their interpretations read the
telescope, and they are `WellDenotedV` under every satisfying valuation.
No fuel parameter.  (from `Model/Claims.lean`, task #305 closing) -/
@[expose] def CtxOk {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (d : Nat) (Δa : List AnnotTerm) (e : Expr) : Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2 ∧
    ∃ tya Aa,
      denoteMeta m.acval env φ d l.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      (∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ tya
          = interp V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya)
