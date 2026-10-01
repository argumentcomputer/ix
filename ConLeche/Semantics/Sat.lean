module

public import ConLeche.Semantics.Interp

@[expose] public section

/-!
# `SetBase/Sat` — the annotated context's satisfaction, and its
transitivity kit

`Sat` (with its two introduction lemmas) and `interpC_trans`, re-based
at THE SEPARATION's S2 (task #161).

`interpC_trans` is the **two-edit sever**'s second edit: the graded
lane's `Steps/WhnfP` imported the whole 2U module `Steps/Whnf` for this
one eight-line composition.  The lemma is model-free — it is `Eq.trans`
under a valuation quantifier — but its *statement* names `Sat`, which
lived in `Annot/EnvModel.lean` beside the `EnvS`-containing invariant.  A
base module may not import a lane, so `Sat` comes down with it; it is
model-free in exactly the same sense (a `List AnnotTerm`, a valuation, and
`interp`), and both lanes state their context currency with it.

Statements verbatim, namespace (`ConLeche.SetR.Interp`) unchanged.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

section
variable (V : Type w) [SetTheory V]

/-- `ρ` satisfies an annotated context over `interp` — the `Sat`
transpose. -/
def Sat (Δa : List AnnotTerm) (ρ : Nat → V) : Prop :=
  ∀ i Aa, Δa[i]? = some Aa →
    ρ i ∈ˢ interp V (fun j => ρ (j + i + 1)) Aa

theorem Sat_nil (ρ : Nat → V) : Sat V [] ρ := by
  intro i Aa hi
  cases hi

theorem Sat_cons {Δa : List AnnotTerm} {Aa : AnnotTerm} {ρ : Nat → V} {x : V}
    (hρ : Sat V Δa ρ) (hx : x ∈ˢ interp V ρ Aa) :
    Sat V (Aa :: Δa) (cons x ρ) := by
  intro i Aa' hi
  cases i with
  | zero =>
    obtain rfl : Aa = Aa' := by simpa using hi
    exact hx
  | succ i =>
    have h := hρ i Aa' (by simpa using hi)
    exact h

end

section
variable {V : Type w} [SetTheory V]

/-- The tail of a satisfying valuation satisfies the tail context —
`Sat_cons`'s inverse, and what every weakening step consumes. -/
theorem Sat_tail {Δa : List AnnotTerm} {Ba : AnnotTerm} {ρ : Nat → V}
    (hρ : Sat V (Ba :: Δa) ρ) : Sat V Δa (fun j => ρ (j + 1)) := by
  intro i Aa hi
  exact hρ (i + 1) Aa (by simpa using hi)

/-- Equalities compose per valuation; the invariant does not travel
with them, because in the hoisted currency it is carried separately
and uniformly. -/
theorem interpC_trans {Δa : List AnnotTerm} {a b c : AnnotTerm}
    (h1 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ a = interp V ρ b)
    (h2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ b = interp V ρ c) :
    ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ a = interp V ρ c :=
  fun ρ hρ => (h1 ρ hρ).trans (h2 ρ hρ)

end

end ConLeche.Semantics
