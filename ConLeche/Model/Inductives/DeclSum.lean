module

public import ConLeche.Model.Inductives.DeclStruct
public import ConLeche.Model.Inductives.SumStageRec
import ConLeche.Verify.Inductives.SumWF
public section

/-!
# The direct sum's install, assembled (task #175 sum-types, indexed)

`declSumP`: the P carrier survives the direct sum install's run
(`DeclSumRun`).  The stages: the former (twice — first with the
empty chain list, to read the constructors' field data and index
readings at a carrier storing the former; then with the restricted
chains `rChains` read off that data, the readings identified by
`denoteP_openPis_agree` (field domains) and `CtorDataI.Es_eq` (index
readings) since neither mentions the former), the constructors in
order (`sumCtorsLoop`, every earlier constructor's data and leaf
crossing each later cons; the pending constructors staying fresh by
the distinct-names guard), and the recursor (`stageSumRec`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

/-- Distinct names, positionally. -/
theorem names_ne_of_nodup {ctorsA : List (ConstantVal × Nat)}
    (hnd : (ctorsA.map (·.1.name)).Nodup) {i j : Nat} {cAi cAj : ConstantVal × Nat}
    (hi : ctorsA[i]? = some cAi) (hj : ctorsA[j]? = some cAj) (hne : i ≠ j) :
    cAi.1.name ≠ cAj.1.name := by
  have hil : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hp := List.pairwise_iff_getElem.mp hnd
  have hi' : ctorsA[i] = cAi := by
    have := List.getElem?_eq_getElem hil; rw [hi] at this; exact (Option.some.inj this).symm
  have hj' : ctorsA[j] = cAj := by
    have := List.getElem?_eq_getElem hjl; rw [hj] at this; exact (Option.some.inj this).symm
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := hp i j (by simpa using hil) (by simpa using hjl) hlt
    simp only [List.getElem_map, hi', hj'] at this
    exact this
  · have := hp j i (by simpa using hjl) (by simpa using hil) hgt
    simp only [List.getElem_map, hi', hj'] at this
    exact fun h => this h.symm

/-! ## The constructors' loop -/

/-- The facts about the pending constructors at an environment. -/
@[expose] def PendingAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, k ≤ i → ctorsA[i]? = some cA →
    env.find? cA.1.name = none ∧ cA.1.type.constsResolve env = true ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF i) (dsF i) (esF i) (srcsF i)

/-- The facts about the consed constructors at an environment. -/
@[expose] def ConsedAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, i < k → ctorsA[i]? = some cA →
    CtorFactsAt m T lps nP nIdx resSort isProp large idxF dsF esF srcsF i cA ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    ∀ ψ, m.acval cA.1.name ψ
      = sumMkAV (resSort.eval ψ) i (dsF i ψ) (((dsF i ψ).drop nP).map (·.2.2))
          (uChains (fssOf nP (ctorDataList dsF esF ψ ctorsA 0)))

/-! ## The assembly -/

end ConLeche.Model
