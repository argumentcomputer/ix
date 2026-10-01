module

public import ConLeche.Model.Inductives.StructCaps
public import ConLeche.Model.Inductives.StructFrames
public section

/-!
# The direct block's family laws (task #175 W4c, P3 module 5, part 2)

The block's own capability laws, from the leaves' semantic summary:

* `formerFold` — the former applied along a fitting parameter spine is
  the instantiated carrier (`structTyAV_fold` under the hereditary
  premise);
* `structUnitLawP` — a fieldless family is unit-like (its carrier is
  `unitSet`, both regimes);
* `structEtaLawP0` — a fieldless family's η law: the member is the
  point and so is the constructor's application.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Fits and folds -/

/-- A value-level fit of a Π-tower reading, of the tower's own
length, is a fit of its domains. -/
theorem spineFit_of_teleFit :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm} {ρ : Nat → V}
      {ts : List V} {rest : V},
      ts.length = pds.length →
      TeleFit V ρ (mkPisAV pds b) ts rest →
      SpineFit ρ (pds.map (·.2.2)) ts
  | [], _, _, [], _, _, _ => trivial
  | [], _, _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, _, [], _, hlen, _ => by simp at hlen
  | d :: pds, b, ρ, t :: ts, rest, hlen, h => by
    cases h with
    | cons ht hfit =>
      exact ⟨ht, spineFit_of_teleFit (by simpa using hlen) hfit⟩

theorem foldl_app_pt : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt ts

/-! ## The fieldless family's laws -/

end ConLeche.Model
