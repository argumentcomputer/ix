import Ix.CompileCert.Opt.LevelSemantics
import Ix.Compile.Pass.ImageView

/-!
Exact origin of the values expansionOfP rewrites.
This derives the reader boundary from BlockView.expansion itself. It does not
assert that arbitrary ConstantInfo values are universe-scoped or that successful
image construction supplies source typing, spine arity, or a conversion rule.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Expr DefinitionVal TheoremVal)
open Ix.Compile.Pass (ViewInput BlockView Expansion)

/-- Every rewrite-enabled stored expansion is exactly a queried definition or
theorem value, with that declaration's unchanged universe parameters and type. -/
theorem expansion_stored_origin (inp : ViewInput) (view : BlockView) (name : Name)
    {x : Expansion} {type : Expr}
    (success : view.expansion inp name = .ok (x, type))
    (rewrite : x.needsRewrite = true) :
    (∃ d : DefinitionVal, inp.const? name = some (.defnInfo d) ∧
      x.levelParams = d.cnst.levelParams ∧ x.value = d.value ∧ type = d.cnst.type) ∨
    (∃ d : TheoremVal, inp.const? name = some (.thmInfo d) ∧
      x.levelParams = d.cnst.levelParams ∧ x.value = d.value ∧ type = d.cnst.type) := by
  unfold BlockView.expansion at success
  split at success
  · obtain ⟨img, _, out⟩ := except_bind_ok success
    have heq := except_pure_ok' out
    cases heq
    cases rewrite
  · rename_i d hd
    have heq := except_pure_ok' success
    cases heq
    exact Or.inl ⟨d, hd, rfl, rfl, rfl⟩
  · rename_i d hd
    have heq := except_pure_ok' success
    cases heq
    exact Or.inr ⟨d, hd, rfl, rfl, rfl⟩
  · cases success

/-- Transport any already-established source property through the actual reader.
For universe scope, the source property must still come from the original source
domain and ingestion refinement; it is not inferred from `success`. -/
theorem expansion_stored_property (inp : ViewInput) (view : BlockView) (name : Name)
    (P : Array Name → Expr → Prop)
    (defs : ∀ d : DefinitionVal, inp.const? name = some (.defnInfo d) →
      P d.cnst.levelParams d.value)
    (thms : ∀ d : TheoremVal, inp.const? name = some (.thmInfo d) →
      P d.cnst.levelParams d.value)
    {x : Expansion} {type : Expr}
    (success : view.expansion inp name = .ok (x, type))
    (rewrite : x.needsRewrite = true) : P x.levelParams x.value := by
  rcases expansion_stored_origin inp view name success rewrite with hd | ht
  · obtain ⟨d, hd, hp, hv, _⟩ := hd
    rw [hp, hv]
    exact defs d hd
  · obtain ⟨d, ht, hp, hv, _⟩ := ht
    rw [hp, hv]
    exact thms d ht

end Ix.CompileCert.Opt
