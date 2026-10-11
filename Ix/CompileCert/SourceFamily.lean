import Ix.AuxGen.SourceFamily
import Ix.CompileCert.SourceIdentity

/-!
The production head filter authenticates actual source declarations against
source-order recipes. These lemmas expose that check and its declaration
data. They do not establish generator correctness, source-recipe totality or
the full semantic interpretation of the dependency traversal.
-/

namespace Ix.CompileCert.SourceFamily

open Ix (Name ConstantInfo)
open Ix.AuxGen (AuxDef)
open Ix.AuxGen.SourceFamily
open Ix.Compile.Image.RawExact (nameEq)

theorem signatureMatches_source {name : Name} {params : Array Name} {type : Ix.Expr}
    {actual : Ix.ConstantVal} (matched : signatureMatches name params type actual = true) :
    name = actual.name ∧ params.size = actual.levelParams.size ∧
      SourceIdentity.ExprAgreement params actual.levelParams type actual.type := by
  simp only [signatureMatches, Bool.and_eq_true] at matched
  exact ⟨(Ix.Compile.Image.RawExact.nameEq_eq_true _ _).mp matched.1.1,
    beq_iff_eq.mp matched.1.2, SourceIdentity.agrees_er matched.2⟩

/-- Even a visited name must have a matching declaration in the actual source
lookup. An arbitrary visited set cannot authenticate a missing/custom body. -/
theorem authenticated_source {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {seen : Array Name} {name : Name}
    (accepted : authenticated env recipes fuel seen name = true) :
    ∃ recipe actual,
      recipes.find? (fun r => nameEq r.name name) = some recipe ∧
      env.get? name = some actual ∧ nameEq name actual.getCnst.name = true ∧
      recipe.matches actual = true := by
  unfold authenticated at accepted
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    unfold authenticatedVisit at accepted
    cases hr : recipes.find? (fun r => nameEq r.name name) <;>
      cases ha : env.get? name <;> simp only [hr, ha] at accepted
    all_goals try contradiction
    rename_i recipe actual
    split at accepted
    · rename_i matched
      simp only [Bool.and_eq_true] at matched
      exact ⟨recipe, actual, rfl, rfl, matched.1, matched.2⟩
    · contradiction

/-- Definitions expose both successfully converted expression skeletons,
including the actual value, using the existing source correspondence lemma. -/
theorem authenticated_definition {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {seen : Array Name} {name : Name} {expected : AuxDef}
    (found : recipes.find? (fun r => nameEq r.name name) = some (.definition expected))
    (accepted : authenticated env recipes fuel seen name = true) :
    ∃ actual : Ix.DefinitionVal,
      env.get? name = some (.defnInfo actual) ∧
      expected.name = actual.cnst.name ∧
      actual.safety = (if expected.isUnsafe then .unsafe else .safe) ∧
      expected.levelParams.size = actual.cnst.levelParams.size ∧
      SourceIdentity.ExprAgreement expected.levelParams actual.cnst.levelParams
        expected.typ actual.cnst.type ∧
      SourceIdentity.ExprAgreement expected.levelParams actual.cnst.levelParams
        expected.value actual.value := by
  obtain ⟨recipe, actual, hr, ha, _, matched⟩ := authenticated_source accepted
  rw [found] at hr
  cases Option.some.inj hr
  obtain ⟨value, rfl, data⟩ := SourceIdentity.definitionMatches_source matched
  exact ⟨value, ha, data⟩

/-- Proof bodies are not used to identify theorem semantics; acceptance still
exposes a theorem declaration and its actual successfully converted statement. -/
theorem authenticated_theorem {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {seen : Array Name} {name : Name} {expected : AuxDef}
    (found : recipes.find? (fun r => nameEq r.name name) = some (.theoremDecl expected))
    (accepted : authenticated env recipes fuel seen name = true) :
    ∃ actual : Ix.TheoremVal,
      env.get? name = some (.thmInfo actual) ∧ expected.isUnsafe = false ∧
      expected.name = actual.cnst.name ∧
      expected.levelParams.size = actual.cnst.levelParams.size ∧
      SourceIdentity.ExprAgreement expected.levelParams actual.cnst.levelParams
        expected.typ actual.cnst.type := by
  obtain ⟨recipe, actual, hr, ha, nameMatched, matched⟩ := authenticated_source accepted
  rw [found] at hr
  cases Option.some.inj hr
  clear nameMatched
  cases actual <;> try contradiction
  case thmInfo value =>
    simp only [Recipe.matches, Bool.and_eq_true] at matched
    exact ⟨value, ha, by simpa using matched.1, signatureMatches_source matched.2⟩

/-- A derived image head must have passed the source-only family check. -/
theorem filterHeads_authenticated {env : Ix.Environment} {all heads : Array Name}
    {name : Name} (kept : name ∈ filterHeads env all heads)
    (derived : isDerived name = true) :
    let recipes := (reconstruct env all (heads.any isBRecOn)).toOption.getD #[]
    authenticated { env with overlay := {} } recipes (recipes.size + 1) #[] name = true := by
  unfold filterHeads at kept
  dsimp at kept
  split at kept
  · rename_i absent
    have present : heads.any isDerived = true := Array.any_eq_true'.mpr ⟨name, kept, derived⟩
    simp [present] at absent
  · have chosen := Array.mem_filter.mp kept
    simpa [derived] using chosen.2

/-- The actual declarations selected by the production filter, with no
assumption that auxiliary spelling or binder count identifies their values. -/
theorem filterHeads_source {env : Ix.Environment} {all heads : Array Name} {name : Name}
    (kept : name ∈ filterHeads env all heads) (derived : isDerived name = true) :
    let recipes := (reconstruct env all (heads.any isBRecOn)).toOption.getD #[]
    ∃ recipe actual,
      recipes.find? (fun r => nameEq r.name name) = some recipe ∧
      ({ env with overlay := {} } : Ix.Environment).get? name = some actual ∧
      nameEq name actual.getCnst.name = true ∧ recipe.matches actual = true := by
  exact authenticated_source (filterHeads_authenticated kept derived)

/-- A reconstruction error cannot authenticate any derived image head. -/
theorem filterHeads_constructed {env : Ix.Environment} {all heads : Array Name} {name : Name}
    (kept : name ∈ filterHeads env all heads) (derived : isDerived name = true) :
    ∃ recipes, reconstruct env all (heads.any isBRecOn) = .ok recipes := by
  have source := filterHeads_source kept derived
  cases built : reconstruct env all (heads.any isBRecOn) with
  | error failure =>
    rw [built] at source
    obtain ⟨recipe, _, missing, _⟩ := source
    change (none : Option Recipe) = some recipe at missing
    contradiction
  | ok recipes => exact ⟨recipes, rfl⟩

end Ix.CompileCert.SourceFamily
