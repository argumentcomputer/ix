import Ix.CompileCert.SourceFamily

/-!
Successful source-family authentication returns a finite set of matching
source declarations containing the requested helper and closed under recipe
dependencies. The proof follows the actual traversal with shared visits;
cycles do not assume that unchecked declarations are valid. Generator laws
and the interpretation of recipe correspondence remain separate obligations.
-/

namespace Ix.CompileCert.SourceFamilyTraversal

open Ix (Name ConstantInfo)
open Ix.AuxGen.SourceFamily
open Ix.Compile.Image.RawExact (nameEq)

def Checked (env : Ix.Environment) (recipes : Array Recipe) (name : Name) : Prop :=
  ∃ recipe actual,
    recipes.find? (fun r => nameEq r.name name) = some recipe ∧
    env.get? name = some actual ∧ nameEq name actual.getCnst.name = true ∧
    recipe.matches actual = true

def AllChecked (env : Ix.Environment) (recipes : Array Recipe) (names : Array Name) : Prop :=
  ∀ name ∈ names, Checked env recipes name

theorem optionListFold_preserves {α β : Type} (step : β → α → Option β)
    (property : β → Prop) (preserves : ∀ before item after,
      property before → step before item = some after → property after)
    (items : List α) {before after : β} (valid : property before)
    (success : items.foldlM step before = some after) : property after := by
  induction items generalizing before with
  | nil => simpa using Option.some.inj success ▸ valid
  | cons item rest ih =>
    cases next : step before item with
    | none => simp [List.foldlM, next] at success
    | some state =>
      simp only [List.foldlM_cons, next, bind, Option.bind] at success
      exact ih (preserves before item state valid next) success

theorem optionArrayFold_preserves {α β : Type} (step : β → α → Option β)
    (property : β → Prop) (preserves : ∀ before item after,
      property before → step before item = some after → property after)
    (items : Array α) {before after : β} (valid : property before)
    (success : items.foldlM step before = some after) : property after := by
  rw [← Array.foldlM_toList] at success
  exact optionListFold_preserves step property preserves items.toList valid success

/-- Every newly retained visit corresponds to a checked source declaration.
This is an invariant of the actual shared traversal, not a second checker. -/
theorem visit_allChecked {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {seen : Array Name} {name : Name} {after : Array Name}
    (valid : AllChecked env recipes seen)
    (success : authenticatedVisit env recipes fuel seen name = some after) :
    AllChecked env recipes after := by
  induction fuel generalizing seen name after with
  | zero => contradiction
  | succ fuel ih =>
    have here : Checked env recipes name := SourceFamily.authenticated_source
      (fuel := fuel + 1) (seen := seen)
      (by simp only [authenticated, success, Option.isSome_some])
    unfold authenticatedVisit at success
    cases hr : recipes.find? (fun r => nameEq r.name name) <;>
      cases ha : env.get? name <;> simp only [hr, ha] at success
    all_goals try contradiction
    split at success
    · split at success
      · cases Option.some.inj success
        exact valid
      · apply optionArrayFold_preserves _ (AllChecked env recipes) _ _ ?_ success
        · intro before item next validBefore step
          split at step
          · exact ih validBefore step
          · cases Option.some.inj step
            exact validBefore
        · intro member present
          rcases Array.mem_push.mp present with previous | same
          · exact valid member previous
          · subst member
            exact here
    · contradiction

theorem fresh_visit_allChecked {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {name : Name} {after : Array Name}
    (success : authenticatedVisit env recipes fuel #[] name = some after) :
    AllChecked env recipes after := by
  apply visit_allChecked (fun _ member => by simp at member) success

def Includes (before after : Array Name) : Prop := ∀ name ∈ before, name ∈ after

theorem includes_trans {a b c : Array Name} (ab : Includes a b) (bc : Includes b c) :
    Includes a c := fun name member => bc name (ab name member)

theorem visit_members {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {seen : Array Name} {name : Name} {after : Array Name}
    (success : authenticatedVisit env recipes fuel seen name = some after) :
    Includes seen after ∧ name ∈ after := by
  induction fuel generalizing seen name after with
  | zero => contradiction
  | succ fuel ih =>
    unfold authenticatedVisit at success
    cases hr : recipes.find? (fun r => nameEq r.name name) <;>
      cases ha : env.get? name <;> simp only [hr, ha] at success
    all_goals try contradiction
    split at success
    · split at success
      · rename_i visited
        cases Option.some.inj success
        obtain ⟨prior, member, same⟩ := Array.any_eq_true'.mp visited
        have equal := (Ix.Compile.Image.RawExact.nameEq_eq_true _ _).mp same
        exact ⟨fun _ member => member, equal ▸ member⟩
      · have grows : Includes (seen.push name) after := by
          apply optionArrayFold_preserves _ (Includes (seen.push name)) _ _
            (fun _ member => member) success
          intro before item next keeps step
          split at step
          · exact includes_trans keeps (ih step).1
          · cases Option.some.inj step
            exact keeps
        exact ⟨fun member present => grows member (Array.mem_push.mpr (Or.inl present)),
          grows name (Array.mem_push.mpr (Or.inr rfl))⟩
    · contradiction

def selected (recipes : Array Recipe) (name : Name) : Bool :=
  recipes.any (fun r => nameEq r.name name)

def step (env : Ix.Environment) (recipes : Array Recipe) (fuel : Nat)
    (seen : Array Name) (name : Name) : Option (Array Name) :=
  if selected recipes name then authenticatedVisit env recipes fuel seen name else some seen

theorem step_extends {env : Ix.Environment} {recipes : Array Recipe} {fuel : Nat}
    {seen after : Array Name} {name : Name} (success : step env recipes fuel seen name = some after) :
    Includes seen after := by
  unfold step at success
  split at success
  · exact (visit_members success).1
  · cases Option.some.inj success
    exact fun _ member => member

theorem step_inserts {env : Ix.Environment} {recipes : Array Recipe} {fuel : Nat}
    {seen after : Array Name} {name : Name}
    (chosen : selected recipes name = true) (success : step env recipes fuel seen name = some after) :
    name ∈ after := by
  simp only [step, chosen, ↓reduceIte] at success
  exact (visit_members success).2

theorem optionListFold_extends (f : Array Name → Name → Option (Array Name))
    (grows : ∀ before item after, f before item = some after → Includes before after)
    (items : List Name) {before after : Array Name}
    (success : items.foldlM f before = some after) : Includes before after := by
  apply optionListFold_preserves f (Includes before) _ items (fun _ member => member) success
  intro a item b prior result
  exact includes_trans prior (grows a item b result)

theorem optionListFold_records (f : Array Name → Name → Option (Array Name))
    (pick : Name → Bool)
    (grows : ∀ before item after, f before item = some after → Includes before after)
    (adds : ∀ before item after, pick item = true → f before item = some after → item ∈ after)
    (items : List Name) {before after : Array Name}
    (success : items.foldlM f before = some after) :
    ∀ item ∈ items, pick item = true → item ∈ after := by
  induction items generalizing before with
  | nil => simp
  | cons item rest ih =>
    cases next : f before item with
    | none => simp [List.foldlM, next] at success
    | some state =>
      simp only [List.foldlM_cons, next, bind, Option.bind] at success
      intro name member chosen
      rcases List.mem_cons.mp member with same | tail
      · subst name
        exact optionListFold_extends f grows rest success item (adds before item state chosen next)
      · exact ih success name tail chosen

theorem optionArrayFold_records (f : Array Name → Name → Option (Array Name))
    (pick : Name → Bool)
    (grows : ∀ before item after, f before item = some after → Includes before after)
    (adds : ∀ before item after, pick item = true → f before item = some after → item ∈ after)
    (items : Array Name) {before after : Array Name}
    (success : items.foldlM f before = some after) :
    ∀ item ∈ items, pick item = true → item ∈ after := by
  rw [← Array.foldlM_toList] at success
  intro name member chosen
  exact optionListFold_records f pick grows adds items.toList success name (by simpa using member) chosen

def DependenciesClosed (recipes : Array Recipe) (name : Name) (visited : Array Name) : Prop :=
  ∀ recipe, recipes.find? (fun r => nameEq r.name name) = some recipe →
    ∀ dependency ∈ recipe.references, selected recipes dependency = true → dependency ∈ visited

theorem closed_mono {recipes : Array Recipe} {name : Name} {before after : Array Name}
    (grows : Includes before after) (closed : DependenciesClosed recipes name before) :
    DependenciesClosed recipes name after := by
  intro recipe found dependency member chosen
  exact grows dependency (closed recipe found dependency member chosen)

/-- Every newly visited node has its recipe dependencies in the returned set.
Initially visited nodes need not be closed: this covers the in-flight ancestors
of a cycle without assuming their dependencies have already been checked. -/
theorem visit_newClosed {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {seen : Array Name} {name : Name} {after : Array Name}
    (success : authenticatedVisit env recipes fuel seen name = some after) :
    ∀ member ∈ after, member ∉ seen → DependenciesClosed recipes member after := by
  induction fuel generalizing seen name after with
  | zero => contradiction
  | succ fuel ih =>
    unfold authenticatedVisit at success
    cases hr : recipes.find? (fun r => nameEq r.name name) <;>
      cases ha : env.get? name <;> simp only [hr, ha] at success
    all_goals try contradiction
    rename_i recipe actual
    split at success
    · split at success
      · cases Option.some.inj success
        exact fun _ member missing => False.elim (missing member)
      · change recipe.references.foldlM (step env recipes fuel) (seen.push name) = some after at success
        have rootClosed : DependenciesClosed recipes name after := by
          intro r found dependency member chosen
          rw [hr] at found
          cases Option.some.inj found
          exact optionArrayFold_records (step env recipes fuel) (selected recipes)
            (fun _ _ _ => step_extends) (fun _ _ _ => step_inserts)
            recipe.references success dependency member chosen
        have otherClosed : ∀ member ∈ after, member ∉ seen → member ≠ name →
            DependenciesClosed recipes member after := by
          let property := fun visited => ∀ member ∈ visited, member ∉ seen → member ≠ name →
            DependenciesClosed recipes member visited
          apply optionArrayFold_preserves (step env recipes fuel) property _ _ ?_ success
          · intro before dependency next closed nextResult member present absent different
            by_cases old : member ∈ before
            · exact closed_mono (step_extends nextResult) (closed member old absent different)
            · unfold step at nextResult
              split at nextResult
              · exact ih nextResult member present old
              · cases Option.some.inj nextResult
                exact False.elim (old present)
          · intro member present absent different
            rcases Array.mem_push.mp present with old | same
            · exact False.elim (absent old)
            · exact False.elim (different same)
        intro member present absent
        by_cases same : member = name
        · subst member
          exact rootClosed
        · exact otherClosed member present absent same
    · contradiction

/-- Successful fresh authentication supplies a finite, closed set of actual
matching source declarations containing the requested helper. -/
theorem authenticated_closed {env : Ix.Environment} {recipes : Array Recipe}
    {fuel : Nat} {name : Name} (accepted : authenticated env recipes fuel #[] name = true) :
    ∃ visited : Array Name, name ∈ visited ∧ AllChecked env recipes visited ∧
      ∀ member ∈ visited, DependenciesClosed recipes member visited := by
  obtain ⟨visited, success⟩ := Option.isSome_iff_exists.mp accepted
  refine ⟨visited, (visit_members success).2, fresh_visit_allChecked success, ?_⟩
  intro member present
  exact visit_newClosed success member present (by simp)

theorem filterHeads_closed_source {env : Ix.Environment} {all heads : Array Name} {name : Name}
    (kept : name ∈ filterHeads env all heads) (derived : isDerived name = true) :
    let recipes := (reconstruct env all (heads.any isBRecOn)).toOption.getD #[]
    ∃ visited : Array Name, name ∈ visited ∧
      AllChecked { env with overlay := {} } recipes visited ∧
      ∀ member ∈ visited, DependenciesClosed recipes member visited := by
  exact authenticated_closed (SourceFamily.filterHeads_authenticated kept derived)

end Ix.CompileCert.SourceFamilyTraversal
