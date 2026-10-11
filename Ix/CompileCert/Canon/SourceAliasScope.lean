import Ix.CompileCert.Canon.SourceScopes
import Ix.CompileCert.Canon.NestedCanonSource

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- A fold invariant whose step may use actual membership in the traversed
list. This avoids any premise about values outside the real class array. -/
theorem list_foldl_inv_mem {α β : Type} (P : β → Prop) (step : β → α → β)
    (xs : List α) (init : β) (initial : P init)
    (each : ∀ x ∈ xs, ∀ state, P state → P (step state x)) :
    P (xs.foldl step init) := by
  induction xs generalizing init with
  | nil => exact initial
  | cons x xs ih =>
    apply ih
    · exact each x List.mem_cons_self init initial
    · intro y hy state hs
      exact each y (List.mem_cons_of_mem _ hy) state hs

theorem array_foldl_inv_mem {α β : Type} (P : β → Prop) (step : β → α → β)
    (xs : Array α) (init : β) (initial : P init)
    (each : ∀ x ∈ xs, ∀ state, P state → P (step state x)) :
    P (xs.foldl step init) := by
  rw [← Array.foldl_toList]
  exact list_foldl_inv_mem P step xs.toList init initial (by simpa using each)

/-- Alias-map results are actual first members of the given classes, even
if source lookup keys have coincident cached digests. -/
theorem aliasesOf_range (classes : Array (Array Name)) {query value : Name}
    (h : (aliasesOf classes).get? query = some value) : value ∈ repsOf classes := by
  let P := fun (m : Std.HashMap Name Name) => ∀ query value,
    m.get? query = some value → value ∈ repsOf classes
  have preserved : P (aliasesOf classes) := by
    unfold aliasesOf
    apply array_foldl_inv_mem P
    · simp [P]
    · intro cls member state hs
      split
      · rename_i rep hrep
        have reached : rep ∈ repsOf classes := by
          unfold repsOf
          exact Array.mem_filterMap.mpr ⟨cls,member,hrep⟩
        apply array_foldl_inv_mem P
        · exact hs
        · intro name _ m hm query value found
          change (m.insert name rep)[query]? = some value at found
          rw [Std.HashMap.getElem?_insert] at found
          by_cases equal : (name == query) = true
          · have hv : rep = value := by
              simpa [equal] using found
            exact hv ▸ reached
          · apply hm query value
            simpa [equal] using found
      · exact hs
  exact preserved query value h

/-- Alias replacement never introduces an unprotected source read: each
replacement is already a seed of this actual canonical expansion. -/
theorem SourceReach.alias_value (source : Ix.Environment)
    (groups : Std.HashMap Name (Array (Array Name))) (classes : Array (Array Name))
    {query value : Name} (h : (aliasesOf classes).get? query = some value) :
    SourceReach source groups (repsOf classes).toList value := by
  apply SourceReach.seed
  simpa using aliasesOf_range classes h

theorem RefScope.canonicalAliases {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {classes : Array (Array Name)}
    {e : Expr} (h : RefScope (SourceReach source groups (repsOf classes).toList) e) :
    RefScope (SourceReach source groups (repsOf classes).toList)
      (Ix.Compile.Canon.canonicalizeConstNames (aliasesOf classes) e) :=
  h.canonicalizeConstNames _ (fun _ _ found => SourceReach.alias_value source groups classes found)

end Ix.CompileCert.Canon
