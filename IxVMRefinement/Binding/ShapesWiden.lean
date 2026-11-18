import IxVMRefinement.Binding.ClauseFold

/-! # The stored shapes after a group that holds no shape role

`RoleFreeShapes` (the composed residual's hypothesis `groupWithoutRoleUnit`) asks, after the
closure of a group with no role unit, for the stored shapes on the groups up to that group
(`Shapes (· < g + 1)`). Each field of `Shapes` is guarded by the group of one of eight roles
(`Bool`, `Char`, `String`, `List`, `Char.ofNat`, `String.ofList`, `Iff`, `Nonempty`). At a group
that holds none of them, the shapes up to the group are the shapes below it, which the invariant
below the group carries (`BoundaryFacts.shapes`).

* `shapeRoles`, `ShapeGroup g`: the eight roles, and a group that holds one of them (the groups
  6, 16, 17 and 41 to 45 of the schedule).
* `shapes_widen`: the shapes below `g` are the shapes up to `g` when `g` holds no shape role.
* `roleFreeShapes_of_shapeGroups`: **`RoleFreeShapes` at every group, from `RoleFreeShapes` at
  the shape groups.** The other groups read no new shape.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

/-- **The roles whose groups guard a field of `Shapes`.** -/
def shapeRoles : List Ix.Kernel.Role :=
  [.bool, .char, .string, .list, .charOfNat, .stringOfList, .iff, .nonempty]

/-- **A group that holds a shape role.** -/
def ShapeGroup (g : Nat) : Prop :=
  ∃ X ∈ shapeRoles, Ix.SpecDigest.groupOf X = g

/-- **The shapes below `g` are the shapes up to `g`** when `g` holds no shape role. -/
theorem shapes_widen {g : Nat} {env : Ix.Kernel.Env .anon} (hs : Shapes (· < g) env)
    (hno : ¬ ShapeGroup g) : Shapes (· < g + 1) env := by
  have below : ∀ X ∈ shapeRoles, Ix.SpecDigest.groupOf X < g + 1 →
      Ix.SpecDigest.groupOf X < g := by
    intro X hX hor
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hor) with h | h
    · exact h
    · exact absurd ⟨X, hX, h⟩ hno
  exact {
    bool := fun h => hs.bool (below .bool (by decide) h)
    char := fun h => hs.char (below .char (by decide) h)
    string := fun h => hs.string (below .string (by decide) h)
    list := fun h => hs.list (below .list (by decide) h)
    charOfNat := fun h => hs.charOfNat (below .charOfNat (by decide) h)
    stringOfList := fun h => hs.stringOfList (below .stringOfList (by decide) h)
    iff := fun h => hs.iff (below .iff (by decide) h)
    nonempty := fun h => hs.nonempty (below .nonempty (by decide) h) }

/-- **`RoleFreeShapes` at every group, from `RoleFreeShapes` at the shape groups**: at a group
that holds no shape role the invariant below the group already has the shapes up to it. -/
theorem roleFreeShapes_of_shapeGroups {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (h : AtGroups Run (fun ρ t g => ShapeGroup g → RoleFreeShapes.{u} L ρ t g)) :
    AtGroups Run (RoleFreeShapes.{u} L) := by
  intro t ρ Rs hrun hall ht g h6 h77
  by_cases hsg : ShapeGroup g
  · exact h t ρ Rs hrun hall ht g h6 h77 hsg
  · intro _ R R₁ R' env₁ _ _ _ hb _
    exact shapes_widen hb.facts.shapes hsg

set_option maxRecDepth 100000 in
/-- The shape groups are the groups 6, 16, 17 and 41 to 45. -/
theorem shapeGroup_iff (g : Nat) :
    ShapeGroup g ↔ g = 6 ∨ g = 16 ∨ g = 17 ∨ (41 ≤ g ∧ g ≤ 45) := by
  have e : shapeRoles.map Ix.SpecDigest.groupOf = [6, 41, 42, 43, 44, 45, 16, 17] := by
    decide +kernel
  constructor
  · rintro ⟨X, hX, rfl⟩
    have hm : Ix.SpecDigest.groupOf X ∈ shapeRoles.map Ix.SpecDigest.groupOf :=
      List.mem_map.mpr ⟨X, hX, rfl⟩
    rw [e] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  · intro hg
    have hm : g ∈ shapeRoles.map Ix.SpecDigest.groupOf := by
      rw [e]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨X, hX, hXg⟩ := List.mem_map.mp hm
    exact ⟨X, hX, hXg⟩

/-- **The composed residual's `groupWithoutRoleUnit`, from its instances at the eight shape
groups.** -/
theorem groupWithoutRoleUnit_of_shapeGroups
    (h : ∀ calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F),
      AtGroups (BindingRun calls)
        (fun ρ t g => ShapeGroup g → RoleFreeShapes.{u} Typing.FormerOpenTraceAt ρ t g)) :
    ∀ calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F),
      AtGroups (BindingRun calls) (RoleFreeShapes.{u} Typing.FormerOpenTraceAt) :=
  fun calls => roleFreeShapes_of_shapeGroups (h calls)

end IxVM.Refinement.Binding
