import IxVMRefinement.Binding.ShapeAnchors

/-! # The stored shapes at the groups of `Iff` and `Nonempty`

`RoleFreeShapes` at group 16 (`Iff`, `Iff.intro`, `Iff.rec`) and group 17 (`Nonempty` and its
constructor and recursor) asks for the stored shapes up to the group. Every field of `Shapes` but
one is guarded by a group below (`Bool` at 6) or above (the literal groups 41 to 45), so it comes
from the invariant below the group or holds vacuously; the one left is `IffPinned` at 16 and
`NonemptyPinned` at 17, the standard axioms' check of the stored family.

* `roleFreeShapes_iffNonempty_of_pinned`: `RoleFreeShapes` at 16 or 17 from `IffPinned`
  (resp. `NonemptyPinned`) of the closure's environment. Producer of that premise: open, the
  stored members read from the group's `validate_role` of the three roles (the member-pin lemmas
  `validateRole_stdMember`, `validateMember_induct`, `validateMember_ctor`,
  `validateMember_storedRecCounts`, `familyKey_of_stdRecPin`, `recLps_of_stdRecPin`) joined to
  the kept declarations (`GroupKept`), as `anchor_stored_matchesPin` does for an anchor.
-/

universe u

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

/-- **`RoleFreeShapes` at the groups of `Iff` and `Nonempty`**, from the stored family's pin at
the closure's environment (module docstring). -/
theorem roleFreeShapes_iffNonempty_of_pinned {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} (hg : g = 16 ∨ g = 17)
    (hpin : ∀ (R R₁ R' : Ixon.Env) (env₁ : Ix.Kernel.Env .anon),
      Admits ρ t g R R' → AdmitsReads ρ t R R' → StoreLe R₁ R' →
      BndOver.{u} L t (· < g) R₁ env₁ → GroupKept t g R₁ env₁ →
      (g = 16 → IffPinned env₁) ∧ (g = 17 → NonemptyPinned env₁)) :
    RoleFreeShapes.{u} L ρ t g := by
  intro _ R R₁ R' env₁ hadm hrd hle hb hk
  have hs := hb.facts.shapes
  obtain ⟨hI, hN⟩ := hpin R R₁ R' env₁ hadm hrd hle hb hk
  obtain ⟨gB, -, -, gC, gS, gL, -, -, gCN, gSL, gI, gN⟩ := anchor_groups
  have below : ∀ X : Ix.Kernel.Role, Ix.SpecDigest.groupOf X < g + 1 →
      Ix.SpecDigest.groupOf X ≠ g → Ix.SpecDigest.groupOf X < g := fun X h hne => by omega
  exact {
    bool := fun h => hs.bool (below _ h (by rw [gB]; omega))
    char := fun h => hs.char (below _ h (by rw [gC]; omega))
    string := fun h => hs.string (below _ h (by rw [gS]; omega))
    list := fun h => hs.list (below _ h (by rw [gL]; omega))
    charOfNat := fun h => hs.charOfNat (below _ h (by rw [gCN]; omega))
    stringOfList := fun h => hs.stringOfList (below _ h (by rw [gSL]; omega))
    iff := fun h => by
      by_cases h16 : g = 16
      · exact hI h16
      · exact hs.iff (below _ h (by rw [gI]; omega))
    nonempty := fun h => by
      by_cases h17 : g = 17
      · exact hN h17
      · exact hs.nonempty (below _ h (by rw [gN]; omega)) }

end IxVM.Refinement.Binding
