import Ix.CompileCert.Canon.FreshFamilySeparation
import Ix.Compile.Canon.Expr

namespace Ix.Compile.Canon
open FreshFamilySeparation

def appendNamePart (n : Lean.Name) : String ⊕ Nat → Lean.Name
  | .inl s => .str n s
  | .inr i => .num n i

def appendIxNamePart (n : Ix.Name) : String ⊕ Nat → Ix.Name
  | .inl s => Ix.Name.mkStr n s
  | .inr i => Ix.Name.mkNat n i

theorem keyName_appendParts (parts : List (String ⊕ Nat)) (start : Ix.Name) :
    keyName (parts.foldl appendIxNamePart start) =
      parts.foldl appendNamePart (keyName start) := by
  induction parts generalizing start with
  | nil => rfl
  | cons part rest ih =>
    cases part with
    | inl s =>
      simpa only [List.foldl, appendIxNamePart, appendNamePart, keyName_mkStr] using
        ih (Ix.Name.mkStr start s)
    | inr i =>
      simpa only [List.foldl, appendIxNamePart, appendNamePart, keyName_mkNat] using
        ih (Ix.Name.mkNat start i)

theorem prefix_appendParts (parts : List (String ⊕ Nat)) (start : Lean.Name) :
    start.isPrefixOf (parts.foldl appendNamePart start) = true := by
  induction parts generalizing start with
  | nil => exact prefix_refl _
  | cons part rest ih =>
    cases part with
    | inl s =>
      exact prefix_trans (by simp [Lean.Name.isPrefixOf, prefix_refl]) (ih (.str start s))
    | inr i =>
      exact prefix_trans (by simp [Lean.Name.isPrefixOf, prefix_refl]) (ih (.num start i))

theorem nameReplacePrefix_child {source old aux : Ix.Name} {parts : List (String ⊕ Nat)}
    (h : stripPrefix source old = some parts) :
    (keyName aux).isPrefixOf (keyName (nameReplacePrefix source old aux)) = true := by
  unfold nameReplacePrefix
  rw [h]
  change (keyName aux).isPrefixOf (keyName (parts.foldl appendIxNamePart aux)) = true
  rw [keyName_appendParts]
  exact prefix_appendParts _ _

/-- Reached constructors need no source prefix condition. A retained rewrite
candidate is a strict child of its auxiliary; a non-prefix source spelling is
already protected and therefore selects the fresh child branch. -/
theorem freshCtorFamily_owner (forbidden : List Lean.Name) (aux source old : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) (hsource : keyName source ∈ forbidden) :
    let generated := freshCtorFamily forbidden aux (nameReplacePrefix source old aux) index ctorRoots
    (keyName aux).isPrefixOf (keyName generated) = true ∧ keyName generated ≠ keyName aux := by
  dsimp only
  unfold freshCtorFamily
  split
  · rename_i free
    have headFree : familyFree (keyName aux :: forbidden)
        (keyName (nameReplacePrefix source old aux)) = true := by
      cases h : familyFree (keyName aux :: forbidden) (keyName (nameReplacePrefix source old aux)) with
      | false => simp [ctorFamilyFree, h] at free
      | true => rfl
    have forbiddenFree := List.all_eq_true.mp headFree
    constructor
    · cases hs : stripPrefix source old with
      | none =>
        have sourceFree := forbiddenFree (keyName source) (List.mem_cons_of_mem _ hsource)
        simp [nameReplacePrefix, hs, prefix_refl] at sourceFree
      | some parts => exact nameReplacePrefix_child hs
    · intro equal
      have selfFree := forbiddenFree (keyName aux) List.mem_cons_self
      simp [equal, prefix_refl] at selfFree
  · constructor
    · simp [keyName_mkStr, keyName_mkNat, Lean.Name.isPrefixOf, prefix_refl]
    · intro equal
      have parts := congrArg Lean.Name.getNumParts equal
      simp only [keyName_mkStr, keyName_mkNat, Lean.Name.getNumParts] at parts
      omega

end Ix.Compile.Canon
