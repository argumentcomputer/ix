import Ix.AuxGen.Names
import Ix.AuxGen.CasesOn
import Ix.Compile.Pass.Names
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

namespace Ix.CompileCert.AuxNames

open Ix (Name RecursorVal)
open Ix.AuxGen (AuxNames AuxDef generateCasesOnFor generateCasesOnPrototype)
open Ix.Compile.Pass (hasReserved isReservedComponent)

theorem reserved_mkStr (owner : Name) (suffix : String) :
    hasReserved (Name.mkStr owner suffix) = (isReservedComponent suffix || hasReserved owner) := rfl

/-- The compiler's helper identities are structurally outside the accepted
source namespace. This says nothing about digest injectivity; the ordinary
checked map/content publication rules remain necessary. -/
theorem member_reserved (representative owner : Name) (perm : Array Nat) (kind : String)
    (helper : kind ≠ "rec") :
    hasReserved ((AuxNames.compiler representative perm).member owner kind) = true := by
  simp [AuxNames.member, AuxNames.compiler, helper, reserved_mkStr,
    isReservedComponent, Ix.Compile.Pass.ixComponent]
  exact Or.inr (Or.inl (String.startsWith_string_iff.mpr ⟨[], by simp⟩))

theorem member_source_disjoint (representative owner source : Name) (perm : Array Nat) (kind : String)
    (helper : kind ≠ "rec") (accepted : hasReserved source = false) :
    (AuxNames.compiler representative perm).member owner kind ≠ source := by
  intro same
  have reserved := member_reserved representative owner perm kind helper
  rw [same, accepted] at reserved
  contradiction

theorem primary_rec_unchanged (representative owner : Name) (perm : Array Nat) :
    (AuxNames.compiler representative perm).member owner "rec" = Name.mkStr owner "rec" := by
  simp [AuxNames.member, AuxNames.compiler]

theorem nested_rec_unchanged (representative owner : Name) (perm : Array Nat) (index : Nat) :
    (AuxNames.compiler representative perm).nested owner "rec" index =
      Name.mkStr owner s!"rec_{index}" := by
  simp [AuxNames.nested, AuxNames.compiler]
  change owner.mkStr (("rec" ++ "_") ++ index.repr) = owner.mkStr ("rec_" ++ index.repr)
  rw [show ("rec" ++ "_" : String) = "rec_" by decide]

theorem nested_reserved (representative owner : Name) (perm : Array Nat) (kind : String)
    (index : Nat) (helper : kind ≠ "rec") :
    hasReserved ((AuxNames.compiler representative perm).nested owner kind index) = true := by
  cases slot : perm[index - 1]? with
  | none =>
    simp [AuxNames.nested, AuxNames.compiler, helper, slot, reserved_mkStr,
      isReservedComponent, Ix.Compile.Pass.ixComponent]
    exact Or.inr (Or.inl (String.startsWith_string_iff.mpr ⟨[], by simp⟩))
  | some value =>
    by_cases outside : value = 0xFFFFFFFFFFFFFFFF <;>
      simp [AuxNames.nested, AuxNames.compiler, helper, slot, outside, reserved_mkStr,
        isReservedComponent, Ix.Compile.Pass.ixComponent]
    all_goals exact Or.inr (Or.inl (String.startsWith_string_iff.mpr ⟨[], by simp⟩))

theorem source_member (owner : Name) (kind : String) :
    ({} : AuxNames).member owner kind = Name.mkStr owner kind := rfl

theorem source_nested (owner : Name) (kind : String) (index : Nat) :
    ({} : AuxNames).nested owner kind index = Name.mkStr owner s!"{kind}_{index}" := rfl

/-- Choosing another emitted name only replaces the result's name field.
The target lookup, generated type/value, failures and state effects agree. -/
theorem casesOn_name_only (left right target : Name) (recursor : RecursorVal) :
    generateCasesOnFor left target recursor =
      (fun result => result.map fun d => { d with name := left }) <$>
        generateCasesOnFor right target recursor := by
  simp only [generateCasesOnFor, Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

end Ix.CompileCert.AuxNames
