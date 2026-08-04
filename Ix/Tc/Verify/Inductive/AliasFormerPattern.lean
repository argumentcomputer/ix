import Ix.Tc.Verify.Inductive.SingletonEnumeration
import Ix.Tc.Verify.Inductive.AliasFormerRecursorFixture

/-!
# Family-result-normalizing enumeration pattern

Once Lean4Lean has normalized `TypeFamilyAlias` to `Type`, `AliasFormer` is
the one-constructor instance of the certified singleton-enumeration fragment.
This module proves that exact fragment classification and instantiates the
generic registered-equation pattern theorem for `AliasFormer.mk`.
-/

namespace Ix.Tc.AliasFormerPattern

open Lean4Lean
open Lean4Lean.InductiveFixtures
open AliasFormerCertificateFixture
open AliasFormerRecursorFixture

private abbrev generation := transaction.certificate.generation

private theorem generationCtorPairsNonempty :
    0 < generation.block.ctorPairs.length := by
  native_decide

/-- The normalized AliasFormer generation is a nonempty, nullary,
nonrecursive singleton enumeration. -/
theorem enumerationShape :
    CertifiedSingletonGeneration.IsEnumeration generation := by
  refine {
    noUniverses := rfl
    noParameters := rfl
    largeElimination := rfl
    noIndices := rfl
    nonempty := generationCtorPairsNonempty
    constructor := ?_ }
  intro index normalized hnormalized
  have hindex : index = 0 := by
    have hlt : index < generation.block.ctorPairs.length :=
      (List.getElem?_eq_some_iff.mp hnormalized).1
    change index < 1 at hlt
    omega
  subst index
  have hnormalizedEq : normalized = mkNormalized := by
    rw [mkNormalizedAt] at hnormalized
    exact (Option.some.inj hnormalized).symm
  subst normalized
  exact ⟨rfl, rfl, rfl⟩

private theorem constructorIndex : 0 < familyLink.constructorIds.size := by
  change 0 < AliasFormerFixture.constructorIds.size
  decide

/-- The concrete production pattern selects the sole minor premise. -/
def pattern : RecursorRulePattern :=
  recursorLink.enumerationPattern 0 constructorIndex mkNormalized

theorem metadata {rule : RecRule .anon}
    (hrule : recursorConcrete.RecursorRuleAt 0 rule) :
    RawRecursorRulePatternMetadataRel catalog nameOf recursorId
      recursorConcrete rule pattern := by
  change RawRecursorRulePatternMetadataRel world.catalog world.nameOf
    recursorLink.recursorId recursorLink.recursorConcrete rule pattern
  obtain ⟨hindex, normalized, hnormalized, hmetadata⟩ :=
    recursorLink.enumerationPatternMetadata enumerationShape hrule
  have hnormalizedEq : normalized = mkNormalized := by
    rw [mkNormalizedAt] at hnormalized
    exact (Option.some.inj hnormalized).symm
  subst normalized
  have hproof : hindex = constructorIndex := Subsingleton.elim _ _
  subst hindex
  exact hmetadata

/-- The pattern denotes the exact registered AliasFormer equation. -/
theorem sound {rule : RecRule .anon}
    (hrule : recursorConcrete.RecursorRuleAt 0 rule) :
    pattern.Sound finalEnv := by
  change (recursorLink.enumerationPattern 0 constructorIndex
    mkNormalized).Sound finalEnv
  exact recursorLink.enumerationPatternSound enumerationShape hrule
    constructorIndex mkNormalized mkNormalizedAt

theorem patternRel {rule : RecRule .anon}
    (hrule : recursorConcrete.RecursorRuleAt 0 rule) :
    RawRecursorRulePatternRel finalEnv catalog nameOf recursorId
      recursorConcrete rule pattern :=
  RawRecursorRulePatternRel.of_metadata_sound (metadata hrule)
    (sound hrule)

end Ix.Tc.AliasFormerPattern
