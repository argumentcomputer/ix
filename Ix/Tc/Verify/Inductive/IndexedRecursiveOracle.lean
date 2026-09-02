import Ix.Tc.Verify.Inductive.IndexedRecursiveSoundness

/-!
# Certificate-backed indexed recursive recursor oracle

This module closes the complete production recursor oracle for the certified
`IndexedVec` fixture.  Unlike the singleton-enumeration oracle, its two rule
patterns validate a uniform parameter and a changing index; the second rule
also reconstructs the recursive call at the predecessor index.
-/

namespace Ix.Tc.IndexedRecursivePattern

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture

/-- The exact two-rule indexed-recursive recursor oracle.  The physical Ix
recursor remains a singleton block member; its rule array is dispatched by
the certified constructor count and each branch uses the corresponding
generated-equation soundness theorem. -/
def oracle
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family) :
    InductiveOracle trProj catalog nameOf trusted natFinalEnv where
  members := fun id => id ∈ link.members
  nonempty := ⟨link.recursorId, link.recursor_mem⟩
  fresh := by
    intro id hmember
    rw [link.member_eq hmember]
    exact link.fresh
  after := indexedVecFinalEnv
  envLE := transaction.facts.envLE
  blockWF := transaction.facts.afterWF
  translateBlock := by
    intro id hmember
    have hid := link.member_eq hmember
    subst id
    obtain ⟨hraw, hlookup, hwf⟩ := link.translateRecursor
    exact ⟨link.recursorConcrete,
      .str transaction.certificate.generation.block.sourceType.name "rec",
      transaction.certificate.generation.recursor,
      link.recursorCatalog, hraw, hlookup, hwf⟩
  recursorFacts := by
    intro id concrete rule hmember hcatalog hrule
    have hid := link.member_eq hmember
    subst id
    have hconcrete : concrete = link.recursorConcrete := by
      rw [link.recursorCatalog] at hcatalog
      exact Option.some.inj hcatalog.symm
    subst concrete
    exact link.registeredRule hrule
  recursorPatterns := by
    intro id concrete ruleIndex rule hmember hcatalog hrule
    have hid := link.member_eq hmember
    subst id
    have hconcrete : concrete = link.recursorConcrete := by
      rw [link.recursorCatalog] at hcatalog
      exact Option.some.inj hcatalog.symm
    subst concrete
    have hcount : family.constructorIds.size = 2 := constructorCount family
    have hbound := link.recursorShape.ruleCount hrule
    have hzero : 0 < family.constructorIds.size := by omega
    have hone : 1 < family.constructorIds.size := by omega
    rcases (show ruleIndex = 0 ∨ ruleIndex = 1 by omega) with rfl | rfl
    · exact ⟨nilPattern (family.constructorIds[0]'hzero),
        nilPatternRel link hzero hrule, rfl⟩
    · exact ⟨consPattern (family.constructorIds[1]'hone),
        consPatternRel link hone hrule, rfl⟩

@[simp] theorem oracle_members_iff
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family) (id : KId .anon) :
    (oracle link).members id ↔ id ∈ link.members := by
  change (id ∈ link.members) ↔ id ∈ link.members
  exact Iff.rfl

end Ix.Tc.IndexedRecursivePattern
