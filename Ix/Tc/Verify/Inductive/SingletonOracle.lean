import Ix.Tc.Verify.Inductive.SingletonEnumeration

/-!
# Certificate-backed singleton recursor oracle

The family/constructor and recursor declarations are separate physical Ix
blocks.  `SingletonFamilyCatalogLink.oracle` closes the former.  This module
closes the latter for the executable enumeration fragment, using the exact
generated equations and pattern-soundness theorem rather than an ambient
reflection premise.
-/

namespace Ix.Tc

open Lean4Lean (VEnv VInductDecl)

namespace SingletonRecursorCatalogLink

/-- The exact physical member array of the singleton recursor block. -/
def members
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family) : Array (KId .anon) :=
  #[link.recursorId]

@[simp] theorem recursor_mem
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family) : link.recursorId ∈ link.members := by
  simp [members]

/-- Membership in the recursor block identifies its sole declaration. -/
theorem member_eq
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    {id : KId .anon} (hmember : id ∈ link.members) :
    id = link.recursorId := by
  simpa [members] using hmember

/-- Construct a complete `InductiveOracle` for the actual singleton recursor
block.  Every rule and pattern is selected by its concrete array position and
is justified by the equation installed by the E2a transaction. -/
def oracle
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation) :
    InductiveOracle trProj catalog nameOf trusted before where
  members := fun id => id ∈ link.members
  nonempty := ⟨link.recursorId, link.recursor_mem⟩
  fresh := by
    intro id hmember
    rw [link.member_eq hmember]
    exact link.fresh
  after := after
  envLE := tx.facts.envLE
  blockWF := tx.facts.afterWF
  translateBlock := by
    intro id hmember
    have hid := link.member_eq hmember
    subst id
    obtain ⟨hraw, hlookup, hwf⟩ := link.translateRecursor
    exact ⟨link.recursorConcrete,
      .str tx.certificate.generation.block.sourceType.name "rec",
      tx.certificate.generation.recursor,
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
    exact link.enumerationPatternRel shape hrule

@[simp] theorem oracle_members_iff
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    (id : KId .anon) :
    (link.oracle shape).members id ↔ id ∈ link.members := by
  change (id ∈ link.members) ↔ id ∈ link.members
  exact Iff.rfl

end SingletonRecursorCatalogLink

end Ix.Tc
