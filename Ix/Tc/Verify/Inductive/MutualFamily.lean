import Ix.Tc.Verify.Check.BlockAcceptance
import Ix.Tc.Verify.Inductive.BlockCertificate

/-!
# Certified mutual-family admission

A Lean4Lean block certificate owns one atomic semantic transaction for every
family and constructor in a mutual declaration.  This module supplies the
Ix-facing representation boundary for the corresponding physical
family/constructor block.  It does not split the source declaration into
singleton transactions and it does not construct an `InductiveOracle`.

The link deliberately excludes generated recursors.  They live in a second
physical Ix block, although their Theory constants and equations are already
installed by the same source transaction.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VConstVal VEnv VInductDecl)

/-- Exact concrete kinds permitted in the family/constructor half of a
mutual-inductive transaction. -/
def KConst.IsMutualFamilyMember : KConst .anon → Prop
  | .indc .. | .ctor .. => True
  | _ => False

namespace KConst.IsMutualFamilyMember

theorem inductiveMember {concrete : KConst .anon}
    (h : concrete.IsMutualFamilyMember) : concrete.IsInductiveMember := by
  cases concrete <;>
    simp_all [KConst.IsMutualFamilyMember, KConst.IsInductiveMember]

theorem noRecursorRule {concrete : KConst .anon}
    (h : concrete.IsMutualFamilyMember) (rule : RecRule .anon) :
    ¬concrete.HasRecursorRule rule := by
  cases concrete <;>
    simp_all [KConst.IsMutualFamilyMember, KConst.HasRecursorRule]

theorem noRecursorRuleAt {concrete : KConst .anon}
    (h : concrete.IsMutualFamilyMember) (index : Nat)
    (rule : RecRule .anon) : ¬concrete.RecursorRuleAt index rule := by
  cases concrete <;>
    simp_all [KConst.IsMutualFamilyMember, KConst.RecursorRuleAt]

theorem notRecursorMemberOf {concrete : KConst .anon}
    (h : concrete.IsMutualFamilyMember) (block : KId .anon) :
    ¬concrete.IsRecursorMemberOf block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsMutualFamilyMember, KConst.IsRecursorMemberOf]

end KConst.IsMutualFamilyMember

/-- A concrete member is tied either to one source family or to one source
constructor of the complete mutual declaration.  The disjunction retains
the exact source inventory membership used by Lean4Lean's lookup theorems. -/
def MutualSourceMember (source : VInductDecl) (name : Lean.Name)
    (constant : VConstant) : Prop :=
  (∃ family, family ∈ source.types ∧ name = family.name ∧
      constant = family.toVConstant) ∨
    (∃ constructor, constructor ∈ source.blockConstructorConstants ∧
      name = constructor.name ∧ constant = constructor.toVConstant)

/-- Exact Ix/source correspondence for the family/constructor block of one
certified mutual transaction.

`member` is exhaustive over the physical array.  Together with an
`ExactCheckBlock`, this means every physically owned declaration is tied to
the source transaction; there is no family-local prefix or ambient semantic
fallback. -/
structure MutualFamilyCatalogLink (trProj : RawProjRel)
    (world : VerifyWorld) {source : VInductDecl} {after : VEnv}
    (tx : CertifiedBlockGenerationTransaction source world.venv after) where
  members : Array (KId .anon)
  nonempty : members.size > 0
  member : ∀ ⦃id⦄, id ∈ members →
    ∃ concrete name constant,
      world.catalog id = some concrete ∧
      concrete.IsMutualFamilyMember ∧
      world.nameOf id.addr = some name ∧
      concrete.lvls.toNat = constant.uvars ∧
      RawExprRel (uvars := concrete.lvls.toNat) after world.nameOf trProj []
        concrete.ty constant.type ∧
      MutualSourceMember source name constant
  fresh : ∀ ⦃id⦄, id ∈ members → ¬world.trusted id

namespace MutualFamilyCatalogLink

/-- Derive the exact Theory lookup and constant-WF facts from the current
Lean4Lean consumer certificate. -/
theorem translateMember {trProj : RawProjRel} {world : VerifyWorld}
    {source : VInductDecl} {after : VEnv}
    {tx : CertifiedBlockGenerationTransaction source world.venv after}
    (link : MutualFamilyCatalogLink trProj world tx)
    {id : KId .anon} (hmember : id ∈ link.members) :
    ∃ concrete name constant,
      world.catalog id = some concrete ∧
      RawInductiveConstRel after world.nameOf trProj id concrete name
        constant ∧
      after.constants name = some constant ∧ constant.WF after := by
  obtain ⟨concrete, name, constant, hcatalog, hkind, hname, huvars,
    htype, hsource⟩ := link.member hmember
  let certificate := tx.toBlockCertificate
  have hlookup : after.constants name = some constant := by
    rcases hsource with
      ⟨family, hfamily, rfl, rfl⟩ |
        ⟨constructor, hconstructor, rfl, rfl⟩
    · exact certificate.familyLookup hfamily
    · exact certificate.constructorLookup hconstructor
  exact ⟨concrete, name, constant, hcatalog,
    { kind := hkind.inductiveMember
      nameEq := hname
      uvars := huvars
      type := htype },
    hlookup, certificate.afterWF.ordered.constWF hlookup⟩

/-- One physical family/constructor member has complete trusted-catalog
provenance in the post-environment of the mutual transaction. -/
theorem semanticEntry {trProj : RawProjRel} {world : VerifyWorld}
    {source : VInductDecl} {after : VEnv}
    {tx : CertifiedBlockGenerationTransaction source world.venv after}
    (link : MutualFamilyCatalogLink trProj world tx)
    {id : KId .anon} (hmember : id ∈ link.members) :
    TrustedCatalogEntry trProj world.catalog world.nameOf after id := by
  obtain ⟨concrete, name, constant, hcatalog, hraw, hlookup, hwf⟩ :=
    link.translateMember hmember
  have hkind : concrete.IsMutualFamilyMember := by
    obtain ⟨_, _, _, hcatalog', hkind, _⟩ := link.member hmember
    rw [hcatalog] at hcatalog'
    cases hcatalog'
    exact hkind
  exact .ambient hcatalog hraw hlookup hwf
    (fun rule hrule => False.elim (hkind.noRecursorRule rule hrule))
    (fun ruleIndex rule hrule =>
      False.elim (hkind.noRecursorRuleAt ruleIndex rule hrule))

/-- Turn the representation link and exact physical ownership into the one
atomic semantic transition for the complete mutual family block. -/
theorem transition {trProj : RawProjRel} {world : VerifyWorld}
    {source : VInductDecl} {after : VEnv}
    {tx : CertifiedBlockGenerationTransaction source world.venv after}
    (link : MutualFamilyCatalogLink trProj world tx)
    {block : KId .anon}
    (exactBlock : ExactCheckBlock world block link.members .inductive') :
    SemanticBlockTransitionCertificate trProj world block link.members
      .inductive' after where
  exactBlock := exactBlock
  fresh := link.fresh
  envLE := tx.toBlockCertificate.envLE
  afterWF := tx.toBlockCertificate.afterWF
  entry := fun {_} hmember => link.semanticEntry hmember

end MutualFamilyCatalogLink

end Ix.Tc
