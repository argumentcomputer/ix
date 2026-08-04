import Ix.Tc.Verify.Check.BlockAcceptance
import Lean4Lean.Theory.Typing.InductiveCertificate

/-!
# Certified nested-block transactions

This is the Ix consumer boundary for Lean4Lean's `NestedBlockCertificate`.
The Theory transaction stores the original source families and constructors,
then restores every generated recursor and rule before committing them.  The
Ix-facing link below covers only the physical source block; generated
recursors remain a separately owned physical block when one is present.

No `InductiveOracle` is constructed here.  A source member enters trust only
after an exhaustive physical catalog link and an `ExactCheckBlock` prove that
the one nested transaction describes the complete checked block.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VConstVal VEnv VInductDecl)

/-- Exact concrete kinds permitted in the stored source half of a nested
transaction. -/
def KConst.IsNestedSourceMember : KConst .anon → Prop
  | .indc .. | .ctor .. => True
  | _ => False

namespace KConst.IsNestedSourceMember

theorem inductiveMember {concrete : KConst .anon}
    (h : concrete.IsNestedSourceMember) : concrete.IsInductiveMember := by
  cases concrete <;>
    simp_all [KConst.IsNestedSourceMember, KConst.IsInductiveMember]

theorem noRecursorRule {concrete : KConst .anon}
    (h : concrete.IsNestedSourceMember) (rule : RecRule .anon) :
    ¬concrete.HasRecursorRule rule := by
  cases concrete <;>
    simp_all [KConst.IsNestedSourceMember, KConst.HasRecursorRule]

theorem noRecursorRuleAt {concrete : KConst .anon}
    (h : concrete.IsNestedSourceMember) (index : Nat)
    (rule : RecRule .anon) : ¬concrete.RecursorRuleAt index rule := by
  cases concrete <;>
    simp_all [KConst.IsNestedSourceMember, KConst.RecursorRuleAt]

end KConst.IsNestedSourceMember

/-- One physical source member is either a stored family or a stored
constructor of the unflattened nested declaration.  Auxiliary flattening
constants cannot inhabit this inventory. -/
def NestedSourceMember (source : VInductDecl) (name : Lean.Name)
    (constant : VConstant) : Prop :=
  (∃ family, family ∈ source.types ∧ name = family.name ∧
      constant = family.toVConstant) ∨
    (∃ constructor, constructor ∈ source.blockConstructorConstants ∧
      name = constructor.name ∧ constant = constructor.toVConstant)

/-- Exhaustive correspondence between one physical Ix family/constructor
block and the stored source inventory of a completed nested transaction. -/
structure NestedFamilyCatalogLink (trProj : RawProjRel)
    (world : VerifyWorld) {source : VInductDecl} {after : VEnv}
    (certificate : source.NestedBlockCertificate world.venv after) where
  members : Array (KId .anon)
  nonempty : members.size > 0
  member : ∀ ⦃id⦄, id ∈ members →
    ∃ concrete name constant,
      world.catalog id = some concrete ∧
      concrete.IsNestedSourceMember ∧
      world.nameOf id.addr = some name ∧
      concrete.lvls.toNat = constant.uvars ∧
      RawExprRel (uvars := concrete.lvls.toNat) after world.nameOf trProj []
        concrete.ty constant.type ∧
      NestedSourceMember source name constant
  fresh : ∀ ⦃id⦄, id ∈ members → ¬world.trusted id

namespace NestedFamilyCatalogLink

/-- Recover the exact final Theory lookup for a physically linked source
member.  The lookup is obtained from the nested certificate, never from an
ambient future-world premise. -/
theorem translateMember {trProj : RawProjRel} {world : VerifyWorld}
    {source : VInductDecl} {after : VEnv}
    {certificate : source.NestedBlockCertificate world.venv after}
    (link : NestedFamilyCatalogLink trProj world certificate)
    {id : KId .anon} (hmember : id ∈ link.members) :
    ∃ concrete name constant,
      world.catalog id = some concrete ∧
      RawInductiveConstRel after world.nameOf trProj id concrete name
        constant ∧
      after.constants name = some constant ∧ constant.WF after := by
  obtain ⟨concrete, name, constant, hcatalog, hkind, hname, huvars,
    htype, hsource⟩ := link.member hmember
  have hlookup : after.constants name = some constant := by
    rcases hsource with
      ⟨family, hfamily, rfl, rfl⟩ |
        ⟨constructor, hconstructor, rfl, rfl⟩
    · exact certificate.familyLookup hfamily
    · rcases List.mem_flatMap.1 hconstructor with
        ⟨family, hfamily, hconstructor⟩
      exact certificate.constructorLookup hfamily hconstructor
  exact ⟨concrete, name, constant, hcatalog,
    { kind := hkind.inductiveMember
      nameEq := hname
      uvars := huvars
      type := htype },
    hlookup, certificate.afterWF.ordered.constWF hlookup⟩

/-- Complete trusted-catalog provenance for one source member. -/
theorem semanticEntry {trProj : RawProjRel} {world : VerifyWorld}
    {source : VInductDecl} {after : VEnv}
    {certificate : source.NestedBlockCertificate world.venv after}
    (link : NestedFamilyCatalogLink trProj world certificate)
    {id : KId .anon} (hmember : id ∈ link.members) :
    TrustedCatalogEntry trProj world.catalog world.nameOf after id := by
  obtain ⟨concrete, name, constant, hcatalog, hraw, hlookup, hwf⟩ :=
    link.translateMember hmember
  have hkind : concrete.IsNestedSourceMember := by
    obtain ⟨_, _, _, hcatalog', hkind, _⟩ := link.member hmember
    rw [hcatalog] at hcatalog'
    cases hcatalog'
    exact hkind
  exact .ambient hcatalog hraw hlookup hwf
    (fun rule hrule => False.elim (hkind.noRecursorRule rule hrule))
    (fun ruleIndex rule hrule =>
      False.elim (hkind.noRecursorRuleAt ruleIndex rule hrule))

/-- Admit the complete physical source block through the one atomic nested
Theory transition. -/
theorem transition {trProj : RawProjRel} {world : VerifyWorld}
    {source : VInductDecl} {after : VEnv}
    {certificate : source.NestedBlockCertificate world.venv after}
    (link : NestedFamilyCatalogLink trProj world certificate)
    {block : KId .anon}
    (exactBlock : ExactCheckBlock world block link.members .inductive') :
    SemanticBlockTransitionCertificate trProj world block link.members
      .inductive' after where
  exactBlock := exactBlock
  fresh := link.fresh
  envLE := certificate.envLE
  afterWF := certificate.afterWF
  entry := fun {_} hmember => link.semanticEntry hmember

end NestedFamilyCatalogLink

end Ix.Tc
