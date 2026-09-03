import Ix.Tc.Verify.Inductive.SingletonRecursor
import Ix.Tc.Verify.Env

/-!
# Loaded singleton-inductive ingress correspondence

Anonymous ingress and the production checker operate on concrete `KEnv`
entries.  The semantic singleton adapters, by contrast, consume immutable
catalog entries.  This module makes that boundary explicit without assigning
semantic authority to loading:

* `SingletonFamilyIngressView` records the exact family and constructor
  entries present in one concrete environment, together with the ghost
  interpretation of their anonymous expressions and addresses;
* `SingletonRecursorIngressView` does the same for the separate physical
  recursor block; and
* `toCatalogLink` transports those representation facts through
  `LoadedAgrees` and derives pre-admission freshness from the trusted log and
  the Lean4Lean generation transaction.

The views contain no catalog lookup, trusted-membership negation, declaration
WF, or checker-success premise.  In particular, an anonymous `KEnv` entry
cannot manufacture its source `Lean.Name`; that interpretation remains
deliberate ghost input and will be constructed from the corresponding Ixon
ingress trace.
-/

namespace Ix.Tc

open Lean4Lean (VConstVal VEnv VInductDecl)

/-! ## Family and constructor ingress -/

/-- Exact representation evidence for the singleton family and constructor
entries loaded by anonymous ingress.

The physical address order is retained, and each source constructor is paired
positionally.  Catalog agreement and semantic freshness are intentionally
absent: both are consequences of the surrounding checker state and certified
Theory transaction. -/
structure SingletonFamilyIngressView
    (trProj : RawProjRel) (env : KEnv .anon)
    (nameOf : Address → Option Lean.Name)
    {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after) where
  familyId : KId .anon
  constructorIds : Array (KId .anon)
  constructorCount :
    constructorIds.size =
      tx.certificate.generation.block.sourceType.ctors.length
  familyConcrete : KConst .anon
  familyLoaded : env.get? familyId = some familyConcrete
  familyShape : familyConcrete.IsCertifiedSingletonFamily source
    tx.certificate.generation constructorIds
  familyName : nameOf familyId.addr =
    some tx.certificate.generation.block.sourceType.name
  familyType : RawExprRel (uvars := familyConcrete.lvls.toNat) after
    nameOf trProj [] familyConcrete.ty
      tx.certificate.generation.block.sourceType.type
  constructor : ∀ (index : Nat) (hindex : index < constructorIds.size),
    ∃ sourceConstructor concrete,
      tx.certificate.generation.block.sourceType.ctors[index]? =
        some sourceConstructor ∧
      env.get? constructorIds[index] = some concrete ∧
      concrete.IsCertifiedSingletonConstructor source familyId index
        sourceConstructor ∧
      nameOf constructorIds[index].addr = some sourceConstructor.name ∧
      RawExprRel (uvars := concrete.lvls.toNat) after nameOf trProj []
        concrete.ty sourceConstructor.type

namespace SingletonFamilyIngressView

/-- The exact physical member array described by a loaded family view. -/
def members
    {trProj : RawProjRel} {env : KEnv .anon}
    {nameOf : Address → Option Lean.Name}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (view : SingletonFamilyIngressView trProj env nameOf tx) :
    Array (KId .anon) :=
  #[view.familyId] ++ view.constructorIds

@[simp] theorem family_mem
    {trProj : RawProjRel} {env : KEnv .anon}
    {nameOf : Address → Option Lean.Name}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (view : SingletonFamilyIngressView trProj env nameOf tx) :
    view.familyId ∈ view.members := by
  simp [members]

/-- Split membership into the leading family or one exact constructor
position. -/
theorem member_cases
    {trProj : RawProjRel} {env : KEnv .anon}
    {nameOf : Address → Option Lean.Name}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (view : SingletonFamilyIngressView trProj env nameOf tx)
    {id : KId .anon} (hmember : id ∈ view.members) :
    id = view.familyId ∨
      ∃ (index : Nat) (hindex : index < view.constructorIds.size),
        view.constructorIds[index] = id := by
  simp only [members, Array.mem_append, Array.mem_singleton] at hmember
  rcases hmember with rfl | hconstructor
  · exact .inl rfl
  · exact .inr (Array.mem_iff_getElem.mp hconstructor)

/-- The family address cannot already be trusted in the transaction's input
world.  Otherwise trusted provenance and the ingress name assignment would
produce the exact Theory lookup which the generation trace proves absent. -/
theorem familyFresh
    {trProj : RawProjRel} {env : KEnv .anon}
    {world : VerifyWorld} {source : VInductDecl} {after : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv after}
    (view : SingletonFamilyIngressView trProj env world.nameOf tx)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    ¬world.trusted view.familyId := by
  intro htrusted
  obtain ⟨_, name, ci, _, hname, hlookup⟩ :=
    trustedCatalog.lookup htrusted
  have hnameEq :
      name = tx.certificate.generation.block.sourceType.name :=
    Option.some.inj (hname.symm.trans view.familyName)
  subst name
  have hcollision :
      (none : Option Lean4Lean.VConstant) = some ci :=
    tx.facts.familyFresh.symm.trans hlookup
  cases hcollision

/-- Every constructor address is likewise fresh.  Positional source lookup
is essential here: it selects the precise constructor freshness fact emitted
by the certified transaction. -/
theorem constructorFresh
    {trProj : RawProjRel} {env : KEnv .anon}
    {world : VerifyWorld} {source : VInductDecl} {after : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv after}
    (view : SingletonFamilyIngressView trProj env world.nameOf tx)
    (trustedCatalog : TrustedCatalogRel trProj world)
    (index : Nat) (hindex : index < view.constructorIds.size) :
    ¬world.trusted view.constructorIds[index] := by
  obtain ⟨sourceConstructor, concrete, hsource, _, _, hsourceName, _⟩ :=
    view.constructor index hindex
  intro htrusted
  obtain ⟨_, name, ci, _, hname, hlookup⟩ :=
    trustedCatalog.lookup htrusted
  have hnameEq : name = sourceConstructor.name :=
    Option.some.inj (hname.symm.trans hsourceName)
  subst name
  have hsourceMem : sourceConstructor ∈
      tx.certificate.generation.block.sourceType.ctors :=
    List.mem_of_getElem? hsource
  have hcollision :
      (none : Option Lean4Lean.VConstant) = some ci :=
    (tx.facts.ctorFresh hsourceMem).symm.trans hlookup
  cases hcollision

/-- Transport actual loaded entries to the immutable catalog and assemble
the semantic family link.  The only semantic input is the trusted log already
carried by the checker-state invariant. -/
def toCatalogLink
    {trProj : RawProjRel} {env : KEnv .anon}
    {world : VerifyWorld} {source : VInductDecl} {after : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv after}
    (view : SingletonFamilyIngressView trProj env world.nameOf tx)
    (loaded : LoadedAgrees world.catalog env)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx where
  familyId := view.familyId
  constructorIds := view.constructorIds
  constructorCount := view.constructorCount
  familyConcrete := view.familyConcrete
  familyCatalog := loaded view.familyLoaded
  familyShape := view.familyShape
  familyName := view.familyName
  familyType := view.familyType
  constructor := by
    intro index hindex
    obtain ⟨sourceConstructor, concrete, hsource, hloaded, hshape,
      hname, htype⟩ := view.constructor index hindex
    exact ⟨sourceConstructor, concrete, hsource, loaded hloaded,
      hshape, hname, htype⟩
  fresh := by
    intro id hmember
    have hviewMember : id ∈ view.members := by
      simpa only [members] using hmember
    rcases view.member_cases hviewMember with rfl | ⟨index, hindex, hid⟩
    · exact view.familyFresh trustedCatalog
    · subst id
      exact view.constructorFresh trustedCatalog index hindex

@[simp] theorem toCatalogLink_members
    {trProj : RawProjRel} {env : KEnv .anon}
    {world : VerifyWorld} {source : VInductDecl} {after : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv after}
    (view : SingletonFamilyIngressView trProj env world.nameOf tx)
    (loaded : LoadedAgrees world.catalog env)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    (view.toCatalogLink loaded trustedCatalog).members = view.members := rfl

end SingletonFamilyIngressView

/-! ## Recursor ingress -/

/-- Exact representation evidence for the separate singleton recursor entry
loaded by anonymous ingress.

The family link is the semantic result of the preceding physical family
block.  This view adds only facts about the recursor entry loaded in `env`;
in particular, it does not assume that the recursor id is untrusted. -/
structure SingletonRecursorIngressView
    (trProj : RawProjRel) (env : KEnv .anon)
    (nameOf : Address → Option Lean.Name)
    {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after)
    {trusted : KId .anon → Prop} {catalog : Catalog}
    (family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx) where
  recursorId : KId .anon
  recursorConcrete : KConst .anon
  recursorLoaded : env.get? recursorId = some recursorConcrete
  recursorShape : recursorConcrete.IsCertifiedSingletonRecursor source
    tx.certificate.generation family.constructorIds
  recursorName : nameOf recursorId.addr =
    some (.str tx.certificate.generation.block.sourceType.name "rec")
  recursorType : RawExprRel (uvars := recursorConcrete.lvls.toNat) after
    nameOf trProj [] recursorConcrete.ty
      tx.certificate.generation.recursor.type
  rule : ∀ (index : Nat) (_hindex : index < family.constructorIds.size),
    ∃ concreteRule normalizedConstructor,
      recursorConcrete.RecursorRuleAt index concreteRule ∧
      tx.certificate.generation.block.ctorPairs[index]? =
        some normalizedConstructor ∧
      concreteRule.fields.toNat =
        (normalizedConstructor.fieldsR source.uvars source.nparams).length ∧
      RawExprRel
        (uvars :=
          (tx.certificate.generation.rule index normalizedConstructor).uvars)
        after nameOf trProj [] concreteRule.rhs
        (tx.certificate.generation.rule index normalizedConstructor).rhs ∧
      TrKExprS after
        (tx.certificate.generation.rule index normalizedConstructor).uvars
        nameOf trProj [] concreteRule.rhs
        (tx.certificate.generation.rule index normalizedConstructor).rhs

namespace SingletonRecursorIngressView

/-- The separate physical recursor block contains exactly its one loaded
recursor declaration. -/
def members
    {trProj : RawProjRel} {env : KEnv .anon}
    {nameOf : Address → Option Lean.Name}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {trusted : KId .anon → Prop} {catalog : Catalog}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (view : SingletonRecursorIngressView trProj env nameOf tx family) :
    Array (KId .anon) :=
  #[view.recursorId]

@[simp] theorem recursor_mem
    {trProj : RawProjRel} {env : KEnv .anon}
    {nameOf : Address → Option Lean.Name}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {trusted : KId .anon → Prop} {catalog : Catalog}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (view : SingletonRecursorIngressView trProj env nameOf tx family) :
    view.recursorId ∈ view.members := by
  simp [members]

/-- Trusted provenance for the same anonymous address would contradict the
certified transaction's absent pre-state recursor lookup. -/
theorem recursorFresh
    {trProj : RawProjRel} {env : KEnv .anon}
    {world : VerifyWorld} {source : VInductDecl} {after : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv after}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (view : SingletonRecursorIngressView trProj env world.nameOf tx family)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    ¬world.trusted view.recursorId := by
  intro htrusted
  obtain ⟨_, name, ci, _, hname, hlookup⟩ :=
    trustedCatalog.lookup htrusted
  have hnameEq : name =
      .str tx.certificate.generation.block.sourceType.name "rec" :=
    Option.some.inj (hname.symm.trans view.recursorName)
  subst name
  have hcollision :
      (none : Option Lean4Lean.VConstant) = some ci :=
    tx.facts.recursorFresh.symm.trans hlookup
  cases hcollision

/-- Transport the actually loaded recursor entry to its immutable catalog
entry and assemble the positional recursor/rule link. -/
def toCatalogLink
    {trProj : RawProjRel} {env : KEnv .anon}
    {world : VerifyWorld} {source : VInductDecl} {after : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv after}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (view : SingletonRecursorIngressView trProj env world.nameOf tx family)
    (loaded : LoadedAgrees world.catalog env)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    SingletonRecursorCatalogLink trProj world.catalog world.nameOf
      world.trusted tx family where
  recursorId := view.recursorId
  recursorConcrete := view.recursorConcrete
  recursorCatalog := loaded view.recursorLoaded
  recursorShape := view.recursorShape
  recursorName := view.recursorName
  recursorType := view.recursorType
  rule := view.rule
  fresh := view.recursorFresh trustedCatalog

end SingletonRecursorIngressView

end Ix.Tc
