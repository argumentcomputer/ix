import Ix.Tc.Verify.Inductive

/-!
# Certified singleton-family admission

This module is the first production-facing half of E2b.  A Lean4Lean
`CertifiedGenerationTransaction` already owns the semantic generation of one
family, all of its constructors, its recursor, and its iota equations.  What
that transaction cannot know is which anonymous Ix addresses contain the
family and constructors.

`SingletonFamilyCatalogLink` supplies exactly that missing representation
link for the physical family block:

* the family is the first member and the remaining members are its constructor
  array in source order;
* every concrete declaration has the production singleton shape and the
  exact source universe/parameter/index/field counts;
* every address resolves to the source name; and
* every stored type has the exact raw Theory translation installed by the
  certified transaction.

The structure deliberately contains no `InductiveOracle`, environment-WF,
environment-extension, constant-WF, or recursor-rule premise.  Those facts
are derived below from the E2a transaction.  The later checker adapter must
construct this link from ingress plus a successful production block run.
-/

namespace Ix.Tc

open Lean4Lean (VConstVal VEnv VExpr VInductDecl)

/-! ## Header facts retained by normalized generation -/

namespace CertifiedSingletonGeneration

/-- The checked singleton family retains the declaration universe arity. -/
theorem checkedTypeUvars {decl : VInductDecl}
    (checked : decl.Checked) : checked.type.uvars = decl.uvars := by
  rcases checked with
    ⟨type, typesEq, params, paramsEq, indices, indicesEq,
      resultLevel, resultEq, elimination, eliminationEq, kTarget, kTargetEq,
      names, namesEq, constructors, constructorsEq, accepted⟩
  cases decl with
  | mk uvars nparams types =>
    change types = [type] at typesEq
    change VInductDecl.stage3Core ⟨uvars, nparams, types⟩ = true at accepted
    rw [typesEq] at accepted
    simp only [VInductDecl.stage3Core, VInductDecl.stage3DirectCore,
      Bool.and_eq_true, beq_iff_eq] at accepted
    change type.uvars = uvars
    exact accepted.1.1.1.1.1

/-- Every checked constructor retains the declaration universe arity. -/
theorem checkedConstructorUvars {decl : VInductDecl}
    (checked : decl.Checked) {constructor : VConstVal}
    (hconstructor : constructor ∈ checked.type.ctors) :
    constructor.uvars = decl.uvars := by
  rcases checked with
    ⟨type, typesEq, params, paramsEq, indices, indicesEq,
      resultLevel, resultEq, elimination, eliminationEq, kTarget, kTargetEq,
      names, namesEq, constructors, constructorsEq, accepted⟩
  cases decl with
  | mk uvars nparams types =>
    change types = [type] at typesEq
    change VInductDecl.stage3Core ⟨uvars, nparams, types⟩ = true at accepted
    rw [typesEq] at accepted
    simp only [VInductDecl.stage3Core, VInductDecl.stage3DirectCore,
      Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at accepted
    change constructor.uvars = uvars
    exact (accepted.1.2 constructor hconstructor).1.1

/-- Positional header coherence transports a common constructor universe
arity from a normalized view back to the stored source constructors. -/
theorem sourceConstructorUvarsOfHeaders
    {raw view : List VConstVal} {uvars : Nat}
    (hheaders : VInductDecl.sameCtorHeaders raw view = true)
    (hview : ∀ constructor ∈ view, constructor.uvars = uvars) :
    ∀ constructor ∈ raw, constructor.uvars = uvars := by
  induction raw generalizing view with
  | nil => simp
  | cons first rest ih =>
      cases view with
      | nil => simp [VInductDecl.sameCtorHeaders] at hheaders
      | cons firstView restView =>
          simp only [VInductDecl.sameCtorHeaders, Bool.and_eq_true,
            beq_iff_eq] at hheaders
          intro constructor hconstructor
          simp only [List.mem_cons] at hconstructor
          rcases hconstructor with rfl | hconstructor
          · exact hheaders.1.2.trans (hview firstView (.head _))
          · exact ih hheaders.2
              (fun candidate hcandidate =>
                hview candidate (.tail _ hcandidate))
              constructor hconstructor

/-- The raw source family selected by a normalized generation has the
declaration's universe arity. -/
theorem sourceTypeUvars {source : VInductDecl}
    (generation : source.GenerationChecked) :
    generation.block.sourceType.uvars = source.uvars := by
  have hview := checkedTypeUvars generation.block.checked
  have hshape := generation.block.normalization.shape_eq
  simp only [VInductDecl.normalizationShape, Bool.and_eq_true,
    beq_iff_eq] at hshape
  have hheaders := hshape.2
  rw [generation.block.source_types_eq,
    generation.block.checked.types_eq] at hheaders
  simp only [VInductDecl.sameTypeHeaders, Bool.and_eq_true,
    beq_iff_eq] at hheaders
  exact hheaders.1.1.2.trans (hview.trans hshape.1.1.symm)

/-- Every raw source constructor selected by a normalized generation has the
same universe arity. -/
theorem sourceConstructorUvars {source : VInductDecl}
    (generation : source.GenerationChecked) {constructor : VConstVal}
    (hconstructor : constructor ∈ generation.block.sourceType.ctors) :
    constructor.uvars = source.uvars := by
  have hshape := generation.block.normalization.shape_eq
  simp only [VInductDecl.normalizationShape, Bool.and_eq_true,
    beq_iff_eq] at hshape
  have hheaders := hshape.2
  rw [generation.block.source_types_eq,
    generation.block.checked.types_eq] at hheaders
  simp only [VInductDecl.sameTypeHeaders, Bool.and_eq_true,
    beq_iff_eq] at hheaders
  exact sourceConstructorUvarsOfHeaders hheaders.1.2
    (fun candidate hcandidate =>
      (checkedConstructorUvars generation.block.checked hcandidate).trans
        hshape.1.1.symm)
    constructor hconstructor

end CertifiedSingletonGeneration

/-! ## Exact supported production shapes -/

/-- The concrete family shape supported by the singleton E2b adapter.

The singleton family is member zero of its physical inductive block.  Its
stored parameter and index counters must agree with the raw/view generation
selected by the certificate, and its constructor array is the exact ordered
physical constructor suffix. -/
def KConst.IsCertifiedSingletonFamily
    (source : VInductDecl) (generation : source.GenerationChecked)
    (constructorIds : Array (KId .anon)) : KConst .anon → Prop
  | .indc (lvls := levels) (params := params) (indices := indices)
      (memberIdx := memberIdx) (ctors := ctors) .. =>
    levels.toNat = source.uvars ∧
      params.toNat = source.nparams ∧
      indices.toNat = generation.block.rawIndices.length ∧
      memberIdx = 0 ∧
      ctors = constructorIds
  | _ => False

/-- The concrete constructor shape at one source position.

The field count is computed from the exact raw constructor stored in the
certificate, not from an independently supplied view. -/
def KConst.IsCertifiedSingletonConstructor
    (source : VInductDecl) (familyId : KId .anon) (index : Nat)
    (constructor : VConstVal) : KConst .anon → Prop
  | .ctor (lvls := levels) (induct := induct) (cidx := cidx)
      (params := params) (fields := fields) .. =>
    levels.toNat = source.uvars ∧
      induct = familyId ∧
      cidx.toNat = index ∧
      params.toNat = source.nparams ∧
      fields.toNat =
        (VInductDecl.ctorFields
          (VExpr.dropN source.nparams constructor.type)).length
  | _ => False

namespace KConst.IsCertifiedSingletonFamily

theorem levels
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonFamily source generation constructorIds) :
    concrete.lvls.toNat = source.uvars := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily, KConst.lvls]

theorem inductiveMember
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonFamily source generation constructorIds) :
    concrete.IsInductiveMember := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily,
      KConst.IsInductiveMember]

theorem noRecursorRule
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonFamily source generation constructorIds)
    (rule : RecRule .anon) : ¬concrete.HasRecursorRule rule := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily, KConst.HasRecursorRule]

theorem noRecursorRuleAt
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonFamily source generation constructorIds)
    (index : Nat) (rule : RecRule .anon) :
    ¬concrete.RecursorRuleAt index rule := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily, KConst.RecursorRuleAt]

end KConst.IsCertifiedSingletonFamily

namespace KConst.IsCertifiedSingletonConstructor

theorem levels
    {source : VInductDecl} {familyId : KId .anon} {index : Nat}
    {constructor : VConstVal} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonConstructor source familyId index
      constructor) :
    concrete.lvls.toNat = source.uvars := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor, KConst.lvls]

theorem inductiveMember
    {source : VInductDecl} {familyId : KId .anon} {index : Nat}
    {constructor : VConstVal} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonConstructor source familyId index
      constructor) :
    concrete.IsInductiveMember := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.IsInductiveMember]

theorem noRecursorRule
    {source : VInductDecl} {familyId : KId .anon} {index : Nat}
    {constructor : VConstVal} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonConstructor source familyId index
      constructor) (rule : RecRule .anon) :
    ¬concrete.HasRecursorRule rule := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.HasRecursorRule]

theorem noRecursorRuleAt
    {source : VInductDecl} {familyId : KId .anon} {index : Nat}
    {constructor : VConstVal} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonConstructor source familyId index
      constructor) (ruleIndex : Nat) (rule : RecRule .anon) :
    ¬concrete.RecursorRuleAt ruleIndex rule := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.RecursorRuleAt]

end KConst.IsCertifiedSingletonConstructor

/-! ## Ix/source correspondence -/

/-- Exact representation link between one certified singleton generation and
the production family/constructor block.

`constructor` is indexed by the physical constructor array.  Its source
lookup is therefore positional and cannot pair an Ix constructor with a
different certificate constructor having the same type. -/
structure SingletonFamilyCatalogLink
    (trProj : RawProjRel) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) (trusted : KId .anon → Prop)
    {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after) where
  familyId : KId .anon
  constructorIds : Array (KId .anon)
  constructorCount :
    constructorIds.size =
      tx.certificate.generation.block.sourceType.ctors.length
  familyConcrete : KConst .anon
  familyCatalog : catalog familyId = some familyConcrete
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
      catalog constructorIds[index] = some concrete ∧
      concrete.IsCertifiedSingletonConstructor source familyId index
        sourceConstructor ∧
      nameOf constructorIds[index].addr = some sourceConstructor.name ∧
      RawExprRel (uvars := concrete.lvls.toNat) after nameOf trProj []
        concrete.ty sourceConstructor.type
  fresh : ∀ id, id ∈ (#[familyId] ++ constructorIds) → ¬trusted id

namespace SingletonFamilyCatalogLink

/-- The exact physical member array certified by this link. -/
def members
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx) :
    Array (KId .anon) :=
  #[link.familyId] ++ link.constructorIds

@[simp] theorem family_mem
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx) :
    link.familyId ∈ link.members := by
  simp [members]

theorem member_cases
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx)
    {id : KId .anon} (hmember : id ∈ link.members) :
    id = link.familyId ∨
      ∃ (index : Nat) (hindex : index < link.constructorIds.size),
        link.constructorIds[index] = id := by
  simp only [members, Array.mem_append, Array.mem_singleton] at hmember
  rcases hmember with rfl | hconstructor
  · exact .inl rfl
  · exact .inr (Array.mem_iff_getElem.mp hconstructor)

/-- Every linked member has the exact raw inductive translation and installed
Theory constant required by `InductiveOracle.translateBlock`.  Constant WF is
derived from the certified post-environment rather than stored in the link. -/
theorem translateMember
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx)
    {id : KId .anon} (hmember : id ∈ link.members) :
    ∃ concrete name ci,
      catalog id = some concrete ∧
      RawInductiveConstRel after nameOf trProj id concrete name ci ∧
      after.constants name = some ci ∧
      ci.WF after := by
  have facts := tx.facts
  rcases link.member_cases hmember with rfl | ⟨index, hindex, hget⟩
  · refine ⟨link.familyConcrete,
      tx.certificate.generation.block.sourceType.name,
      tx.certificate.generation.block.sourceType.toVConstant,
      link.familyCatalog, ?_, facts.familyLookup, ?_⟩
    · exact {
        kind := KConst.IsCertifiedSingletonFamily.inductiveMember
          link.familyShape
        nameEq := link.familyName
        uvars := (KConst.IsCertifiedSingletonFamily.levels
          link.familyShape).trans
          (CertifiedSingletonGeneration.sourceTypeUvars
            tx.certificate.generation).symm
        type := link.familyType }
    · exact facts.afterWF.ordered.constWF facts.familyLookup
  · obtain ⟨sourceConstructor, concrete, hsource, hcatalog, hshape,
      hname, htype⟩ := link.constructor index hindex
    subst id
    have hsourceMem : sourceConstructor ∈
        tx.certificate.generation.block.sourceType.ctors :=
      List.mem_of_getElem? hsource
    refine ⟨concrete, sourceConstructor.name, sourceConstructor.toVConstant,
      hcatalog, ?_, facts.ctorLookup hsourceMem, ?_⟩
    · exact {
        kind := KConst.IsCertifiedSingletonConstructor.inductiveMember hshape
        nameEq := hname
        uvars := (KConst.IsCertifiedSingletonConstructor.levels hshape).trans
          (CertifiedSingletonGeneration.sourceConstructorUvars
            tx.certificate.generation hsourceMem).symm
        type := htype }
    · exact facts.afterWF.ordered.constWF
        (facts.ctorLookup hsourceMem)

/-- No family-block member can carry a concrete recursor rule.  This closes
the rule clauses of the family admission by contradiction rather than by an
unrelated rule oracle. -/
theorem noRecursorRule
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx)
    {id : KId .anon} (hmember : id ∈ link.members)
    {concrete : KConst .anon} (hcatalog : catalog id = some concrete)
    (rule : RecRule .anon) : ¬concrete.HasRecursorRule rule := by
  rcases link.member_cases hmember with rfl | ⟨index, hindex, hget⟩
  · have hconcrete : concrete = link.familyConcrete := by
      rw [link.familyCatalog] at hcatalog
      exact Option.some.inj hcatalog.symm
    subst concrete
    exact link.familyShape.noRecursorRule rule
  · obtain ⟨sourceConstructor, linked, _, hlinked, hshape, _⟩ :=
      link.constructor index hindex
    rw [hget] at hlinked
    have hconcrete : concrete = linked := by
      rw [hlinked] at hcatalog
      exact Option.some.inj hcatalog.symm
    subst concrete
    exact hshape.noRecursorRule rule

theorem noRecursorRuleAt
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx)
    {id : KId .anon} (hmember : id ∈ link.members)
    {concrete : KConst .anon} (hcatalog : catalog id = some concrete)
    (ruleIndex : Nat) (rule : RecRule .anon) :
    ¬concrete.RecursorRuleAt ruleIndex rule := by
  rcases link.member_cases hmember with rfl | ⟨index, hindex, hget⟩
  · have hconcrete : concrete = link.familyConcrete := by
      rw [link.familyCatalog] at hcatalog
      exact Option.some.inj hcatalog.symm
    subst concrete
    exact link.familyShape.noRecursorRuleAt ruleIndex rule
  · obtain ⟨sourceConstructor, linked, _, hlinked, hshape, _⟩ :=
      link.constructor index hindex
    rw [hget] at hlinked
    have hconcrete : concrete = linked := by
      rw [hlinked] at hcatalog
      exact Option.some.inj hcatalog.symm
    subst concrete
    exact hshape.noRecursorRuleAt ruleIndex rule

/-- Construct the complete family-block oracle from the exact Ix/source link
and E2a's certified transaction.  The recursor clauses are vacuous for this
physical block because it contains only the family and its constructors. -/
def oracle
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx) :
    InductiveOracle trProj catalog nameOf trusted before where
  members := fun id => id ∈ link.members
  nonempty := ⟨link.familyId, link.family_mem⟩
  fresh := by
    intro id hmember
    exact link.fresh id hmember
  after := after
  envLE := tx.facts.envLE
  blockWF := tx.facts.afterWF
  translateBlock := by
    intro id hmember
    exact link.translateMember hmember
  recursorFacts := by
    intro id concrete rule hmember hcatalog hrule
    exact False.elim (link.noRecursorRule hmember hcatalog rule hrule)
  recursorPatterns := by
    intro id concrete ruleIndex rule hmember hcatalog hrule
    exact False.elim
      (link.noRecursorRuleAt hmember hcatalog ruleIndex rule hrule)

@[simp] theorem oracle_members_iff
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    (link : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx)
    (id : KId .anon) :
    link.oracle.members id ↔ id ∈ link.members :=
  by
    change (id ∈ link.members) ↔ id ∈ link.members
    exact Iff.rfl

end SingletonFamilyCatalogLink

end Ix.Tc
