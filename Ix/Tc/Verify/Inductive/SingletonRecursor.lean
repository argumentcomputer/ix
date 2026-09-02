import Ix.Tc.Verify.Inductive.SingletonFamily

/-!
# Certified singleton-recursor correspondence

The Lean4Lean transaction used by E2a installs a singleton family's recursor
and all of its iota equations atomically with the family.  Anonymous Ix
ingress does not: the family/constructor block and the recursor block are
distinct physical blocks.  This module links the latter block to the exact
artifacts already installed by the transaction.

The link is deliberately positional.  Rule `i` is paired with normalized
constructor `i`, the generated equation at `i`, and the stored constructor at
`i`; an existential search by equal RHS is never sufficient.  Pattern
compilation is kept for the next module because it has an additional semantic
obligation beyond raw/structural translation.
-/

namespace Ix.Tc

open Lean4Lean (VConstVal VDefEq VEnv VExpr VInductDecl)

namespace CertifiedSingletonGeneration

/-- The generated rule array is positionally the map over `ctorPairs.zipIdx`.
This small theorem prevents later adapters from selecting an arbitrary
registered equation with an equal body. -/
theorem generatedRuleAt {source : VInductDecl}
    (generation : source.GenerationChecked) {index : Nat}
    {constructor : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some constructor) :
    generation.generatedRules[index]? =
      some (generation.rule index constructor) := by
  unfold VInductDecl.GenerationChecked.generatedRules
  simp only [List.getElem?_map]
  rw [List.getElem?_zipIdx]
  simp [hconstructor]

/-- Positional pairing retains the raw source constructor at the same index. -/
theorem rawConstructorAt {source : VInductDecl}
    (generation : source.GenerationChecked) {index : Nat}
    {constructor : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some constructor) :
    generation.block.sourceType.ctors[index]? = some constructor.raw := by
  have hmapped :
      (generation.block.ctorPairs.map (·.raw))[index]? =
        some constructor.raw := by
    rw [List.getElem?_map, hconstructor]
    rfl
  rw [generation.rawCtors_eq] at hmapped
  exact hmapped

/-- A generated iota equation is recursor-headed below its closed rule
telescope.  This is the shape actually emitted by Lean4Lean; its outer node
is never directly a constant-headed application when the telescope is
nonempty. -/
theorem generatedRuleHead {source : VInductDecl}
    (generation : source.GenerationChecked) (index : Nat)
    (constructor : VInductDecl.NormalizedCtor) :
    HeadConstUnderLambdas
      (.str generation.block.sourceType.name "rec")
      (generation.rule index constructor).lhs := by
  unfold VInductDecl.GenerationChecked.rule
  apply HeadConstUnderLambdas.lamN
  apply HeadConst.appN
  apply HeadConst.appN
  exact .const _

end CertifiedSingletonGeneration

/-! ## Exact supported recursor shape -/

/-- Concrete recursor metadata supported by E2b's singleton adapter.

`motives = 1` is the explicit no-mutual/no-nested boundary of this adapter.
The exact rule count is retained, and `RecursorMajorIdxCoherent` rules out the
wrapping-`UInt64` disagreement between production's ordinary iota path and
its Nat descriptor path.

The universe arity is taken from `generation.recUvars` rather than spelled as
`source.uvars + 1`: the fresh motive universe exists only under large
elimination, so a small-eliminating (`Prop`-valued) family's recursor carries
exactly the source universes. -/
def KConst.IsCertifiedSingletonRecursor
    (source : VInductDecl) (generation : source.GenerationChecked)
    (constructorIds : Array (KId .anon)) : KConst .anon → Prop
  | concrete@(.recr (k := k) (lvls := levels) (params := params)
      (indices := indices) (motives := motives) (minors := minors)
      (memberIdx := memberIdx) (rules := rules) ..) =>
    levels.toNat = generation.recUvars ∧
      params.toNat = source.nparams ∧
      indices.toNat = generation.block.rawIndices.length ∧
      motives.toNat = 1 ∧
      minors.toNat = constructorIds.size ∧
      memberIdx = 0 ∧
      rules.size = constructorIds.size ∧
      concrete.RecursorMajorIdxCoherent ∧
      k = generation.kTarget
  | _ => False

namespace KConst.IsCertifiedSingletonRecursor

theorem inductiveMember
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds) : concrete.IsInductiveMember := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonRecursor,
      KConst.IsInductiveMember]

theorem levels
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds) :
    concrete.lvls.toNat = generation.recursor.uvars := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonRecursor, KConst.lvls,
      VInductDecl.GenerationChecked.recursor]

/-- The physical recursor's declared K bit is exactly the independently
computed flag retained by the certified Lean4Lean generation. -/
theorem kTarget
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds) :
    ∀ {k : Bool}, (∃ name levelParams isUnsafe levels params indices motives
        minors block memberIdx type rules leanAll,
      concrete = .recr name levelParams k isUnsafe levels params indices
        motives minors block memberIdx type rules leanAll) →
      k = generation.kTarget := by
  cases concrete <;> simp_all [KConst.IsCertifiedSingletonRecursor]

theorem coherent
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds) : concrete.RecursorMajorIdxCoherent := by
  cases concrete <;>
    simp only [KConst.IsCertifiedSingletonRecursor] at h
  exact h.2.2.2.2.2.2.2.1

theorem ruleCount
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (h : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds) :
    ∀ {index : Nat} {rule : RecRule .anon},
      concrete.RecursorRuleAt index rule → index < constructorIds.size := by
  cases concrete with
  | recr name levelParams k isUnsafe levels params indices motives minors
      block memberIdx type rules leanAll =>
      simp only [KConst.IsCertifiedSingletonRecursor] at h
      intro index rule hrule
      change rules[index]? = some rule at hrule
      have hlt : index < rules.size :=
        (Array.getElem?_eq_some_iff.mp hrule).choose
      simpa only [h.2.2.2.2.2.2.1] using hlt
  | _ => simp [KConst.IsCertifiedSingletonRecursor] at h

end KConst.IsCertifiedSingletonRecursor

/-! ## Exact recursor/rule correspondence -/

/-- Positional correspondence between the one physical Ix recursor block and
the recursor/equations already installed by an E2a transaction.

The structure contains representation facts only.  Registration, equation
WF, recursor WF, and recursor-headedness are derived from the transaction and
the generator definition below. -/
structure SingletonRecursorCatalogLink
    (trProj : RawProjRel) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) (trusted : KId .anon → Prop)
    {source : VInductDecl} {before after : VEnv}
    (tx : CertifiedGenerationTransaction source before after)
    (family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx) where
  recursorId : KId .anon
  recursorConcrete : KConst .anon
  recursorCatalog : catalog recursorId = some recursorConcrete
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
  fresh : ¬trusted recursorId

namespace SingletonRecursorCatalogLink

/-- The recursor's exact raw translation and certified post-environment
lookup. -/
theorem translateRecursor
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family) :
    RawInductiveConstRel after nameOf trProj link.recursorId
        link.recursorConcrete
        (.str tx.certificate.generation.block.sourceType.name "rec")
        tx.certificate.generation.recursor ∧
      after.constants
          (.str tx.certificate.generation.block.sourceType.name "rec") =
        some tx.certificate.generation.recursor ∧
      tx.certificate.generation.recursor.WF after := by
  have facts := tx.facts
  refine ⟨?_, facts.recursorLookup,
    facts.afterWF.ordered.constWF facts.recursorLookup⟩
  exact {
    kind := link.recursorShape.inductiveMember
    nameEq := link.recursorName
    uvars := link.recursorShape.levels
    type := link.recursorType }

/-- Select the exact normalized constructor and generated equation paired
with a concrete rule at the requested array index. -/
theorem ruleAt
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    {index : Nat} {concreteRule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt index concreteRule) :
    ∃ normalizedConstructor,
      tx.certificate.generation.block.ctorPairs[index]? =
        some normalizedConstructor ∧
      tx.certificate.generation.generatedRules[index]? =
        some (tx.certificate.generation.rule index normalizedConstructor) ∧
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
        (tx.certificate.generation.rule index normalizedConstructor).rhs := by
  have hindex := link.recursorShape.ruleCount hrule
  obtain ⟨linkedRule, normalizedConstructor, hlinkedRule, hnormalized,
    hfields, hraw, htyped⟩ := link.rule index hindex
  have hruleEq : linkedRule = concreteRule :=
    KConst.RecursorRuleAt.unique hlinkedRule hrule
  subst linkedRule
  exact ⟨normalizedConstructor, hnormalized,
    CertifiedSingletonGeneration.generatedRuleAt _ hnormalized,
    hfields, hraw, htyped⟩

/-- E2a registration plus the exact positional Ix link yields the complete
registered-rule semantic relation. -/
theorem registeredRuleAt
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    {index : Nat} {concreteRule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt index concreteRule) :
    ∃ normalizedConstructor,
      tx.certificate.generation.block.ctorPairs[index]? =
        some normalizedConstructor ∧
      RegisteredRecursorRuleRhsRel after nameOf trProj link.recursorId
        link.recursorConcrete concreteRule
        (tx.certificate.generation.rule index normalizedConstructor) := by
  obtain ⟨normalizedConstructor, hnormalized, hgenerated, _, hraw, htyped⟩ :=
    link.ruleAt hrule
  have hgeneratedMem :
      tx.certificate.generation.rule index normalizedConstructor ∈
        tx.certificate.generation.generatedRules :=
    List.mem_of_getElem? hgenerated
  have hrecursor := link.translateRecursor
  refine ⟨normalizedConstructor, hnormalized,
    .str tx.certificate.generation.block.sourceType.name "rec",
    tx.certificate.generation.recursor, hrecursor.1,
    hrecursor.2.1, tx.facts.ruleMem hgeneratedMem, ?_, ?_, hraw, htyped⟩
  · exact tx.facts.afterWF.ordered.defEqWF
      (tx.facts.ruleMem hgeneratedMem)
  · exact CertifiedSingletonGeneration.generatedRuleHead
      tx.certificate.generation index normalizedConstructor

/-- Membership-only rule evidence is recovered by first retaining the exact
array position. -/
theorem registeredRule
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    {concreteRule : RecRule .anon}
    (hrule : link.recursorConcrete.HasRecursorRule concreteRule) :
    RawRecursorRuleRel after nameOf trProj link.recursorId
      link.recursorConcrete concreteRule := by
  obtain ⟨index, hat⟩ := hrule.exists_ruleAt
  obtain ⟨normalizedConstructor, _, hregistered⟩ :=
    link.registeredRuleAt hat
  exact ⟨_, hregistered⟩

/-- The exact physical member array of a singleton recursor block.  This is a
representation fact shared by enumeration and genuinely recursive recursors,
so it lives below either pattern-specific oracle. -/
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

end SingletonRecursorCatalogLink

end Ix.Tc
