import Ix.Tc.Verify.Inductive.IotaPattern

/-!
# Certified singleton enumerations

This module is E2b's first executable inductive fragment.  A singleton
enumeration has no declaration universes, parameters, indices, constructor
fields, or recursive arguments.  It may have several nullary constructors,
so its generated iota rules are non-vacuous: rule `i` returns the exact
`i`-th minor premise.

The restriction is intentionally stated over the normalized generation
retained by E2a.  It is therefore a decidable fragment boundary around the
actual generated artifacts, not a second inductive-declaration model.
-/

namespace Ix.Tc

open Lean4Lean (VConstVal VEnv VExpr VInductDecl)

namespace CertifiedSingletonGeneration

/-- The first executable E2b fragment: one nonempty, universe-free,
parameter-free, index-free family whose constructors are nullary and
nonrecursive. -/
structure IsEnumeration {source : VInductDecl}
    (generation : source.GenerationChecked) : Prop where
  noUniverses : source.uvars = 0
  noParameters : source.nparams = 0
  noIndices : generation.block.rawIndices = []
  nonempty : 0 < generation.block.ctorPairs.length
  constructor : ∀ {index : Nat}
      {normalized : VInductDecl.NormalizedCtor},
    generation.block.ctorPairs[index]? = some normalized →
      normalized.fieldsR source.uvars source.nparams = [] ∧
      normalized.recArgsR source.uvars = [] ∧
      normalized.resultIndicesR source.uvars = []

namespace IsEnumeration

/-- Closed equation binders for the enumeration fragment: one motive and
one minor per constructor. -/
def ruleBinders {source : VInductDecl}
    (generation : source.GenerationChecked) : List VExpr :=
  generation.motiveType :: generation.minorTypes

/-- The raw parameter telescope is empty, as opposed to merely having a
counter that claims zero parameters. -/
theorem rawParams_nil {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation) :
    generation.block.rawParams = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [generation.shape.1, shape.noParameters]

@[simp] theorem paramsTel_nil {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation) :
    generation.paramsTel = [] := by
  simp [VInductDecl.GenerationChecked.paramsTel, shape.rawParams_nil]

@[simp] theorem idxTel_nil {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation) :
    generation.idxTel = [] := by
  simp [VInductDecl.GenerationChecked.idxTel, shape.noIndices]

/-- Every certified enum constructor contributes no field binders to its
generated equation. -/
theorem fields_nil {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    {index : Nat} {normalized : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some normalized) :
    normalized.fieldsR source.uvars source.nparams = [] :=
  (shape.constructor hconstructor).1

/-- Every certified enum constructor contributes no recursive calls. -/
theorem recursive_nil {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    {index : Nat} {normalized : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some normalized) :
    normalized.recArgsR source.uvars = [] :=
  (shape.constructor hconstructor).2.1

/-- An index-free enum constructor has no normalized result-index spine. -/
theorem resultIndices_nil {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    {index : Nat} {normalized : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some normalized) :
    normalized.resultIndicesR source.uvars = [] :=
  (shape.constructor hconstructor).2.2

@[simp] theorem ruleBinders_length {source : VInductDecl}
    {generation : source.GenerationChecked} :
    (ruleBinders generation).length =
      generation.block.ctorPairs.length + 1 := by
  simp [ruleBinders, generation.minorTypes_length, Nat.add_comm]

/-- Exact generated left-hand side for a nullary enum constructor. -/
theorem rule_lhs {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    {index : Nat} {normalized : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some normalized) :
    (generation.rule index normalized).lhs =
      VExpr.lamN (ruleBinders generation)
        (.app
          (VExpr.appN
            (.const
              (.str generation.block.sourceType.name "rec")
              (Lean4Lean.VLevel.params 1))
            (VExpr.bvarRevRange 0
              (generation.block.ctorPairs.length + 1)))
          (.const normalized.raw.name [])) := by
  unfold VInductDecl.GenerationChecked.rule
  rw [shape.paramsTel_nil, shape.fields_nil hconstructor,
    shape.resultIndices_nil hconstructor]
  simp [ruleBinders, VExpr.liftTelN, VExpr.appN,
    VExpr.bvarRevRange, shape.noUniverses, shape.noParameters,
    Lean4Lean.VLevel.params']

/-- Exact generated right-hand side: enum rule `index` is the corresponding
minor variable and has no field/IH application suffix. -/
theorem rule_rhs {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    {index : Nat} {normalized : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some normalized) :
    (generation.rule index normalized).rhs =
      VExpr.lamN (ruleBinders generation)
        (.bvar (generation.block.ctorPairs.length - 1 - index)) := by
  unfold VInductDecl.GenerationChecked.rule
  rw [shape.paramsTel_nil, shape.fields_nil hconstructor,
    shape.recursive_nil hconstructor]
  simp [ruleBinders, VExpr.liftTelN, VExpr.appN,
    VExpr.bvarRevRange]

/-- Universe instantiation does not change the number of arguments needed to
open a generated enumeration equation. -/
@[simp] theorem ruleBinders_instL_length {source : VInductDecl}
    {generation : source.GenerationChecked}
    (levels : List Lean4Lean.VLevel) :
    ((ruleBinders generation).map (VExpr.instL levels)).length =
      generation.block.ctorPairs.length + 1 := by
  simp

/-- After universe instantiation, the enumeration recursor and every
generated equation expose the same motive/minor telescope.  The recursor
retains only its final major binder after that common prefix. -/
theorem recType_instantiated {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    (levels : List Lean4Lean.VLevel) :
    generation.recType.instL levels =
      VExpr.forallN
        ((ruleBinders generation).map (VExpr.instL levels))
        (.forallE
          (.const generation.block.sourceType.name [])
          (.app
            (.bvar (generation.block.ctorPairs.length + 1))
            (.bvar 0))) := by
  unfold VInductDecl.GenerationChecked.recType
  rw [shape.paramsTel_nil, shape.idxTel_nil]
  simp [ruleBinders, VExpr.forallN, VExpr.appN, VExpr.instL,
    VExpr.instL_forallN, VExpr.liftTelN, VExpr.bvarRevRange, shape.noUniverses,
    shape.noParameters, Lean4Lean.VLevel.params']

/-- After universe instantiation, an enumeration equation has exactly the
same motive/minor telescope as the recursor.  Its result body applies the
selected motive to the selected nullary constructor. -/
theorem ruleType_instantiated {source : VInductDecl}
    {generation : source.GenerationChecked}
    (shape : IsEnumeration generation)
    {index : Nat} {normalized : VInductDecl.NormalizedCtor}
    (hconstructor : generation.block.ctorPairs[index]? = some normalized)
    (levels : List Lean4Lean.VLevel) :
    (generation.rule index normalized).type.instL levels =
      VExpr.forallN
        ((ruleBinders generation).map (VExpr.instL levels))
        (.app
          (.bvar generation.block.ctorPairs.length)
          (.const normalized.raw.name [])) := by
  unfold VInductDecl.GenerationChecked.rule
  rw [shape.paramsTel_nil, shape.fields_nil hconstructor,
    shape.resultIndices_nil hconstructor]
  simp [ruleBinders, VExpr.forallN, VExpr.appN, VExpr.instL,
    VExpr.instL_forallN, VExpr.liftTelN, VExpr.bvarRevRange, shape.noUniverses,
    shape.noParameters, Lean4Lean.VLevel.params']

/-- Opening the exact generated enumeration LHS with one universe and the
complete motive/minor spine produces the expression matched by the compiled
iota pattern. -/
theorem ruleLhsBody_instantiated {source : VInductDecl}
    {generation : source.GenerationChecked}
    (normalized : VInductDecl.NormalizedCtor)
    (levels : List Lean4Lean.VLevel) (arguments : List VExpr)
    (hlevels : levels.length = 1)
    (harguments : arguments.length =
      generation.block.ctorPairs.length + 1) :
    VExpr.instRev
        ((VExpr.app
          (VExpr.appN
            (.const
              (.str generation.block.sourceType.name "rec")
              (Lean4Lean.VLevel.params 1))
            (VExpr.bvarRevRange 0
              (generation.block.ctorPairs.length + 1)))
          (.const normalized.raw.name [])).instL levels)
        arguments =
      VExpr.app
        (VExpr.appN
          (.const
            (.str generation.block.sourceType.name "rec") levels)
          arguments)
        (.const normalized.raw.name []) := by
  simp only [VExpr.instL, VExpr.instL_appN,
    Lean4Lean.VLevel.inst_map_id hlevels,
    VInductDecl.bvarRevRange_instL]
  change VExpr.instRev
      (VExpr.appN
        (VExpr.appN
          (.const
            (.str generation.block.sourceType.name "rec") levels)
          (VExpr.bvarRevRange 0
            (generation.block.ctorPairs.length + 1)))
        [.const normalized.raw.name []])
      arguments = _
  rw [VExpr.instRev_appN, VExpr.instRev_appN,
    VExpr.instRev_closedN arguments (C :=
      .const (.str generation.block.sourceType.name "rec") levels) trivial,
    ← harguments, VExpr.map_instRev_bvarRevRange]
  simp only [List.map_cons, List.map_nil, VExpr.appN]
  rw [VExpr.instRev_closedN arguments (C :=
    .const normalized.raw.name []) trivial]

/-- Opening the exact generated enumeration RHS selects the same
left-to-right minor argument encoded by the dependent pattern path. -/
theorem ruleRhsBody_instantiated {source : VInductDecl}
    {generation : source.GenerationChecked}
    (index : Nat) (hindex : index < generation.block.ctorPairs.length)
    (levels : List Lean4Lean.VLevel) (arguments : List VExpr)
    (harguments : arguments.length =
      generation.block.ctorPairs.length + 1) :
    VExpr.instRev
        ((VExpr.bvar
          (generation.block.ctorPairs.length - 1 - index)).instL levels)
        arguments =
      arguments[index + 1] := by
  have hargument : index + 1 < arguments.length := by omega
  have hdeBruijn :
      generation.block.ctorPairs.length - 1 - index =
        arguments.length - 1 - (index + 1) := by omega
  change VExpr.instRev
      (.bvar (generation.block.ctorPairs.length - 1 - index)) arguments = _
  rw [hdeBruijn]
  exact VExpr.instRev_bvar_at arguments (index + 1) hargument

end IsEnumeration

end CertifiedSingletonGeneration

namespace KConst.IsCertifiedSingletonRecursor

/-- In the enumeration fragment the production major is immediately after
the motive and all constructor minors. -/
theorem enumerationMajorIdx
    {source : VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    (hrecursor : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds)
    (shape : CertifiedSingletonGeneration.IsEnumeration generation) :
    concrete.RecursorMajorIdx = some (constructorIds.size + 1) := by
  cases concrete with
  | recr name levelParams k isUnsafe levels params indices motives minors
      block memberIdx type rules leanAll =>
      simp only [KConst.IsCertifiedSingletonRecursor] at hrecursor
      simp only [KConst.RecursorMajorIdx]
      apply congrArg some
      have hparams : params.toNat = 0 :=
        hrecursor.2.1.trans shape.noParameters
      have hindices : indices.toNat = 0 := by
        simpa [shape.noIndices] using hrecursor.2.2.1
      calc
        (params + motives + minors + indices).toNat =
            params.toNat + motives.toNat + minors.toNat + indices.toNat :=
          hrecursor.2.2.2.2.2.2.2
        _ = 0 + 1 + constructorIds.size + 0 := by
          rw [hparams, hrecursor.2.2.2.1,
            hrecursor.2.2.2.2.1, hindices]
        _ = constructorIds.size + 1 := by omega
  | _ => simp [KConst.IsCertifiedSingletonRecursor] at hrecursor

end KConst.IsCertifiedSingletonRecursor

namespace SingletonRecursorCatalogLink

/-- The concrete pattern compiled for enumeration rule `index`.  The
recursor prefix consists of one motive followed by one minor per
constructor; the selected RHS is therefore minor `index` at prefix position
`index + 1`. -/
def enumerationPattern
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (_link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (index : Nat) (hindex : index < family.constructorIds.size)
    (normalized : VInductDecl.NormalizedCtor) : RecursorRulePattern where
  recursorName :=
    .str tx.certificate.generation.block.sourceType.name "rec"
  constructorId := family.constructorIds[index]
  constructorName := normalized.raw.name
  constructorParams := 0
  constructorFields := 0
  ruleIndex := index
  majorIdx := family.constructorIds.size + 1
  rhs := RecursorIotaPattern.recursorArgumentRhs
    (.str tx.certificate.generation.block.sourceType.name "rec")
    (family.constructorIds.size + 1) normalized.raw.name 0
    ⟨index + 1, by omega⟩
  checks := .true

@[simp] theorem enumerationPattern_ruleIndex
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (_link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (index : Nat) (hindex : index < family.constructorIds.size)
    (normalized : VInductDecl.NormalizedCtor) :
    (_link.enumerationPattern index hindex normalized).ruleIndex = index := rfl

/-- Resolve a normalized enum constructor to the exact physical constructor
slot used by production iota dispatch. -/
theorem enumerationConstructorAt
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (_link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {index : Nat} (hindex : index < family.constructorIds.size)
    {normalized : VInductDecl.NormalizedCtor}
    (hnormalized :
      tx.certificate.generation.block.ctorPairs[index]? = some normalized) :
    ∃ concrete,
      catalog family.constructorIds[index] = some concrete ∧
      concrete.ConstructorAt index 0 0 ∧
      nameOf family.constructorIds[index].addr = some normalized.raw.name := by
  obtain ⟨sourceConstructor, concrete, hsource, hcatalog, hconcrete,
    hname, _⟩ := family.constructor index hindex
  have hnormalizedSource :=
    CertifiedSingletonGeneration.rawConstructorAt
      tx.certificate.generation hnormalized
  have hsourceEq : sourceConstructor = normalized.raw := by
    rw [hsource] at hnormalizedSource
    exact Option.some.inj hnormalizedSource
  subst sourceConstructor
  have hfieldsR := shape.fields_nil hnormalized
  have hrawFields : normalized.rawFields source.nparams = [] := by
    simpa [VInductDecl.NormalizedCtor.fieldsR] using hfieldsR
  change VInductDecl.ctorFields
    (VExpr.dropN source.nparams normalized.raw.type) = [] at hrawFields
  refine ⟨concrete, hcatalog, ?_, hname⟩
  cases concrete with
  | ctor name levelParams isUnsafe levels induct cidx params fields type =>
      simp only [KConst.IsCertifiedSingletonConstructor] at hconcrete
      simp only [KConst.ConstructorAt]
      refine ⟨hconcrete.2.2.1, ?_, ?_⟩
      · apply UInt64.toNat_inj.mp
        simpa [shape.noParameters] using hconcrete.2.2.2.1
      · apply UInt64.toNat_inj.mp
        rw [hrawFields] at hconcrete
        simpa using hconcrete.2.2.2.2
  | _ => simp [KConst.IsCertifiedSingletonConstructor] at hconcrete

/-- All finite pattern metadata for an enum rule is forced by the two exact
catalog links and the E2a generation position.  No semantic rewrite premise
is used here. -/
theorem enumerationPatternMetadata
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {index : Nat} {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt index rule) :
    ∃ (hindex : index < family.constructorIds.size)
        (normalized : VInductDecl.NormalizedCtor),
      tx.certificate.generation.block.ctorPairs[index]? = some normalized ∧
      RawRecursorRulePatternMetadataRel catalog nameOf link.recursorId
        link.recursorConcrete rule
        (link.enumerationPattern index hindex normalized) := by
  have hindex := link.recursorShape.ruleCount hrule
  obtain ⟨normalized, hnormalized, _, hfields, _, _⟩ :=
    link.ruleAt hrule
  obtain ⟨constructor, hconstructorCatalog, hconstructorAt,
    hconstructorName⟩ :=
    link.enumerationConstructorAt shape hindex hnormalized
  have hruleFields : rule.fields = 0 := by
    apply UInt64.toNat_inj.mp
    rw [hfields, shape.fields_nil hnormalized]
    rfl
  refine ⟨hindex, normalized, hnormalized, {
    recursorName := ?_
    majorIdx := ?_
    majorIdxCoherent := link.recursorShape.coherent
    ruleAt := ?_
    constructorName := ?_
    constructorAt := ?_
    fields := ?_ }⟩
  · simpa [enumerationPattern] using link.recursorName
  · simpa [enumerationPattern] using
      link.recursorShape.enumerationMajorIdx shape
  · simpa [enumerationPattern] using hrule
  · simpa [enumerationPattern] using hconstructorName
  · exact ⟨constructor, by
      simpa [enumerationPattern] using hconstructorCatalog, by
      simpa [enumerationPattern] using hconstructorAt⟩
  · simpa [enumerationPattern] using hruleFields

/-- The compiled enum pattern is semantically justified by the exact
registered generated equation.  This is the central E2b bridge: a successful
pattern match is reduced through Lean4Lean's registered equality, rather than
through an independently postulated iota law. -/
theorem enumerationPatternSound
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {index : Nat} {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt index rule)
    (hindex : index < family.constructorIds.size)
    (normalized : VInductDecl.NormalizedCtor)
    (hnormalized :
      tx.certificate.generation.block.ctorPairs[index]? = some normalized) :
    (link.enumerationPattern index hindex normalized).Sound after := by
  intro future hfuture hfutureWF uvars Gamma matched levels captures A
    hGamma hmatches htype _hchecks
  let generation := tx.certificate.generation
  have hcount : family.constructorIds.size =
      generation.block.ctorPairs.length := by
    rw [family.constructorCount, ← generation.rawCtors_eq]
    simp
  change Lean4Lean.Pattern.Matches
      (RecursorIotaPattern
        (.str generation.block.sourceType.name "rec")
        (family.constructorIds.size + 1) normalized.raw.name 0)
      matched levels captures at hmatches
  obtain ⟨recursorArguments, constructorLevels, constructorArguments,
    hrecursorLength, hconstructorLength, hmatched, hcaptures⟩ :=
    RecursorIotaPattern.matches_spines hmatches
  have hconstructorArguments : constructorArguments = [] :=
    List.eq_nil_of_length_eq_zero hconstructorLength
  rw [hmatched] at htype
  obtain ⟨majorDomain, majorBody, hrecursorApplied, hconstructorApplied⟩ :=
    htype.app_inv hfutureWF.ordered hGamma

  have hrecursorHead :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hrecursorApplied
  obtain ⟨recursorHeadType, hrecursorHeadType⟩ := hrecursorHead
  obtain ⟨recursorConstant, hrecursorLookup, hlevelsWF,
    hlevelsArity⟩ :=
    hrecursorHeadType.const_inv hfutureWF.ordered hGamma
  have hcertifiedRecursorLookup :=
    hfuture.constants tx.facts.recursorLookup
  have hrecursorConstant : recursorConstant = generation.recursor := by
    exact Option.some.inj
      (hrecursorLookup.symm.trans hcertifiedRecursorLookup)
  subst recursorConstant
  have hlevelsLength : levels.length = 1 := by
    simpa [VInductDecl.GenerationChecked.recursor,
      shape.noUniverses] using hlevelsArity

  rw [hconstructorArguments] at hconstructorApplied
  simp only [VExpr.appN] at hconstructorApplied
  obtain ⟨constructorConstant, hconstructorLookup, _,
    hconstructorLevelsArity⟩ :=
    hconstructorApplied.const_inv hfutureWF.ordered hGamma
  have hrawConstructor :=
    CertifiedSingletonGeneration.rawConstructorAt generation hnormalized
  have hrawConstructorMem :
      normalized.raw ∈ generation.block.sourceType.ctors :=
    List.mem_of_getElem? hrawConstructor
  have hcertifiedConstructorLookup :=
    hfuture.constants (tx.facts.ctorLookup hrawConstructorMem)
  have hconstructorConstant :
      constructorConstant = normalized.raw.toVConstant := by
    exact Option.some.inj
      (hconstructorLookup.symm.trans hcertifiedConstructorLookup)
  subst constructorConstant
  have hconstructorLevelsLength : constructorLevels.length = 0 := by
    calc
      constructorLevels.length = normalized.raw.toVConstant.uvars :=
        hconstructorLevelsArity
      _ = normalized.raw.uvars := rfl
      _ = source.uvars :=
        CertifiedSingletonGeneration.sourceConstructorUvars generation
          hrawConstructorMem
      _ = 0 := shape.noUniverses
  have hconstructorLevels : constructorLevels = [] :=
    List.eq_nil_of_length_eq_zero hconstructorLevelsLength

  obtain ⟨registeredNormalized, hregisteredNormalized, hregistered⟩ :=
    link.registeredRuleAt hrule
  have hnormalizedEq : registeredNormalized = normalized := by
    rw [hnormalized] at hregisteredNormalized
    exact (Option.some.inj hregisteredNormalized).symm
  subst registeredNormalized
  have hregisteredFuture := hregistered.mono hfuture
  obtain ⟨_, _, _, _, hdefeqRegistered, hdefeqWF, _, _, _⟩ :=
    hregisteredFuture
  have hlevelsRuleArity :
      levels.length = (generation.rule index normalized).uvars := by
    simpa [VInductDecl.GenerationChecked.rule, shape.noUniverses] using
      hlevelsLength
  have hequation : future.IsDefEq uvars Gamma
      ((generation.rule index normalized).lhs.instL levels)
      ((generation.rule index normalized).rhs.instL levels)
      ((generation.rule index normalized).type.instL levels) :=
    .extra hdefeqRegistered hlevelsWF hlevelsRuleArity

  have hrecursorConstantTyped : future.HasType uvars Gamma
      (.const (.str generation.block.sourceType.name "rec") levels)
      (generation.recType.instL levels) := by
    simpa [VInductDecl.GenerationChecked.recursor] using
      (Lean4Lean.VEnv.HasType.const
        (Γ := Gamma) hcertifiedRecursorLookup hlevelsWF hlevelsArity)
  have hrecursorCommonType : future.HasType uvars Gamma
      (.const (.str generation.block.sourceType.name "rec") levels)
      (VExpr.forallN
        ((CertifiedSingletonGeneration.IsEnumeration.ruleBinders generation).map
          (VExpr.instL levels))
        (.forallE
          (.const generation.block.sourceType.name [])
          (.app (.bvar (generation.block.ctorPairs.length + 1))
            (.bvar 0)))) := by
    rw [← shape.recType_instantiated levels]
    exact hrecursorConstantTyped
  have hequationLhsCommonType : future.HasType uvars Gamma
      ((generation.rule index normalized).lhs.instL levels)
      (VExpr.forallN
        ((CertifiedSingletonGeneration.IsEnumeration.ruleBinders generation).map
          (VExpr.instL levels))
        (.app (.bvar generation.block.ctorPairs.length)
          (.const normalized.raw.name []))) := by
    rw [← shape.ruleType_instantiated hnormalized levels]
    exact hequation.hasType.1
  have hargumentLength : recursorArguments.length =
      ((CertifiedSingletonGeneration.IsEnumeration.ruleBinders generation).map
        (VExpr.instL levels)).length := by
    rw [hrecursorLength, List.length_map,
      CertifiedSingletonGeneration.IsEnumeration.ruleBinders_length,
      hcount]
  obtain ⟨equationApplicationType, hequationLhsApplied⟩ :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope
      hfutureWF hGamma hargumentLength hrecursorApplied
      hrecursorCommonType hequationLhsCommonType
  have hequationApplied :=
    Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma hequation
      hequationLhsApplied
  have hequationRhsApplied : future.HasType uvars Gamma
      (VExpr.appN ((generation.rule index normalized).rhs.instL levels)
        recursorArguments) equationApplicationType :=
    (hequationApplied.of_l hfutureWF hGamma hequationLhsApplied).hasType.2

  have hequationLhsApplied' : future.HasType uvars Gamma
      (VExpr.appN
        (VExpr.lamN
          ((CertifiedSingletonGeneration.IsEnumeration.ruleBinders generation).map
            (VExpr.instL levels))
          ((VExpr.app
            (VExpr.appN
              (.const (.str generation.block.sourceType.name "rec")
                (Lean4Lean.VLevel.params 1))
              (VExpr.bvarRevRange 0
                (generation.block.ctorPairs.length + 1)))
            (.const normalized.raw.name [])).instL levels))
        recursorArguments) equationApplicationType := by
    have hcopy := hequationLhsApplied
    rw [CertifiedSingletonGeneration.IsEnumeration.rule_lhs shape hnormalized,
      VExpr.instL_lamN] at hcopy
    exact hcopy
  have hlhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hargumentLength hequationLhsApplied'
  rw [CertifiedSingletonGeneration.IsEnumeration.ruleLhsBody_instantiated
    normalized levels recursorArguments
    hlevelsLength (by simpa [hcount] using hrecursorLength)] at hlhsBeta
  have hlhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN ((generation.rule index normalized).lhs.instL levels)
        recursorArguments)
      (.app
        (VExpr.appN
          (.const (.str generation.block.sourceType.name "rec") levels)
          recursorArguments)
        (.const normalized.raw.name [])) := by
    rw [CertifiedSingletonGeneration.IsEnumeration.rule_lhs shape hnormalized,
      VExpr.instL_lamN]
    exact hlhsBeta

  have hequationRhsApplied' : future.HasType uvars Gamma
      (VExpr.appN
        (VExpr.lamN
          ((CertifiedSingletonGeneration.IsEnumeration.ruleBinders generation).map
            (VExpr.instL levels))
          ((.bvar (generation.block.ctorPairs.length - 1 - index) : VExpr).instL
            levels))
        recursorArguments) equationApplicationType := by
    have hcopy := hequationRhsApplied
    rw [CertifiedSingletonGeneration.IsEnumeration.rule_rhs shape hnormalized,
      VExpr.instL_lamN] at hcopy
    exact hcopy
  have hrhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hargumentLength hequationRhsApplied'
  have hindexGeneration : index < generation.block.ctorPairs.length := by
    simpa [hcount] using hindex
  rw [CertifiedSingletonGeneration.IsEnumeration.ruleRhsBody_instantiated
    index hindexGeneration levels
    recursorArguments (by simpa [hcount] using hrecursorLength)] at hrhsBeta
  let selected : Fin (family.constructorIds.size + 1) :=
    ⟨index + 1, by omega⟩
  have hselected : recursorArguments[index + 1] =
      captures (RecursorIotaPattern.recursorArgumentPath
        (.str generation.block.sourceType.name "rec")
        (family.constructorIds.size + 1) normalized.raw.name 0 selected) := by
    have hselected? := hcaptures selected
    have hselectedBound : selected.val < recursorArguments.length := by
      simp only [selected]
      rw [hrecursorLength]
      omega
    rw [List.getElem?_eq_getElem hselectedBound] at hselected?
    exact Option.some.inj hselected?
  rw [hselected] at hrhsBeta
  have hrhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN ((generation.rule index normalized).rhs.instL levels)
        recursorArguments)
      (captures (RecursorIotaPattern.recursorArgumentPath
        (.str generation.block.sourceType.name "rec")
        (family.constructorIds.size + 1) normalized.raw.name 0 selected)) := by
    rw [CertifiedSingletonGeneration.IsEnumeration.rule_rhs shape hnormalized,
      VExpr.instL_lamN]
    exact hrhsBeta

  have hresult := (hlhsBeta'.symm.trans hfutureWF hGamma
    hequationApplied).trans hfutureWF hGamma hrhsBeta'
  rw [hconstructorArguments, hconstructorLevels] at hmatched
  have hmatchedExact : matched =
      .app
        (VExpr.appN
          (.const (.str generation.block.sourceType.name "rec") levels)
          recursorArguments)
        (.const normalized.raw.name []) := by
    simpa only [VExpr.appN] using hmatched
  rw [hmatchedExact]
  simpa [SingletonRecursorCatalogLink.enumerationPattern, selected,
    RecursorIotaPattern.recursorArgumentRhs_apply] using hresult

/-- Package the finite pattern metadata and its registered-equation proof as
the exact historical relation consumed by the production iota verifier. -/
theorem enumerationPatternRel
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {source : VInductDecl} {before after : VEnv}
    {tx : CertifiedGenerationTransaction source before after}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {index : Nat} {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt index rule) :
    ∃ pattern,
      RawRecursorRulePatternRel after catalog nameOf link.recursorId
          link.recursorConcrete rule pattern ∧
        pattern.ruleIndex = index := by
  obtain ⟨hindex, normalized, hnormalized, hmetadata⟩ :=
    link.enumerationPatternMetadata shape hrule
  let pattern := link.enumerationPattern index hindex normalized
  refine ⟨pattern, RawRecursorRulePatternRel.of_metadata_sound hmetadata ?_,
    rfl⟩
  exact link.enumerationPatternSound shape hrule hindex normalized hnormalized

end SingletonRecursorCatalogLink

end Ix.Tc
