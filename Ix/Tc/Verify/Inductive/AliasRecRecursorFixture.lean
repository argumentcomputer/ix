import Ix.Tc.Verify.Inductive.AliasRecFixture

/-!
# Production `AliasRec.rec` fixture

This module stores and checks the canonical recursor generated for the raw
recursive-field-alias-bearing family.  Its minor premise retains the raw field
`a : RecAlias AliasRec`, while the generated induction hypothesis targets the
normalized direct-recursive value `motive a`.
-/

namespace Ix.Tc.AliasRecRecursorFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open AliasRecCertificateFixture
open AliasRecFixture
open InductiveConcreteFixture

local instance recursorAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

local instance recursorAnonKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-! ## Canonical anonymous recursor syntax -/

private def rawFieldType : Ixon.Expr :=
  .app (.ref 0 #[1]) (.ref 1 #[])

private def familyRef : Ixon.Expr := .ref 1 #[]
private def constructorRef : Ixon.Expr := .ref 2 #[]

private def motiveType : Ixon.Expr :=
  .all familyRef (.sort 0)

private def inductionHypothesisType : Ixon.Expr :=
  .app (.var 1) (.var 0)

private def minorType : Ixon.Expr :=
  .all rawFieldType
    (.all inductionHypothesisType
      (.app (.var 2) (.app constructorRef (.var 1))))

def recursorType : Ixon.Expr :=
  .all motiveType
    (.all minorType
      (.all familyRef (.app (.var 2) (.var 0))))

/-- `mk a (AliasRec.rec motive mk a)`. -/
def mkRuleRhs : Ixon.Expr :=
  .lam motiveType
    (.lam minorType
      (.lam rawFieldType
        (.app (.app (.var 1) (.var 0))
          (.app
            (.app
              (.app (.recur 0 #[0]) (.var 2))
              (.var 1))
            (.var 0)))))

def recursorIxon : Ixon.Recursor :=
  ⟨false, false, 1, 0, 0, 1, 1, recursorType,
    #[⟨1, mkRuleRhs⟩]⟩

/-- Reference positions are `RecAlias`, `AliasRec`, and `AliasRec.mk`.
Universe positions are the recursor result universe and `1`. -/
def recursorBlockConstant : Ixon.Constant :=
  ⟨.muts #[.recr recursorIxon], #[],
    #[recAliasId.addr, familyId.addr, mkId.addr],
    #[.var 0, .succ .zero]⟩

def recursorStored : Ixon.Env × Address :=
  storeBlockWithProjections ixonEnv recursorBlockConstant

def recursorIxonEnv : Ixon.Env := recursorStored.1
def recursorBlockAddress : Address := recursorStored.2
def recursorBlockId : KId .anon := ⟨recursorBlockAddress, ()⟩
def recursorId : KId .anon :=
  ⟨recrProjAddr recursorBlockAddress 0, ()⟩
def recursorMembers : Array (KId .anon) := #[recursorId]

/-! ## Actual recursor ingress -/

def recursorIngressOutcome :=
  ingressAnonBlockWithTrace recursorIxonEnv recursorBlockConstant
    recursorBlockAddress familyIngressAfter

def recursorIngressResult : AnonBlockIngressTrace :=
  match recursorIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def recursorIngressAfter : AnonEnv :=
  match recursorIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorIngressSucceeded : Bool :=
  match recursorIngressOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem recursorIngressSucceededNative :
    recursorIngressSucceeded = true := by
  native_decide

theorem recursorIngressSucceeded_eq : recursorIngressSucceeded = true :=
  recursorIngressSucceededNative

theorem recursorIngressRun :
    recursorIngressOutcome =
      .ok recursorIngressResult recursorIngressAfter := by
  have success := recursorIngressSucceeded_eq
  unfold recursorIngressSucceeded at success
  unfold recursorIngressResult recursorIngressAfter
  generalize houtcome : recursorIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def recursorIngressExecution : AnonBlockIngressSuccessTrace recursorIxonEnv
    recursorBlockConstant recursorBlockAddress familyIngressAfter
      recursorIngressAfter recursorIngressResult :=
  AnonBlockIngressSuccessTrace.of_run recursorIngressRun

private theorem recursorMemberKidsNative :
    recursorIngressResult.memberKids = #[recursorId] := by
  native_decide

theorem recursorMemberKids :
    recursorIngressResult.memberKids = #[recursorId] :=
  recursorMemberKidsNative

private theorem recursorEntryIdsNative :
    recursorIngressResult.allEntries.map (·.1) = recursorMembers := by
  native_decide

theorem recursorEntryIds :
    recursorIngressResult.allEntries.map (·.1) = recursorMembers :=
  recursorEntryIdsNative

private theorem recursorEntriesUniqueNative :
    EntryKeysUnique recursorIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide

theorem recursorEntriesUnique :
    EntryKeysUnique recursorIngressResult.allEntries :=
  recursorEntriesUniqueNative

private theorem recursorEntrySizeNative :
    recursorIngressResult.allEntries.size = 1 := by
  native_decide

theorem recursorEntrySize : recursorIngressResult.allEntries.size = 1 :=
  recursorEntrySizeNative

private theorem recursorIndexZero :
    0 < recursorIngressResult.allEntries.size := by
  rw [recursorEntrySize]
  omega

def recursorConcrete : KConst .anon :=
  (recursorIngressResult.allEntries[0]'recursorIndexZero).2

private theorem recursorEntryNative :
    (recursorId, recursorConcrete) ∈ recursorIngressResult.allEntries := by
  have member := Array.getElem_mem recursorIndexZero
  have identifier :
      (recursorIngressResult.allEntries[0]'recursorIndexZero).1 =
        recursorId := by
    native_decide
  unfold recursorConcrete
  rw [← identifier]
  exact member

theorem recursorEntry :
    (recursorId, recursorConcrete) ∈ recursorIngressResult.allEntries :=
  recursorEntryNative

/-! ## Actual family and recursor checker sequence -/

def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon recursorIngressAfter with
    recFuel := AliasRecFixture.checkerFuel
    fuelBudget := AliasRecFixture.checkerFuel }

private theorem recAliasLoadedNative :
    checkerInitial.env.get? recAliasId =
      some AliasRecFixture.recAliasConcrete := by
  native_decide

theorem recAliasLoaded :
    checkerInitial.env.get? recAliasId =
      some AliasRecFixture.recAliasConcrete :=
  recAliasLoadedNative

private theorem familyBlockLoadedNative :
    checkerInitial.env.getBlock? familyBlockId = some members := by
  native_decide

theorem familyBlockLoaded :
    checkerInitial.env.getBlock? familyBlockId = some members :=
  familyBlockLoadedNative

private theorem recursorBlockLoadedNative :
    checkerInitial.env.getBlock? recursorBlockId = some recursorMembers := by
  native_decide

theorem recursorBlockLoaded :
    checkerInitial.env.getBlock? recursorBlockId = some recursorMembers :=
  recursorBlockLoadedNative

def familyKernelOutcome :=
  (RecM.checkInductiveBlock familyBlockId members).run checkerMethods
    checkerInitial

def familyKernelAfter : TcState .anon :=
  match familyKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyKernelSucceeded : Bool :=
  match familyKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyKernelSucceededNative :
    familyKernelSucceeded = true := by
  native_decide

theorem familyKernelSucceeded_eq : familyKernelSucceeded = true :=
  familyKernelSucceededNative

theorem familyKernelRun :
    (RecM.checkInductiveBlock familyBlockId members).run checkerMethods
      checkerInitial = .ok () familyKernelAfter := by
  have success := familyKernelSucceeded_eq
  unfold familyKernelSucceeded at success
  unfold familyKernelAfter
  generalize houtcome : familyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyKernelOutcome]

def recursorKernelOutcome :=
  (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
    checkerMethods familyKernelAfter

def recursorKernelAfter : TcState .anon :=
  match recursorKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorKernelSucceeded : Bool :=
  match recursorKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem recursorKernelSucceededNative :
    recursorKernelSucceeded = true := by
  native_decide

theorem recursorKernelSucceeded_eq : recursorKernelSucceeded = true :=
  recursorKernelSucceededNative

/-- Production reconstructs the recursive-field-normalizing recursor and accepts
the independently stored type and rule. -/
theorem recursorKernelRun :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter := by
  have success := recursorKernelSucceeded_eq
  unfold recursorKernelSucceeded at success
  unfold recursorKernelAfter
  generalize houtcome : recursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [recursorKernelOutcome]

/-! ## Complete source interpretation -/

def nameOf (address : Address) : Option Lean.Name :=
  if address == recursorId.addr then some ``AliasRec.rec
  else AliasRecFixture.nameOf address

private theorem nameOfRecursorNative :
    nameOf recursorId.addr = some ``AliasRec.rec := by
  native_decide

theorem nameOf_recursor : nameOf recursorId.addr = some ``AliasRec.rec :=
  nameOfRecursorNative

private theorem nameOfRecAliasNative :
    nameOf recAliasId.addr = some ``RecAlias := by
  native_decide

theorem nameOf_recAlias : nameOf recAliasId.addr = some ``RecAlias :=
  nameOfRecAliasNative

private theorem nameOfFamilyNative :
    nameOf familyId.addr = some ``AliasRec := by
  native_decide

theorem nameOf_family : nameOf familyId.addr = some ``AliasRec :=
  nameOfFamilyNative

private theorem nameOfMkNative :
    nameOf mkId.addr = some ``AliasRec.mk := by
  native_decide

theorem nameOf_mk : nameOf mkId.addr = some ``AliasRec.mk :=
  nameOfMkNative

private abbrev generation := transaction.certificate.generation

local instance certifiedSingletonFamilyDecidable
    (source : VInductDecl) (sourceGeneration : source.GenerationChecked)
    (ids : Array (KId .anon)) (concrete : KConst .anon) :
    Decidable
      (concrete.IsCertifiedSingletonFamily source sourceGeneration ids) := by
  cases concrete <;>
    simp only [KConst.IsCertifiedSingletonFamily] <;> infer_instance

local instance certifiedSingletonConstructorDecidable
    (source : VInductDecl) (inductiveId : KId .anon) (index : Nat)
    (sourceConstructor : VConstVal) (concrete : KConst .anon) :
    Decidable (concrete.IsCertifiedSingletonConstructor source inductiveId
      index sourceConstructor) := by
  cases concrete <;>
    simp only [KConst.IsCertifiedSingletonConstructor] <;> infer_instance

local instance recursorMajorIdxCoherentDecidable (concrete : KConst .anon) :
    Decidable concrete.RecursorMajorIdxCoherent := by
  cases concrete <;>
    simp only [KConst.RecursorMajorIdxCoherent] <;> infer_instance

local instance certifiedSingletonRecursorDecidable
    (source : VInductDecl) (sourceGeneration : source.GenerationChecked)
    (ids : Array (KId .anon)) (concrete : KConst .anon) :
    Decidable
      (concrete.IsCertifiedSingletonRecursor source sourceGeneration ids) := by
  cases concrete <;>
    simp only [KConst.IsCertifiedSingletonRecursor] <;> infer_instance

private theorem familyTypeRawNative :
    RawExprRel (uvars := AliasRecFixture.familyConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      AliasRecFixture.familyConcrete.ty
      generation.block.sourceType.type := by
  apply translateCore?_raw
  native_decide

theorem familyTypeRaw :
    RawExprRel (uvars := AliasRecFixture.familyConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      AliasRecFixture.familyConcrete.ty
      generation.block.sourceType.type :=
  familyTypeRawNative

private theorem mkTypeRawNative :
    RawExprRel (uvars := AliasRecFixture.mkConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      AliasRecFixture.mkConcrete.ty AliasRecFixture.mkSource.type := by
  apply translateCore?_raw
  native_decide

theorem mkTypeRaw :
    RawExprRel (uvars := AliasRecFixture.mkConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      AliasRecFixture.mkConcrete.ty AliasRecFixture.mkSource.type :=
  mkTypeRawNative

private theorem constructorCountNative :
    constructorIds.size = generation.block.sourceType.ctors.length := by
  native_decide

private theorem mkSourceNameNative :
    AliasRecFixture.mkSource.name = ``AliasRec.mk := by
  native_decide

def familyInterpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf AliasRecFixture.familyIngressResult
      transaction where
  familyId := familyId
  constructorIds := constructorIds
  memberKids := AliasRecFixture.memberKids
  entryIds := by
    simpa [AliasRecFixture.members, constructorIds] using
      AliasRecFixture.entryIds
  entriesUnique := AliasRecFixture.entriesUnique
  constructorCount := constructorCountNative
  familyConcrete := AliasRecFixture.familyConcrete
  familyEntry := AliasRecFixture.familyEntry
  familyShape := AliasRecFixture.familyShape
  familyName := nameOf_family
  familyType := familyTypeRaw
  constructor := by
    intro index hindex
    change index < 1 at hindex
    have : index = 0 := by omega
    subst index
    refine ⟨AliasRecFixture.mkSource, AliasRecFixture.mkConcrete,
      AliasRecFixture.mkSourceAt, ?_, AliasRecFixture.mkShape, ?_,
      mkTypeRaw⟩
    · simpa [constructorIds] using AliasRecFixture.mkEntry
    · simpa [constructorIds, mkSourceNameNative] using nameOf_mk

/-! ## One immutable catalog and promoted base world -/

def catalog : Catalog := fun id =>
  if id == recAliasId then some AliasRecFixture.recAliasConcrete
  else if id == familyId then some AliasRecFixture.familyConcrete
  else if id == mkId then some AliasRecFixture.mkConcrete
  else if id == recursorId then some recursorConcrete
  else none

def blockCatalog : BlockCatalog := fun id => recursorIngressAfter.getBlock? id

private theorem catalogRecAliasNative :
    catalog recAliasId = some AliasRecFixture.recAliasConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_recAlias :
    catalog recAliasId = some AliasRecFixture.recAliasConcrete :=
  catalogRecAliasNative

private theorem catalogFamilyNative :
    catalog familyId = some AliasRecFixture.familyConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_family :
    catalog familyId = some AliasRecFixture.familyConcrete :=
  catalogFamilyNative

private theorem catalogMkNative :
    catalog mkId = some AliasRecFixture.mkConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_mk : catalog mkId = some AliasRecFixture.mkConcrete :=
  catalogMkNative

private theorem catalogRecursorNative :
    catalog recursorId = some recursorConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_recursor : catalog recursorId = some recursorConcrete :=
  catalogRecursorNative

private theorem recAliasTranslationsNative :
    translateCore? VEnv.empty nameOf AliasRecFixture.recAliasTypeConcrete =
        some recAliasValue.type ∧
      translateCore? VEnv.empty nameOf
        AliasRecFixture.recAliasValueConcrete =
          some recAliasValue.value := by
  native_decide

private theorem recAliasTypeRaw :
    RawExprRel (uvars := AliasRecFixture.recAliasConcrete.lvls.toNat)
      VEnv.empty nameOf RawProjRel.none []
      AliasRecFixture.recAliasTypeConcrete recAliasValue.type :=
  translateCore?_raw recAliasTranslationsNative.1

private theorem recAliasValueRaw :
    RawExprRel (uvars := AliasRecFixture.recAliasConcrete.lvls.toNat)
      VEnv.empty nameOf RawProjRel.none []
      AliasRecFixture.recAliasValueConcrete recAliasValue.value :=
  translateCore?_raw recAliasTranslationsNative.2

theorem recAliasRaw : RawDeclRel VEnv.empty nameOf RawProjRel.none
    recAliasId AliasRecFixture.recAliasConcrete (.def recAliasValue) := by
  apply RawDeclRel.defn nameOf_recAlias
  · exact recAliasTypeRaw
  · exact recAliasValueRaw
  · exact .defn

private theorem noReferencesFromEmpty
    {uvars : Nat} {source : KExpr .anon} {target : VExpr}
    (raw : RawExprRel (uvars := uvars) VEnv.empty nameOf RawProjRel.none []
      source target)
    (id : KId .anon) : ¬source.References id := by
  intro href
  obtain ⟨_name, _constant, _hname, hlookup⟩ :=
    raw.reference_resolved href
  simp [VEnv.empty] at hlookup

theorem recAliasClosed :
    CatalogClosed catalog AliasRecFixture.recAliasConcrete := by
  intro id href
  change AliasRecFixture.recAliasTypeConcrete.References id ∨
    AliasRecFixture.recAliasValueConcrete.References id ∨
      recAliasId = id at href
  rcases href with href | href | href
  · exact False.elim (noReferencesFromEmpty recAliasTypeRaw id href)
  · exact False.elim (noReferencesFromEmpty recAliasValueRaw id href)
  · subst id
    exact ⟨AliasRecFixture.recAliasConcrete, catalog_recAlias⟩

def trusted : KId .anon → Prop :=
  TrustInsert (fun _ => False) recAliasId

def world : VerifyWorld where
  catalog := catalog
  trusted := trusted
  venv := recAliasEnv
  nameOf := nameOf
  venvWF := beforeWF
  trustedCatalogued := by
    intro id htrusted
    rcases htrusted with hnew | hold
    · subst id
      exact ⟨AliasRecFixture.recAliasConcrete, catalog_recAlias⟩
    · exact False.elim hold
  blocks := blockCatalog

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world := by
  exact TrustedCatalogLog.promote TrustedCatalogLog.empty catalog_recAlias
    recAliasRaw recAliasClosed (by simp) recAliasDeclWF

theorem familyCatalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry :
      (id, concrete) ∈ AliasRecFixture.familyIngressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [AliasRecFixture.entriesSize] at hindex
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · rw [AliasRecFixture.entryAtZero] at hget
    cases hget
    exact catalog_family
  · rw [AliasRecFixture.entryAtOne] at hget
    cases hget
    exact catalog_mk

def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  familyInterpretation.toCatalogLinkOfEntries
    AliasRecFixture.familyIngressExecution familyCatalogEntry trustedCatalog

/-! ## Exact generated recursor semantics -/

private theorem recursorShapeNative :
    recursorConcrete.IsCertifiedSingletonRecursor aliasRecRawDecl generation
      constructorIds := by
  native_decide

theorem recursorShape :
    recursorConcrete.IsCertifiedSingletonRecursor aliasRecRawDecl generation
      constructorIds :=
  recursorShapeNative

def recursorRules : Array (RecRule .anon) :=
  match recursorConcrete with
  | .recr (rules := rules) .. => rules
  | _ => #[]

private theorem recursorRulesSizeNative : recursorRules.size = 1 := by
  native_decide

theorem recursorRulesSize : recursorRules.size = 1 :=
  recursorRulesSizeNative

def concreteRule : RecRule .anon := recursorRules[0]!

theorem recursorRuleAt_iff {index : Nat} {rule : RecRule .anon} :
    recursorConcrete.RecursorRuleAt index rule ↔
      recursorRules[index]? = some rule := by
  unfold KConst.RecursorRuleAt recursorRules
  cases recursorConcrete <;> simp

theorem concreteRule_ruleAt :
    recursorConcrete.RecursorRuleAt 0 concreteRule := by
  rw [recursorRuleAt_iff]
  have hposition : 0 < recursorRules.size := by
    rw [recursorRulesSize]
    omega
  rw [Array.getElem?_eq_getElem hposition]
  congr 1
  exact (getElem!_pos recursorRules 0 hposition).symm

private theorem generationCtorPairZero :
    0 < generation.block.ctorPairs.length := by
  native_decide

def mkNormalized : VInductDecl.NormalizedCtor :=
  generation.block.ctorPairs[0]'generationCtorPairZero

theorem mkNormalizedAt :
    generation.block.ctorPairs[0]? = some mkNormalized := rfl

private theorem recursorTypeRawNative :
    RawExprRel (uvars := generation.recursor.uvars) finalEnv nameOf
      RawProjRel.none [] recursorConcrete.ty
      generation.recursor.type := by
  apply translateCore?_raw
  native_decide

theorem recursorTypeRaw :
    RawExprRel (uvars := generation.recursor.uvars) finalEnv nameOf
      RawProjRel.none [] recursorConcrete.ty
      generation.recursor.type :=
  recursorTypeRawNative

private theorem recursorUniverseCountNative :
    recursorConcrete.lvls.toNat = generation.recursor.uvars := by
  native_decide

theorem recursorTypeRawConcrete :
    RawExprRel (uvars := recursorConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] recursorConcrete.ty generation.recursor.type := by
  simpa only [recursorUniverseCountNative] using recursorTypeRaw

private theorem recursorTypeBinderCoreNative :
    recursorConcrete.ty.binderCore = true := by
  native_decide

private theorem recursorTypeScopedNative :
    recursorConcrete.ty.Scoped 0 generation.recursor.uvars := by
  native_decide

private theorem recursorTypeSizeBoundNative :
    recursorConcrete.ty.size < UInt64.size := by
  native_decide

def recursorTypePre : PreTrKExprS finalEnv generation.recursor.uvars
    nameOf RawProjRel.none [] recursorConcrete.ty generation.recursor.type :=
  recursorTypeRaw.toPreBinderCore_of_scoped recursorTypeBinderCoreNative
    recursorTypeScopedNative recursorTypeSizeBoundNative

theorem recursorTypeTyped : TrKExprS finalEnv generation.recursor.uvars
    nameOf RawProjRel.none [] recursorConcrete.ty generation.recursor.type := by
  have htype := transaction.generationEnv.recType_isType
  have htargetWF : VExpr.WF finalEnv generation.recursor.uvars []
      generation.recursor.type :=
    ⟨.sort htype.choose, htype.choose_spec⟩
  exact recursorTypePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) recursorTypeBinderCoreNative
    (by simpa [KVLCtx.toCtx] using htargetWF)

private theorem mkRuleRawNative :
    RawExprRel (uvars := (generation.rule 0 mkNormalized).uvars) finalEnv
      nameOf RawProjRel.none [] concreteRule.rhs
      (generation.rule 0 mkNormalized).rhs := by
  apply translateCore?_raw
  native_decide

theorem mkRuleRaw :
    RawExprRel (uvars := (generation.rule 0 mkNormalized).uvars) finalEnv
      nameOf RawProjRel.none [] concreteRule.rhs
      (generation.rule 0 mkNormalized).rhs :=
  mkRuleRawNative

private theorem mkRuleFieldsNative :
    concreteRule.fields.toNat =
      (mkNormalized.fieldsR aliasRecRawDecl.uvars
        aliasRecRawDecl.nparams).length := by
  native_decide

theorem mkRuleFields :
    concreteRule.fields.toNat =
      (mkNormalized.fieldsR aliasRecRawDecl.uvars
        aliasRecRawDecl.nparams).length :=
  mkRuleFieldsNative

private theorem mkRuleBinderCoreNative :
    concreteRule.rhs.binderCore = true := by
  native_decide

private theorem mkRuleScopedNative :
    concreteRule.rhs.Scoped 0 (generation.rule 0 mkNormalized).uvars := by
  native_decide

private theorem mkRuleSizeBoundNative :
    concreteRule.rhs.size < UInt64.size := by
  native_decide

def mkRulePre : PreTrKExprS finalEnv
    (generation.rule 0 mkNormalized).uvars nameOf RawProjRel.none []
    concreteRule.rhs (generation.rule 0 mkNormalized).rhs :=
  mkRuleRaw.toPreBinderCore_of_scoped mkRuleBinderCoreNative
    mkRuleScopedNative mkRuleSizeBoundNative

theorem mkGeneratedRuleMem :
    generation.rule 0 mkNormalized ∈ generation.generatedRules :=
  List.mem_of_getElem?
    (CertifiedSingletonGeneration.generatedRuleAt generation mkNormalizedAt)

theorem mkGeneratedRuleWF :
    (generation.rule 0 mkNormalized).WF finalEnv :=
  transaction.facts.afterWF.ordered.defEqWF
    (transaction.facts.ruleMem mkGeneratedRuleMem)

theorem mkRuleTyped : TrKExprS finalEnv
    (generation.rule 0 mkNormalized).uvars nameOf RawProjRel.none []
    concreteRule.rhs (generation.rule 0 mkNormalized).rhs := by
  exact mkRulePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) mkRuleBinderCoreNative
    ⟨_, mkGeneratedRuleWF.2⟩

def recursorInterpretation : SingletonRecursorIngressInterpretation
    RawProjRel.none world.nameOf recursorIngressResult transaction
      familyLink where
  recursorId := recursorId
  memberKids := recursorMemberKids
  entryIds := recursorEntryIds
  entriesUnique := recursorEntriesUnique
  recursorConcrete := recursorConcrete
  recursorEntry := recursorEntry
  recursorShape := recursorShape
  recursorName := nameOf_recursor
  recursorType := recursorTypeRawConcrete
  rule := by
    intro index hindex
    change index < 1 at hindex
    have : index = 0 := by omega
    subst index
    exact ⟨concreteRule, mkNormalized, concreteRule_ruleAt,
      mkNormalizedAt, mkRuleFields, mkRuleRaw, mkRuleTyped⟩

def recursorLink : SingletonRecursorCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction familyLink :=
  recursorInterpretation.toCatalogLinkOfEntry recursorIngressExecution
    catalog_recursor trustedCatalog

end Ix.Tc.AliasRecRecursorFixture
