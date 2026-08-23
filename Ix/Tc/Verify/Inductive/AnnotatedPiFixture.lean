import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.AnnotatedPiCertificate
import Ix.Tc.Verify.Ingress.AnonStructural

/-!
# Production annotation-normalizing recursive-Pi fixture

This fixture materializes the transparent `outParam` definition followed by
the singleton `AnnotatedPi` family.  Its constructor retains the raw domain
`outParam Prop`, while production checking unfolds the reducible annotation
before classifying the recursive occurrence.

The dependency is an ordinary content-addressed definition.  It is ingressed,
related to the exact Theory declaration, and promoted before the certified
family transition; no ambient inductive or normalization oracle is used.
-/

namespace Ix.Tc.AnnotatedPiFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open AnnotatedPiCertificateFixture
open InductiveConcreteFixture

local instance anonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

local instance anonKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-! ## Transparent `outParam` dependency -/

/-- Anonymous syntax for `outParam.{u} : Sort u -> Sort u`. -/
def outParamConstant : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 1,
      .leanAll (.sort 0) (.sort 0),
      .leanLam (.sort 0) (.var 0)⟩,
    #[], #[], #[.var 0]⟩

def outParamStored : Ixon.Env × Address :=
  storeConstant {} outParamConstant

def outParamAddress : Address := outParamStored.2
def outParamId : KId .anon := ⟨outParamAddress, ()⟩

/-- `[reducible]` is represented by the anonymous hint channel rather than
the alpha-invariant constant payload. -/
def outParamIxonEnv : Ixon.Env :=
  { outParamStored.1 with
    anonHints := outParamStored.1.anonHints.insert outParamAddress .abbrev }

/-! ## Compiler-shaped `AnnotatedPi` family block -/

def familyType : Ixon.Expr := .sort 0

def mkType : Ixon.Expr :=
  .leanAll
    (.leanAll
      (.app (.ref 0 #[0]) (.sort 1))
      (.recur 0 #[]))
    (.recur 0 #[])

def familyIxon : Ixon.Inductive :=
  ⟨false, 0, 0, 0, familyType,
    #[⟨false, 0, 0, 0, 1, mkType⟩]⟩

/-- Universe position zero is `1`, used by both the family sort and
`outParam.{1}`; position one is `0` (Prop). -/
def familyBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc familyIxon], #[], #[outParamId.addr],
    #[.succ .zero, .zero]⟩

def familyStored : Ixon.Env × Address :=
  storeBlockWithProjections outParamIxonEnv familyBlockConstant

def ixonEnv : Ixon.Env := familyStored.1
def familyBlockAddress : Address := familyStored.2
def familyBlockId : KId .anon := ⟨familyBlockAddress, ()⟩
def familyId : KId .anon := ⟨indcProjAddr familyBlockAddress 0, ()⟩
def mkId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 0, ()⟩
def constructorIds : Array (KId .anon) := #[mkId]
def members : Array (KId .anon) := #[familyId, mkId]

/-! ## Dependency-ordered anonymous ingress -/

def outParamIngressOutcome :=
  ingressAnonAddrShallow ixonEnv outParamAddress true ({} : AnonEnv)

def outParamIngressAfter : AnonEnv :=
  match outParamIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def outParamIngressSucceeded : Bool :=
  match outParamIngressOutcome with
  | .ok found _ => found
  | .error _ _ => false

private theorem outParamIngressSucceededNative :
    outParamIngressSucceeded = true := by
  native_decide

theorem outParamIngressRun :
    outParamIngressOutcome = .ok true outParamIngressAfter := by
  have success := outParamIngressSucceededNative
  unfold outParamIngressSucceeded at success
  unfold outParamIngressAfter
  generalize houtcome : outParamIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def outParamUniverse : KUniv .anon := KUniv.mkParam 0 ()
def outParamSort : KExpr .anon := KExpr.mkSort outParamUniverse
def outParamTypeConcrete : KExpr .anon :=
  KExpr.mkAll () () outParamSort outParamSort
def outParamValueConcrete : KExpr .anon :=
  KExpr.mkLam () () outParamSort (KExpr.mkVar 0 ())

def outParamConcrete : KConst .anon :=
  .defn () () .defn .safe .abbrev 1 outParamTypeConcrete
    outParamValueConcrete () outParamId

private theorem outParamLoadedNative :
    outParamIngressAfter.get? outParamId = some outParamConcrete := by
  native_decide

theorem outParamLoaded :
    outParamIngressAfter.get? outParamId = some outParamConcrete :=
  outParamLoadedNative

def familyIngressOutcome :=
  ingressAnonBlockWithTrace ixonEnv familyBlockConstant familyBlockAddress
    outParamIngressAfter

def familyIngressResult : AnonBlockIngressTrace :=
  match familyIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyIngressAfter : AnonEnv :=
  match familyIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyIngressSucceeded : Bool :=
  match familyIngressOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyIngressSucceededNative :
    familyIngressSucceeded = true := by
  native_decide

theorem familyIngressRun :
    familyIngressOutcome = .ok familyIngressResult familyIngressAfter := by
  have success := familyIngressSucceededNative
  unfold familyIngressSucceeded at success
  unfold familyIngressResult familyIngressAfter
  generalize houtcome : familyIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def familyIngressExecution : AnonBlockIngressSuccessTrace ixonEnv
    familyBlockConstant familyBlockAddress outParamIngressAfter
      familyIngressAfter familyIngressResult :=
  AnonBlockIngressSuccessTrace.of_run familyIngressRun

private theorem memberKidsNative :
    familyIngressResult.memberKids = #[familyId] := by
  native_decide

theorem memberKids : familyIngressResult.memberKids = #[familyId] :=
  memberKidsNative

private theorem entryIdsNative :
    familyIngressResult.allEntries.map (·.1) = members := by
  native_decide

theorem entryIds : familyIngressResult.allEntries.map (·.1) = members :=
  entryIdsNative

private theorem entriesUniqueNative :
    EntryKeysUnique familyIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide

theorem entriesUnique : EntryKeysUnique familyIngressResult.allEntries :=
  entriesUniqueNative

/-! ## Actual production family checker -/

def checkerFuel : UInt64 := 1024
def checkerMethods : Methods .anon := methodsN checkerFuel.toNat

def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon familyIngressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

private theorem outParamStillLoadedNative :
    checkerInitial.env.get? outParamId = some outParamConcrete := by
  native_decide

theorem outParamStillLoaded :
    checkerInitial.env.get? outParamId = some outParamConcrete :=
  outParamStillLoadedNative

private theorem blockLoadedNative :
    checkerInitial.env.getBlock? familyBlockId = some members := by
  native_decide

theorem blockLoaded :
    checkerInitial.env.getBlock? familyBlockId = some members :=
  blockLoadedNative

def kernelOutcome :=
  (RecM.checkInductiveBlock familyBlockId members).run checkerMethods
    checkerInitial

def kernelAfter : TcState .anon :=
  match kernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def kernelSucceeded : Bool :=
  match kernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem kernelSucceededNative : kernelSucceeded = true := by
  native_decide

theorem kernelSucceeded_eq : kernelSucceeded = true :=
  kernelSucceededNative

theorem kernelRun :
    (RecM.checkInductiveBlock familyBlockId members).run checkerMethods
      checkerInitial = .ok () kernelAfter := by
  have success := kernelSucceeded_eq
  unfold kernelSucceeded at success
  unfold kernelAfter
  generalize houtcome : kernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [kernelOutcome]

/-! ## Exact converted family entries -/

private theorem entriesSizeNative : familyIngressResult.allEntries.size = 2 := by
  native_decide

theorem entriesSize : familyIngressResult.allEntries.size = 2 :=
  entriesSizeNative

private theorem indexZero : 0 < familyIngressResult.allEntries.size := by
  rw [entriesSize]
  omega

private theorem indexOne : 1 < familyIngressResult.allEntries.size := by
  rw [entriesSize]
  omega

def familyConcrete : KConst .anon :=
  (familyIngressResult.allEntries[0]'indexZero).2

def mkConcrete : KConst .anon :=
  (familyIngressResult.allEntries[1]'indexOne).2

private theorem familyEntryNative :
    (familyId, familyConcrete) ∈ familyIngressResult.allEntries := by
  have member := Array.getElem_mem indexZero
  have identifier :
      (familyIngressResult.allEntries[0]'indexZero).1 = familyId := by
    native_decide
  unfold familyConcrete
  rw [← identifier]
  exact member

theorem familyEntry :
    (familyId, familyConcrete) ∈ familyIngressResult.allEntries :=
  familyEntryNative

private theorem mkEntryNative :
    (mkId, mkConcrete) ∈ familyIngressResult.allEntries := by
  have member := Array.getElem_mem indexOne
  have identifier :
      (familyIngressResult.allEntries[1]'indexOne).1 = mkId := by
    native_decide
  unfold mkConcrete
  rw [← identifier]
  exact member

theorem mkEntry :
    (mkId, mkConcrete) ∈ familyIngressResult.allEntries :=
  mkEntryNative

/-! ## Exact source interpretation -/

def nameOf (address : Address) : Option Lean.Name :=
  if address == outParamId.addr then some ``outParam
  else if address == familyId.addr then some ``AnnotatedPi
  else if address == mkId.addr then some ``AnnotatedPi.mk
  else none

private theorem nameOfOutParamNative :
    nameOf outParamId.addr = some ``outParam := by
  native_decide

theorem nameOf_outParam : nameOf outParamId.addr = some ``outParam :=
  nameOfOutParamNative

private theorem nameOfFamilyNative :
    nameOf familyId.addr = some ``AnnotatedPi := by
  native_decide

theorem nameOf_family : nameOf familyId.addr = some ``AnnotatedPi :=
  nameOfFamilyNative

private theorem nameOfMkNative :
    nameOf mkId.addr = some ``AnnotatedPi.mk := by
  native_decide

theorem nameOf_mk : nameOf mkId.addr = some ``AnnotatedPi.mk :=
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

private theorem familyShapeNative :
    familyConcrete.IsCertifiedSingletonFamily annotatedPiRawDecl generation
      constructorIds := by
  native_decide

theorem familyShape :
    familyConcrete.IsCertifiedSingletonFamily annotatedPiRawDecl generation
      constructorIds :=
  familyShapeNative

private theorem sourceConstructorZero :
    0 < generation.block.sourceType.ctors.length := by
  native_decide

def mkSource : VConstVal :=
  generation.block.sourceType.ctors[0]'sourceConstructorZero

theorem mkSourceAt :
    generation.block.sourceType.ctors[0]? = some mkSource := rfl

private theorem mkShapeNative :
    mkConcrete.IsCertifiedSingletonConstructor annotatedPiRawDecl familyId 0
      mkSource := by
  native_decide

theorem mkShape :
    mkConcrete.IsCertifiedSingletonConstructor annotatedPiRawDecl familyId 0
      mkSource :=
  mkShapeNative

private theorem familyTypeRawNative :
    RawExprRel (uvars := familyConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] familyConcrete.ty
      generation.block.sourceType.type := by
  apply translateCore?_raw
  native_decide

theorem familyTypeRaw :
    RawExprRel (uvars := familyConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] familyConcrete.ty
      generation.block.sourceType.type :=
  familyTypeRawNative

private theorem mkTypeRawNative :
    RawExprRel (uvars := mkConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] mkConcrete.ty
      mkSource.type := by
  apply translateCore?_raw
  native_decide

theorem mkTypeRaw :
    RawExprRel (uvars := mkConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] mkConcrete.ty
      mkSource.type :=
  mkTypeRawNative

private theorem constructorCountNative :
    constructorIds.size = generation.block.sourceType.ctors.length := by
  native_decide

private theorem mkSourceNameNative : mkSource.name = ``AnnotatedPi.mk := by
  native_decide

def interpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf familyIngressResult transaction where
  familyId := familyId
  constructorIds := constructorIds
  memberKids := memberKids
  entryIds := by simpa [members, constructorIds] using entryIds
  entriesUnique := entriesUnique
  constructorCount := constructorCountNative
  familyConcrete := familyConcrete
  familyEntry := familyEntry
  familyShape := familyShape
  familyName := nameOf_family
  familyType := familyTypeRaw
  constructor := by
    intro index hindex
    change index < 1 at hindex
    have : index = 0 := by omega
    subst index
    refine ⟨mkSource, mkConcrete, mkSourceAt, ?_, mkShape, ?_, mkTypeRaw⟩
    · simpa [constructorIds] using mkEntry
    · simpa [constructorIds, mkSourceNameNative] using nameOf_mk

/-! ## Immutable semantic world and exact dependency promotion -/

def catalog : Catalog := fun id =>
  if id == outParamId then some outParamConcrete
  else if id == familyId then some familyConcrete
  else if id == mkId then some mkConcrete
  else none

def blockCatalog : BlockCatalog := fun id => familyIngressAfter.getBlock? id

private theorem catalogOutParamNative :
    catalog outParamId = some outParamConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_outParam : catalog outParamId = some outParamConcrete :=
  catalogOutParamNative

private theorem catalogFamilyNative :
    catalog familyId = some familyConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_family : catalog familyId = some familyConcrete :=
  catalogFamilyNative

private theorem catalogMkNative : catalog mkId = some mkConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_mk : catalog mkId = some mkConcrete :=
  catalogMkNative

private theorem outParamTranslationsNative :
    translateCore? VEnv.empty nameOf outParamTypeConcrete =
        some outParamValue.type ∧
      translateCore? VEnv.empty nameOf outParamValueConcrete =
        some outParamValue.value := by
  native_decide

private theorem outParamTypeRaw :
    RawExprRel (uvars := outParamConcrete.lvls.toNat) VEnv.empty nameOf
      RawProjRel.none [] outParamTypeConcrete
      outParamValue.type :=
  translateCore?_raw outParamTranslationsNative.1

private theorem outParamValueRaw :
    RawExprRel (uvars := outParamConcrete.lvls.toNat) VEnv.empty nameOf
      RawProjRel.none [] outParamValueConcrete
      outParamValue.value :=
  translateCore?_raw outParamTranslationsNative.2

theorem outParamRaw : RawDeclRel VEnv.empty nameOf RawProjRel.none
    outParamId outParamConcrete (.def outParamValue) := by
  apply RawDeclRel.defn nameOf_outParam
  · exact outParamTypeRaw
  · exact outParamValueRaw
  · exact .defn

private theorem noReferencesFromEmpty
    {uvars : Nat} {source : KExpr .anon} {target : VExpr}
    (raw : RawExprRel (uvars := uvars) VEnv.empty nameOf RawProjRel.none []
      source target)
    (id : KId .anon) : ¬source.References id := by
  intro href
  obtain ⟨name, constant, _hname, hlookup⟩ :=
    raw.reference_resolved href
  simp [VEnv.empty] at hlookup

theorem outParamClosed : CatalogClosed catalog outParamConcrete := by
  intro id href
  change outParamTypeConcrete.References id ∨
    outParamValueConcrete.References id ∨ outParamId = id at href
  rcases href with href | href | href
  · exact False.elim (noReferencesFromEmpty outParamTypeRaw id href)
  · exact False.elim (noReferencesFromEmpty outParamValueRaw id href)
  · subst id
    exact ⟨outParamConcrete, catalog_outParam⟩

def trusted : KId .anon → Prop :=
  TrustInsert (fun _ => False) outParamId

def world : VerifyWorld where
  catalog := catalog
  trusted := trusted
  venv := outParamEnv
  nameOf := nameOf
  venvWF := beforeWF
  trustedCatalogued := by
    intro id htrusted
    rcases htrusted with hnew | hold
    · subst id
      exact ⟨outParamConcrete, catalog_outParam⟩
    · exact False.elim hold
  blocks := blockCatalog

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world := by
  exact TrustedCatalogLog.promote TrustedCatalogLog.empty catalog_outParam
    outParamRaw outParamClosed (by simp) outParamDeclWF

private theorem entryAtZeroNative :
    familyIngressResult.allEntries[0]'indexZero =
      (familyId, familyConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem entryAtZero :
    familyIngressResult.allEntries[0]'indexZero =
      (familyId, familyConcrete) :=
  entryAtZeroNative

private theorem entryAtOneNative :
    familyIngressResult.allEntries[1]'indexOne = (mkId, mkConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem entryAtOne :
    familyIngressResult.allEntries[1]'indexOne = (mkId, mkConcrete) :=
  entryAtOneNative

theorem catalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry : (id, concrete) ∈ familyIngressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [entriesSize] at hindex
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · rw [entryAtZero] at hget
    cases hget
    exact catalog_family
  · rw [entryAtOne] at hget
    cases hget
    exact catalog_mk

/-- The actual `AnnotatedPi` ingress block extends the explicitly promoted
`outParam` world through the certified non-identity generation. -/
def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  interpretation.toCatalogLinkOfEntries familyIngressExecution catalogEntry
    trustedCatalog

end Ix.Tc.AnnotatedPiFixture
