import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.AliasRecCertificate
import Ix.Tc.Verify.Ingress.AnonStructural

/-!
# Production recursive-field-normalizing fixture

This fixture materializes the transparent `RecAlias` identity definition and
then the singleton `AliasRec` family.  Its constructor retains the raw field
`RecAlias AliasRec`, while production checking unfolds that wrapper before
classifying the direct recursive occurrence.

The dependency is an ordinary content-addressed definition.  It is ingressed,
related to the exact Theory declaration, and promoted before the certified
family transition; no ambient inductive or normalization oracle is used.
-/

namespace Ix.Tc.AliasRecFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open AliasRecCertificateFixture
open InductiveConcreteFixture

local instance anonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

local instance anonKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-! ## Transparent `RecAlias` dependency -/

/-- Anonymous syntax for `RecAlias.{u} : Sort u → Sort u := id`. -/
def recAliasConstant : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 1,
      .leanAll (.sort 0) (.sort 0),
      .leanLam (.sort 0) (.var 0)⟩,
    #[], #[], #[.var 0]⟩

def recAliasStored : Ixon.Env × Address :=
  storeConstant {} recAliasConstant

def recAliasAddress : Address := recAliasStored.2
def recAliasId : KId .anon := ⟨recAliasAddress, ()⟩

/-- `[reducible]` is represented by the anonymous hint channel rather than
the alpha-invariant constant payload. -/
def recAliasIxonEnv : Ixon.Env :=
  { recAliasStored.1 with
    anonHints := recAliasStored.1.anonHints.insert recAliasAddress .abbrev }

/-! ## Compiler-shaped `AliasRec` family block -/

def familyType : Ixon.Expr := .sort 0

def rawFieldType : Ixon.Expr :=
  .app (.ref 0 #[0]) (.recur 0 #[])

def mkType : Ixon.Expr :=
  .leanAll rawFieldType (.recur 0 #[])

def familyIxon : Ixon.Inductive :=
  ⟨false, 0, 0, 0, familyType,
    #[⟨false, 0, 0, 0, 1, mkType⟩]⟩

/-- Universe position zero is `1`, used by both the family sort and
`RecAlias.{1}`. -/
def familyBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc familyIxon], #[], #[recAliasId.addr],
    #[.succ .zero]⟩

def familyStored : Ixon.Env × Address :=
  storeBlockWithProjections recAliasIxonEnv familyBlockConstant

def ixonEnv : Ixon.Env := familyStored.1
def familyBlockAddress : Address := familyStored.2
def familyBlockId : KId .anon := ⟨familyBlockAddress, ()⟩
def familyId : KId .anon := ⟨indcProjAddr familyBlockAddress 0, ()⟩
def mkId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 0, ()⟩
def constructorIds : Array (KId .anon) := #[mkId]
def members : Array (KId .anon) := #[familyId, mkId]

/-! ## Dependency-ordered anonymous ingress -/

def recAliasIngressOutcome :=
  ingressAnonAddrShallow ixonEnv recAliasAddress true ({} : AnonEnv)

def recAliasIngressAfter : AnonEnv :=
  match recAliasIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recAliasIngressSucceeded : Bool :=
  match recAliasIngressOutcome with
  | .ok found _ => found
  | .error _ _ => false

private theorem recAliasIngressSucceededNative :
    recAliasIngressSucceeded = true := by
  native_decide

theorem recAliasIngressRun :
    recAliasIngressOutcome = .ok true recAliasIngressAfter := by
  have success := recAliasIngressSucceededNative
  unfold recAliasIngressSucceeded at success
  unfold recAliasIngressAfter
  generalize houtcome : recAliasIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def recAliasUniverse : KUniv .anon := KUniv.mkParam 0 ()
def recAliasSort : KExpr .anon := KExpr.mkSort recAliasUniverse
def recAliasTypeConcrete : KExpr .anon :=
  KExpr.mkAll () () recAliasSort recAliasSort
def recAliasValueConcrete : KExpr .anon :=
  KExpr.mkLam () () recAliasSort (KExpr.mkVar 0 ())

def recAliasConcrete : KConst .anon :=
  .defn () () .defn .safe .abbrev 1 recAliasTypeConcrete
    recAliasValueConcrete () recAliasId

private theorem recAliasLoadedNative :
    recAliasIngressAfter.get? recAliasId = some recAliasConcrete := by
  native_decide

theorem recAliasLoaded :
    recAliasIngressAfter.get? recAliasId = some recAliasConcrete :=
  recAliasLoadedNative

def familyIngressOutcome :=
  ingressAnonBlockWithTrace ixonEnv familyBlockConstant familyBlockAddress
    recAliasIngressAfter

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
    familyBlockConstant familyBlockAddress recAliasIngressAfter
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

private theorem recAliasStillLoadedNative :
    checkerInitial.env.get? recAliasId = some recAliasConcrete := by
  native_decide

theorem recAliasStillLoaded :
    checkerInitial.env.get? recAliasId = some recAliasConcrete :=
  recAliasStillLoadedNative

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
  if address == recAliasId.addr then some ``RecAlias
  else if address == familyId.addr then some ``AliasRec
  else if address == mkId.addr then some ``AliasRec.mk
  else none

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

private theorem familyShapeNative :
    familyConcrete.IsCertifiedSingletonFamily aliasRecRawDecl generation
      constructorIds := by
  native_decide

theorem familyShape :
    familyConcrete.IsCertifiedSingletonFamily aliasRecRawDecl generation
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
    mkConcrete.IsCertifiedSingletonConstructor aliasRecRawDecl familyId 0
      mkSource := by
  native_decide

theorem mkShape :
    mkConcrete.IsCertifiedSingletonConstructor aliasRecRawDecl familyId 0
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

private theorem mkSourceNameNative : mkSource.name = ``AliasRec.mk := by
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
  if id == recAliasId then some recAliasConcrete
  else if id == familyId then some familyConcrete
  else if id == mkId then some mkConcrete
  else none

def blockCatalog : BlockCatalog := fun id => familyIngressAfter.getBlock? id

private theorem catalogRecAliasNative :
    catalog recAliasId = some recAliasConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_recAlias : catalog recAliasId = some recAliasConcrete :=
  catalogRecAliasNative

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

private theorem recAliasTranslationsNative :
    translateCore? VEnv.empty nameOf recAliasTypeConcrete =
        some recAliasValue.type ∧
      translateCore? VEnv.empty nameOf recAliasValueConcrete =
        some recAliasValue.value := by
  native_decide

private theorem recAliasTypeRaw :
    RawExprRel (uvars := recAliasConcrete.lvls.toNat) VEnv.empty nameOf
      RawProjRel.none [] recAliasTypeConcrete
      recAliasValue.type :=
  translateCore?_raw recAliasTranslationsNative.1

private theorem recAliasValueRaw :
    RawExprRel (uvars := recAliasConcrete.lvls.toNat) VEnv.empty nameOf
      RawProjRel.none [] recAliasValueConcrete
      recAliasValue.value :=
  translateCore?_raw recAliasTranslationsNative.2

theorem recAliasRaw : RawDeclRel VEnv.empty nameOf RawProjRel.none
    recAliasId recAliasConcrete (.def recAliasValue) := by
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
  obtain ⟨name, constant, _hname, hlookup⟩ :=
    raw.reference_resolved href
  simp [VEnv.empty] at hlookup

theorem recAliasClosed : CatalogClosed catalog recAliasConcrete := by
  intro id href
  change recAliasTypeConcrete.References id ∨
    recAliasValueConcrete.References id ∨ recAliasId = id at href
  rcases href with href | href | href
  · exact False.elim (noReferencesFromEmpty recAliasTypeRaw id href)
  · exact False.elim (noReferencesFromEmpty recAliasValueRaw id href)
  · subst id
    exact ⟨recAliasConcrete, catalog_recAlias⟩

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
      exact ⟨recAliasConcrete, catalog_recAlias⟩
    · exact False.elim hold
  blocks := blockCatalog

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world := by
  exact TrustedCatalogLog.promote TrustedCatalogLog.empty catalog_recAlias
    recAliasRaw recAliasClosed (by simp) recAliasDeclWF

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

/-- The actual `AliasRec` ingress block extends the explicitly promoted
`RecAlias` world through the certified non-identity generation. -/
def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  interpretation.toCatalogLinkOfEntries familyIngressExecution catalogEntry
    trustedCatalog

end Ix.Tc.AliasRecFixture
