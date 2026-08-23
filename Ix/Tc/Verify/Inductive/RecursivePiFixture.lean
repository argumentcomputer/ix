import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.RecursivePiCertificate

/-!
# Production recursive-Pi fixture

This fixture stores and ingresses the actual one-family shape of `Acc`. Its
constructor's recursive occurrence is beneath the telescope
`(b : α) → r b a → Acc r b`, so a successful production run exercises the
recursive-Pi positivity and generated-induction-hypothesis paths which the
direct `IndexedVec` fixture does not reach.

The first slice below fixes the compiler-shaped Ixon block, exact projected
member order, successful anonymous ingress, and successful production family
check. Semantic catalog linkage and generated-recursor admission are layered
on these exact executions rather than assumed by the fixture.
-/

namespace Ix.Tc.RecursivePiFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open RecursivePiCertificateFixture
open InductiveConcreteFixture

local instance anonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-! ## Compiler-shaped Acc family block -/

private def accApp (alpha relation index : Ixon.Expr) : Ixon.Expr :=
  .app (.app (.app (.recur 0 #[0]) alpha) relation) index

/-- `Acc.{u} : (α : Sort u) → (α → α → Prop) → α → Prop`.

Universe-table position zero is `u`; position one is `0` (Prop). -/
def familyType : Ixon.Expr :=
  .leanAll (.sort 0)
    (.leanAll (.leanAll (.var 0) (.leanAll (.var 1) (.sort 1)))
      (.leanAll (.var 1) (.sort 1)))

/-- The raw `Acc.intro` type. The recursive field is the fourth outer binder
and opens `b` plus the relation proof before reaching `Acc r b`. -/
def introType : Ixon.Expr :=
  .leanAll (.sort 0)
    (.leanAll (.leanAll (.var 0) (.leanAll (.var 1) (.sort 1)))
      (.leanAll (.var 1)
        (.leanAll
          (.leanAll (.var 2)
            (.leanAll
              (.app (.app (.var 2) (.var 0)) (.var 1))
              (accApp (.var 4) (.var 3) (.var 1))))
          (accApp (.var 3) (.var 2) (.var 1)))))

def familyIxon : Ixon.Inductive :=
  ⟨false, 1, 2, 1, familyType,
    #[⟨false, 1, 0, 2, 2, introType⟩]⟩

def familyBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc familyIxon], #[], #[], #[.var 0, .zero]⟩

def familyStored : Ixon.Env × Address :=
  storeBlockWithProjections {} familyBlockConstant

def ixonEnv : Ixon.Env := familyStored.1
def familyBlockAddress : Address := familyStored.2
def familyBlockId : KId .anon := ⟨familyBlockAddress, ()⟩
def familyId : KId .anon := ⟨indcProjAddr familyBlockAddress 0, ()⟩
def introId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 0, ()⟩
def constructorIds : Array (KId .anon) := #[introId]
def members : Array (KId .anon) := #[familyId, introId]

/-! ## Actual anonymous ingress -/

def ingressOutcome :=
  ingressAnonBlockWithTrace ixonEnv familyBlockConstant familyBlockAddress
    ({} : AnonEnv)

def ingressResult : AnonBlockIngressTrace :=
  match ingressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def ingressAfter : AnonEnv :=
  match ingressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ingressSucceeded : Bool :=
  match ingressOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ingressSucceededNative : ingressSucceeded = true := by
  native_decide

theorem ingressSucceeded_eq : ingressSucceeded = true :=
  ingressSucceededNative

theorem ingressRun :
    ingressOutcome = .ok ingressResult ingressAfter := by
  have success := ingressSucceeded_eq
  unfold ingressSucceeded at success
  unfold ingressResult ingressAfter
  generalize houtcome : ingressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def ingressExecution : AnonBlockIngressSuccessTrace ixonEnv
    familyBlockConstant familyBlockAddress {} ingressAfter ingressResult :=
  AnonBlockIngressSuccessTrace.of_run ingressRun

private theorem memberKidsNative :
    ingressResult.memberKids = #[familyId] := by
  native_decide

theorem memberKids : ingressResult.memberKids = #[familyId] :=
  memberKidsNative

private theorem entryIdsNative :
    ingressResult.allEntries.map (·.1) = members := by
  native_decide

theorem entryIds : ingressResult.allEntries.map (·.1) = members :=
  entryIdsNative

private theorem entriesUniqueNative :
    EntryKeysUnique ingressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide

theorem entriesUnique : EntryKeysUnique ingressResult.allEntries :=
  entriesUniqueNative

/-! ## Actual production family checker -/

def checkerFuel : UInt64 := 1024
def checkerMethods : Methods .anon := methodsN checkerFuel.toNat

def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon ingressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

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

/-! ## Exact converted entries -/

private theorem entriesSizeNative : ingressResult.allEntries.size = 2 := by
  native_decide

theorem entriesSize : ingressResult.allEntries.size = 2 :=
  entriesSizeNative

private theorem indexZero : 0 < ingressResult.allEntries.size := by
  rw [entriesSize]
  omega

private theorem indexOne : 1 < ingressResult.allEntries.size := by
  rw [entriesSize]
  omega

def familyConcrete : KConst .anon :=
  (ingressResult.allEntries[0]'indexZero).2

def introConcrete : KConst .anon :=
  (ingressResult.allEntries[1]'indexOne).2

private theorem familyEntryNative :
    (familyId, familyConcrete) ∈ ingressResult.allEntries := by
  have member := Array.getElem_mem indexZero
  have identifier :
      (ingressResult.allEntries[0]'indexZero).1 = familyId := by
    native_decide
  unfold familyConcrete
  rw [← identifier]
  exact member

theorem familyEntry :
    (familyId, familyConcrete) ∈ ingressResult.allEntries :=
  familyEntryNative

private theorem introEntryNative :
    (introId, introConcrete) ∈ ingressResult.allEntries := by
  have member := Array.getElem_mem indexOne
  have identifier :
      (ingressResult.allEntries[1]'indexOne).1 = introId := by
    native_decide
  unfold introConcrete
  rw [← identifier]
  exact member

theorem introEntry :
    (introId, introConcrete) ∈ ingressResult.allEntries :=
  introEntryNative

/-! ## Exact source interpretation -/

/-- Deliberate names for the two projected declarations in this block.
These finite equalities are checked directly; no address-hash injectivity is
assumed. -/
def nameOf (address : Address) : Option Lean.Name :=
  if address == familyId.addr then some ``Acc
  else if address == introId.addr then some ``Acc.intro
  else none

private theorem nameOfFamilyNative :
    nameOf familyId.addr = some ``Acc := by
  native_decide

theorem nameOf_family : nameOf familyId.addr = some ``Acc :=
  nameOfFamilyNative

private theorem nameOfIntroNative :
    nameOf introId.addr = some ``Acc.intro := by
  native_decide

theorem nameOf_intro : nameOf introId.addr = some ``Acc.intro :=
  nameOfIntroNative

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
    familyConcrete.IsCertifiedSingletonFamily accDecl generation
      constructorIds := by
  native_decide

theorem familyShape :
    familyConcrete.IsCertifiedSingletonFamily accDecl generation
      constructorIds :=
  familyShapeNative

private theorem sourceConstructorZero :
    0 < generation.block.sourceType.ctors.length := by
  native_decide

def introSource : VConstVal :=
  generation.block.sourceType.ctors[0]'sourceConstructorZero

theorem introSourceAt :
    generation.block.sourceType.ctors[0]? = some introSource := rfl

private theorem introShapeNative :
    introConcrete.IsCertifiedSingletonConstructor accDecl familyId 0
      introSource := by
  native_decide

theorem introShape :
    introConcrete.IsCertifiedSingletonConstructor accDecl familyId 0
      introSource :=
  introShapeNative

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

private theorem introTypeRawNative :
    RawExprRel (uvars := introConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] introConcrete.ty
      introSource.type := by
  apply translateCore?_raw
  native_decide

theorem introTypeRaw :
    RawExprRel (uvars := introConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] introConcrete.ty
      introSource.type :=
  introTypeRawNative

private theorem constructorCountNative :
    constructorIds.size = generation.block.sourceType.ctors.length := by
  native_decide

private theorem introSourceNameNative :
    introSource.name = ``Acc.intro := by
  native_decide

/-- The actual converted family block represents the certified `Acc`
transaction, including its recursive occurrence beneath two Pi binders. -/
def interpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf ingressResult transaction where
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
    refine ⟨introSource, introConcrete, introSourceAt, ?_, introShape, ?_,
      introTypeRaw⟩
    · simpa [constructorIds] using introEntry
    · simpa [constructorIds, introSourceNameNative] using nameOf_intro

/-! ## Immutable semantic world and exact ingress link -/

def catalog : Catalog := fun id =>
  if id == familyId then some familyConcrete
  else if id == introId then some introConcrete
  else none

def blockCatalog : BlockCatalog := fun id => ingressAfter.getBlock? id

private theorem catalogFamilyNative :
    catalog familyId = some familyConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_family : catalog familyId = some familyConcrete :=
  catalogFamilyNative

private theorem catalogIntroNative :
    catalog introId = some introConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_intro : catalog introId = some introConcrete :=
  catalogIntroNative

private theorem entryAtZeroNative :
    ingressResult.allEntries[0]'indexZero = (familyId, familyConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem entryAtZero :
    ingressResult.allEntries[0]'indexZero = (familyId, familyConcrete) :=
  entryAtZeroNative

private theorem entryAtOneNative :
    ingressResult.allEntries[1]'indexOne = (introId, introConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem entryAtOne :
    ingressResult.allEntries[1]'indexOne = (introId, introConcrete) :=
  entryAtOneNative

theorem catalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry : (id, concrete) ∈ ingressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [entriesSize] at hindex
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · rw [entryAtZero] at hget
    cases hget
    exact catalog_family
  · rw [entryAtOne] at hget
    cases hget
    exact catalog_intro

/-- Empty semantic base used only to admit the actual `Acc` ingress block. -/
def world : VerifyWorld where
  catalog := catalog
  trusted := fun _ => False
  venv := .empty
  nameOf := nameOf
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h
  blocks := blockCatalog

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world :=
  TrustedCatalogLog.empty

/-- Exact production-ingress/catalog correspondence for the certified
recursive-Pi family transaction. -/
def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  interpretation.toCatalogLinkOfEntries ingressExecution catalogEntry
    trustedCatalog

end Ix.Tc.RecursivePiFixture
