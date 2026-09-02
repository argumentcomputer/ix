import Ix.Tc.Verify.Inductive.RecursivePiAcceptance

/-!
# Production recursive-Pi recursor fixture

This module adds the compiler-shaped `Acc.rec` block to the already certified
family fixture. Its sole iota rule contains the generated induction hypothesis
under the two binders of `Acc.intro`'s recursive function field.

The family and recursor are then checked from one final anonymous ingress
environment. Thus successful comparison exercises the production recursor
generator and rule builder, not merely the Theory-side certificate.
-/

namespace Ix.Tc.RecursivePiRecursorFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open RecursivePiCertificateFixture
open RecursivePiFixture
open InductiveConcreteFixture

local instance recursorAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-! ## Compiler-shaped Acc.rec block -/

/-- Shared expression table emitted by the compiler for the canonical
`Acc.rec` type and iota RHS. References zero and one below denote the exact
family and constructor projections of `RecursivePiFixture`. -/
def recursorSharing : Array Ixon.Expr :=
  #[.app (.app (.var 4) (.var 0)) (.var 2),
    .app (.var 2) (.var 1),
    .app (.share 1) (.var 0),
    .app (.app (.var 4) (.var 1)) (.share 2),
    .leanAll (.share 0) (.share 3),
    .leanAll (.var 4) (.share 4),
    .app (.app (.var 3) (.var 0)) (.var 1),
    .ref 0 #[2],
    .app (.share 7) (.var 5),
    .app (.share 8) (.var 4),
    .app (.share 9) (.var 1),
    .leanAll (.share 6) (.share 10),
    .app (.share 7) (.var 2),
    .app (.share 12) (.var 1),
    .app (.share 13) (.var 0),
    .app (.ref 1 #[2]) (.var 5),
    .app (.share 15) (.var 4),
    .app (.share 16) (.var 2),
    .leanAll (.var 0) (.leanAll (.var 1) (.sort 0)),
    .leanAll (.share 14) (.sort 1),
    .leanAll (.var 1) (.share 19),
    .leanAll (.var 3) (.share 11),
    .app (.share 17) (.var 1),
    .app (.app (.var 3) (.var 2)) (.share 22),
    .leanAll (.share 5) (.share 23),
    .leanAll (.share 21) (.share 24),
    .leanAll (.var 2) (.share 25)]

def recursorType : Ixon.Expr :=
  .leanAll (.sort 2)
    (.leanAll (.share 18)
      (.leanAll (.share 20)
        (.leanAll (.share 26)
          (.leanAll (.var 3)
            (.leanAll
              (.app
                (.app (.app (.share 7) (.var 4)) (.var 3))
                (.var 0))
              (.app (.app (.var 3) (.var 1)) (.var 0)))))))

/-- Canonical recursive-Pi iota RHS. The innermost two lambdas are the
arguments of the generated induction hypothesis, and the recursive call
targets `h y hy`. -/
def introRuleRhs : Ixon.Expr :=
  .leanLam (.sort 2)
    (.leanLam (.share 18)
      (.leanLam (.share 20)
        (.leanLam (.share 26)
          (.leanLam (.var 3)
            (.leanLam
              (.leanAll (.var 4)
                (.leanAll
                  (.app (.app (.var 4) (.var 0)) (.var 1))
                  (.app
                    (.app (.app (.share 7) (.var 6)) (.var 5))
                    (.var 1))))
              (.app (.share 2)
                (.leanLam (.var 5)
                  (.leanLam
                    (.app (.app (.var 5) (.var 0)) (.var 2))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app (.recur 0 #[1, 2]) (.var 7))
                              (.var 6))
                            (.var 5))
                          (.var 4))
                        (.var 1))
                      (.share 2))))))))))

def recursorIxon : Ixon.Recursor :=
  ⟨false, false, 2, 2, 1, 1, 1, recursorType,
    #[⟨2, introRuleRhs⟩]⟩

def recursorBlockConstant : Ixon.Constant :=
  ⟨.muts #[.recr recursorIxon], recursorSharing,
    #[familyId.addr, introId.addr],
    #[.zero, .var 0, .var 1]⟩

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
    recursorBlockAddress ingressAfter

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
    recursorBlockConstant recursorBlockAddress ingressAfter
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
    recFuel := RecursivePiFixture.checkerFuel
    fuelBudget := RecursivePiFixture.checkerFuel }

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

/-- The production checker builds the canonical recursive-Pi artifacts and
accepts the independently ingressed `Acc.rec` declaration and iota rule. -/
theorem recursorKernelRun :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter := by
  have success := recursorKernelSucceeded_eq
  unfold recursorKernelSucceeded at success
  unfold recursorKernelAfter
  generalize houtcome : recursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [recursorKernelOutcome]

/-! ## Certified source interpretation -/

/-- Deliberate names for the complete three-declaration fixture. The fallback
is the already checked family/constructor interpretation. -/
def nameOf (address : Address) : Option Lean.Name :=
  if address == recursorId.addr then some ``Acc.rec
  else RecursivePiFixture.nameOf address

private theorem nameOfRecursorNative :
    nameOf recursorId.addr = some ``Acc.rec := by
  native_decide

theorem nameOf_recursor : nameOf recursorId.addr = some ``Acc.rec :=
  nameOfRecursorNative

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
    RawExprRel (uvars := RecursivePiFixture.familyConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      RecursivePiFixture.familyConcrete.ty
      generation.block.sourceType.type := by
  apply translateCore?_raw
  native_decide

theorem familyTypeRaw :
    RawExprRel (uvars := RecursivePiFixture.familyConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      RecursivePiFixture.familyConcrete.ty
      generation.block.sourceType.type :=
  familyTypeRawNative

private theorem introTypeRawNative :
    RawExprRel (uvars := RecursivePiFixture.introConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      RecursivePiFixture.introConcrete.ty
      RecursivePiFixture.introSource.type := by
  apply translateCore?_raw
  native_decide

theorem introTypeRaw :
    RawExprRel (uvars := RecursivePiFixture.introConcrete.lvls.toNat)
      finalEnv nameOf RawProjRel.none []
      RecursivePiFixture.introConcrete.ty
      RecursivePiFixture.introSource.type :=
  introTypeRawNative

private theorem constructorCountNative :
    constructorIds.size = generation.block.sourceType.ctors.length := by
  native_decide

private theorem introSourceNameNative :
    RecursivePiFixture.introSource.name = ``Acc.intro := by
  native_decide

/-- Family interpretation rebuilt over the complete name map. This keeps the
immutable catalog fixed before either physical block is admitted. -/
def familyInterpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf RecursivePiFixture.ingressResult transaction where
  familyId := familyId
  constructorIds := constructorIds
  memberKids := RecursivePiFixture.memberKids
  entryIds := by
    simpa [RecursivePiFixture.members, constructorIds] using
      RecursivePiFixture.entryIds
  entriesUnique := RecursivePiFixture.entriesUnique
  constructorCount := constructorCountNative
  familyConcrete := RecursivePiFixture.familyConcrete
  familyEntry := RecursivePiFixture.familyEntry
  familyShape := RecursivePiFixture.familyShape
  familyName := nameOf_family
  familyType := familyTypeRaw
  constructor := by
    intro index hindex
    change index < 1 at hindex
    have : index = 0 := by omega
    subst index
    refine ⟨RecursivePiFixture.introSource,
      RecursivePiFixture.introConcrete,
      RecursivePiFixture.introSourceAt, ?_, RecursivePiFixture.introShape,
      ?_, introTypeRaw⟩
    · simpa [constructorIds] using RecursivePiFixture.introEntry
    · simpa [constructorIds, introSourceNameNative] using nameOf_intro

/-! ## One immutable catalog for both blocks -/

def catalog : Catalog := fun id =>
  if id == familyId then some RecursivePiFixture.familyConcrete
  else if id == introId then some RecursivePiFixture.introConcrete
  else if id == recursorId then some recursorConcrete
  else none

def blockCatalog : BlockCatalog := fun id => recursorIngressAfter.getBlock? id

private theorem catalogFamilyNative :
    catalog familyId = some RecursivePiFixture.familyConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_family :
    catalog familyId = some RecursivePiFixture.familyConcrete :=
  catalogFamilyNative

private theorem catalogIntroNative :
    catalog introId = some RecursivePiFixture.introConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_intro :
    catalog introId = some RecursivePiFixture.introConcrete :=
  catalogIntroNative

private theorem catalogRecursorNative :
    catalog recursorId = some recursorConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_recursor : catalog recursorId = some recursorConcrete :=
  catalogRecursorNative

theorem familyCatalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry :
      (id, concrete) ∈ RecursivePiFixture.ingressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [RecursivePiFixture.entriesSize] at hindex
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · rw [RecursivePiFixture.entryAtZero] at hget
    cases hget
    exact catalog_family
  · rw [RecursivePiFixture.entryAtOne] at hget
    cases hget
    exact catalog_intro

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

def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  familyInterpretation.toCatalogLinkOfEntries
    RecursivePiFixture.ingressExecution familyCatalogEntry trustedCatalog

/-! ## Exact generated recursor semantics -/

private theorem recursorShapeNative :
    recursorConcrete.IsCertifiedSingletonRecursor accDecl generation
      constructorIds := by
  native_decide

theorem recursorShape :
    recursorConcrete.IsCertifiedSingletonRecursor accDecl generation
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

def introNormalized : VInductDecl.NormalizedCtor :=
  generation.block.ctorPairs[0]'generationCtorPairZero

theorem introNormalizedAt :
    generation.block.ctorPairs[0]? = some introNormalized := rfl

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

theorem recursorTypeRawConcrete :
    RawExprRel (uvars := recursorConcrete.lvls.toNat) finalEnv nameOf
      RawProjRel.none [] recursorConcrete.ty generation.recursor.type := by
  simpa only [recursorShape.levels] using recursorTypeRaw

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

private theorem introRuleRawNative :
    RawExprRel
      (uvars := (generation.rule 0 introNormalized).uvars)
      finalEnv nameOf RawProjRel.none [] concreteRule.rhs
      (generation.rule 0 introNormalized).rhs := by
  apply translateCore?_raw
  native_decide

theorem introRuleRaw :
    RawExprRel
      (uvars := (generation.rule 0 introNormalized).uvars)
      finalEnv nameOf RawProjRel.none [] concreteRule.rhs
      (generation.rule 0 introNormalized).rhs :=
  introRuleRawNative

private theorem introRuleFieldsNative :
    concreteRule.fields.toNat =
      (introNormalized.fieldsR accDecl.uvars accDecl.nparams).length := by
  native_decide

theorem introRuleFields :
    concreteRule.fields.toNat =
      (introNormalized.fieldsR accDecl.uvars accDecl.nparams).length :=
  introRuleFieldsNative

private theorem introRuleBinderCoreNative :
    concreteRule.rhs.binderCore = true := by
  native_decide

private theorem introRuleScopedNative :
    concreteRule.rhs.Scoped 0
      (generation.rule 0 introNormalized).uvars := by
  native_decide

private theorem introRuleSizeBoundNative :
    concreteRule.rhs.size < UInt64.size := by
  native_decide

def introRulePre : PreTrKExprS finalEnv
    (generation.rule 0 introNormalized).uvars nameOf RawProjRel.none []
    concreteRule.rhs (generation.rule 0 introNormalized).rhs :=
  introRuleRaw.toPreBinderCore_of_scoped introRuleBinderCoreNative
    introRuleScopedNative introRuleSizeBoundNative

theorem introGeneratedRuleMem :
    generation.rule 0 introNormalized ∈ generation.generatedRules :=
  List.mem_of_getElem?
    (CertifiedSingletonGeneration.generatedRuleAt generation
      introNormalizedAt)

theorem introGeneratedRuleWF :
    (generation.rule 0 introNormalized).WF finalEnv :=
  transaction.facts.afterWF.ordered.defEqWF
    (transaction.facts.ruleMem introGeneratedRuleMem)

theorem introRuleTyped : TrKExprS finalEnv
    (generation.rule 0 introNormalized).uvars nameOf RawProjRel.none []
    concreteRule.rhs (generation.rule 0 introNormalized).rhs := by
  exact introRulePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) introRuleBinderCoreNative
    ⟨_, introGeneratedRuleWF.2⟩

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
    exact ⟨concreteRule, introNormalized, concreteRule_ruleAt,
      introNormalizedAt, introRuleFields, introRuleRaw, introRuleTyped⟩

def recursorLink : SingletonRecursorCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction familyLink :=
  recursorInterpretation.toCatalogLinkOfEntry recursorIngressExecution
    catalog_recursor trustedCatalog

end Ix.Tc.RecursivePiRecursorFixture
