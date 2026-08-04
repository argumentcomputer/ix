import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.IndexedRecursiveOracle

/-!
# Concrete parameterized, indexed, recursive fixture

This module connects the certified Lean4Lean `IndexedVec` generation to the
actual anonymous Ixon layout.  `Nat`, the family/constructor block, and the
separate recursor block are ingressed in dependency order.  Later sections
retain the exact converted entries so the production checker and atomic
admission theorem consume the same physical declarations.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture
open InductiveConcreteFixture

local instance anonKIdDecidableEq : DecidableEq (KId .anon) := fun left right =>
  if h : left == right then
    .isTrue (eq_of_beq h)
  else
    .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-! ## Compiler-shaped Ixon blocks -/

/-- Ambient `Nat`, loaded solely as the dependency of `IndexedVec`. -/
def natIxon : Ixon.Inductive :=
  ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
      ⟨false, 0, 1, 0, 1, .all (.recur 0 #[]) (.recur 0 #[])⟩]⟩

def natBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc natIxon], #[], #[], #[.succ .zero]⟩

def natStored : Ixon.Env × Address :=
  storeBlockWithProjections {} natBlockConstant

def natIxonEnv : Ixon.Env := natStored.1
def natBlockAddress : Address := natStored.2
def natId : KId .anon := ⟨indcProjAddr natBlockAddress 0, ()⟩
def zeroId : KId .anon := ⟨ctorProjAddr natBlockAddress 0 0, ()⟩
def succId : KId .anon := ⟨ctorProjAddr natBlockAddress 0 1, ()⟩

/-- `IndexedVec.{u} : Sort (u+1) → Nat → Sort (u+1)`.  Universe table
position 0 is `u+1`; position 1 is `u`. -/
def familyType : Ixon.Expr :=
  .all (.sort 0) (.all (.ref 0 #[]) (.sort 0))

def nilType : Ixon.Expr :=
  .all (.sort 0)
    (.app (.app (.recur 0 #[1]) (.var 0)) (.ref 1 #[]))

def consType : Ixon.Expr :=
  .all (.sort 0)
    (.all (.ref 0 #[])
      (.all (.var 1)
        (.all
          (.app (.app (.recur 0 #[1]) (.var 2)) (.var 1))
          (.app
            (.app (.recur 0 #[1]) (.var 3))
            (.app (.ref 2 #[]) (.var 2))))))

def familyIxon : Ixon.Inductive :=
  ⟨false, 1, 1, 1, familyType,
    #[⟨false, 1, 0, 1, 0, nilType⟩,
      ⟨false, 1, 1, 1, 3, consType⟩]⟩

def familyBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc familyIxon], #[],
    #[natId.addr, zeroId.addr, succId.addr],
    #[.succ (.var 0), .var 0]⟩

def familyStored : Ixon.Env × Address :=
  storeBlockWithProjections natIxonEnv familyBlockConstant

def familyIxonEnv : Ixon.Env := familyStored.1
def familyBlockAddress : Address := familyStored.2
def familyId : KId .anon := ⟨indcProjAddr familyBlockAddress 0, ()⟩
def nilId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 0, ()⟩
def consId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 1, ()⟩
def constructorIds : Array (KId .anon) := #[nilId, consId]

/-! ### Canonical recursor syntax -/

private def natRef : Ixon.Expr := .ref 3 #[]
private def zeroRef : Ixon.Expr := .ref 4 #[]
private def succRef : Ixon.Expr := .ref 5 #[]

private def familyRef (alpha index : Ixon.Expr) : Ixon.Expr :=
  .app (.app (.ref 0 #[1]) alpha) index

private def nilRef (alpha : Ixon.Expr) : Ixon.Expr :=
  .app (.ref 1 #[1]) alpha

private def consRef (alpha index head tail : Ixon.Expr) : Ixon.Expr :=
  .app (.app (.app (.app (.ref 2 #[1]) alpha) index) head) tail

private def motiveType : Ixon.Expr :=
  .all natRef
    (.all (familyRef (.var 1) (.var 0)) (.sort 0))

private def nilMinorType : Ixon.Expr :=
  .app (.app (.var 0) zeroRef) (nilRef (.var 1))

private def consMinorType : Ixon.Expr :=
  .all natRef
    (.all (.var 3)
      (.all (familyRef (.var 4) (.var 1))
        (.all (.app (.app (.var 4) (.var 2)) (.var 0))
          (.app
            (.app (.var 5) (.app succRef (.var 3)))
            (consRef (.var 6) (.var 3) (.var 2) (.var 1))))))

def recursorType : Ixon.Expr :=
  .all (.sort 2)
    (.all motiveType
      (.all nilMinorType
        (.all consMinorType
          (.all natRef
            (.all (familyRef (.var 4) (.var 0))
              (.app (.app (.var 4) (.var 1)) (.var 0)))))))

def nilRuleRhs : Ixon.Expr :=
  .lam (.sort 2)
    (.lam motiveType
      (.lam nilMinorType
        (.lam consMinorType (.var 1))))

def consRuleRhs : Ixon.Expr :=
  .lam (.sort 2)
    (.lam motiveType
      (.lam nilMinorType
        (.lam consMinorType
          (.lam natRef
            (.lam (.var 4)
              (.lam (familyRef (.var 5) (.var 1))
                (.app
                  (.app
                    (.app
                      (.app (.var 3) (.var 2))
                      (.var 1))
                    (.var 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app (.recur 0 #[0, 1]) (.var 6))
                            (.var 5))
                          (.var 4))
                        (.var 3))
                      (.var 2))
                    (.var 0)))))))))

def recursorIxon : Ixon.Recursor :=
  ⟨false, false, 2, 1, 1, 1, 2, recursorType,
    #[⟨0, nilRuleRhs⟩, ⟨3, consRuleRhs⟩]⟩

def recursorBlockConstant : Ixon.Constant :=
  ⟨.muts #[.recr recursorIxon], #[],
    #[familyId.addr, nilId.addr, consId.addr,
      natId.addr, zeroId.addr, succId.addr],
    #[.var 0, .var 1, .succ (.var 1)]⟩

def recursorStored : Ixon.Env × Address :=
  storeBlockWithProjections familyIxonEnv recursorBlockConstant

def recursorIxonEnv : Ixon.Env := recursorStored.1
def recursorBlockAddress : Address := recursorStored.2
def recursorId : KId .anon := ⟨recrProjAddr recursorBlockAddress 0, ()⟩

/-! ## Actual dependency-ordered ingress -/

def natIngressOutcome :=
  ingressAnonBlockWithTrace recursorIxonEnv natBlockConstant natBlockAddress
    ({} : AnonEnv)

def natIngressResult : AnonBlockIngressTrace :=
  match natIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def natIngressAfter : AnonEnv :=
  match natIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def natIngressSucceeded : Bool :=
  match natIngressOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem natIngressSucceededNative : natIngressSucceeded = true := by
  native_decide

theorem natIngressSucceeded_eq : natIngressSucceeded = true :=
  natIngressSucceededNative

theorem natIngressRun :
    natIngressOutcome = .ok natIngressResult natIngressAfter := by
  have success := natIngressSucceeded_eq
  unfold natIngressSucceeded at success
  unfold natIngressResult natIngressAfter
  generalize houtcome : natIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def natIngressExecution : AnonBlockIngressSuccessTrace recursorIxonEnv
    natBlockConstant natBlockAddress {} natIngressAfter natIngressResult :=
  AnonBlockIngressSuccessTrace.of_run natIngressRun

def familyIngressOutcome :=
  ingressAnonBlockWithTrace recursorIxonEnv familyBlockConstant
    familyBlockAddress natIngressAfter

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

theorem familyIngressSucceeded_eq : familyIngressSucceeded = true :=
  familyIngressSucceededNative

theorem familyIngressRun :
    familyIngressOutcome = .ok familyIngressResult familyIngressAfter := by
  have success := familyIngressSucceeded_eq
  unfold familyIngressSucceeded at success
  unfold familyIngressResult familyIngressAfter
  generalize houtcome : familyIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def familyIngressExecution : AnonBlockIngressSuccessTrace recursorIxonEnv
    familyBlockConstant familyBlockAddress natIngressAfter familyIngressAfter
      familyIngressResult :=
  AnonBlockIngressSuccessTrace.of_run familyIngressRun

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

/-! ## Computed physical layout -/

private theorem natMemberKidsNative :
    natIngressResult.memberKids = #[natId] := by native_decide
theorem natMemberKids : natIngressResult.memberKids = #[natId] :=
  natMemberKidsNative

private theorem natEntryIdsNative :
    natIngressResult.allEntries.map (·.1) = #[natId, zeroId, succId] := by
  native_decide
theorem natEntryIds :
    natIngressResult.allEntries.map (·.1) = #[natId, zeroId, succId] :=
  natEntryIdsNative

private theorem natEntriesUniqueNative :
    EntryKeysUnique natIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide
theorem natEntriesUnique : EntryKeysUnique natIngressResult.allEntries :=
  natEntriesUniqueNative

private theorem familyMemberKidsNative :
    familyIngressResult.memberKids = #[familyId] := by native_decide
theorem familyMemberKids : familyIngressResult.memberKids = #[familyId] :=
  familyMemberKidsNative

private theorem familyEntryIdsNative :
    familyIngressResult.allEntries.map (·.1) =
      #[familyId] ++ constructorIds := by native_decide
theorem familyEntryIds :
    familyIngressResult.allEntries.map (·.1) =
      #[familyId] ++ constructorIds := familyEntryIdsNative

private theorem familyEntriesUniqueNative :
    EntryKeysUnique familyIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide
theorem familyEntriesUnique :
    EntryKeysUnique familyIngressResult.allEntries := familyEntriesUniqueNative

private theorem recursorMemberKidsNative :
    recursorIngressResult.memberKids = #[recursorId] := by native_decide
theorem recursorMemberKids :
    recursorIngressResult.memberKids = #[recursorId] :=
  recursorMemberKidsNative

private theorem recursorEntryIdsNative :
    recursorIngressResult.allEntries.map (·.1) = #[recursorId] := by
  native_decide
theorem recursorEntryIds :
    recursorIngressResult.allEntries.map (·.1) = #[recursorId] :=
  recursorEntryIdsNative

private theorem recursorEntriesUniqueNative :
    EntryKeysUnique recursorIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide
theorem recursorEntriesUnique :
    EntryKeysUnique recursorIngressResult.allEntries :=
  recursorEntriesUniqueNative

/-! ## Retained converted declarations -/

private theorem natEntriesSizeNative : natIngressResult.allEntries.size = 3 := by
  native_decide
theorem natEntriesSize : natIngressResult.allEntries.size = 3 :=
  natEntriesSizeNative

private theorem natIndexZero : 0 < natIngressResult.allEntries.size := by
  rw [natEntriesSize]
  omega
private theorem natIndexOne : 1 < natIngressResult.allEntries.size := by
  rw [natEntriesSize]
  omega
private theorem natIndexTwo : 2 < natIngressResult.allEntries.size := by
  rw [natEntriesSize]
  omega

def natConcrete : KConst .anon :=
  (natIngressResult.allEntries[0]'natIndexZero).2
def zeroConcrete : KConst .anon :=
  (natIngressResult.allEntries[1]'natIndexOne).2
def succConcrete : KConst .anon :=
  (natIngressResult.allEntries[2]'natIndexTwo).2

private theorem natEntryNative :
    (natId, natConcrete) ∈ natIngressResult.allEntries := by
  have member := Array.getElem_mem natIndexZero
  have identifier :
      (natIngressResult.allEntries[0]'natIndexZero).1 = natId := by
    native_decide
  unfold natConcrete
  rw [← identifier]
  exact member
theorem natEntry : (natId, natConcrete) ∈ natIngressResult.allEntries :=
  natEntryNative

private theorem zeroEntryNative :
    (zeroId, zeroConcrete) ∈ natIngressResult.allEntries := by
  have member := Array.getElem_mem natIndexOne
  have identifier :
      (natIngressResult.allEntries[1]'natIndexOne).1 = zeroId := by
    native_decide
  unfold zeroConcrete
  rw [← identifier]
  exact member
theorem zeroEntry : (zeroId, zeroConcrete) ∈ natIngressResult.allEntries :=
  zeroEntryNative

private theorem succEntryNative :
    (succId, succConcrete) ∈ natIngressResult.allEntries := by
  have member := Array.getElem_mem natIndexTwo
  have identifier :
      (natIngressResult.allEntries[2]'natIndexTwo).1 = succId := by
    native_decide
  unfold succConcrete
  rw [← identifier]
  exact member
theorem succEntry : (succId, succConcrete) ∈ natIngressResult.allEntries :=
  succEntryNative

private theorem familyEntriesSizeNative :
    familyIngressResult.allEntries.size = 3 := by native_decide
theorem familyEntriesSize : familyIngressResult.allEntries.size = 3 :=
  familyEntriesSizeNative

private theorem familyIndexZero :
    0 < familyIngressResult.allEntries.size := by
  rw [familyEntriesSize]
  omega
private theorem familyIndexOne :
    1 < familyIngressResult.allEntries.size := by
  rw [familyEntriesSize]
  omega
private theorem familyIndexTwo :
    2 < familyIngressResult.allEntries.size := by
  rw [familyEntriesSize]
  omega

def familyConcrete : KConst .anon :=
  (familyIngressResult.allEntries[0]'familyIndexZero).2
def nilConcrete : KConst .anon :=
  (familyIngressResult.allEntries[1]'familyIndexOne).2
def consConcrete : KConst .anon :=
  (familyIngressResult.allEntries[2]'familyIndexTwo).2

private theorem familyEntryNative :
    (familyId, familyConcrete) ∈ familyIngressResult.allEntries := by
  have member := Array.getElem_mem familyIndexZero
  have identifier :
      (familyIngressResult.allEntries[0]'familyIndexZero).1 = familyId := by
    native_decide
  unfold familyConcrete
  rw [← identifier]
  exact member
theorem familyEntry :
    (familyId, familyConcrete) ∈ familyIngressResult.allEntries :=
  familyEntryNative

private theorem nilEntryNative :
    (nilId, nilConcrete) ∈ familyIngressResult.allEntries := by
  have member := Array.getElem_mem familyIndexOne
  have identifier :
      (familyIngressResult.allEntries[1]'familyIndexOne).1 = nilId := by
    native_decide
  unfold nilConcrete
  rw [← identifier]
  exact member
theorem nilEntry :
    (nilId, nilConcrete) ∈ familyIngressResult.allEntries := nilEntryNative

private theorem consEntryNative :
    (consId, consConcrete) ∈ familyIngressResult.allEntries := by
  have member := Array.getElem_mem familyIndexTwo
  have identifier :
      (familyIngressResult.allEntries[2]'familyIndexTwo).1 = consId := by
    native_decide
  unfold consConcrete
  rw [← identifier]
  exact member
theorem consEntry :
    (consId, consConcrete) ∈ familyIngressResult.allEntries := consEntryNative

private theorem recursorEntriesSizeNative :
    recursorIngressResult.allEntries.size = 1 := by native_decide
theorem recursorEntriesSize : recursorIngressResult.allEntries.size = 1 :=
  recursorEntriesSizeNative

private theorem recursorIndexZero :
    0 < recursorIngressResult.allEntries.size := by
  rw [recursorEntriesSize]
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

/-! ## Exact source interpretation -/

/-- Deliberate address/name interpretation for the dependency and the four
new declarations.  Every relevant projected address is checked concretely;
no content-hash injectivity theorem is assumed. -/
def nameOf (address : Address) : Option Lean.Name :=
  if address == recursorId.addr then some ``IndexedVec.rec
  else if address == familyId.addr then some ``IndexedVec
  else if address == nilId.addr then some ``IndexedVec.nil
  else if address == consId.addr then some ``IndexedVec.cons
  else if address == natId.addr then some ``Nat
  else if address == zeroId.addr then some ``Nat.zero
  else if address == succId.addr then some ``Nat.succ
  else none

private theorem nameOfRecursorNative :
    nameOf recursorId.addr = some ``IndexedVec.rec := by native_decide
theorem nameOf_recursor : nameOf recursorId.addr = some ``IndexedVec.rec :=
  nameOfRecursorNative

private theorem nameOfFamilyNative :
    nameOf familyId.addr = some ``IndexedVec := by native_decide
theorem nameOf_family : nameOf familyId.addr = some ``IndexedVec :=
  nameOfFamilyNative

private theorem nameOfNilNative :
    nameOf nilId.addr = some ``IndexedVec.nil := by native_decide
theorem nameOf_nil : nameOf nilId.addr = some ``IndexedVec.nil :=
  nameOfNilNative

private theorem nameOfConsNative :
    nameOf consId.addr = some ``IndexedVec.cons := by native_decide
theorem nameOf_cons : nameOf consId.addr = some ``IndexedVec.cons :=
  nameOfConsNative

private theorem nameOfNatNative : nameOf natId.addr = some ``Nat := by
  native_decide
theorem nameOf_nat : nameOf natId.addr = some ``Nat := nameOfNatNative

private theorem nameOfZeroNative :
    nameOf zeroId.addr = some ``Nat.zero := by native_decide
theorem nameOf_zero : nameOf zeroId.addr = some ``Nat.zero := nameOfZeroNative

private theorem nameOfSuccNative :
    nameOf succId.addr = some ``Nat.succ := by native_decide
theorem nameOf_succ : nameOf succId.addr = some ``Nat.succ := nameOfSuccNative

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

/-! ### Ambient Nat transaction -/

def natCertificate : natDecl.GenerationCertificate VEnv.empty where
  generation := natChecked.identityGeneration
  wf := (natChecked.wf_of_decl natDecl_wf).identityGeneration .empty

theorem natTheorySuccess :
    VEnv.empty.addInductCertified natCertificate = some natFinalEnv := rfl

def natTransaction : CertifiedGenerationTransaction natDecl VEnv.empty
    natFinalEnv where
  certificate := natCertificate
  success := natTheorySuccess
  beforeWF := ⟨[], .empty⟩

private abbrev natGeneration := natTransaction.certificate.generation
def natConstructorIds : Array (KId .anon) := #[zeroId, succId]

private theorem natFamilyShapeNative :
    natConcrete.IsCertifiedSingletonFamily natDecl natGeneration
      natConstructorIds := by native_decide
theorem natFamilyShape :
    natConcrete.IsCertifiedSingletonFamily natDecl natGeneration
      natConstructorIds := natFamilyShapeNative

private theorem natSourceConstructorZero :
    0 < natGeneration.block.sourceType.ctors.length := by native_decide
private theorem natSourceConstructorOne :
    1 < natGeneration.block.sourceType.ctors.length := by native_decide

def zeroSource : VConstVal :=
  natGeneration.block.sourceType.ctors[0]'natSourceConstructorZero
def succSource : VConstVal :=
  natGeneration.block.sourceType.ctors[1]'natSourceConstructorOne

theorem zeroSourceAt :
    natGeneration.block.sourceType.ctors[0]? = some zeroSource := rfl
theorem succSourceAt :
    natGeneration.block.sourceType.ctors[1]? = some succSource := rfl

private theorem zeroShapeNative :
    zeroConcrete.IsCertifiedSingletonConstructor natDecl natId 0 zeroSource := by
  native_decide
theorem zeroShape :
    zeroConcrete.IsCertifiedSingletonConstructor natDecl natId 0 zeroSource :=
  zeroShapeNative

private theorem succShapeNative :
    succConcrete.IsCertifiedSingletonConstructor natDecl natId 1 succSource := by
  native_decide
theorem succShape :
    succConcrete.IsCertifiedSingletonConstructor natDecl natId 1 succSource :=
  succShapeNative

private theorem natTypeRawNative :
    RawExprRel (uvars := natConcrete.lvls.toNat) natFinalEnv nameOf
      RawProjRel.none [] natConcrete.ty
      natGeneration.block.sourceType.type := by
  apply translateCore?_raw
  native_decide
theorem natTypeRaw :
    RawExprRel (uvars := natConcrete.lvls.toNat) natFinalEnv nameOf
      RawProjRel.none [] natConcrete.ty
      natGeneration.block.sourceType.type := natTypeRawNative

private theorem zeroTypeRawNative :
    RawExprRel (uvars := zeroConcrete.lvls.toNat) natFinalEnv nameOf
      RawProjRel.none [] zeroConcrete.ty
      zeroSource.type := by
  apply translateCore?_raw
  native_decide
theorem zeroTypeRaw :
    RawExprRel (uvars := zeroConcrete.lvls.toNat) natFinalEnv nameOf
      RawProjRel.none [] zeroConcrete.ty
      zeroSource.type := zeroTypeRawNative

private theorem succTypeRawNative :
    RawExprRel (uvars := succConcrete.lvls.toNat) natFinalEnv nameOf
      RawProjRel.none [] succConcrete.ty
      succSource.type := by
  apply translateCore?_raw
  native_decide
theorem succTypeRaw :
    RawExprRel (uvars := succConcrete.lvls.toNat) natFinalEnv nameOf
      RawProjRel.none [] succConcrete.ty
      succSource.type := succTypeRawNative

private theorem natConstructorCountNative :
    natConstructorIds.size = natGeneration.block.sourceType.ctors.length := by
  native_decide

private theorem zeroSourceNameNative : zeroSource.name = ``Nat.zero := by
  native_decide

private theorem succSourceNameNative : succSource.name = ``Nat.succ := by
  native_decide

def natInterpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf natIngressResult natTransaction where
  familyId := natId
  constructorIds := natConstructorIds
  memberKids := natMemberKids
  entryIds := by simpa [natConstructorIds] using natEntryIds
  entriesUnique := natEntriesUnique
  constructorCount := natConstructorCountNative
  familyConcrete := natConcrete
  familyEntry := natEntry
  familyShape := natFamilyShape
  familyName := nameOf_nat
  familyType := natTypeRaw
  constructor := by
    intro index hindex
    change index < 2 at hindex
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · refine ⟨zeroSource, zeroConcrete, zeroSourceAt, ?_, zeroShape, ?_,
        zeroTypeRaw⟩
      · simpa [natConstructorIds] using zeroEntry
      · simpa [natConstructorIds, zeroSourceNameNative] using nameOf_zero
    · refine ⟨succSource, succConcrete, succSourceAt, ?_, succShape, ?_,
        succTypeRaw⟩
      · simpa [natConstructorIds] using succEntry
      · simpa [natConstructorIds, succSourceNameNative] using nameOf_succ

private theorem familyShapeNative :
    familyConcrete.IsCertifiedSingletonFamily indexedVecDecl generation
      constructorIds := by native_decide
theorem familyShape :
    familyConcrete.IsCertifiedSingletonFamily indexedVecDecl generation
      constructorIds := familyShapeNative

private theorem sourceConstructorZero :
    0 < generation.block.sourceType.ctors.length := by native_decide
private theorem sourceConstructorOne :
    1 < generation.block.sourceType.ctors.length := by native_decide

def nilSource : VConstVal :=
  generation.block.sourceType.ctors[0]'sourceConstructorZero
def consSource : VConstVal :=
  generation.block.sourceType.ctors[1]'sourceConstructorOne

theorem nilSourceAt :
    generation.block.sourceType.ctors[0]? = some nilSource := rfl
theorem consSourceAt :
    generation.block.sourceType.ctors[1]? = some consSource := rfl

private theorem nilShapeNative :
    nilConcrete.IsCertifiedSingletonConstructor indexedVecDecl familyId 0
      nilSource := by native_decide
theorem nilShape :
    nilConcrete.IsCertifiedSingletonConstructor indexedVecDecl familyId 0
      nilSource := nilShapeNative

private theorem consShapeNative :
    consConcrete.IsCertifiedSingletonConstructor indexedVecDecl familyId 1
      consSource := by native_decide
theorem consShape :
    consConcrete.IsCertifiedSingletonConstructor indexedVecDecl familyId 1
      consSource := consShapeNative

private theorem familyTypeRawNative :
    RawExprRel (uvars := familyConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] familyConcrete.ty
      generation.block.sourceType.type := by
  apply translateCore?_raw
  native_decide
theorem familyTypeRaw :
    RawExprRel (uvars := familyConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] familyConcrete.ty
      generation.block.sourceType.type := familyTypeRawNative

private theorem nilTypeRawNative :
    RawExprRel (uvars := nilConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] nilConcrete.ty
      nilSource.type := by
  apply translateCore?_raw
  native_decide
theorem nilTypeRaw :
    RawExprRel (uvars := nilConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] nilConcrete.ty
      nilSource.type := nilTypeRawNative

private theorem consTypeRawNative :
    RawExprRel (uvars := consConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] consConcrete.ty
      consSource.type := by
  apply translateCore?_raw
  native_decide
theorem consTypeRaw :
    RawExprRel (uvars := consConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] consConcrete.ty
      consSource.type := consTypeRawNative

private theorem recursorShapeNative :
    recursorConcrete.IsCertifiedSingletonRecursor indexedVecDecl generation
      constructorIds := by native_decide
theorem recursorShape :
    recursorConcrete.IsCertifiedSingletonRecursor indexedVecDecl generation
      constructorIds := recursorShapeNative

def recursorRules : Array (RecRule .anon) :=
  match recursorConcrete with
  | .recr (rules := rules) .. => rules
  | _ => #[]

private theorem recursorRulesSizeNative : recursorRules.size = 2 := by
  native_decide
theorem recursorRulesSize : recursorRules.size = 2 := recursorRulesSizeNative

def concreteRuleAt (index : Nat) : RecRule .anon := recursorRules[index]!

theorem recursorRuleAt_iff {index : Nat} {rule : RecRule .anon} :
    recursorConcrete.RecursorRuleAt index rule ↔
      recursorRules[index]? = some rule := by
  unfold KConst.RecursorRuleAt recursorRules
  cases recursorConcrete <;> simp

theorem concreteRuleAt_ruleAt (index : Nat) (hindex : index < 2) :
    recursorConcrete.RecursorRuleAt index (concreteRuleAt index) := by
  rw [recursorRuleAt_iff]
  have hposition : index < recursorRules.size := by
    rw [recursorRulesSize]
    exact hindex
  rw [Array.getElem?_eq_getElem hposition]
  congr 1
  exact (getElem!_pos recursorRules index hposition).symm

private theorem generationCtorPairZero :
    0 < generation.block.ctorPairs.length := by native_decide
private theorem generationCtorPairOne :
    1 < generation.block.ctorPairs.length := by native_decide

def nilNormalized : VInductDecl.NormalizedCtor :=
  generation.block.ctorPairs[0]'generationCtorPairZero
def consNormalized : VInductDecl.NormalizedCtor :=
  generation.block.ctorPairs[1]'generationCtorPairOne

theorem nilNormalizedAt :
    generation.block.ctorPairs[0]? = some nilNormalized := rfl
theorem consNormalizedAt :
    generation.block.ctorPairs[1]? = some consNormalized := rfl

private theorem recursorTypeRawNative :
    RawExprRel (uvars := generation.recursor.uvars) indexedVecFinalEnv nameOf
      RawProjRel.none []
      recursorConcrete.ty generation.recursor.type := by
  apply translateCore?_raw
  native_decide
theorem recursorTypeRaw :
    RawExprRel (uvars := generation.recursor.uvars) indexedVecFinalEnv nameOf
      RawProjRel.none []
      recursorConcrete.ty generation.recursor.type := recursorTypeRawNative

private theorem recursorUniverseCountNative :
    recursorConcrete.lvls.toNat = generation.recursor.uvars := by
  native_decide

theorem recursorUniverseCount :
    recursorConcrete.lvls.toNat = generation.recursor.uvars :=
  recursorUniverseCountNative

theorem recursorTypeRawConcrete :
    RawExprRel (uvars := recursorConcrete.lvls.toNat) indexedVecFinalEnv nameOf
      RawProjRel.none [] recursorConcrete.ty generation.recursor.type := by
  simpa only [recursorUniverseCount] using recursorTypeRaw

private theorem recursorTypeBinderCoreNative :
    recursorConcrete.ty.binderCore = true := by native_decide
theorem recursorTypeBinderCore : recursorConcrete.ty.binderCore = true :=
  recursorTypeBinderCoreNative

private theorem recursorTypeScopedNative :
    recursorConcrete.ty.Scoped 0 generation.recursor.uvars := by
  native_decide
theorem recursorTypeScoped :
    recursorConcrete.ty.Scoped 0 generation.recursor.uvars :=
  recursorTypeScopedNative

private theorem recursorTypeSizeBoundNative :
    recursorConcrete.ty.size < UInt64.size := by native_decide
theorem recursorTypeSizeBound :
    recursorConcrete.ty.size < UInt64.size := recursorTypeSizeBoundNative

def recursorTypePre : PreTrKExprS indexedVecFinalEnv
    generation.recursor.uvars nameOf RawProjRel.none []
    recursorConcrete.ty generation.recursor.type :=
  recursorTypeRaw.toPreBinderCore_of_scoped recursorTypeBinderCore
    recursorTypeScoped recursorTypeSizeBound

/-- The separately ingressed IndexedVec recursor type is an exact typed
translation of the canonical mixed type from the same certified transaction. -/
theorem recursorTypeTyped : TrKExprS indexedVecFinalEnv
    generation.recursor.uvars nameOf RawProjRel.none []
    recursorConcrete.ty generation.recursor.type := by
  have htype := transaction.generationEnv.recType_isType
  have htargetWF : VExpr.WF indexedVecFinalEnv generation.recursor.uvars []
      generation.recursor.type :=
    ⟨.sort htype.choose, htype.choose_spec⟩
  exact recursorTypePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) recursorTypeBinderCore
    (by simpa [KVLCtx.toCtx] using htargetWF)

private theorem nilRuleRawNative :
    RawExprRel (uvars := (generation.rule 0 nilNormalized).uvars)
      indexedVecFinalEnv nameOf RawProjRel.none []
      (concreteRuleAt 0).rhs (generation.rule 0 nilNormalized).rhs := by
  apply translateCore?_raw
  native_decide
theorem nilRuleRaw :
    RawExprRel (uvars := (generation.rule 0 nilNormalized).uvars)
      indexedVecFinalEnv nameOf RawProjRel.none []
      (concreteRuleAt 0).rhs (generation.rule 0 nilNormalized).rhs :=
  nilRuleRawNative

private theorem consRuleRawNative :
    RawExprRel (uvars := (generation.rule 1 consNormalized).uvars)
      indexedVecFinalEnv nameOf RawProjRel.none []
      (concreteRuleAt 1).rhs (generation.rule 1 consNormalized).rhs := by
  apply translateCore?_raw
  native_decide
theorem consRuleRaw :
    RawExprRel (uvars := (generation.rule 1 consNormalized).uvars)
      indexedVecFinalEnv nameOf RawProjRel.none []
      (concreteRuleAt 1).rhs (generation.rule 1 consNormalized).rhs :=
  consRuleRawNative

private theorem nilRuleFieldsNative :
    (concreteRuleAt 0).fields.toNat =
      (nilNormalized.fieldsR indexedVecDecl.uvars
        indexedVecDecl.nparams).length := by native_decide
theorem nilRuleFields :
    (concreteRuleAt 0).fields.toNat =
      (nilNormalized.fieldsR indexedVecDecl.uvars
        indexedVecDecl.nparams).length := nilRuleFieldsNative

private theorem consRuleFieldsNative :
    (concreteRuleAt 1).fields.toNat =
      (consNormalized.fieldsR indexedVecDecl.uvars
        indexedVecDecl.nparams).length := by native_decide
theorem consRuleFields :
    (concreteRuleAt 1).fields.toNat =
      (consNormalized.fieldsR indexedVecDecl.uvars
        indexedVecDecl.nparams).length := consRuleFieldsNative

private theorem nilRuleBinderCoreNative :
    (concreteRuleAt 0).rhs.binderCore = true := by native_decide
theorem nilRuleBinderCore : (concreteRuleAt 0).rhs.binderCore = true :=
  nilRuleBinderCoreNative

private theorem consRuleBinderCoreNative :
    (concreteRuleAt 1).rhs.binderCore = true := by native_decide
theorem consRuleBinderCore : (concreteRuleAt 1).rhs.binderCore = true :=
  consRuleBinderCoreNative

private theorem nilRuleScopedNative :
    (concreteRuleAt 0).rhs.Scoped 0
      (generation.rule 0 nilNormalized).uvars := by native_decide
theorem nilRuleScoped :
    (concreteRuleAt 0).rhs.Scoped 0
      (generation.rule 0 nilNormalized).uvars := nilRuleScopedNative

private theorem consRuleScopedNative :
    (concreteRuleAt 1).rhs.Scoped 0
      (generation.rule 1 consNormalized).uvars := by native_decide
theorem consRuleScoped :
    (concreteRuleAt 1).rhs.Scoped 0
      (generation.rule 1 consNormalized).uvars := consRuleScopedNative

private theorem nilRuleSizeBoundNative :
    (concreteRuleAt 0).rhs.size < UInt64.size := by native_decide
theorem nilRuleSizeBound :
    (concreteRuleAt 0).rhs.size < UInt64.size := nilRuleSizeBoundNative

private theorem consRuleSizeBoundNative :
    (concreteRuleAt 1).rhs.size < UInt64.size := by native_decide
theorem consRuleSizeBound :
    (concreteRuleAt 1).rhs.size < UInt64.size := consRuleSizeBoundNative

def nilRulePre : PreTrKExprS indexedVecFinalEnv
    (generation.rule 0 nilNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 0).rhs (generation.rule 0 nilNormalized).rhs :=
  nilRuleRaw.toPreBinderCore_of_scoped nilRuleBinderCore nilRuleScoped
    nilRuleSizeBound

def consRulePre : PreTrKExprS indexedVecFinalEnv
    (generation.rule 1 consNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 1).rhs (generation.rule 1 consNormalized).rhs :=
  consRuleRaw.toPreBinderCore_of_scoped consRuleBinderCore consRuleScoped
    consRuleSizeBound

theorem nilGeneratedRuleMem :
    generation.rule 0 nilNormalized ∈ generation.generatedRules :=
  List.mem_of_getElem?
    (CertifiedSingletonGeneration.generatedRuleAt generation nilNormalizedAt)

theorem consGeneratedRuleMem :
    generation.rule 1 consNormalized ∈ generation.generatedRules :=
  List.mem_of_getElem?
    (CertifiedSingletonGeneration.generatedRuleAt generation consNormalizedAt)

theorem nilGeneratedRuleWF :
    (generation.rule 0 nilNormalized).WF indexedVecFinalEnv :=
  transaction.facts.afterWF.ordered.defEqWF
    (transaction.facts.ruleMem nilGeneratedRuleMem)

theorem consGeneratedRuleWF :
    (generation.rule 1 consNormalized).WF indexedVecFinalEnv :=
  transaction.facts.afterWF.ordered.defEqWF
    (transaction.facts.ruleMem consGeneratedRuleMem)

theorem nilRuleTyped : TrKExprS indexedVecFinalEnv
    (generation.rule 0 nilNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 0).rhs (generation.rule 0 nilNormalized).rhs := by
  exact nilRulePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) nilRuleBinderCore
    ⟨_, nilGeneratedRuleWF.2⟩

theorem consRuleTyped : TrKExprS indexedVecFinalEnv
    (generation.rule 1 consNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 1).rhs (generation.rule 1 consNormalized).rhs := by
  exact consRulePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) consRuleBinderCore
    ⟨_, consGeneratedRuleWF.2⟩

private theorem constructorCountNative :
    constructorIds.size = generation.block.sourceType.ctors.length := by
  native_decide

private theorem nilSourceNameNative :
    nilSource.name = ``IndexedVec.nil := by
  native_decide

private theorem consSourceNameNative :
    consSource.name = ``IndexedVec.cons := by
  native_decide

def familyInterpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf familyIngressResult transaction where
  familyId := familyId
  constructorIds := constructorIds
  memberKids := familyMemberKids
  entryIds := familyEntryIds
  entriesUnique := familyEntriesUnique
  constructorCount := constructorCountNative
  familyConcrete := familyConcrete
  familyEntry := familyEntry
  familyShape := familyShape
  familyName := nameOf_family
  familyType := familyTypeRaw
  constructor := by
    intro index hindex
    change index < 2 at hindex
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · refine ⟨nilSource, nilConcrete, nilSourceAt, ?_, nilShape, ?_,
        nilTypeRaw⟩
      · simpa [constructorIds] using nilEntry
      · simpa [constructorIds, nilSourceNameNative] using nameOf_nil
    · refine ⟨consSource, consConcrete, consSourceAt, ?_, consShape, ?_,
        consTypeRaw⟩
      · simpa [constructorIds] using consEntry
      · simpa [constructorIds, consSourceNameNative] using nameOf_cons

/-! ## One immutable semantic world and exact ingress links -/

def catalog : Catalog := fun id =>
  if id == familyId then some familyConcrete
  else if id == nilId then some nilConcrete
  else if id == consId then some consConcrete
  else if id == recursorId then some recursorConcrete
  else if id == natId then some natConcrete
  else if id == zeroId then some zeroConcrete
  else if id == succId then some succConcrete
  else none

def blockCatalog : BlockCatalog := fun id => recursorIngressAfter.getBlock? id

private theorem catalogFamilyNative :
    catalog familyId = some familyConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]
theorem catalog_family : catalog familyId = some familyConcrete :=
  catalogFamilyNative

private theorem catalogNilNative : catalog nilId = some nilConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]
theorem catalog_nil : catalog nilId = some nilConcrete := catalogNilNative

private theorem catalogConsNative : catalog consId = some consConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]
theorem catalog_cons : catalog consId = some consConcrete := catalogConsNative

private theorem catalogRecursorNative :
    catalog recursorId = some recursorConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]
theorem catalog_recursor : catalog recursorId = some recursorConcrete :=
  catalogRecursorNative

private theorem catalogNatNative : catalog natId = some natConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]
theorem catalog_nat : catalog natId = some natConcrete := catalogNatNative

private theorem catalogZeroNative : catalog zeroId = some zeroConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]
theorem catalog_zero : catalog zeroId = some zeroConcrete := catalogZeroNative

private theorem catalogSuccNative : catalog succId = some succConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]
theorem catalog_succ : catalog succId = some succConcrete := catalogSuccNative

private theorem natEntryAtZeroNative :
    natIngressResult.allEntries[0]'natIndexZero = (natId, natConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl
theorem natEntryAtZero :
    natIngressResult.allEntries[0]'natIndexZero = (natId, natConcrete) :=
  natEntryAtZeroNative

private theorem natEntryAtOneNative :
    natIngressResult.allEntries[1]'natIndexOne = (zeroId, zeroConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl
theorem natEntryAtOne :
    natIngressResult.allEntries[1]'natIndexOne = (zeroId, zeroConcrete) :=
  natEntryAtOneNative

private theorem natEntryAtTwoNative :
    natIngressResult.allEntries[2]'natIndexTwo = (succId, succConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl
theorem natEntryAtTwo :
    natIngressResult.allEntries[2]'natIndexTwo = (succId, succConcrete) :=
  natEntryAtTwoNative

theorem natCatalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry : (id, concrete) ∈ natIngressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [natEntriesSize] at hindex
  rcases (show index = 0 ∨ index = 1 ∨ index = 2 by omega) with
    rfl | rfl | rfl
  · rw [natEntryAtZero] at hget
    cases hget
    exact catalog_nat
  · rw [natEntryAtOne] at hget
    cases hget
    exact catalog_zero
  · rw [natEntryAtTwo] at hget
    cases hget
    exact catalog_succ

/-- Empty semantic base used only to admit the actual Nat ingress block. -/
def natBaseWorld : VerifyWorld where
  catalog := catalog
  trusted := fun _ => False
  venv := .empty
  nameOf := nameOf
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h
  blocks := blockCatalog

theorem natBaseTrustedCatalog :
    TrustedCatalogRel RawProjRel.none natBaseWorld :=
  TrustedCatalogLog.empty

def natFamilyLink : SingletonFamilyCatalogLink RawProjRel.none
    natBaseWorld.catalog natBaseWorld.nameOf natBaseWorld.trusted
      natTransaction :=
  natInterpretation.toCatalogLinkOfEntries natIngressExecution
    natCatalogEntry natBaseTrustedCatalog

/-- Consumer-facing provenance for one exact member of the certified Nat
transaction.  Family and constructor declarations carry no recursor rules,
so the two rule obligations close from their concrete shapes. -/
private def natFamilySemanticEntry {id : KId .anon}
    (hmember : id ∈ natFamilyLink.members) :
    TrustedCatalogEntry RawProjRel.none catalog nameOf natFinalEnv id := by
  obtain ⟨concrete, name, ci, hcatalog, hraw, hlookup, hwf⟩ :=
    natFamilyLink.translateMember hmember
  exact .ambient hcatalog hraw hlookup hwf
    (by
      intro rule hrule
      exact False.elim
        (natFamilyLink.noRecursorRule hmember hcatalog rule hrule))
    (by
      intro ruleIndex rule hrule
      exact False.elim
        (natFamilyLink.noRecursorRuleAt hmember hcatalog
          ruleIndex rule hrule))

/-- Exact trust delta introduced by the certified Nat family transaction. -/
def natTrusted : KId .anon → Prop :=
  fun id => id ∈ natFamilyLink.members ∨ natBaseWorld.trusted id

def natTrustedCatalogLog : TrustedCatalogLog RawProjRel.none catalog nameOf
    natTrusted natFinalEnv :=
  .semanticBlock natBaseTrustedCatalog natTransaction.facts.envLE
    natTransaction.facts.afterWF (fun {_} hmember =>
      natFamilySemanticEntry hmember)

/-- The IndexedVec checking world starts from the Nat transaction justified
by the preceding physical ingress block.  Its semantic state is materialized
directly from the certified transaction and exact member provenance, without
an existential inductive oracle. -/
def world : VerifyWorld where
  catalog := catalog
  trusted := natTrusted
  venv := natFinalEnv
  nameOf := nameOf
  venvWF := natTransaction.facts.afterWF
  trustedCatalogued := natTrustedCatalogLog.catalogued
  blocks := blockCatalog

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world :=
  natTrustedCatalogLog

private theorem familyEntryAtZeroNative :
    familyIngressResult.allEntries[0]'familyIndexZero =
      (familyId, familyConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl
theorem familyEntryAtZero :
    familyIngressResult.allEntries[0]'familyIndexZero =
      (familyId, familyConcrete) := familyEntryAtZeroNative

private theorem familyEntryAtOneNative :
    familyIngressResult.allEntries[1]'familyIndexOne =
      (nilId, nilConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl
theorem familyEntryAtOne :
    familyIngressResult.allEntries[1]'familyIndexOne =
      (nilId, nilConcrete) := familyEntryAtOneNative

private theorem familyEntryAtTwoNative :
    familyIngressResult.allEntries[2]'familyIndexTwo =
      (consId, consConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl
theorem familyEntryAtTwo :
    familyIngressResult.allEntries[2]'familyIndexTwo =
      (consId, consConcrete) := familyEntryAtTwoNative

theorem familyCatalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry : (id, concrete) ∈ familyIngressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [familyEntriesSize] at hindex
  rcases (show index = 0 ∨ index = 1 ∨ index = 2 by omega) with
    rfl | rfl | rfl
  · rw [familyEntryAtZero] at hget
    cases hget
    exact catalog_family
  · rw [familyEntryAtOne] at hget
    cases hget
    exact catalog_nil
  · rw [familyEntryAtTwo] at hget
    cases hget
    exact catalog_cons

def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  familyInterpretation.toCatalogLinkOfEntries familyIngressExecution
    familyCatalogEntry trustedCatalog

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
    change index < 2 at hindex
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · exact ⟨concreteRuleAt 0, nilNormalized,
        concreteRuleAt_ruleAt 0 (by omega), nilNormalizedAt,
        nilRuleFields, nilRuleRaw, nilRuleTyped⟩
    · exact ⟨concreteRuleAt 1, consNormalized,
        concreteRuleAt_ruleAt 1 (by omega), consNormalizedAt,
        consRuleFields, consRuleRaw, consRuleTyped⟩

def recursorLink : SingletonRecursorCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction familyLink :=
  recursorInterpretation.toCatalogLinkOfEntry recursorIngressExecution
    catalog_recursor trustedCatalog

end Ix.Tc.IndexedRecursiveFixture
