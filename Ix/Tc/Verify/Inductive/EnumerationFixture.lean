import Ix.Tc.Verify.Check.SingletonInductive
import Ix.Tc.Verify.Check.PreTranslationCompatibility
import Lean4Lean.Theory.InductiveFixtures

/-!
# Concrete singleton-enumeration fixture

This module closes E2b's executable witness with a two-constructor Boolean
enumeration.  The Theory side uses Lean4Lean's checked identity-generation
certificate; the concrete side below is built from the actual Ixon block
encoding and production anonymous ingress/checker functions.
-/

namespace Ix.Tc

namespace BooleanEnumerationFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open VInductDecl

local instance anonKIdDecidableEq : DecidableEq (KId .anon) := fun left right =>
  if h : left == right then
    .isTrue (eq_of_beq h)
  else
    .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-! ## Lean4Lean certificate -/

def checked : boolDecl.Checked where
  type := boolType
  types_eq := rfl
  params := []
  params_eq := rfl
  indices := []
  indices_eq := rfl
  resultLevel := .succ .zero
  result_eq := rfl
  elimination := .large
  elimination_eq := rfl
  kTarget := VInductDecl.isKTarget 0 (.succ .zero) boolType
  kTarget_eq := rfl
  names := VInductDecl.generatedNames boolType
  names_eq := rfl
  constructors := boolType.ctors.map
    (VInductDecl.CheckedCtor.ofDirect 0 ``Bool 0 0)
  constructors_eq := rfl
  accepted := by decide

def generation : GenerationChecked boolDecl := checked.identityGeneration

theorem declarationWF : boolDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = boolType :=
    List.mem_singleton.1 (by simpa [boolDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · trivial
  · intro ctor hctor
    simp [boolType] at hctor
    rcases hctor with rfl | rfl <;> exact ⟨trivial, .nil⟩

theorem generationWF : generation.WF VEnv.empty := by
  exact (checked.wf_of_decl declarationWF).identityGeneration .empty

def certificate : boolDecl.GenerationCertificate VEnv.empty where
  generation := generation
  wf := generationWF

def theoryAfter : VEnv :=
  (VEnv.empty.addInductCertified certificate).get (by decide)

theorem theorySuccess :
    VEnv.empty.addInductCertified certificate = some theoryAfter := rfl

def transaction : CertifiedGenerationTransaction boolDecl VEnv.empty
    theoryAfter where
  certificate := certificate
  success := theorySuccess
  beforeWF := ⟨[], .empty⟩

private theorem enumerationShapeNative :
    CertifiedSingletonGeneration.IsEnumeration generation := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, ?_⟩
  intro index normalized hnormalized
  have hindex : index = 0 ∨ index = 1 := by
    have hlt : index < generation.block.ctorPairs.length :=
      (List.getElem?_eq_some_iff.mp hnormalized).1
    change index < 2 at hlt
    omega
  rcases hindex with rfl | rfl
  all_goals
    simp [generation, checked, boolDecl, boolType,
      VInductDecl.Checked.identityGeneration,
      VInductDecl.Checked.identityBlock,
      VInductDecl.Normalization.identity,
      VInductDecl.NormalizedChecked.ctorPairs,
      VInductDecl.pairNormalizedCtors,
      VInductDecl.CheckedCtor.ofDirect] at hnormalized
    cases hnormalized
    native_decide

theorem enumerationShape :
    CertifiedSingletonGeneration.IsEnumeration generation :=
  enumerationShapeNative

/-! ## Concrete Ixon family block -/

/-- Store a constant at its production content address. -/
def storeConstant (env : Ixon.Env) (constant : Ixon.Constant) :
    Ixon.Env × Address :=
  let address := Address.blake3 (Ixon.serConstant constant)
  (env.storeConst address constant, address)

/-- Store a Muts block together with every projection constant required by
anonymous ingress.  This is the same physical layout emitted by the compiler. -/
def storeBlockWithProjections (env : Ixon.Env) (block : Ixon.Constant) :
    Ixon.Env × Address := Id.run do
  let (env, blockAddress) := storeConstant env block
  let mut env := env
  let .muts members := block.info | return (env, blockAddress)
  for h : index in [0:members.size] do
    let memberIndex := index.toUInt64
    match members[index] with
    | .defn _ =>
      env := (storeConstant env
        ⟨.dPrj ⟨memberIndex, blockAddress⟩, #[], #[], #[]⟩).1
    | .recr _ =>
      env := (storeConstant env
        ⟨.rPrj ⟨memberIndex, blockAddress⟩, #[], #[], #[]⟩).1
    | .indc ind =>
      env := (storeConstant env
        ⟨.iPrj ⟨memberIndex, blockAddress⟩, #[], #[], #[]⟩).1
      for constructorIndex in [0:ind.ctors.size] do
        env := (storeConstant env
          ⟨.cPrj ⟨memberIndex, constructorIndex.toUInt64, blockAddress⟩,
            #[], #[], #[]⟩).1
  return (env, blockAddress)

def familyIxon : Ixon.Inductive :=
  ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
      ⟨false, 0, 1, 0, 0, .recur 0 #[]⟩]⟩

def familyBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc familyIxon], #[], #[], #[.succ .zero]⟩

def familyStored : Ixon.Env × Address :=
  storeBlockWithProjections {} familyBlockConstant

def familyIxonEnv : Ixon.Env := familyStored.1
def familyBlockAddress : Address := familyStored.2

def familyId : KId .anon := ⟨indcProjAddr familyBlockAddress 0, ()⟩
def falseId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 0, ()⟩
def trueId : KId .anon := ⟨ctorProjAddr familyBlockAddress 0 1, ()⟩
def constructorIds : Array (KId .anon) := #[falseId, trueId]

/-! ## Concrete Ixon recursor block -/

/-- `Bool → Sort u`, encoded against the recursor block's first reference
(`Bool`) and its sole universe parameter. -/
def motiveType : Ixon.Expr :=
  .leanAll (.ref 0 #[]) (.sort 0)

/-- The canonical enumeration recursor type
`∀ motive, motive false → motive true → ∀ value, motive value`. -/
def recursorType : Ixon.Expr :=
  .leanAll motiveType
    (.leanAll (.app (.var 0) (.ref 1 #[]))
      (.leanAll (.app (.var 1) (.ref 2 #[]))
        (.leanAll (.ref 0 #[]) (.app (.var 3) (.var 0)))))

/-- The `false` equation selects the first minor. -/
def falseRuleRhs : Ixon.Expr :=
  .leanLam motiveType
    (.leanLam (.app (.var 0) (.ref 1 #[]))
      (.leanLam (.app (.var 1) (.ref 2 #[])) (.var 1)))

/-- The `true` equation selects the second minor. -/
def trueRuleRhs : Ixon.Expr :=
  .leanLam motiveType
    (.leanLam (.app (.var 0) (.ref 1 #[]))
      (.leanLam (.app (.var 1) (.ref 2 #[])) (.var 0)))

def recursorIxon : Ixon.Recursor :=
  ⟨false, false, 1, 0, 0, 1, 2, recursorType,
    #[⟨0, falseRuleRhs⟩, ⟨0, trueRuleRhs⟩]⟩

def recursorBlockConstant : Ixon.Constant :=
  ⟨.muts #[.recr recursorIxon], #[],
    #[familyId.addr, falseId.addr, trueId.addr], #[.var 0]⟩

def recursorStored : Ixon.Env × Address :=
  storeBlockWithProjections familyIxonEnv recursorBlockConstant

def recursorIxonEnv : Ixon.Env := recursorStored.1
def recursorBlockAddress : Address := recursorStored.2
def recursorId : KId .anon :=
  ⟨recrProjAddr recursorBlockAddress 0, ()⟩

/-- The unmodified production ingress computation on the concrete family
block.  Result and state selectors let the proof retain the actual opaque
hash-map state without postulating an equality for it. -/
def familyIngressOutcome :=
  ingressAnonBlockWithTrace familyIxonEnv familyBlockConstant
    familyBlockAddress ({} : AnonEnv)

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

def familyIngressExecution : AnonBlockIngressSuccessTrace familyIxonEnv
    familyBlockConstant familyBlockAddress {} familyIngressAfter
    familyIngressResult :=
  AnonBlockIngressSuccessTrace.of_run familyIngressRun

private theorem familyMemberKidsNative :
    familyIngressResult.memberKids = #[familyId] := by
  native_decide

theorem familyMemberKids : familyIngressResult.memberKids = #[familyId] :=
  familyMemberKidsNative

private theorem familyEntryIdsNative :
    familyIngressResult.allEntries.map (·.1) =
      #[familyId] ++ constructorIds := by
  native_decide

theorem familyEntryIds :
    familyIngressResult.allEntries.map (·.1) =
      #[familyId] ++ constructorIds :=
  familyEntryIdsNative

private theorem familyEntriesUniqueNative :
    EntryKeysUnique familyIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide

theorem familyEntriesUnique :
    EntryKeysUnique familyIngressResult.allEntries :=
  familyEntriesUniqueNative

private theorem familyEntriesSizeNative :
    familyIngressResult.allEntries.size = 3 := by
  native_decide

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

def falseConcrete : KConst .anon :=
  (familyIngressResult.allEntries[1]'familyIndexOne).2

def trueConcrete : KConst .anon :=
  (familyIngressResult.allEntries[2]'familyIndexTwo).2

private theorem familyEntryNative :
    (familyId, familyConcrete) ∈ familyIngressResult.allEntries := by
  have member : familyIngressResult.allEntries[0]'familyIndexZero ∈
      familyIngressResult.allEntries :=
    Array.getElem_mem familyIndexZero
  have identifier :
      (familyIngressResult.allEntries[0]'familyIndexZero).1 = familyId := by
    native_decide
  unfold familyConcrete
  rw [← identifier]
  exact member

theorem familyEntry :
    (familyId, familyConcrete) ∈ familyIngressResult.allEntries :=
  familyEntryNative

private theorem falseEntryNative :
    (falseId, falseConcrete) ∈ familyIngressResult.allEntries := by
  have member : familyIngressResult.allEntries[1]'familyIndexOne ∈
      familyIngressResult.allEntries :=
    Array.getElem_mem familyIndexOne
  have identifier :
      (familyIngressResult.allEntries[1]'familyIndexOne).1 = falseId := by
    native_decide
  unfold falseConcrete
  rw [← identifier]
  exact member

theorem falseEntry :
    (falseId, falseConcrete) ∈ familyIngressResult.allEntries :=
  falseEntryNative

private theorem trueEntryNative :
    (trueId, trueConcrete) ∈ familyIngressResult.allEntries := by
  have member : familyIngressResult.allEntries[2]'familyIndexTwo ∈
      familyIngressResult.allEntries :=
    Array.getElem_mem familyIndexTwo
  have identifier :
      (familyIngressResult.allEntries[2]'familyIndexTwo).1 = trueId := by
    native_decide
  unfold trueConcrete
  rw [← identifier]
  exact member

theorem trueEntry :
    (trueId, trueConcrete) ∈ familyIngressResult.allEntries :=
  trueEntryNative

/-! ## Concrete recursor ingress -/

/-- The recursor is ingressed into the actual family post-state, matching the
two physical-block sequence used by production. -/
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

private theorem recursorEntriesSizeNative :
    recursorIngressResult.allEntries.size = 1 := by
  native_decide

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
  have member : recursorIngressResult.allEntries[0]'recursorIndexZero ∈
      recursorIngressResult.allEntries :=
    Array.getElem_mem recursorIndexZero
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

/-- A proof-relevant structural discriminator which never equates expressions
by their content addresses. -/
def IsSortOne : KExpr .anon → Prop
  | .sort (.succ (.zero _) _) _ => True
  | _ => False

/-- Likewise, recognize a universe-free reference by constructor shape and
exact declaration id, not by expression-address equality. -/
def IsConstZero (expected : KId .anon) : KExpr .anon → Prop
  | .const actual universes _ => actual = expected ∧ universes.size = 0
  | _ => False

local instance isSortOneDecidable (expression : KExpr .anon) :
    Decidable (IsSortOne expression) := by
  cases expression <;> try exact .isFalse id
  next level _ =>
    cases level <;> try exact .isFalse id
    next inner _ =>
      cases inner <;> try exact .isFalse id
      exact .isTrue trivial

local instance isConstZeroDecidable (expected : KId .anon)
    (expression : KExpr .anon) : Decidable (IsConstZero expected expression) := by
  cases expression <;> simp only [IsConstZero] <;> infer_instance

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

/-- Executable counterpart of the proof-only universe-scoping predicate. -/
private def scopedUnivB (bound : Nat) : KUniv .anon → Bool
  | .zero _ => true
  | .succ u _ => scopedUnivB bound u
  | .max a b _ | .imax a b _ =>
      scopedUnivB bound a && scopedUnivB bound b
  | .param index _ _ => decide (index.toNat < bound)

/-- Executable counterpart of the proof-only expression-scoping predicate.
Keeping this checker explicit makes the concrete fixture suitable for
`native_decide` without adding a classical `Decidable` instance. -/
private def scopedExprB (depth : UInt64) (levelBound : Nat) :
    KExpr .anon → Bool
  | .var index _ _ => decide (index < depth)
  | .fvar .. => true
  | .sort u _ => scopedUnivB levelBound u
  | .const _ us _ => us.all (scopedUnivB levelBound)
  | .app fn argument _ =>
      scopedExprB depth levelBound fn &&
        scopedExprB depth levelBound argument
  | .lam _ _ type body _ | .all _ _ type body _ =>
      scopedExprB depth levelBound type &&
        scopedExprB (depth + 1) levelBound body
  | .letE _ type value body _ _ =>
      scopedExprB depth levelBound type &&
        scopedExprB depth levelBound value &&
        scopedExprB (depth + 1) levelBound body
  | .prj _ _ value _ => scopedExprB depth levelBound value
  | .nat .. | .str .. => true

private theorem scopedUnivB_eq_true_iff (bound : Nat) (u : KUniv .anon) :
    scopedUnivB bound u = true ↔ u.Scoped bound := by
  induction u with
  | zero => simp [scopedUnivB, KUniv.Scoped]
  | succ u _ ih => simpa [scopedUnivB, KUniv.Scoped] using ih
  | max a b _ iha ihb =>
      simp [scopedUnivB, KUniv.Scoped, iha, ihb]
  | imax a b _ iha ihb =>
      simp [scopedUnivB, KUniv.Scoped, iha, ihb]
  | param => simp [scopedUnivB, KUniv.Scoped]

private theorem scopedExprB_eq_true_iff (depth : UInt64)
    (levelBound : Nat) (expression : KExpr .anon) :
    scopedExprB depth levelBound expression = true ↔
      expression.Scoped depth levelBound := by
  induction expression generalizing depth with
  | var => simp [scopedExprB, KExpr.Scoped]
  | fvar => simp [scopedExprB, KExpr.Scoped]
  | sort => simp [scopedExprB, KExpr.Scoped, scopedUnivB_eq_true_iff]
  | const =>
      simp only [scopedExprB, Array.all_eq_true,
        scopedUnivB_eq_true_iff, KExpr.Scoped]
      constructor
      · intro h u hu
        obtain ⟨index, hindex, rfl⟩ := Array.mem_iff_getElem.mp hu
        exact h index hindex
      · intro h index hindex
        exact h _ (Array.getElem_mem hindex)
  | app fn argument _ ihFn ihArgument =>
      simp [scopedExprB, KExpr.Scoped, ihFn, ihArgument]
  | lam _ _ type body _ ihType ihBody =>
      simp [scopedExprB, KExpr.Scoped, ihType, ihBody]
  | all _ _ type body _ ihType ihBody =>
      simp [scopedExprB, KExpr.Scoped, ihType, ihBody]
  | letE _ type value body _ _ ihType ihValue ihBody =>
      simp [scopedExprB, KExpr.Scoped, ihType, ihValue, ihBody, and_assoc]
  | prj _ _ value _ ihValue =>
      simp [scopedExprB, KExpr.Scoped, ihValue]
  | nat => simp [scopedExprB, KExpr.Scoped]
  | str => simp [scopedExprB, KExpr.Scoped]

local instance kExprScopedDecidable (depth : UInt64) (levelBound : Nat)
    (expression : KExpr .anon) :
    Decidable (expression.Scoped depth levelBound) :=
  if h : scopedExprB depth levelBound expression = true then
    .isTrue ((scopedExprB_eq_true_iff depth levelBound expression).mp h)
  else
    .isFalse fun hscoped =>
      h ((scopedExprB_eq_true_iff depth levelBound expression).mpr hscoped)

theorem rawSortOne {nameOf : Address → Option Lean.Name}
    {uvars : Nat} {expression : KExpr .anon}
    (shape : IsSortOne expression) :
    RawExprRel (uvars := uvars) theoryAfter nameOf RawProjRel.none [] expression
      (.sort (.succ .zero)) := by
  cases expression <;> simp [IsSortOne] at shape
  next u _ =>
    cases u with
    | zero _ => simp at shape
    | max _ _ _ => simp at shape
    | imax _ _ _ => simp at shape
    | param _ _ _ => simp at shape
    | succ inner _ =>
      cases inner with
      | zero _ => exact RawExprRel.sort
      | succ _ _ => simp at shape
      | max _ _ _ => simp at shape
      | imax _ _ _ => simp at shape
      | param _ _ _ => simp at shape

/-- The fixture's deliberate address-to-name interpretation.  The computed
projection addresses are checked distinct below; no hash injectivity theorem
is assumed. -/
def nameOf (address : Address) : Option Lean.Name :=
  if address == recursorId.addr then some ``Bool.rec
  else if address == familyId.addr then some ``Bool
  else if address == falseId.addr then some ``Bool.false
  else if address == trueId.addr then some ``Bool.true
  else none

private theorem nameOfRecursorNative :
    nameOf recursorId.addr = some ``Bool.rec := by
  native_decide

theorem nameOf_recursor : nameOf recursorId.addr = some ``Bool.rec :=
  nameOfRecursorNative

private theorem nameOfFamilyNative :
    nameOf familyId.addr = some ``Bool := by
  native_decide

theorem nameOf_family : nameOf familyId.addr = some ``Bool :=
  nameOfFamilyNative

private theorem nameOfFalseNative :
    nameOf falseId.addr = some ``Bool.false := by
  native_decide

theorem nameOf_false : nameOf falseId.addr = some ``Bool.false :=
  nameOfFalseNative

private theorem nameOfTrueNative :
    nameOf trueId.addr = some ``Bool.true := by
  native_decide

theorem nameOf_true : nameOf trueId.addr = some ``Bool.true :=
  nameOfTrueNative

/-- Turn the structural reference discriminator into raw translation once
the corresponding Theory constant and universe arity are known. -/
theorem rawConstZero {expected : KId .anon} {expression : KExpr .anon}
    {uvars : Nat}
    (shape : IsConstZero expected expression)
    {name : Lean.Name} {constant : VConstant}
    (hname : nameOf expected.addr = some name)
    (hlookup : theoryAfter.constants name = some constant)
    (hlevels : constant.uvars = 0) :
    RawExprRel (uvars := uvars) theoryAfter nameOf RawProjRel.none [] expression
      (.const name []) := by
  cases expression <;> simp [IsConstZero] at shape
  next actual universes _ =>
    rcases shape with ⟨rfl, hsize⟩
    subst universes
    exact RawExprRel.const hname hlookup (by simpa using hlevels.symm)

/-! ## Executable raw translation for the fixture's core syntax -/

/-- Translate the closed core syntax used by the Boolean family and recursor.
The partiality is intentional: free variables, lets, projections, and
literals are outside this E2b fixture.  Constant translation consults the
same immutable Theory environment and address-to-name interpretation used by
`RawExprRel`. -/
def translateCore? : KExpr .anon → Option VExpr
  | .var index _ _ => some (.bvar index.toNat)
  | .sort level _ => some (.sort level.toVLevel)
  | .const id levels _ =>
      match nameOf id.addr with
      | none => none
      | some name =>
          match theoryAfter.constants name with
          | none => none
          | some constant =>
              if levels.size = constant.uvars then
                some (.const name (levels.toList.map KUniv.toVLevel))
              else none
  | .app fn argument _ => do
      return .app (← translateCore? fn) (← translateCore? argument)
  | .lam _ _ type body _ => do
      return .lam (← translateCore? type) (← translateCore? body)
  | .all _ _ type body _ => do
      return .forallE (← translateCore? type) (← translateCore? body)
  | _ => none

/-- Successful executable translation is proof-relevant raw translation.
This theorem lets native evaluation establish only the finite syntax shape;
the trusted conclusion is assembled constructor by constructor. -/
theorem translateCore?_raw {ctx : List VExpr} {source : KExpr .anon}
    {uvars : Nat} {target : VExpr}
    (success : translateCore? source = some target) :
    RawExprRel (uvars := uvars) theoryAfter nameOf RawProjRel.none ctx source
      target := by
  induction source generalizing ctx target with
  | var index name info =>
      simp only [translateCore?, Option.some.injEq] at success
      subst target
      exact .var
  | fvar => simp [translateCore?] at success
  | sort level info =>
      simp only [translateCore?, Option.some.injEq] at success
      subst target
      exact .sort
  | const id levels info =>
      simp only [translateCore?] at success
      split at success
      · contradiction
      · rename_i name hname
        split at success
        · contradiction
        · rename_i constant hconstant
          split at success
          · rename_i harity
            cases success
            exact .const hname hconstant harity
          · contradiction
  | app fn argument info ihFn ihArgument =>
      simp only [translateCore?] at success
      obtain ⟨fnTarget, hfn, success⟩ :=
        Option.bind_eq_some_iff.mp success
      obtain ⟨argumentTarget, hargument, success⟩ :=
        Option.bind_eq_some_iff.mp success
      cases success
      exact .app (ihFn hfn) (ihArgument hargument)
  | lam name bi type body info ihType ihBody =>
      simp only [translateCore?] at success
      obtain ⟨typeTarget, htype, success⟩ :=
        Option.bind_eq_some_iff.mp success
      obtain ⟨bodyTarget, hbody, success⟩ :=
        Option.bind_eq_some_iff.mp success
      cases success
      exact .lam (ihType htype) (ihBody hbody)
  | all name bi type body info ihType ihBody =>
      simp only [translateCore?] at success
      obtain ⟨typeTarget, htype, success⟩ :=
        Option.bind_eq_some_iff.mp success
      obtain ⟨bodyTarget, hbody, success⟩ :=
        Option.bind_eq_some_iff.mp success
      cases success
      exact .all (ihType htype) (ihBody hbody)
  | letE => simp [translateCore?] at success
  | prj => simp [translateCore?] at success
  | nat => simp [translateCore?] at success
  | str => simp [translateCore?] at success

/-! ## Concrete recursor interpretation -/

private theorem recursorShapeNative :
    recursorConcrete.IsCertifiedSingletonRecursor boolDecl generation
      constructorIds := by
  native_decide

theorem recursorShape :
    recursorConcrete.IsCertifiedSingletonRecursor boolDecl generation
      constructorIds :=
  recursorShapeNative

/-- The physical rule array selected from the converted recursor. -/
def recursorRules : Array (RecRule .anon) :=
  match recursorConcrete with
  | .recr (rules := rules) .. => rules
  | _ => #[]

private theorem recursorRulesSizeNative : recursorRules.size = 2 := by
  native_decide

theorem recursorRulesSize : recursorRules.size = 2 :=
  recursorRulesSizeNative

/-- Total finite selector; the accompanying size theorem proves that E2b
uses it only at actual rule positions. -/
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
    0 < generation.block.ctorPairs.length := by
  native_decide

private theorem generationCtorPairOne :
    1 < generation.block.ctorPairs.length := by
  native_decide

def falseNormalized : VInductDecl.NormalizedCtor :=
  generation.block.ctorPairs[0]'generationCtorPairZero

def trueNormalized : VInductDecl.NormalizedCtor :=
  generation.block.ctorPairs[1]'generationCtorPairOne

theorem falseNormalizedAt :
    generation.block.ctorPairs[0]? = some falseNormalized := by
  rfl

theorem trueNormalizedAt :
    generation.block.ctorPairs[1]? = some trueNormalized := by
  rfl

private theorem recursorTypeRawNative :
    RawExprRel (uvars := recursorConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] recursorConcrete.ty
      generation.recursor.type := by
  apply translateCore?_raw
  native_decide

theorem recursorTypeRaw :
    RawExprRel (uvars := recursorConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] recursorConcrete.ty
      generation.recursor.type :=
  recursorTypeRawNative

private theorem falseRuleRawNative :
    RawExprRel (uvars := (generation.rule 0 falseNormalized).uvars)
      theoryAfter nameOf RawProjRel.none []
      (concreteRuleAt 0).rhs (generation.rule 0 falseNormalized).rhs := by
  apply translateCore?_raw
  native_decide

theorem falseRuleRaw :
    RawExprRel (uvars := (generation.rule 0 falseNormalized).uvars)
      theoryAfter nameOf RawProjRel.none []
      (concreteRuleAt 0).rhs (generation.rule 0 falseNormalized).rhs :=
  falseRuleRawNative

private theorem trueRuleRawNative :
    RawExprRel (uvars := (generation.rule 1 trueNormalized).uvars)
      theoryAfter nameOf RawProjRel.none []
      (concreteRuleAt 1).rhs (generation.rule 1 trueNormalized).rhs := by
  apply translateCore?_raw
  native_decide

theorem trueRuleRaw :
    RawExprRel (uvars := (generation.rule 1 trueNormalized).uvars)
      theoryAfter nameOf RawProjRel.none []
      (concreteRuleAt 1).rhs (generation.rule 1 trueNormalized).rhs :=
  trueRuleRawNative

private theorem falseRuleFieldsNative :
    (concreteRuleAt 0).fields.toNat =
      (falseNormalized.fieldsR boolDecl.uvars boolDecl.nparams).length := by
  native_decide

theorem falseRuleFields :
    (concreteRuleAt 0).fields.toNat =
      (falseNormalized.fieldsR boolDecl.uvars boolDecl.nparams).length :=
  falseRuleFieldsNative

private theorem trueRuleFieldsNative :
    (concreteRuleAt 1).fields.toNat =
      (trueNormalized.fieldsR boolDecl.uvars boolDecl.nparams).length := by
  native_decide

theorem trueRuleFields :
    (concreteRuleAt 1).fields.toNat =
      (trueNormalized.fieldsR boolDecl.uvars boolDecl.nparams).length :=
  trueRuleFieldsNative

private theorem falseRuleBinderCoreNative :
    (concreteRuleAt 0).rhs.binderCore = true := by
  native_decide

theorem falseRuleBinderCore : (concreteRuleAt 0).rhs.binderCore = true :=
  falseRuleBinderCoreNative

private theorem trueRuleBinderCoreNative :
    (concreteRuleAt 1).rhs.binderCore = true := by
  native_decide

theorem trueRuleBinderCore : (concreteRuleAt 1).rhs.binderCore = true :=
  trueRuleBinderCoreNative

private theorem falseRuleScopedNative :
    (concreteRuleAt 0).rhs.Scoped 0
      (generation.rule 0 falseNormalized).uvars := by
  native_decide

theorem falseRuleScoped :
    (concreteRuleAt 0).rhs.Scoped 0
      (generation.rule 0 falseNormalized).uvars :=
  falseRuleScopedNative

private theorem trueRuleScopedNative :
    (concreteRuleAt 1).rhs.Scoped 0
      (generation.rule 1 trueNormalized).uvars := by
  native_decide

theorem trueRuleScoped :
    (concreteRuleAt 1).rhs.Scoped 0
      (generation.rule 1 trueNormalized).uvars :=
  trueRuleScopedNative

private theorem falseRuleSizeBoundNative :
    (concreteRuleAt 0).rhs.size < UInt64.size := by
  native_decide

theorem falseRuleSizeBound :
    (concreteRuleAt 0).rhs.size < UInt64.size :=
  falseRuleSizeBoundNative

private theorem trueRuleSizeBoundNative :
    (concreteRuleAt 1).rhs.size < UInt64.size := by
  native_decide

theorem trueRuleSizeBound :
    (concreteRuleAt 1).rhs.size < UInt64.size :=
  trueRuleSizeBoundNative

def falseRulePre : PreTrKExprS theoryAfter
    (generation.rule 0 falseNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 0).rhs (generation.rule 0 falseNormalized).rhs :=
  falseRuleRaw.toPreBinderCore_of_scoped falseRuleBinderCore
    falseRuleScoped falseRuleSizeBound

def trueRulePre : PreTrKExprS theoryAfter
    (generation.rule 1 trueNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 1).rhs (generation.rule 1 trueNormalized).rhs :=
  trueRuleRaw.toPreBinderCore_of_scoped trueRuleBinderCore
    trueRuleScoped trueRuleSizeBound

theorem falseGeneratedRuleMem :
    generation.rule 0 falseNormalized ∈ generation.generatedRules := by
  exact List.mem_of_getElem?
    (CertifiedSingletonGeneration.generatedRuleAt generation falseNormalizedAt)

theorem trueGeneratedRuleMem :
    generation.rule 1 trueNormalized ∈ generation.generatedRules := by
  exact List.mem_of_getElem?
    (CertifiedSingletonGeneration.generatedRuleAt generation trueNormalizedAt)

theorem falseGeneratedRuleWF :
    (generation.rule 0 falseNormalized).WF theoryAfter :=
  transaction.facts.afterWF.ordered.defEqWF
    (transaction.facts.ruleMem falseGeneratedRuleMem)

theorem trueGeneratedRuleWF :
    (generation.rule 1 trueNormalized).WF theoryAfter :=
  transaction.facts.afterWF.ordered.defEqWF
    (transaction.facts.ruleMem trueGeneratedRuleMem)

theorem falseRuleTyped : TrKExprS theoryAfter
    (generation.rule 0 falseNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 0).rhs (generation.rule 0 falseNormalized).rhs := by
  exact falseRulePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) falseRuleBinderCore
    ⟨_, falseGeneratedRuleWF.2⟩

theorem trueRuleTyped : TrKExprS theoryAfter
    (generation.rule 1 trueNormalized).uvars nameOf RawProjRel.none []
    (concreteRuleAt 1).rhs (generation.rule 1 trueNormalized).rhs := by
  exact trueRulePre.upgradeBinderCoreOfWF transaction.facts.afterWF
    (Delta := []) (hDelta := trivial) trueRuleBinderCore
    ⟨_, trueGeneratedRuleWF.2⟩

private theorem familyShapeNative :
    familyConcrete.IsCertifiedSingletonFamily boolDecl generation
      constructorIds := by
  native_decide

theorem familyShape :
    familyConcrete.IsCertifiedSingletonFamily boolDecl generation
      constructorIds :=
  familyShapeNative

private theorem familyTypeNative :
    RawExprRel (uvars := familyConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] familyConcrete.ty
      generation.block.sourceType.type := by
  apply rawSortOne
  native_decide

theorem familyType :
    RawExprRel (uvars := familyConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] familyConcrete.ty
      generation.block.sourceType.type :=
  familyTypeNative

private theorem sourceConstructorZero :
    0 < generation.block.sourceType.ctors.length := by
  native_decide

private theorem sourceConstructorOne :
    1 < generation.block.sourceType.ctors.length := by
  native_decide

def falseSource : VConstVal :=
  generation.block.sourceType.ctors[0]'sourceConstructorZero

def trueSource : VConstVal :=
  generation.block.sourceType.ctors[1]'sourceConstructorOne

theorem falseSourceAt :
    generation.block.sourceType.ctors[0]? = some falseSource := by
  rfl

theorem trueSourceAt :
    generation.block.sourceType.ctors[1]? = some trueSource := by
  rfl

private theorem falseSourceTypeNative :
    falseSource.type = .const ``Bool [] := by
  native_decide

theorem falseSourceType : falseSource.type = .const ``Bool [] :=
  falseSourceTypeNative

private theorem trueSourceTypeNative :
    trueSource.type = .const ``Bool [] := by
  native_decide

theorem trueSourceType : trueSource.type = .const ``Bool [] :=
  trueSourceTypeNative

private theorem falseShapeNative :
    falseConcrete.IsCertifiedSingletonConstructor boolDecl familyId 0
      falseSource := by
  native_decide

theorem falseShape :
    falseConcrete.IsCertifiedSingletonConstructor boolDecl familyId 0
      falseSource :=
  falseShapeNative

private theorem trueShapeNative :
    trueConcrete.IsCertifiedSingletonConstructor boolDecl familyId 1
      trueSource := by
  native_decide

theorem trueShape :
    trueConcrete.IsCertifiedSingletonConstructor boolDecl familyId 1
      trueSource :=
  trueShapeNative

private theorem falseTypeNative :
    RawExprRel (uvars := falseConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] falseConcrete.ty
      falseSource.type := by
  rw [falseSourceType]
  apply rawConstZero (expected := familyId)
  · native_decide
  · exact nameOf_family
  · exact transaction.facts.familyLookup
  · native_decide

theorem falseType :
    RawExprRel (uvars := falseConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] falseConcrete.ty
      falseSource.type :=
  falseTypeNative

private theorem trueTypeNative :
    RawExprRel (uvars := trueConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] trueConcrete.ty
      trueSource.type := by
  rw [trueSourceType]
  apply rawConstZero (expected := familyId)
  · native_decide
  · exact nameOf_family
  · exact transaction.facts.familyLookup
  · native_decide

theorem trueType :
    RawExprRel (uvars := trueConcrete.lvls.toNat) theoryAfter nameOf
      RawProjRel.none [] trueConcrete.ty
      trueSource.type :=
  trueTypeNative

private theorem familyConstructorCountNative :
    constructorIds.size =
      generation.block.sourceType.ctors.length := by
  native_decide

/-- The actual family ingress result, interpreted positionally as the
certificate's Boolean family and its two constructors. -/
def familyInterpretation : SingletonFamilyIngressInterpretation
    RawProjRel.none nameOf familyIngressResult transaction where
  familyId := familyId
  constructorIds := constructorIds
  memberKids := familyMemberKids
  entryIds := familyEntryIds
  entriesUnique := familyEntriesUnique
  constructorCount := familyConstructorCountNative
  familyConcrete := familyConcrete
  familyEntry := familyEntry
  familyShape := familyShape
  familyName := nameOf_family
  familyType := familyType
  constructor := by
    intro index hindex
    change index < 2 at hindex
    have hcases : index = 0 ∨ index = 1 := by omega
    rcases hcases with rfl | rfl
    · refine ⟨falseSource, falseConcrete, falseSourceAt, ?_, falseShape,
        ?_, falseType⟩
      · simpa [constructorIds] using falseEntry
      · simpa [constructorIds, falseSource, generation, checked, boolDecl,
          boolType] using nameOf_false
    · refine ⟨trueSource, trueConcrete, trueSourceAt, ?_, trueShape,
        ?_, trueType⟩
      · simpa [constructorIds] using trueEntry
      · simpa [constructorIds, trueSource, generation, checked, boolDecl,
          boolType] using nameOf_true

/-! ## One immutable world for both physical blocks -/

/-- The immutable semantic catalog records exactly the four declarations
identified by the two successful ingress traces.  Stating this finite map
directly keeps its proof boundary at declaration ids: it does not require a
decidable equality for full kernel constants or any injectivity property of
their content addresses. -/
def catalog : Catalog := fun id =>
  if id == familyId then some familyConcrete
  else if id == falseId then some falseConcrete
  else if id == trueId then some trueConcrete
  else if id == recursorId then some recursorConcrete
  else none

/-- Likewise, retain the block table published by those same calls. -/
def blockCatalog : BlockCatalog := fun id =>
  recursorIngressAfter.getBlock? id

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

private theorem catalogFamilyNative :
    catalog familyId = some familyConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_family : catalog familyId = some familyConcrete :=
  catalogFamilyNative

private theorem catalogFalseNative :
    catalog falseId = some falseConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_false : catalog falseId = some falseConcrete :=
  catalogFalseNative

private theorem catalogTrueNative :
    catalog trueId = some trueConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_true : catalog trueId = some trueConcrete :=
  catalogTrueNative

private theorem catalogRecursorNative :
    catalog recursorId = some recursorConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_recursor : catalog recursorId = some recursorConcrete :=
  catalogRecursorNative

private theorem familyEntryAtZeroNative :
    familyIngressResult.allEntries[0]'familyIndexZero =
      (familyId, familyConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem familyEntryAtZero :
    familyIngressResult.allEntries[0]'familyIndexZero =
      (familyId, familyConcrete) :=
  familyEntryAtZeroNative

private theorem familyEntryAtOneNative :
    familyIngressResult.allEntries[1]'familyIndexOne =
      (falseId, falseConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem familyEntryAtOne :
    familyIngressResult.allEntries[1]'familyIndexOne =
      (falseId, falseConcrete) :=
  familyEntryAtOneNative

private theorem familyEntryAtTwoNative :
    familyIngressResult.allEntries[2]'familyIndexTwo =
      (trueId, trueConcrete) := by
  apply Prod.ext
  · native_decide
  · rfl

theorem familyEntryAtTwo :
    familyIngressResult.allEntries[2]'familyIndexTwo =
      (trueId, trueConcrete) :=
  familyEntryAtTwoNative

theorem familyCatalogEntry {id : KId .anon} {concrete : KConst .anon}
    (hentry : (id, concrete) ∈ familyIngressResult.allEntries) :
    catalog id = some concrete := by
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hentry
  rw [familyEntriesSize] at hindex
  have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [familyEntryAtZero] at hget
    cases hget
    exact catalog_family
  · rw [familyEntryAtOne] at hget
    cases hget
    exact catalog_false
  · rw [familyEntryAtTwo] at hget
    cases hget
    exact catalog_true

def familyLink : SingletonFamilyCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction :=
  familyInterpretation.toCatalogLinkOfEntries familyIngressExecution
    familyCatalogEntry trustedCatalog

/-- The successful recursor ingress result interpreted against the same
Boolean generation certificate and the already-linked family block.  The
rule proof splits only on the two physically present array positions. -/
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
  recursorType := recursorTypeRaw
  rule := by
    intro index hindex
    change index < 2 at hindex
    have hcases : index = 0 ∨ index = 1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨concreteRuleAt 0, falseNormalized,
        concreteRuleAt_ruleAt 0 (by omega), falseNormalizedAt,
        falseRuleFields, falseRuleRaw, falseRuleTyped⟩
    · exact ⟨concreteRuleAt 1, trueNormalized,
        concreteRuleAt_ruleAt 1 (by omega), trueNormalizedAt,
        trueRuleFields, trueRuleRaw, trueRuleTyped⟩

/-- One immutable semantic catalog now contains the exact family,
constructors, recursor, and both registered Boolean equations produced by
the two physical ingress calls. -/
def recursorLink : SingletonRecursorCatalogLink RawProjRel.none world.catalog
    world.nameOf world.trusted transaction familyLink :=
  recursorInterpretation.toCatalogLinkOfEntry recursorIngressExecution
    catalog_recursor trustedCatalog


end BooleanEnumerationFixture

end Ix.Tc
