import Ix.CompileDriver
import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.SingletonRecursor
import Ix.Tc.Verify.Ingress.AnonStructural
import Lean4Lean.Verify.Environment.EliminationFixturesEq
import Lean4Lean.Verify.Environment.EliminationFixturesSmall

/-!
# Concrete small-elimination and K-target breadth

Lean4Lean's L4L-06 fixtures retain the exact kernel elimination traversal and
align it with the generated Theory metadata.  This module takes the remaining
Ix step: it compiles those same kernel declarations to production Ixon blocks,
ingresses the family and recursor projections, and runs both production block
checkers.

The two cases are deliberately complementary:

* `L4L06SmallSource` keeps its source universe but introduces no fresh
  elimination universe; and
* `Eq` uses large elimination and declares the independently computed K bit.

Thus the shared singleton-recursor relation is exercised at both universe
layouts and at both values of the physical `k` field.
-/

namespace Ix.Tc.EliminationBreadthFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures

local instance eliminationAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance eliminationKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance eliminationKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

local instance recursorMajorIdxCoherentDecidable
    (concrete : KConst .anon) :
    Decidable concrete.RecursorMajorIdxCoherent := by
  cases concrete <;>
    simp only [KConst.RecursorMajorIdxCoherent] <;> infer_instance

local instance certifiedSingletonRecursorDecidable
    (source : VInductDecl) (generation : source.GenerationChecked)
    (constructors : Array (KId .anon)) (concrete : KConst .anon) :
    Decidable
      (concrete.IsCertifiedSingletonRecursor source generation constructors) := by
  cases concrete <;>
    simp only [KConst.IsCertifiedSingletonRecursor] <;> infer_instance

/-! ## Shared production compiler harness -/

def canonicalConstants (constants : Array Lean.ConstantInfo) :
    Array (Ix.Name × Ix.ConstantInfo) :=
  (StateT.run (constants.mapM fun info => do
    let canonical ← Ix.CanonM.canonConst info
    pure (canonical.getCnst.name, canonical)) {}).1

def compilerEnvironment (constants : Array Lean.ConstantInfo) :
    Ix.Environment :=
  { consts := (canonicalConstants constants).foldl (init := {})
      fun environment row => environment.insert row.1 row.2 }

def compilerReferences (constants : Array Lean.ConstantInfo) :
    Ix.Map Ix.Name (Ix.Set Ix.Name) :=
  (canonicalConstants constants).foldl (init := {}) fun references row =>
    let (out, _) :=
      Ix.GraphM.run { consts := {} } .init (Ix.graphConst row.2)
    references.insert row.1 out

def compilerBlocks (constants : Array Lean.ConstantInfo) :
    Ix.CondensedBlocks :=
  Ix.CondenseM.run (compilerReferences constants)

def compilerOutcome (constants : Array Lean.ConstantInfo) :=
  Ix.CompileM.compileEnvAux (compilerEnvironment constants)
    (compilerBlocks constants)

def compilerResult (constants : Array Lean.ConstantInfo) :
    Ixon.Env × Nat × Ix.CompileM.CompileEnv :=
  match compilerOutcome constants with
  | .ok result => result
  | .error _ => ({}, 0, Ix.CompileM.CompileEnv.new (compilerEnvironment constants))

def compiledEnv (constants : Array Lean.ConstantInfo) : Ixon.Env :=
  (compilerResult constants).1

def compiledState (constants : Array Lean.ConstantInfo) :
    Ix.CompileM.CompileEnv :=
  (compilerResult constants).2.2

def inductiveProjectionBlock? (environment : Ixon.Env)
    (id : KId .anon) : Option Address := do
  let projection ← environment.getConst? id.addr
  match projection.info with
  | .iPrj value => some value.block
  | _ => none

def recursorProjectionBlock? (environment : Ixon.Env)
    (id : KId .anon) : Option Address := do
  let projection ← environment.getConst? id.addr
  match projection.info with
  | .rPrj value => some value.block
  | .recr _ => some id.addr
  | _ => none

/-! ## Source-universe small elimination -/

def smallKernelConstants : Array Lean.ConstantInfo :=
  #[smallSourceInfo06, smallSourceLeftInfo06, smallSourceRightInfo06,
    smallSourceRecInfo06]

abbrev smallCompilerOutcome := compilerOutcome smallKernelConstants
abbrev smallCompilerResult := compilerResult smallKernelConstants
abbrev smallCompiledEnv := compiledEnv smallKernelConstants
abbrev smallCompiledState := compiledState smallKernelConstants

def smallFamilyCompilerName : Ix.Name :=
  Ix.Name.fromLeanName smallSourceInfo06.name
def smallLeftCompilerName : Ix.Name :=
  Ix.Name.fromLeanName smallSourceLeftInfo06.name
def smallRightCompilerName : Ix.Name :=
  Ix.Name.fromLeanName smallSourceRightInfo06.name
def smallRecursorCompilerName : Ix.Name :=
  Ix.Name.fromLeanName smallSourceRecInfo06.name

def smallFamilyId : KId .anon :=
  ⟨(smallCompiledEnv.getAddr? smallFamilyCompilerName).getD default, ()⟩
def smallLeftId : KId .anon :=
  ⟨(smallCompiledEnv.getAddr? smallLeftCompilerName).getD default, ()⟩
def smallRightId : KId .anon :=
  ⟨(smallCompiledEnv.getAddr? smallRightCompilerName).getD default, ()⟩
def smallRecursorId : KId .anon :=
  ⟨(smallCompiledEnv.getAddr? smallRecursorCompilerName).getD default, ()⟩

def smallFamilyBlockAddress : Address :=
  (inductiveProjectionBlock? smallCompiledEnv smallFamilyId).getD default
def smallRecursorBlockAddress : Address :=
  (recursorProjectionBlock? smallCompiledEnv smallRecursorId).getD default

def smallFamilyBlockId : KId .anon := ⟨smallFamilyBlockAddress, ()⟩
def smallRecursorBlockId : KId .anon := ⟨smallRecursorBlockAddress, ()⟩

def smallFamilyBlockConstant : Ixon.Constant :=
  (smallCompiledEnv.getConst? smallFamilyBlockAddress).getD default
def smallRecursorBlockConstant : Ixon.Constant :=
  (smallCompiledEnv.getConst? smallRecursorBlockAddress).getD default

def smallFamilyMembers : Array (KId .anon) :=
  #[smallFamilyId, smallLeftId, smallRightId]
def smallConstructorIds : Array (KId .anon) :=
  #[smallLeftId, smallRightId]
def smallRecursorMembers : Array (KId .anon) := #[smallRecursorId]

structure SmallCompiledIdentity : Prop where
  compilerSuccess : smallCompilerOutcome = .ok smallCompilerResult
  grounded : smallCompiledState.ungrounded.isEmpty = true
  familyPresent :
    smallCompiledEnv.getAddr? smallFamilyCompilerName = some smallFamilyId.addr
  leftPresent :
    smallCompiledEnv.getAddr? smallLeftCompilerName = some smallLeftId.addr
  rightPresent :
    smallCompiledEnv.getAddr? smallRightCompilerName = some smallRightId.addr
  recursorPresent :
    smallCompiledEnv.getAddr? smallRecursorCompilerName =
      some smallRecursorId.addr
  familyBlock :
    inductiveProjectionBlock? smallCompiledEnv smallFamilyId =
      some smallFamilyBlockAddress
  recursorBlock :
    recursorProjectionBlock? smallCompiledEnv smallRecursorId =
      some smallRecursorBlockAddress

private theorem smallCompilerSucceededNative :
    (match smallCompilerOutcome with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem smallCompilerRun :
    smallCompilerOutcome = .ok smallCompilerResult := by
  have success := smallCompilerSucceededNative
  unfold smallCompilerResult compilerResult
  generalize houtcome : smallCompilerOutcome = outcome at success ⊢
  cases outcome <;> simp_all

theorem smallCompiledIdentity : SmallCompiledIdentity :=
  { compilerSuccess := smallCompilerRun
    grounded := by native_decide
    familyPresent := by native_decide
    leftPresent := by native_decide
    rightPresent := by native_decide
    recursorPresent := by native_decide
    familyBlock := by native_decide
    recursorBlock := by native_decide }

/-! ## Indexed singleton K target -/

def eqKernelConstants : Array Lean.ConstantInfo :=
  #[eqInfo, eqReflInfo, eqRecInfo]

abbrev eqCompilerOutcome := compilerOutcome eqKernelConstants
abbrev eqCompilerResult := compilerResult eqKernelConstants
abbrev eqCompiledEnv := compiledEnv eqKernelConstants
abbrev eqCompiledState := compiledState eqKernelConstants

def eqFamilyCompilerName : Ix.Name := Ix.Name.fromLeanName eqInfo.name
def eqReflCompilerName : Ix.Name := Ix.Name.fromLeanName eqReflInfo.name
def eqRecursorCompilerName : Ix.Name := Ix.Name.fromLeanName eqRecInfo.name

def eqFamilyId : KId .anon :=
  ⟨(eqCompiledEnv.getAddr? eqFamilyCompilerName).getD default, ()⟩
def eqReflId : KId .anon :=
  ⟨(eqCompiledEnv.getAddr? eqReflCompilerName).getD default, ()⟩
def eqRecursorId : KId .anon :=
  ⟨(eqCompiledEnv.getAddr? eqRecursorCompilerName).getD default, ()⟩

def eqFamilyBlockAddress : Address :=
  (inductiveProjectionBlock? eqCompiledEnv eqFamilyId).getD default
def eqRecursorBlockAddress : Address :=
  (recursorProjectionBlock? eqCompiledEnv eqRecursorId).getD default

def eqFamilyBlockId : KId .anon := ⟨eqFamilyBlockAddress, ()⟩
def eqRecursorBlockId : KId .anon := ⟨eqRecursorBlockAddress, ()⟩

def eqFamilyBlockConstant : Ixon.Constant :=
  (eqCompiledEnv.getConst? eqFamilyBlockAddress).getD default
def eqRecursorBlockConstant : Ixon.Constant :=
  (eqCompiledEnv.getConst? eqRecursorBlockAddress).getD default

def eqFamilyMembers : Array (KId .anon) := #[eqFamilyId, eqReflId]
def eqConstructorIds : Array (KId .anon) := #[eqReflId]
def eqRecursorMembers : Array (KId .anon) := #[eqRecursorId]

structure EqCompiledIdentity : Prop where
  compilerSuccess : eqCompilerOutcome = .ok eqCompilerResult
  grounded : eqCompiledState.ungrounded.isEmpty = true
  familyPresent :
    eqCompiledEnv.getAddr? eqFamilyCompilerName = some eqFamilyId.addr
  reflPresent :
    eqCompiledEnv.getAddr? eqReflCompilerName = some eqReflId.addr
  recursorPresent :
    eqCompiledEnv.getAddr? eqRecursorCompilerName = some eqRecursorId.addr
  familyBlock :
    inductiveProjectionBlock? eqCompiledEnv eqFamilyId =
      some eqFamilyBlockAddress
  recursorBlock :
    recursorProjectionBlock? eqCompiledEnv eqRecursorId =
      some eqRecursorBlockAddress

private theorem eqCompilerSucceededNative :
    (match eqCompilerOutcome with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem eqCompilerRun :
    eqCompilerOutcome = .ok eqCompilerResult := by
  have success := eqCompilerSucceededNative
  unfold eqCompilerResult compilerResult
  generalize houtcome : eqCompilerOutcome = outcome at success ⊢
  cases outcome <;> simp_all

theorem eqCompiledIdentity : EqCompiledIdentity :=
  { compilerSuccess := eqCompilerRun
    grounded := by native_decide
    familyPresent := by native_decide
    reflPresent := by native_decide
    recursorPresent := by native_decide
    familyBlock := by native_decide
    recursorBlock := by native_decide }

/-! ## Small-elimination production execution -/

def smallFamilyIngressOutcome :=
  ingressAnonBlockWithTrace smallCompiledEnv smallFamilyBlockConstant
    smallFamilyBlockAddress ({} : AnonEnv)

def smallFamilyIngressResult : AnonBlockIngressTrace :=
  match smallFamilyIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def smallFamilyIngressAfter : AnonEnv :=
  match smallFamilyIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem smallFamilyIngressSucceededNative :
    (match smallFamilyIngressOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem smallFamilyIngressRun :
    smallFamilyIngressOutcome =
      .ok smallFamilyIngressResult smallFamilyIngressAfter := by
  have success := smallFamilyIngressSucceededNative
  unfold smallFamilyIngressResult smallFamilyIngressAfter
  generalize houtcome : smallFamilyIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def smallRecursorIngressOutcome :=
  ingressAnonStandalone smallCompiledEnv smallRecursorId.addr
    smallRecursorBlockConstant smallFamilyIngressAfter

def smallRecursorIngressAfter : AnonEnv :=
  match smallRecursorIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem smallRecursorIngressSucceededNative :
    (match smallRecursorIngressOutcome with
      | .ok id _ => id == smallRecursorId
      | .error _ _ => false) = true := by
  native_decide

theorem smallRecursorIngressRun :
    smallRecursorIngressOutcome =
      .ok smallRecursorId smallRecursorIngressAfter := by
  have success := smallRecursorIngressSucceededNative
  unfold smallRecursorIngressAfter
  generalize houtcome : smallRecursorIngressOutcome = outcome at success ⊢
  cases outcome with
  | error => simp at success
  | ok id after =>
      simp only at success
      have hid : id = smallRecursorId := eq_of_beq success
      subst id
      rfl

def smallCheckerFuel : UInt64 := 1024
def smallCheckerMethods : Methods .anon := methodsN smallCheckerFuel.toNat
def smallCheckerInitial : TcState .anon :=
  { TcState.ofEnvAnon smallRecursorIngressAfter with
    recFuel := smallCheckerFuel
    fuelBudget := smallCheckerFuel }

def smallFamilyKernelOutcome :=
  (RecM.checkInductiveBlock smallFamilyBlockId smallFamilyMembers).run
    smallCheckerMethods smallCheckerInitial

def smallFamilyKernelAfter : TcState .anon :=
  match smallFamilyKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem smallFamilyKernelSucceededNative :
    (match smallFamilyKernelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem smallFamilyKernelRun :
    smallFamilyKernelOutcome = .ok () smallFamilyKernelAfter := by
  have success := smallFamilyKernelSucceededNative
  unfold smallFamilyKernelAfter
  generalize houtcome : smallFamilyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def smallRecursorKernelOutcome :=
  (RecM.checkRecursorBlock smallRecursorBlockId smallRecursorMembers).run
    smallCheckerMethods smallFamilyKernelAfter

def smallRecursorKernelAfter : TcState .anon :=
  match smallRecursorKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem smallRecursorKernelSucceededNative :
    (match smallRecursorKernelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem smallRecursorKernelRun :
    smallRecursorKernelOutcome = .ok () smallRecursorKernelAfter := by
  have success := smallRecursorKernelSucceededNative
  unfold smallRecursorKernelAfter
  generalize houtcome : smallRecursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def smallRecursorConcrete : KConst .anon :=
  (smallRecursorIngressAfter.get? smallRecursorId).getD default

theorem smallRecursorLookup :
    smallRecursorIngressAfter.get? smallRecursorId =
      some smallRecursorConcrete := by
  native_decide

theorem smallRecursorShape :
    smallRecursorConcrete.IsCertifiedSingletonRecursor smallSourceDecl06
      smallSourceGeneration06 smallConstructorIds := by
  native_decide

private theorem smallExecutionModeNative :
    smallSourceExecution06.elimination.large.result = false := by
  native_decide

private theorem smallExecutionKNative :
    smallSourceExecution06.kTarget.result = false := by
  native_decide

theorem smallTheoryMode :
    smallSourceGeneration06.elimination = .small :=
  smallSourceAlignment06.small_result_iff.mp smallExecutionModeNative

theorem smallTheoryKTarget :
    smallSourceGeneration06.kTarget = false :=
  smallSourceAlignment06.kTarget_result_false_iff.mp smallExecutionKNative

theorem smallTheoryRecUvars : smallSourceGeneration06.recUvars = 1 := by
  calc
    smallSourceGeneration06.recUvars =
        smallSourceExecution06.recLevelParams.length :=
      smallSourceAlignment06.recUvars_eq
    _ = 1 := by native_decide

def smallPreparationOutcome :=
  (RecM.prepareGeneratedRecursorBuildInputs smallFamilyBlockId).run
    smallCheckerMethods smallCheckerInitial

def smallPreparationMatches : Bool :=
  match smallPreparationOutcome with
  | .ok (some inputs) _ =>
      decide (inputs.isLarge = false) &&
        decide (inputs.univOffset = 0) &&
        decide (inputs.recLvls = 1) &&
        decide (inputs.nParams = 1) &&
        decide (inputs.nMinors = 2)
  | _ => false

theorem smallPreparationMatches_eq : smallPreparationMatches = true := by
  native_decide

def smallComputeKOutcome :=
  (RecM.computeKTarget smallFamilyId).run smallCheckerMethods
    smallCheckerInitial

def smallComputeKMatches : Bool :=
  match smallComputeKOutcome with
  | .ok false _ => true
  | _ => false

theorem smallComputeKMatches_eq : smallComputeKMatches = true := by
  native_decide

/-- Concrete vertical regression for a source-universe-bearing small
eliminator.  Both the Theory analyzer and Ix production preparation retain
one universe; neither introduces the large-elimination offset. -/
structure SmallEliminationAcceptance : Prop where
  compiled : SmallCompiledIdentity
  familyIngress :
    smallFamilyIngressOutcome =
      .ok smallFamilyIngressResult smallFamilyIngressAfter
  recursorIngress :
    smallRecursorIngressOutcome =
      .ok smallRecursorId smallRecursorIngressAfter
  familyChecked : smallFamilyKernelOutcome = .ok () smallFamilyKernelAfter
  recursorChecked :
    smallRecursorKernelOutcome = .ok () smallRecursorKernelAfter
  theoryMode : smallSourceGeneration06.elimination = .small
  theoryK : smallSourceGeneration06.kTarget = false
  theoryRecUvars : smallSourceGeneration06.recUvars = 1
  physicalShape :
    smallRecursorConcrete.IsCertifiedSingletonRecursor smallSourceDecl06
      smallSourceGeneration06 smallConstructorIds
  productionLayout : smallPreparationMatches = true
  productionK : smallComputeKMatches = true

theorem smallEliminationAcceptance : SmallEliminationAcceptance where
  compiled := smallCompiledIdentity
  familyIngress := smallFamilyIngressRun
  recursorIngress := smallRecursorIngressRun
  familyChecked := smallFamilyKernelRun
  recursorChecked := smallRecursorKernelRun
  theoryMode := smallTheoryMode
  theoryK := smallTheoryKTarget
  theoryRecUvars := smallTheoryRecUvars
  physicalShape := smallRecursorShape
  productionLayout := smallPreparationMatches_eq
  productionK := smallComputeKMatches_eq

/-! ## K-target production execution -/

def eqFamilyIngressOutcome :=
  ingressAnonBlockWithTrace eqCompiledEnv eqFamilyBlockConstant
    eqFamilyBlockAddress ({} : AnonEnv)

def eqFamilyIngressResult : AnonBlockIngressTrace :=
  match eqFamilyIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def eqFamilyIngressAfter : AnonEnv :=
  match eqFamilyIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem eqFamilyIngressSucceededNative :
    (match eqFamilyIngressOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem eqFamilyIngressRun :
    eqFamilyIngressOutcome = .ok eqFamilyIngressResult eqFamilyIngressAfter := by
  have success := eqFamilyIngressSucceededNative
  unfold eqFamilyIngressResult eqFamilyIngressAfter
  generalize houtcome : eqFamilyIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def eqRecursorIngressOutcome :=
  ingressAnonStandalone eqCompiledEnv eqRecursorId.addr
    eqRecursorBlockConstant eqFamilyIngressAfter

def eqRecursorIngressAfter : AnonEnv :=
  match eqRecursorIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem eqRecursorIngressSucceededNative :
    (match eqRecursorIngressOutcome with
      | .ok id _ => id == eqRecursorId
      | .error _ _ => false) = true := by
  native_decide

theorem eqRecursorIngressRun :
    eqRecursorIngressOutcome = .ok eqRecursorId eqRecursorIngressAfter := by
  have success := eqRecursorIngressSucceededNative
  unfold eqRecursorIngressAfter
  generalize houtcome : eqRecursorIngressOutcome = outcome at success ⊢
  cases outcome with
  | error => simp at success
  | ok id after =>
      simp only at success
      have hid : id = eqRecursorId := eq_of_beq success
      subst id
      rfl

def eqCheckerFuel : UInt64 := 1024
def eqCheckerMethods : Methods .anon := methodsN eqCheckerFuel.toNat
def eqCheckerInitial : TcState .anon :=
  { TcState.ofEnvAnon eqRecursorIngressAfter with
    recFuel := eqCheckerFuel
    fuelBudget := eqCheckerFuel }

def eqFamilyKernelOutcome :=
  (RecM.checkInductiveBlock eqFamilyBlockId eqFamilyMembers).run
    eqCheckerMethods eqCheckerInitial

def eqFamilyKernelAfter : TcState .anon :=
  match eqFamilyKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem eqFamilyKernelSucceededNative :
    (match eqFamilyKernelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem eqFamilyKernelRun :
    eqFamilyKernelOutcome = .ok () eqFamilyKernelAfter := by
  have success := eqFamilyKernelSucceededNative
  unfold eqFamilyKernelAfter
  generalize houtcome : eqFamilyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def eqRecursorKernelOutcome :=
  (RecM.checkRecursorBlock eqRecursorBlockId eqRecursorMembers).run
    eqCheckerMethods eqFamilyKernelAfter

def eqRecursorKernelAfter : TcState .anon :=
  match eqRecursorKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem eqRecursorKernelSucceededNative :
    (match eqRecursorKernelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem eqRecursorKernelRun :
    eqRecursorKernelOutcome = .ok () eqRecursorKernelAfter := by
  have success := eqRecursorKernelSucceededNative
  unfold eqRecursorKernelAfter
  generalize houtcome : eqRecursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def eqRecursorConcrete : KConst .anon :=
  (eqRecursorIngressAfter.get? eqRecursorId).getD default

theorem eqRecursorLookup :
    eqRecursorIngressAfter.get? eqRecursorId = some eqRecursorConcrete := by
  native_decide

theorem eqRecursorShape :
    eqRecursorConcrete.IsCertifiedSingletonRecursor eqDecl
      eqGenerationChecked eqConstructorIds := by
  native_decide

private theorem eqExecutionModeNative :
    eqExecution06.elimination.large.result = true := by
  native_decide

private theorem eqExecutionKNative : eqExecution06.kTarget.result = true := by
  native_decide

theorem eqTheoryMode : eqGenerationChecked.elimination = .large :=
  eqAlignment06.large_result_iff.mp eqExecutionModeNative

theorem eqTheoryKTarget : eqGenerationChecked.kTarget = true :=
  eqAlignment06.kTarget_result_true_iff.mp eqExecutionKNative

theorem eqTheoryRecUvars : eqGenerationChecked.recUvars = 2 := by
  calc
    eqGenerationChecked.recUvars = eqExecution06.recLevelParams.length :=
      eqAlignment06.recUvars_eq
    _ = 2 := by native_decide

def eqPreparationOutcome :=
  (RecM.prepareGeneratedRecursorBuildInputs eqFamilyBlockId).run
    eqCheckerMethods eqCheckerInitial

def eqPreparationMatches : Bool :=
  match eqPreparationOutcome with
  | .ok (some inputs) _ =>
      decide (inputs.isLarge = true) &&
        decide (inputs.univOffset = 1) &&
        decide (inputs.recLvls = 2) &&
        decide (inputs.nParams = 2) &&
        decide (inputs.nMinors = 1)
  | _ => false

theorem eqPreparationMatches_eq : eqPreparationMatches = true := by
  native_decide

def eqComputeKOutcome :=
  (RecM.computeKTarget eqFamilyId).run eqCheckerMethods eqCheckerInitial

def eqComputeKMatches : Bool :=
  match eqComputeKOutcome with
  | .ok true _ => true
  | _ => false

theorem eqComputeKMatches_eq : eqComputeKMatches = true := by
  native_decide

/-- Concrete vertical regression for the positive K branch.  The physical
`Eq.rec` declares `k = true`, the Theory generation retains the same bit, and
the production classifier recomputes it before accepting the recursor. -/
structure KTargetAcceptance : Prop where
  compiled : EqCompiledIdentity
  familyIngress :
    eqFamilyIngressOutcome = .ok eqFamilyIngressResult eqFamilyIngressAfter
  recursorIngress :
    eqRecursorIngressOutcome = .ok eqRecursorId eqRecursorIngressAfter
  familyChecked : eqFamilyKernelOutcome = .ok () eqFamilyKernelAfter
  recursorChecked : eqRecursorKernelOutcome = .ok () eqRecursorKernelAfter
  theoryMode : eqGenerationChecked.elimination = .large
  theoryK : eqGenerationChecked.kTarget = true
  theoryRecUvars : eqGenerationChecked.recUvars = 2
  physicalShape :
    eqRecursorConcrete.IsCertifiedSingletonRecursor eqDecl
      eqGenerationChecked eqConstructorIds
  productionLayout : eqPreparationMatches = true
  productionK : eqComputeKMatches = true

theorem kTargetAcceptance : KTargetAcceptance where
  compiled := eqCompiledIdentity
  familyIngress := eqFamilyIngressRun
  recursorIngress := eqRecursorIngressRun
  familyChecked := eqFamilyKernelRun
  recursorChecked := eqRecursorKernelRun
  theoryMode := eqTheoryMode
  theoryK := eqTheoryKTarget
  theoryRecUvars := eqTheoryRecUvars
  physicalShape := eqRecursorShape
  productionLayout := eqPreparationMatches_eq
  productionK := eqComputeKMatches_eq

end Ix.Tc.EliminationBreadthFixture
