/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Verify.Environment.IndexedVecConsReplay
import Ix.Theory.Named.Verify.Name

/-!
# IndexedVec outer normalization-candidate replay

Exact post-family declaration and constructor-validation executions for the
real one-parameter, one-index `IndexedVec` metadata. The final theorem closes
the complete `buildNormalizationCandidate` call and retains the ordered
`nil`/`cons` candidate package produced in the staged kernel environments.
-/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta
open Ix.Theory.Named.InductiveFixtures
open IndexedVecConsReplay

def indexedVecCtorValidationContext : AddInductive.Context :=
  { indexedVecFamilyCandidate.trace.terminalContext with env := ctorEnv }

def indexedVecValidationAlpha : Expr :=
  indexedVecFamilyCandidateContext.freshExpr

def indexedVecValidationAlphaId : FVarId :=
  indexedVecFamilyCandidateContext.freshFVarId

def indexedVecValidationIndexId : FVarId :=
  ⟨indexedVecFamilyCandidateContext.ngen.next.curr⟩

theorem validationTerminalEnv :
    indexedVecFamilyCandidate.trace.terminalContext.env =
      indexedVecKernelEnv := by
  rfl

theorem validationTerminalLparams :
    indexedVecFamilyCandidate.trace.terminalContext.lparams = [`u] := by
  rfl

theorem validationTerminalAllowPrimitive :
    indexedVecFamilyCandidate.trace.terminalContext.allowPrimitive = false := by
  rfl

theorem validationFamilyEnvNotContains :
    indexedVecKernelEnv.contains ``IndexedVec = false := by
  unfold Kernel.Environment.contains
  change natMap.contains ``IndexedVec = false
  rw [SMap.find?_isSome, indexedVecType_fresh]
  rfl

theorem validationFamilyEnvCheckName :
    indexedVecKernelEnv.checkName ``IndexedVec false = .ok () := by
  simp [Kernel.Environment.checkName, validationFamilyEnvNotContains, Kernel.Environment.primitives,
    NameSet.ofList, NameSet.contains, Pure.pure, Except.pure]

theorem indexedVecDeclareRoot :
    AddInductive.declareInductiveTypes indexedVecCandidateInductiveStats 1
        #[indexedVecKernelType] 0 false
        indexedVecFamilyCandidateContext =
      .ok ctorEnv := by
  simp [AddInductive.declareInductiveTypes,
    indexedVecCandidateInductiveStats_nindices,
    indexedVecCandidateInductiveStats_indConsts,
    indexedVecKernelType, indexedVecKernelNil, indexedVecKernelCons,
    indexedVecInfo, indexedVecNilInfo, indexedVecConsInfo,
    ConstantInfo.name, ConstantInfo.type, ConstantInfo.toConstantVal,
    ctorEnv, indexedVecKernelEnv, indexedVecFamilyCandidateContext,
    indexedVecTypeMap,
    AddInductive.isRec, AddInductive.isRec.loop,
    AddInductive.isReflexive, AddInductive.isReflexive.loop,
    AddInductive.hasIndOcc, Expr.constName!,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  have hcheck :
      (Kernel.Environment.ofConstants `_indexedVecCandidate natMap).checkName
          ``IndexedVec false = .ok () := by
    simpa [indexedVecKernelEnv] using validationFamilyEnvCheckName
  rw [hcheck]
  rfl

theorem indexedVecDeclareFromTerminal :
    AddInductive.declareInductiveTypes indexedVecCandidateInductiveStats 1
        #[indexedVecKernelType] 0 false
        indexedVecFamilyCandidate.trace.terminalContext =
      .ok ctorEnv := by
  calc
    _ = AddInductive.declareInductiveTypes
        indexedVecCandidateInductiveStats 1 #[indexedVecKernelType]
        0 false indexedVecFamilyCandidateContext :=
      AddInductive.declareInductiveTypes_context_eq _ _ _ _ _ _ _
        validationTerminalEnv validationTerminalLparams
        validationTerminalAllowPrimitive
    _ = .ok ctorEnv := indexedVecDeclareRoot

example : indexedVecCtorValidationContext.env = ctorEnv := by rfl
example : indexedVecCtorValidationContext.lparams = [`u] := by rfl
example : indexedVecCtorValidationContext.safety = .safe := by rfl
example : indexedVecCtorValidationContext.allowPrimitive = false := by rfl
example : indexedVecCtorValidationContext.fuel = ({} : FuelConfig) := by rfl
example : indexedVecCtorValidationContext.ngen =
    ({ namePrefix := `_ind_fresh } : NameGenerator).next.next := by rfl

def indexedVecValidationParamName : Name :=
  indexedVecInfo.type.bindingName!

def indexedVecValidationIndexName : Name :=
  indexedVecInfo.type.bindingBody!.bindingName!

def indexedVecValidationParamContext : AddInductive.Context :=
  indexedVecFamilyCandidateContext.pushLocalDecl
    indexedVecValidationParamName .default
      (.sort (.succ (.param `u)))

def indexedVecValidationFamilyContext : AddInductive.Context :=
  indexedVecValidationParamContext.pushLocalDecl
    indexedVecValidationIndexName .default (.const ``Nat [])

theorem indexedVecValidationTerminalContextShape :
    indexedVecFamilyCandidate.trace.terminalContext =
      indexedVecValidationFamilyContext := by
  rfl

theorem indexedVecCtorValidationContextShape :
    indexedVecCtorValidationContext =
      { indexedVecValidationFamilyContext with env := ctorEnv } := by
  rfl

theorem indexedVecValidationParamContextWF :
    indexedVecValidationParamContext.lctx.WF := by
  have hfresh : indexedVecFamilyCandidateContext.lctx.find?
      indexedVecFamilyCandidateContext.freshFVarId = none := by
    have h := LocalContext.WF.find?_eq_find?_toList
      (fv := indexedVecFamilyCandidateContext.freshFVarId)
      LocalContext.WF.nil
    change
      ({ fvarIdToDecl := PersistentHashMap.empty,
         decls := PersistentArray.empty,
         auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
        indexedVecFamilyCandidateContext.freshFVarId = none
    rw [h]
    simp [LocalContext.toList]
  change (({} : LocalContext).mkLocalDecl
    indexedVecFamilyCandidateContext.freshFVarId
    indexedVecValidationParamName
    (.sort (.succ (.param `u))) .default).WF
  exact LocalContext.WF.mkLocalDecl LocalContext.WF.nil hfresh

theorem indexedVecValidationFamilyContextFresh :
    indexedVecValidationParamContext.lctx.find?
      indexedVecValidationParamContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecValidationParamContext.freshFVarId)
    indexedVecValidationParamContextWF
  rw [h]
  simp only [indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  intro heq
  injection heq with hname
  injection hname with hidx
  omega

theorem indexedVecValidationFamilyContextWF :
    indexedVecValidationFamilyContext.lctx.WF := by
  simpa [indexedVecValidationFamilyContext,
    AddInductive.Context.pushLocalDecl] using
      (LocalContext.WF.mkLocalDecl indexedVecValidationParamContextWF
        indexedVecValidationFamilyContextFresh)

theorem indexedVecValidationAlphaFind :
    indexedVecCtorValidationContext.lctx.find?
        indexedVecValidationAlphaId =
      some (.cdecl 0 indexedVecValidationAlphaId
        indexedVecValidationParamName
        (.sort (.succ (.param `u))) .default .default) := by
  change indexedVecValidationFamilyContext.lctx.find?
      indexedVecValidationAlphaId = _
  rw [indexedVecValidationFamilyContextWF.find?_eq_find?_toList]
  simp [indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecValidationAlphaId,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId,
    LocalContext.mkLocalDecl,
    LocalContext.toList, LocalDecl.fvarId,
    NameGenerator.next, NameGenerator.curr]

@[simp] theorem indexedVecValidationAlphaShape : indexedVecValidationAlpha =
    .fvar indexedVecValidationAlphaId := by rfl

theorem localContextFindNew
    (lctx : LocalContext) (id : FVarId) (name : Name)
    (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind)
    (hwf : lctx.WF) (hfresh : lctx.find? id = none) :
    (lctx.mkLocalDecl id name type bi kind).find? id =
      some (.cdecl lctx.decls.size id name type bi kind) := by
  have hwf' := LocalContext.WF.mkLocalDecl
    (name := name) (ty := type) (bi := bi) (kind := kind) hwf hfresh
  rw [hwf'.find?_eq_find?_toList]
  rw [LocalContext.mkLocalDecl_toList]
  simp [LocalDecl.fvarId]

theorem localContextFindOld
    (lctx : LocalContext) (oldId newId : FVarId)
    (newName : Name) (newType : Expr) (newBi : BinderInfo)
    (newKind : LocalDeclKind) (oldDecl : LocalDecl)
    (hwf : lctx.WF) (hfresh : lctx.find? newId = none)
    (hne : oldId ≠ newId) (hold : lctx.find? oldId = some oldDecl) :
    (lctx.mkLocalDecl newId newName newType newBi newKind).find? oldId =
      some oldDecl := by
  have hwf' := LocalContext.WF.mkLocalDecl
    (name := newName) (ty := newType) (bi := newBi)
    (kind := newKind) hwf hfresh
  rw [hwf'.find?_eq_find?_toList]
  rw [LocalContext.mkLocalDecl_toList]
  simp only [List.find?_cons, LocalDecl.fvarId]
  rw [show (oldId == newId) = false by
    exact beq_eq_false_iff_ne.mpr hne]
  rw [hwf.find?_eq_find?_toList] at hold
  simpa only [LocalDecl.fvarId] using hold

def validationFirstAppState (alphaId : FVarId) : TypeChecker.State :=
  replayInsert
    (replayInsert
      (replayInsert ({} : TypeChecker.State)
        (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
      (.fvar alphaId) (.sort (.succ (.param `u))))
    (replayFirstApp (.fvar alphaId)) vecFamilyTail

def validationIndexState (alphaId nId : FVarId) : TypeChecker.State :=
  replayInsert (validationFirstAppState alphaId)
    (.fvar nId) (.const ``Nat [])

def validationIndexedVecState
    (alphaId nId : FVarId) : TypeChecker.State :=
  replayInsert (validationIndexState alphaId nId)
    (ctorIndexedVecApp (.fvar alphaId) (.fvar nId))
    (.sort (.succ (.param `u)))

theorem ctorIndexedVecFVarCheckTypeM
    (lctx : LocalContext) (alphaId nId : FVarId)
    (hne : alphaId ≠ nId)
    (halpha : lctx.find? alphaId = some (.cdecl alphaIndex alphaId
      alphaName (.sort (.succ (.param `u))) alphaBi alphaKind))
    (hn : lctx.find? nId = some (.cdecl nIndex nId nName
      (.const ``Nat []) nBi nKind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType
        (ctorIndexedVecApp (.fvar alphaId) (.fvar nId))) =
      .ok (.sort (.succ (.param `u))) := by
  have hfirst :
      TypeChecker.Inner.inferType'
        (replayFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (vecFamilyTail, validationFirstAppState alphaId) := by
    simpa [validationFirstAppState] using
      (replayInferFirstAppFVarCore 9999 lctx
        ({} : TypeChecker.State) alphaId
        (by simp)
        (by simp [replayInsert])
        (by simp [replayFirstApp])
        halpha)
  have hnmiss :
      (validationFirstAppState alphaId).inferTypeC[
        (.fvar nId : Expr)]? = none := by
    have halphaN :
        ((.fvar alphaId : Expr) == .fvar nId) = false := by
      change Expr.eqv (.fvar alphaId) (.fvar nId) = false
      rw [Expr.eqv_eq]
      simp [Expr.eqv', hne]
    simp [validationFirstAppState, replayInsert, replayFirstApp,
      halphaN]
  have hnrun :
      TypeChecker.Inner.inferType' (.fvar nId) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        (validationFirstAppState alphaId) =
      .ok (.const ``Nat [], validationIndexState alphaId nId) := by
    simpa [validationIndexState, replayInsert] using
      (inferTypeFVarCore 9999 lctx
        (validationFirstAppState alphaId) nId (.const ``Nat [])
        hnmiss hn)
  have htail :
      (({} : TypeChecker.State).inferTypeC[
        ctorIndexedVecApp (.fvar alphaId) (.fvar nId)]?) = none := by
    simp
  have hrun :
      TypeChecker.Inner.inferType'
        (ctorIndexedVecApp (.fvar alphaId) (.fvar nId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.param `u)),
        validationIndexedVecState alphaId nId) := by
    simpa [validationIndexedVecState] using
      (replayInferIndexedVecAppCore 9999 lctx
        ({} : TypeChecker.State) (validationFirstAppState alphaId)
        (validationIndexState alphaId nId)
        (.fvar alphaId) (.fvar nId)
        (by simp [ctorIndexedVecApp, Expr.hasLooseBVars,
          Expr.looseBVarRange'])
        htail hfirst hnrun (by rfl))
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId) (.fvar nId)) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [hrun]
  rfl

def indexedVecValidationNilResult : Expr :=
  ctorIndexedVecApp indexedVecValidationAlpha (.const ``Nat.zero [])

def indexedVecValidationConsAfterParam : Expr :=
  consNTypeRaw.instantiate1 indexedVecValidationAlpha

def indexedVecValidationNId : FVarId :=
  indexedVecCtorValidationContext.freshFVarId

def indexedVecValidationNExpr : Expr :=
  indexedVecCtorValidationContext.freshExpr

@[simp] theorem indexedVecValidationNExprShape :
    indexedVecValidationNExpr = .fvar indexedVecValidationNId := by
  rfl

def indexedVecValidationNContext : AddInductive.Context :=
  indexedVecCtorValidationContext.pushLocalDecl
    consNName .implicit (.const ``Nat [])

def indexedVecValidationConsAfterN : Expr :=
  .forallE consHeadName indexedVecValidationAlpha
    (.forallE consTailName
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
      (ctorIndexedVecApp indexedVecValidationAlpha
        (replaySuccApp indexedVecValidationNExpr))
      .default)
    .default

def indexedVecValidationHeadId : FVarId :=
  indexedVecValidationNContext.freshFVarId

def indexedVecValidationHeadExpr : Expr :=
  indexedVecValidationNContext.freshExpr

@[simp] theorem indexedVecValidationHeadExprShape :
    indexedVecValidationHeadExpr =
      .fvar indexedVecValidationHeadId := by
  rfl

def indexedVecValidationHeadContext : AddInductive.Context :=
  indexedVecValidationNContext.pushLocalDecl
    consHeadName .default indexedVecValidationAlpha

def indexedVecValidationConsAfterHead : Expr :=
  .forallE consTailName
    (ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)
    (ctorIndexedVecApp indexedVecValidationAlpha
      (replaySuccApp indexedVecValidationNExpr))
    .default

def indexedVecValidationTailId : FVarId :=
  indexedVecValidationHeadContext.freshFVarId

def indexedVecValidationTailContext : AddInductive.Context :=
  indexedVecValidationHeadContext.pushLocalDecl consTailName .default
    (ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)

def indexedVecValidationConsResult : Expr :=
  ctorIndexedVecApp indexedVecValidationAlpha
    (replaySuccApp indexedVecValidationNExpr)

theorem indexedVecValidationNilResultShape :
    indexedVecNilInfo.type.bindingBody!.instantiate1
        indexedVecValidationAlpha =
      indexedVecValidationNilResult := by
  simp [indexedVecNilInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, indexedVecValidationNilResult,
    ctorIndexedVecApp, indexedVecValidationAlpha,
    indexedVecFamilyCandidateContext,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero]

theorem indexedVecValidationConsAfterParamShape :
    indexedVecConsInfo.type.bindingBody!.instantiate1
        indexedVecValidationAlpha =
      indexedVecValidationConsAfterParam := by
  rw [consInfoTypeShape]
  rfl

theorem indexedVecValidationConsAfterParamExplicitShape :
    indexedVecValidationConsAfterParam =
      .forallE consNName (.const ``Nat [])
        (.forallE consHeadName indexedVecValidationAlpha
          (.forallE consTailName
            (ctorIndexedVecApp indexedVecValidationAlpha (.bvar 1))
            (ctorIndexedVecApp indexedVecValidationAlpha
              (replaySuccApp (.bvar 2)))
            .default)
          .default)
        .implicit := by
  simp [indexedVecValidationConsAfterParam, consNTypeRaw,
    consHeadTypeRaw, consTailTypeRaw, consTerminalRaw,
    ctorIndexedVecApp, replaySuccApp,
    Expr.instantiate1_eq, Expr.instantiate1']

theorem indexedVecValidationConsAfterNShape :
    indexedVecValidationConsAfterParam.bindingBody!.instantiate1
        indexedVecValidationNExpr =
      indexedVecValidationConsAfterN := by
  simp [indexedVecValidationConsAfterParam, consNTypeRaw,
    consHeadTypeRaw, consTailTypeRaw, consTerminalRaw,
    indexedVecValidationConsAfterN,
    indexedVecValidationNExpr,
    indexedVecValidationAlpha,
    indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    ctorIndexedVecApp, replaySuccApp,
    AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1',
    NameGenerator.curr]

theorem indexedVecValidationConsAfterHeadShape :
    indexedVecValidationConsAfterN.bindingBody!.instantiate1
        indexedVecValidationHeadExpr =
      indexedVecValidationConsAfterHead := by
  simp [indexedVecValidationConsAfterN,
    indexedVecValidationConsAfterHead,
    ctorIndexedVecApp, replaySuccApp,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem indexedVecValidationConsResultShape :
    indexedVecValidationConsAfterHead.bindingBody!.instantiate1
        indexedVecValidationHeadContext.freshExpr =
      indexedVecValidationConsResult := by
  simp [indexedVecValidationConsAfterHead,
    indexedVecValidationConsResult,
    ctorIndexedVecApp, replaySuccApp,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem indexedVecCtorValidationContextWF :
    indexedVecCtorValidationContext.lctx.WF := by
  simpa [indexedVecCtorValidationContextShape] using
    indexedVecValidationFamilyContextWF

theorem indexedVecCtorValidationContextLctxSize :
    indexedVecCtorValidationContext.lctx.decls.size = 2 := by
  change indexedVecFamilyCandidate.trace.terminalContext.lctx.decls.size = 2
  rw [indexedVecValidationTerminalContextShape]
  simp [indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    LocalContext.mkLocalDecl]

theorem indexedVecCtorValidationContextFresh :
    indexedVecCtorValidationContext.lctx.find?
      indexedVecCtorValidationContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecCtorValidationContext.freshFVarId)
    indexedVecCtorValidationContextWF
  rw [h]
  simp only [indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  constructor <;> intro heq
  · injection heq with hname
    injection hname with hidx
    omega
  · injection heq with hname
    injection hname with hidx
    omega

theorem indexedVecValidationNContextWF :
    indexedVecValidationNContext.lctx.WF := by
  simpa [indexedVecValidationNContext,
    AddInductive.Context.pushLocalDecl] using
      (LocalContext.WF.mkLocalDecl indexedVecCtorValidationContextWF
        indexedVecCtorValidationContextFresh)

theorem indexedVecValidationNContextFresh :
    indexedVecValidationNContext.lctx.find?
      indexedVecValidationNContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecValidationNContext.freshFVarId)
    indexedVecValidationNContextWF
  rw [h]
  simp only [indexedVecValidationNContext,
    indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  constructor
  · intro heq
    injection heq with hname
    injection hname with hidx
    omega
  · constructor <;> intro heq
    · injection heq with hname
      injection hname with hidx
      omega
    · injection heq with hname
      injection hname with hidx
      omega

theorem indexedVecValidationHeadContextWF :
    indexedVecValidationHeadContext.lctx.WF := by
  simpa [indexedVecValidationHeadContext,
    AddInductive.Context.pushLocalDecl] using
      (LocalContext.WF.mkLocalDecl indexedVecValidationNContextWF
        indexedVecValidationNContextFresh)

theorem indexedVecValidationAlphaNeN :
    indexedVecValidationAlphaId ≠ indexedVecValidationNId := by
  change indexedVecValidationAlphaId ≠
    indexedVecCtorValidationContext.freshFVarId
  intro heq
  have hfresh := indexedVecCtorValidationContextFresh
  rw [← heq] at hfresh
  rw [indexedVecValidationAlphaFind] at hfresh
  contradiction

theorem indexedVecValidationNNeHead :
    indexedVecValidationNId ≠ indexedVecValidationHeadId := by
  change indexedVecValidationNId ≠
    indexedVecValidationNContext.freshFVarId
  intro heq
  have hfresh := indexedVecValidationNContextFresh
  rw [← heq] at hfresh
  have hnew := localContextFindNew
    indexedVecCtorValidationContext.lctx indexedVecValidationNId
    consNName (.const ``Nat []) .implicit .default
    indexedVecCtorValidationContextWF
    indexedVecCtorValidationContextFresh
  have hfind : indexedVecValidationNContext.lctx.find?
      indexedVecValidationNId = some (.cdecl 2
        indexedVecValidationNId consNName (.const ``Nat [])
        .implicit .default) := by
    rw [indexedVecCtorValidationContextLctxSize] at hnew
    simpa [indexedVecValidationNContext,
      indexedVecValidationNId,
      AddInductive.Context.pushLocalDecl] using hnew
  rw [hfind] at hfresh
  contradiction

theorem indexedVecValidationAlphaFindInN :
    indexedVecValidationNContext.lctx.find?
        indexedVecValidationAlphaId =
      some (.cdecl 0 indexedVecValidationAlphaId
        indexedVecValidationParamName
        (.sort (.succ (.param `u))) .default .default) := by
  have h := localContextFindOld
    (lctx := indexedVecCtorValidationContext.lctx)
    (oldId := indexedVecValidationAlphaId)
    (newId := indexedVecValidationNId)
    (newName := consNName) (newType := .const ``Nat [])
    (newBi := .implicit) (newKind := .default)
    (oldDecl := .cdecl 0 indexedVecValidationAlphaId
      indexedVecValidationParamName (.sort (.succ (.param `u)))
      .default .default)
    indexedVecCtorValidationContextWF
    indexedVecCtorValidationContextFresh
    indexedVecValidationAlphaNeN indexedVecValidationAlphaFind
  simpa [indexedVecValidationNContext,
    indexedVecValidationNId,
    AddInductive.Context.pushLocalDecl] using h

theorem indexedVecValidationNFindInHead :
    indexedVecValidationHeadContext.lctx.find?
        indexedVecValidationNId =
      some (.cdecl 2 indexedVecValidationNId consNName
        (.const ``Nat []) .implicit .default) := by
  have hnew := localContextFindNew
    indexedVecCtorValidationContext.lctx indexedVecValidationNId
    consNName (.const ``Nat []) .implicit .default
    indexedVecCtorValidationContextWF
    indexedVecCtorValidationContextFresh
  have hold : indexedVecValidationNContext.lctx.find?
      indexedVecValidationNId =
      some (.cdecl 2 indexedVecValidationNId consNName
        (.const ``Nat []) .implicit .default) := by
    rw [indexedVecCtorValidationContextLctxSize] at hnew
    simpa [indexedVecValidationNContext,
      indexedVecValidationNId,
      AddInductive.Context.pushLocalDecl] using hnew
  have h := localContextFindOld
    (lctx := indexedVecValidationNContext.lctx)
    (oldId := indexedVecValidationNId)
    (newId := indexedVecValidationHeadId)
    (newName := consHeadName)
    (newType := indexedVecValidationAlpha)
    (newBi := .default) (newKind := .default)
    (oldDecl := .cdecl 2 indexedVecValidationNId consNName
      (.const ``Nat []) .implicit .default)
    indexedVecValidationNContextWF indexedVecValidationNContextFresh
    indexedVecValidationNNeHead hold
  simpa [indexedVecValidationHeadContext,
    indexedVecValidationHeadId,
    AddInductive.Context.pushLocalDecl] using h

theorem indexedVecValidationAlphaFindInHead :
    indexedVecValidationHeadContext.lctx.find?
        indexedVecValidationAlphaId =
      some (.cdecl 0 indexedVecValidationAlphaId
        indexedVecValidationParamName
        (.sort (.succ (.param `u))) .default .default) := by
  have hne : indexedVecValidationAlphaId ≠
      indexedVecValidationHeadId := by
    change indexedVecValidationAlphaId ≠
      indexedVecValidationNContext.freshFVarId
    intro heq
    have hfresh := indexedVecValidationNContextFresh
    rw [← heq] at hfresh
    rw [indexedVecValidationAlphaFindInN] at hfresh
    contradiction
  have h := localContextFindOld
    (lctx := indexedVecValidationNContext.lctx)
    (oldId := indexedVecValidationAlphaId)
    (newId := indexedVecValidationHeadId)
    (newName := consHeadName)
    (newType := indexedVecValidationAlpha)
    (newBi := .default) (newKind := .default)
    (oldDecl := .cdecl 0 indexedVecValidationAlphaId
      indexedVecValidationParamName (.sort (.succ (.param `u)))
      .default .default)
    indexedVecValidationNContextWF indexedVecValidationNContextFresh
    hne indexedVecValidationAlphaFindInN
  simpa [indexedVecValidationHeadContext,
    indexedVecValidationHeadId,
    AddInductive.Context.pushLocalDecl] using h

theorem indexedVecValidationGetTypeAlpha :
    AddInductive.getType indexedVecValidationAlpha
        indexedVecCtorValidationContext =
      .ok (.sort (.succ (.param `u))) := by
  unfold AddInductive.getType
  simp only [getLCtx,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  change Except.ok ((indexedVecCtorValidationContext.lctx.get!
    indexedVecValidationAlpha.fvarId!).type) = _
  rw [show indexedVecValidationAlpha.fvarId! =
      indexedVecValidationAlphaId by
    rw [indexedVecValidationAlphaShape]
    rfl]
  simp [LocalContext.get!, indexedVecValidationAlphaFind,
    LocalDecl.type]

theorem indexedVecValidationParamIsDefEq :
    TypeChecker.M.run indexedVecCtorValidationContext.env
        indexedVecCtorValidationContext.safety
        indexedVecCtorValidationContext.lctx
        indexedVecCtorValidationContext.lparams
        indexedVecCtorValidationContext.fuel
        (TypeChecker.isDefEq (.sort (.succ (.param `u)))
          (.sort (.succ (.param `u)))) = .ok true := by
  exact candidateIsDefEqSelfValid indexedVecCtorValidationContext
    (.sort (.succ (.param `u))) 9999 rfl

theorem indexedVecNilNoMVarNoFVar :
    ctorEnv.checkNoMVarNoFVar indexedVecKernelNil.name
        indexedVecKernelNil.type = .ok () := by
  have hexpr : indexedVecKernelNil.type.data.hasExprMVar = false := by
    change indexedVecNilInfo.type.hasExprMVar = false
    rw [Expr.hasExprMVar_eq]
    rfl
  have hlevel : indexedVecKernelNil.type.data.hasLevelMVar = false := by
    change indexedVecNilInfo.type.hasLevelMVar = false
    rw [Expr.hasLevelMVar_eq]
    simp [indexedVecNilInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.hasLevelMVar',
      Level.hasMVar_eq, Level.hasMVar']
  have hfvar : indexedVecKernelNil.type.data.hasFVar = false := by
    change indexedVecNilInfo.type.hasFVar = false
    rw [Expr.hasFVar_eq]
    rfl
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show indexedVecKernelNil.type.hasMVar = false by
    change (indexedVecKernelNil.type.data.hasExprMVar ||
      indexedVecKernelNil.type.data.hasLevelMVar) = false
    rw [hexpr, hlevel]
    rfl]
  rw [show indexedVecKernelNil.type.hasFVar = false by
    exact hfvar]
  rfl

theorem indexedVecConsNoMVarNoFVar :
    ctorEnv.checkNoMVarNoFVar indexedVecKernelCons.name
        indexedVecKernelCons.type = .ok () := by
  have hexpr : indexedVecKernelCons.type.data.hasExprMVar = false := by
    change indexedVecConsInfo.type.hasExprMVar = false
    rw [Expr.hasExprMVar_eq]
    rfl
  have hlevel : indexedVecKernelCons.type.data.hasLevelMVar = false := by
    change indexedVecConsInfo.type.hasLevelMVar = false
    rw [Expr.hasLevelMVar_eq]
    simp [indexedVecConsInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.hasLevelMVar',
      Level.hasMVar_eq, Level.hasMVar']
  have hfvar : indexedVecKernelCons.type.data.hasFVar = false := by
    change indexedVecConsInfo.type.hasFVar = false
    rw [Expr.hasFVar_eq]
    rfl
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show indexedVecKernelCons.type.hasMVar = false by
    change (indexedVecKernelCons.type.data.hasExprMVar ||
      indexedVecKernelCons.type.data.hasLevelMVar) = false
    rw [hexpr, hlevel]
    rfl]
  rw [show indexedVecKernelCons.type.hasFVar = false by
    exact hfvar]
  rfl

theorem indexedVecValidationNilRootCheckTypeM :
    TypeChecker.M.run indexedVecCtorValidationContext.env
        indexedVecCtorValidationContext.safety {}
        indexedVecCtorValidationContext.lparams
        indexedVecCtorValidationContext.fuel
        (TypeChecker.checkType indexedVecKernelNil.type) =
      .ok (.sort nilCtorInferredLevel) := by
  change TypeChecker.M.run ctorEnv .safe {} [`u] ({} : FuelConfig)
    (TypeChecker.checkType indexedVecKernelNil.type) =
      .ok (.sort nilCtorInferredLevel)
  simpa [indexedVecKernelNil] using nilRootCheckTypeM

theorem indexedVecValidationConsRootCheckTypeM :
    TypeChecker.M.run indexedVecCtorValidationContext.env
        indexedVecCtorValidationContext.safety {}
        indexedVecCtorValidationContext.lparams
        indexedVecCtorValidationContext.fuel
        (TypeChecker.checkType indexedVecKernelCons.type) =
      .ok (.sort (.succ (.succ (.param `u)))) := by
  change TypeChecker.M.run ctorEnv .safe {} [`u] ({} : FuelConfig)
    (TypeChecker.checkType indexedVecKernelCons.type) =
      .ok (.sort (.succ (.succ (.param `u))))
  simpa [indexedVecKernelCons, consRootContext, ctorContext] using
    replayConsRootCheckTypeM

def validationInferOnlyInsert
    (state : TypeChecker.State) (e type : Expr) : TypeChecker.State :=
  { state with inferTypeI := state.inferTypeI.insert e type }

@[simp] theorem inferConstantFamilyOnly (lctx : LocalContext) :
    TypeChecker.Inner.inferConstant (tcContext lctx) ``IndexedVec
      [.param `u] true = .ok indexedVecInfo.type := by
  unfold TypeChecker.Inner.inferConstant
  simp only [tcContext]
  rw [type_get_family]
  simp [indexedVecInfo,
    ConstantInfo.levelParams, ConstantInfo.type,
    ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq,
    Expr.instantiateLevelParamsCore', Level.substParams',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] theorem inferConstantNatOnly (lctx : LocalContext) :
    TypeChecker.Inner.inferConstant (tcContext lctx) ``Nat [] true =
      .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.Inner.inferConstant
  simp [tcContext, natInfo,
    ConstantInfo.levelParams, ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq,
    Expr.instantiateLevelParamsCore', Level.substParams',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem inferTypeNatOnlyCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache : state.inferTypeI[(.const ``Nat [] : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.const ``Nat []) true
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.sort (.succ .zero),
          validationInferOnlyInsert state (.const ``Nat [])
            (.sort (.succ .zero))) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    validationInferOnlyInsert, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem inferTypeFamilyOnlyCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache : state.inferTypeI[
      (.const ``IndexedVec [.param `u] : Expr)]? = none) :
    TypeChecker.Inner.inferType'
      (.const ``IndexedVec [.param `u]) true
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (indexedVecInfo.type,
          validationInferOnlyInsert state
            (.const ``IndexedVec [.param `u]) indexedVecInfo.type) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    validationInferOnlyInsert, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem inferTypeFVarOnlyCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (id : FVarId) (type : Expr)
    (hcache : state.inferTypeI[(.fvar id : Expr)]? = none)
    (hfind : lctx.find? id = some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType' (.fvar id) true
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (type, validationInferOnlyInsert state (.fvar id) type) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    TypeChecker.Inner.inferFVar, tcContext, hfind, LocalDecl.type,
    validationInferOnlyInsert, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

def validationFamilyOnlyState : TypeChecker.State :=
  validationInferOnlyInsert ({} : TypeChecker.State)
    (.const ``IndexedVec [.param `u]) indexedVecInfo.type

def validationIndexedVecOnlyState
    (alpha index : Expr) : TypeChecker.State :=
  validationInferOnlyInsert validationFamilyOnlyState
    (ctorIndexedVecApp alpha index) (.sort (.succ (.param `u)))

@[simp] theorem ctorIndexedVecAppGetAppArgs (alpha index : Expr) :
    (ctorIndexedVecApp alpha index).getAppArgs = #[alpha, index] := by
  rfl

@[simp] theorem ctorIndexedVecAppGetAppNumArgs (alpha index : Expr) :
    (ctorIndexedVecApp alpha index).getAppNumArgs = 2 := by
  rfl

theorem inferTypeIndexedVecOnlyCore
    (fuel : Nat) (lctx : LocalContext) (alpha index : Expr)
    (hclosed : (ctorIndexedVecApp alpha index).hasLooseBVars = false) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp alpha index) true
      (TypeChecker.Methods.withFuel (fuel + 1)) (tcContext lctx)
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          validationIndexedVecOnlyState alpha index) := by
  unfold ctorIndexedVecApp at hclosed ⊢
  have hfn :
      (((.const ``IndexedVec [.param `u] : Expr).app alpha).app index).getAppFn =
        .const ``IndexedVec [.param `u] := by
    rfl
  have hargs :
      (((.const ``IndexedVec [.param `u] : Expr).app alpha).app index).getAppArgs =
        #[alpha, index] := by
    rfl
  unfold TypeChecker.Inner.inferType'
  rw [hclosed]
  simp [TypeChecker.Inner.inferApp,
    TypeChecker.Inner.inferApp.loop,
    hfn, hargs, ctorIndexedVecApp,
    validationFamilyOnlyState, validationIndexedVecOnlyState,
    validationInferOnlyInsert,
    inferTypeFamilyOnlyCore,
    indexedVecInfoTypeShape, vecFamilyTail,
    Expr.instantiate1',
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem ensureTypeMOfInferOnly
    (context : AddInductive.Context) (e : Expr) (level : Level)
    (finalState : TypeChecker.State)
    (hrun : TypeChecker.Inner.inferType e true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort level, finalState)) :
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.ensureType e) =
      .ok (.sort level) := by
  unfold TypeChecker.ensureType TypeChecker.inferType
    TypeChecker.ensureSort TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType e true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      { env := context.env, lctx := context.lctx,
        safety := context.safety, lparams := context.lparams,
        fuel := context.fuel } ({} : TypeChecker.State) =
        .ok (.sort level, finalState) by
    simpa [AddInductive.Context.toTypeChecker] using hrun]
  rfl

def validationNatOnlyState : TypeChecker.State :=
  validationInferOnlyInsert ({} : TypeChecker.State)
    (.const ``Nat []) (.sort (.succ .zero))

theorem indexedVecValidationNatInferOnly :
    TypeChecker.Inner.inferType (.const ``Nat []) true
      (TypeChecker.Methods.withFuel
        indexedVecCtorValidationContext.fuel.recDepth)
      indexedVecCtorValidationContext.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), validationNatOnlyState) := by
  change TypeChecker.Inner.inferType' (.const ``Nat []) true
    (TypeChecker.Methods.withFuel 9999)
    (tcContext indexedVecCtorValidationContext.lctx)
    ({} : TypeChecker.State) = _
  simpa [validationNatOnlyState] using
    (inferTypeNatOnlyCore 9999 indexedVecCtorValidationContext.lctx
      ({} : TypeChecker.State) (by simp))

theorem indexedVecValidationNatEnsureTypeM :
    TypeChecker.M.run indexedVecCtorValidationContext.env
        indexedVecCtorValidationContext.safety
        indexedVecCtorValidationContext.lctx
        indexedVecCtorValidationContext.lparams
        indexedVecCtorValidationContext.fuel
        (TypeChecker.ensureType (.const ``Nat [])) =
      .ok (.sort (.succ .zero)) := by
  exact ensureTypeMOfInferOnly indexedVecCtorValidationContext
    (.const ``Nat []) (.succ .zero) validationNatOnlyState
    indexedVecValidationNatInferOnly

def validationAlphaOnlyState : TypeChecker.State :=
  validationInferOnlyInsert ({} : TypeChecker.State)
    indexedVecValidationAlpha (.sort (.succ (.param `u)))

theorem indexedVecValidationAlphaInferOnly :
    TypeChecker.Inner.inferType indexedVecValidationAlpha true
      (TypeChecker.Methods.withFuel
        indexedVecValidationNContext.fuel.recDepth)
      indexedVecValidationNContext.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)), validationAlphaOnlyState) := by
  rw [indexedVecValidationAlphaShape]
  change TypeChecker.Inner.inferType'
      (.fvar indexedVecValidationAlphaId) true
      (TypeChecker.Methods.withFuel 9999)
      (tcContext indexedVecValidationNContext.lctx)
      ({} : TypeChecker.State) = _
  simpa [validationAlphaOnlyState,
    indexedVecValidationAlphaShape] using
    (inferTypeFVarOnlyCore 9999 indexedVecValidationNContext.lctx
      ({} : TypeChecker.State) indexedVecValidationAlphaId
      (.sort (.succ (.param `u))) (by simp)
      indexedVecValidationAlphaFindInN)

theorem indexedVecValidationAlphaEnsureTypeM :
    TypeChecker.M.run indexedVecValidationNContext.env
        indexedVecValidationNContext.safety
        indexedVecValidationNContext.lctx
        indexedVecValidationNContext.lparams
        indexedVecValidationNContext.fuel
        (TypeChecker.ensureType indexedVecValidationAlpha) =
      .ok (.sort (.succ (.param `u))) := by
  exact ensureTypeMOfInferOnly indexedVecValidationNContext
    indexedVecValidationAlpha (.succ (.param `u))
    validationAlphaOnlyState indexedVecValidationAlphaInferOnly

theorem indexedVecValidationTailInferOnly :
    TypeChecker.Inner.inferType
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) true
      (TypeChecker.Methods.withFuel
        indexedVecValidationHeadContext.fuel.recDepth)
      indexedVecValidationHeadContext.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          validationIndexedVecOnlyState indexedVecValidationAlpha
            indexedVecValidationNExpr) := by
  change TypeChecker.Inner.inferType'
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) true
      (TypeChecker.Methods.withFuel 9999)
      (tcContext indexedVecValidationHeadContext.lctx)
      ({} : TypeChecker.State) = _
  exact inferTypeIndexedVecOnlyCore 9998
    indexedVecValidationHeadContext.lctx
    indexedVecValidationAlpha indexedVecValidationNExpr
    (by simp [ctorIndexedVecApp, Expr.hasLooseBVars,
      Expr.looseBVarRange'])

theorem indexedVecValidationTailEnsureTypeM :
    TypeChecker.M.run indexedVecValidationHeadContext.env
        indexedVecValidationHeadContext.safety
        indexedVecValidationHeadContext.lctx
        indexedVecValidationHeadContext.lparams
        indexedVecValidationHeadContext.fuel
        (TypeChecker.ensureType
          (ctorIndexedVecApp indexedVecValidationAlpha
            indexedVecValidationNExpr)) =
      .ok (.sort (.succ (.param `u))) := by
  exact ensureTypeMOfInferOnly indexedVecValidationHeadContext
    (ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr) (.succ (.param `u))
    (validationIndexedVecOnlyState indexedVecValidationAlpha
      indexedVecValidationNExpr)
    indexedVecValidationTailInferOnly

theorem indexedVecValidationStatsParams :
    indexedVecCandidateInductiveStats.params =
      #[indexedVecValidationAlpha] := by
  simpa [indexedVecValidationAlpha] using
    indexedVecCandidateInductiveStats_params

@[simp] theorem validationExprBneSelf (e : Expr) :
    (e != e) = false := by
  change (!Expr.eqv e e) = false
  rw [show Expr.eqv e e = true by exact Expr.eqv_refl e]
  rfl

theorem indexedVecValidationAppIsValidIdx (index : Expr)
    (hindex : AddInductive.hasIndOcc
      indexedVecCandidateInductiveStats.indConsts index = false) :
    AddInductive.isValidIndAppIdx indexedVecCandidateInductiveStats
      (ctorIndexedVecApp indexedVecValidationAlpha index) 0 = true := by
  have hparam :
      (indexedVecValidationAlpha != indexedVecValidationAlpha) = false := by
    change (!Expr.eqv indexedVecValidationAlpha
      indexedVecValidationAlpha) = false
    rw [show Expr.eqv indexedVecValidationAlpha
      indexedVecValidationAlpha = true by
      exact Expr.eqv_refl indexedVecValidationAlpha]
    rfl
  have hindex' : AddInductive.hasIndOcc
      #[.const ``IndexedVec [.param `u]] index = false := by
    simpa [indexedVecCandidateInductiveStats_indConsts] using hindex
  simp +decide [AddInductive.isValidIndAppIdx,
    indexedVecCandidateInductiveStats_nindices,
    indexedVecValidationStatsParams,
    indexedVecCandidateInductiveStats_indConsts,
    ctorIndexedVecAppGetAppFn, ctorIndexedVecAppGetAppArgs,
    hindex']

theorem indexedVecValidationAppIsValid (index : Expr)
    (hindex : AddInductive.hasIndOcc
      indexedVecCandidateInductiveStats.indConsts index = false) :
    AddInductive.isValidIndApp? indexedVecCandidateInductiveStats
      (ctorIndexedVecApp indexedVecValidationAlpha index) = some 0 := by
  exact AddInductive.isValidIndApp?_singleton_zero
    indexedVecCandidateInductiveStats
    (ctorIndexedVecApp indexedVecValidationAlpha index)
    (by simp [indexedVecCandidateInductiveStats_indConsts])
    (indexedVecValidationAppIsValidIdx index hindex)

theorem indexedVecValidationZeroHasNoIndOcc :
    AddInductive.hasIndOcc indexedVecCandidateInductiveStats.indConsts
      (.const ``Nat.zero []) = false := by
  simp [AddInductive.hasIndOcc,
    indexedVecCandidateInductiveStats_indConsts, Expr.constName!]

theorem indexedVecValidationNHasNoIndOcc :
    AddInductive.hasIndOcc indexedVecCandidateInductiveStats.indConsts
      indexedVecValidationNExpr = false := by
  simp [AddInductive.hasIndOcc,
    indexedVecCandidateInductiveStats_indConsts,
    indexedVecValidationNExprShape]

theorem indexedVecValidationSuccNHasNoIndOcc :
    AddInductive.hasIndOcc indexedVecCandidateInductiveStats.indConsts
      (replaySuccApp indexedVecValidationNExpr) = false := by
  simp [AddInductive.hasIndOcc,
    indexedVecCandidateInductiveStats_indConsts,
    replaySuccApp, Expr.constName!]

theorem indexedVecValidationNilResultIsValid :
    AddInductive.isValidIndAppIdx indexedVecCandidateInductiveStats
      indexedVecValidationNilResult 0 = true := by
  exact indexedVecValidationAppIsValidIdx (.const ``Nat.zero [])
    indexedVecValidationZeroHasNoIndOcc

theorem indexedVecValidationConsResultIsValid :
    AddInductive.isValidIndAppIdx indexedVecCandidateInductiveStats
      indexedVecValidationConsResult 0 = true := by
  exact indexedVecValidationAppIsValidIdx
    (replaySuccApp indexedVecValidationNExpr)
    indexedVecValidationSuccNHasNoIndOcc

theorem indexedVecValidationNatHasNoIndOcc :
    AddInductive.hasIndOcc indexedVecCandidateInductiveStats.indConsts
      (.const ``Nat []) = false := by
  simp [AddInductive.hasIndOcc,
    indexedVecCandidateInductiveStats_indConsts, Expr.constName!]

theorem indexedVecValidationAlphaHasNoIndOcc :
    AddInductive.hasIndOcc indexedVecCandidateInductiveStats.indConsts
      indexedVecValidationAlpha = false := by
  simp [AddInductive.hasIndOcc,
    indexedVecCandidateInductiveStats_indConsts,
    indexedVecValidationAlphaShape]

theorem indexedVecValidationTailHasIndOcc :
    AddInductive.hasIndOcc indexedVecCandidateInductiveStats.indConsts
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) = true := by
  simp [AddInductive.hasIndOcc,
    indexedVecCandidateInductiveStats_indConsts,
    ctorIndexedVecApp, Expr.constName!]

theorem indexedVecValidationNatPositivity :
    AddInductive.checkPositivity indexedVecCandidateInductiveStats
      (.const ``Nat []) indexedVecKernelCons.name 1
      indexedVecCtorValidationContext = .ok () := by
  unfold AddInductive.checkPositivity
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show indexedVecCtorValidationContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkPositivity.loop
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [show TypeChecker.M.run indexedVecCtorValidationContext.env
      indexedVecCtorValidationContext.safety
      indexedVecCtorValidationContext.lctx
      indexedVecCtorValidationContext.lparams
      indexedVecCtorValidationContext.fuel
      (TypeChecker.whnf (.const ``Nat [])) =
        .ok (.const ``Nat []) by
    change TypeChecker.M.run ctorEnv .safe
      indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
      (TypeChecker.whnf (.const ``Nat [])) = .ok (.const ``Nat [])
    exact ctorNatWhnfM indexedVecCtorValidationContext.lctx]
  simp only [Except.bind]
  rw [indexedVecValidationNatHasNoIndOcc]
  simp only [Bool.not_false, if_true,
    ReaderT.pure, Pure.pure, Except.pure]

theorem indexedVecValidationAlphaPositivity :
    AddInductive.checkPositivity indexedVecCandidateInductiveStats
      indexedVecValidationAlpha indexedVecKernelCons.name 2
      indexedVecValidationNContext = .ok () := by
  unfold AddInductive.checkPositivity
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show indexedVecValidationNContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkPositivity.loop
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [show TypeChecker.M.run indexedVecValidationNContext.env
      indexedVecValidationNContext.safety
      indexedVecValidationNContext.lctx
      indexedVecValidationNContext.lparams
      indexedVecValidationNContext.fuel
      (TypeChecker.whnf indexedVecValidationAlpha) =
        .ok indexedVecValidationAlpha by
    rw [indexedVecValidationAlphaShape]
    change TypeChecker.M.run ctorEnv .safe
      indexedVecValidationNContext.lctx [`u] ({} : FuelConfig)
      (TypeChecker.whnf (.fvar indexedVecValidationAlphaId)) =
        .ok (.fvar indexedVecValidationAlphaId)
    exact ctorFVarWhnfM indexedVecValidationNContext.lctx
      indexedVecValidationAlphaId indexedVecValidationAlphaFindInN]
  simp only [Except.bind]
  rw [indexedVecValidationAlphaHasNoIndOcc]
  simp only [Bool.not_false, if_true,
    ReaderT.pure, Pure.pure, Except.pure]

theorem indexedVecValidationTailPositivity :
    AddInductive.checkPositivity indexedVecCandidateInductiveStats
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
      indexedVecKernelCons.name 3 indexedVecValidationHeadContext =
      .ok () := by
  unfold AddInductive.checkPositivity
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure,
    Except.bind, Except.pure]
  rw [show indexedVecValidationHeadContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkPositivity.loop
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [show TypeChecker.M.run indexedVecValidationHeadContext.env
      indexedVecValidationHeadContext.safety
      indexedVecValidationHeadContext.lctx
      indexedVecValidationHeadContext.lparams
      indexedVecValidationHeadContext.fuel
      (TypeChecker.whnf
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)) =
        .ok (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr) by
    change TypeChecker.M.run ctorEnv .safe
      indexedVecValidationHeadContext.lctx [`u] ({} : FuelConfig)
      (TypeChecker.whnf
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)) =
        .ok (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)
    exact ctorIndexedVecWhnfM indexedVecValidationHeadContext.lctx
      indexedVecValidationAlpha indexedVecValidationNExpr]
  simp only [Except.bind]
  rw [indexedVecValidationTailHasIndOcc]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, Pure.pure]
  rw [indexedVecValidationAppIsValid indexedVecValidationNExpr
    indexedVecValidationNHasNoIndOcc]
  rfl

theorem indexedVecValidationNilLoopTerminal :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelNil.name indexedVecValidationNilResult 1 999
      indexedVecCtorValidationContext = .ok () := by
  rw [show 999 = 998 + 1 by rfl]
  have hvalid : AddInductive.isValidIndAppIdx
      indexedVecCandidateInductiveStats
      ((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar indexedVecValidationAlphaId) |>.app
          (.const ``Nat.zero [])) 0 =
      true := by
    simpa [indexedVecValidationNilResult, ctorIndexedVecApp,
      indexedVecValidationAlphaShape] using
      indexedVecValidationNilResultIsValid
  unfold indexedVecValidationNilResult ctorIndexedVecApp
  unfold AddInductive.checkConstructorType.loop
  simp [hvalid,
    ReaderT.pure, Pure.pure, Except.pure]

theorem indexedVecValidationNilLoop :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelNil.name indexedVecKernelNil.type 0
      indexedVecCtorValidationContext.fuel.inductiveFuel
      indexedVecCtorValidationContext = .ok () := by
  rw [show indexedVecCtorValidationContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkConstructorType.loop
  simp only [indexedVecKernelNil, indexedVecNilInfo,
    ConstantInfo.name, ConstantInfo.type, ConstantInfo.toConstantVal]
  rw [show indexedVecCandidateInductiveStats.params[0]? =
      some indexedVecValidationAlpha by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind]
  rw [indexedVecValidationGetTypeAlpha]
  simp only [Except.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationParamIsDefEq]
  simp only [if_true]
  simpa [indexedVecValidationNilResult, ctorIndexedVecApp,
    indexedVecKernelNil, indexedVecNilInfo, ConstantInfo.name,
    ConstantInfo.toConstantVal,
    Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero] using indexedVecValidationNilLoopTerminal

@[simp] theorem indexedVecValidationConsumeNat :
    AddInductive.consumeTypeAnnotations (.const ``Nat []) =
      .const ``Nat [] := by
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem indexedVecValidationConsumeAlpha :
    AddInductive.consumeTypeAnnotations indexedVecValidationAlpha =
      indexedVecValidationAlpha := by
  rw [indexedVecValidationAlphaShape]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem indexedVecValidationConsumeTail :
    AddInductive.consumeTypeAnnotations
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) =
      ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr := by
  simp [ctorIndexedVecApp, AddInductive.consumeTypeAnnotations]

theorem indexedVecValidationConsLoopTerminal :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelCons.name indexedVecValidationConsResult 4 996
      indexedVecValidationTailContext = .ok () := by
  rw [show 996 = 995 + 1 by rfl]
  have hvalid : AddInductive.isValidIndAppIdx
      indexedVecCandidateInductiveStats
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar indexedVecValidationAlphaId)).app
          ((.const ``Nat.succ [] : Expr).app
            (.fvar indexedVecValidationNId))) 0 = true := by
    simpa [indexedVecValidationConsResult, ctorIndexedVecApp,
      replaySuccApp, indexedVecValidationAlphaShape,
      indexedVecValidationNExprShape] using
        indexedVecValidationConsResultIsValid
  unfold indexedVecValidationConsResult ctorIndexedVecApp replaySuccApp
  unfold AddInductive.checkConstructorType.loop
  simp [hvalid, ReaderT.pure, Pure.pure, Except.pure]

theorem indexedVecValidationConsLoopTail :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelCons.name indexedVecValidationConsAfterHead 3 997
      indexedVecValidationHeadContext = .ok () := by
  rw [show 997 = 996 + 1 by rfl]
  unfold indexedVecValidationConsAfterHead
  unfold AddInductive.checkConstructorType.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[3]? = none by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationTailEnsureTypeM]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.levelStructGe
      indexedVecCandidateInductiveStats.resultLevel
      (Expr.sort (.succ (.param `u))).sortLevel! = true from by
    simp [Expr.sortLevel!, indexedVecCandidateInductiveStats_resultLevel,
      AddInductive.levelStructGe, AddInductive.levelStructEq])]
  simp only [↓reduceIte, Bool.not_false, ReaderT.bind, Bind.bind, Except.bind]
  rw [indexedVecValidationTailPositivity]
  rw [AddInductive.withLocalDecl_apply]
  rw [indexedVecValidationConsumeTail]
  rw [show (ctorIndexedVecApp indexedVecValidationAlpha
      (replaySuccApp indexedVecValidationNExpr)).instantiate1
        indexedVecValidationHeadContext.freshExpr =
      indexedVecValidationConsResult by
    simp [indexedVecValidationConsResult, ctorIndexedVecApp,
      replaySuccApp, Expr.instantiate1_eq, Expr.instantiate1']]
  simpa [indexedVecValidationTailContext,
    AddInductive.Context.pushLocalDecl,
    ReaderT.pure, Pure.pure, Except.pure] using
      indexedVecValidationConsLoopTerminal

theorem indexedVecValidationConsLoopHead :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelCons.name indexedVecValidationConsAfterN 2 998
      indexedVecValidationNContext = .ok () := by
  rw [show 998 = 997 + 1 by rfl]
  unfold indexedVecValidationConsAfterN
  unfold AddInductive.checkConstructorType.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[2]? = none by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationAlphaEnsureTypeM]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.levelStructGe
      indexedVecCandidateInductiveStats.resultLevel
      (Expr.sort (.succ (.param `u))).sortLevel! = true from by
    simp [Expr.sortLevel!, indexedVecCandidateInductiveStats_resultLevel,
      AddInductive.levelStructGe, AddInductive.levelStructEq])]
  simp only [↓reduceIte, Bool.not_false, ReaderT.bind, Bind.bind, Except.bind]
  rw [indexedVecValidationAlphaPositivity]
  rw [AddInductive.withLocalDecl_apply]
  rw [indexedVecValidationConsumeAlpha]
  rw [show
      ((.forallE consTailName
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)
        (ctorIndexedVecApp indexedVecValidationAlpha
          (replaySuccApp indexedVecValidationNExpr))
        .default : Expr).instantiate1
          indexedVecValidationNContext.freshExpr) =
        indexedVecValidationConsAfterHead by
    simp [indexedVecValidationConsAfterHead,
      ctorIndexedVecApp, replaySuccApp,
      Expr.instantiate1_eq, Expr.instantiate1']]
  simpa [indexedVecValidationHeadContext,
    AddInductive.Context.pushLocalDecl,
    ReaderT.pure, Pure.pure, Except.pure] using
      indexedVecValidationConsLoopTail

theorem indexedVecValidationConsLoopN :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelCons.name indexedVecValidationConsAfterParam 1 999
      indexedVecCtorValidationContext = .ok () := by
  rw [show 999 = 998 + 1 by rfl]
  rw [indexedVecValidationConsAfterParamExplicitShape]
  unfold AddInductive.checkConstructorType.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[1]? = none by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationNatEnsureTypeM]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.levelStructGe
      indexedVecCandidateInductiveStats.resultLevel
      (Expr.sort (.succ .zero)).sortLevel! = true from by
    simp [Expr.sortLevel!, indexedVecCandidateInductiveStats_resultLevel,
      AddInductive.levelStructGe])]
  simp only [↓reduceIte, Bool.not_false, ReaderT.bind, Bind.bind, Except.bind]
  rw [indexedVecValidationNatPositivity]
  rw [AddInductive.withLocalDecl_apply]
  rw [indexedVecValidationConsumeNat]
  rw [show
      ((.forallE consHeadName indexedVecValidationAlpha
        (.forallE consTailName
          (ctorIndexedVecApp indexedVecValidationAlpha (.bvar 1))
          (ctorIndexedVecApp indexedVecValidationAlpha
            (replaySuccApp (.bvar 2)))
          .default)
        .default : Expr).instantiate1
          indexedVecCtorValidationContext.freshExpr) =
        indexedVecValidationConsAfterN by
    simp [indexedVecValidationConsAfterN,
      ctorIndexedVecApp, replaySuccApp,
      indexedVecValidationNExpr,
      AddInductive.Context.freshExpr,
      Expr.instantiate1_eq, Expr.instantiate1']]
  simpa [indexedVecValidationNContext,
    AddInductive.Context.pushLocalDecl,
    ReaderT.pure, Pure.pure, Except.pure] using
      indexedVecValidationConsLoopHead

theorem indexedVecValidationConsLoop :
    AddInductive.checkConstructorType.loop
      indexedVecCandidateInductiveStats false 0
      indexedVecKernelCons.name indexedVecKernelCons.type 0
      indexedVecCtorValidationContext.fuel.inductiveFuel
      indexedVecCtorValidationContext = .ok () := by
  rw [show indexedVecCtorValidationContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  rw [show indexedVecKernelCons.type = consCtorTypeRaw by
    simpa [indexedVecKernelCons] using consInfoTypeShape]
  unfold consCtorTypeRaw
  unfold AddInductive.checkConstructorType.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[0]? =
      some indexedVecValidationAlpha by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind]
  rw [indexedVecValidationGetTypeAlpha]
  simp only [Except.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationParamIsDefEq]
  simp only [if_true]
  simpa [indexedVecValidationConsAfterParam] using
    indexedVecValidationConsLoopN

theorem indexedVecValidationNilUniverseLoopTerminal :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecValidationNilResult 1 999
      indexedVecCtorValidationContext = .ok () := by
  rw [show 999 = 998 + 1 by rfl]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  rfl

theorem indexedVecValidationNilUniverseLoop :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecKernelNil.type 0
      indexedVecCtorValidationContext.fuel.inductiveFuel
      indexedVecCtorValidationContext = .ok () := by
  rw [show indexedVecCtorValidationContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  simp only [indexedVecKernelNil, indexedVecNilInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal]
  rw [show indexedVecCandidateInductiveStats.params[0]? =
      some indexedVecValidationAlpha by
    simp [indexedVecValidationStatsParams]]
  simpa [indexedVecValidationNilResult, ctorIndexedVecApp,
    indexedVecKernelNil, indexedVecNilInfo, ConstantInfo.toConstantVal,
    Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero] using
      indexedVecValidationNilUniverseLoopTerminal

theorem indexedVecValidationConsUniverseLoopTerminal :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecValidationConsResult 4 996
      indexedVecValidationTailContext = .ok () := by
  rw [show 996 = 995 + 1 by rfl]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  rfl

theorem indexedVecValidationConsUniverseLoopTail :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecValidationConsAfterHead 3 997
      indexedVecValidationHeadContext = .ok () := by
  rw [show 997 = 996 + 1 by rfl]
  unfold indexedVecValidationConsAfterHead
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[3]? = none by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind, AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationTailEnsureTypeM]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.constructorUniverseSemanticGe
      indexedVecCandidateInductiveStats.resultLevel
      (Expr.sort (.succ (.param `u))).sortLevel! = true from by
    simp [Expr.sortLevel!, AddInductive.constructorUniverseSemanticGe,
      indexedVecCandidateInductiveStats_resultLevel,
      AddInductive.levelStructGe, AddInductive.levelStructEq])]
  rw [AddInductive.withLocalDecl_apply]
  simpa [indexedVecValidationTailContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.consumeTypeAnnotations,
    indexedVecValidationConsResult, ctorIndexedVecApp,
    replaySuccApp, Expr.instantiate1_eq, Expr.instantiate1'] using
      indexedVecValidationConsUniverseLoopTerminal

theorem indexedVecValidationConsUniverseLoopHead :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecValidationConsAfterN 2 998
      indexedVecValidationNContext = .ok () := by
  rw [show 998 = 997 + 1 by rfl]
  unfold indexedVecValidationConsAfterN
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[2]? = none by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind, AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationAlphaEnsureTypeM]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.constructorUniverseSemanticGe
      indexedVecCandidateInductiveStats.resultLevel
      (Expr.sort (.succ (.param `u))).sortLevel! = true from by
    simp [Expr.sortLevel!, AddInductive.constructorUniverseSemanticGe,
      indexedVecCandidateInductiveStats_resultLevel,
      AddInductive.levelStructGe, AddInductive.levelStructEq])]
  rw [AddInductive.withLocalDecl_apply]
  simpa [indexedVecValidationHeadContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.consumeTypeAnnotations,
    indexedVecValidationConsAfterHead,
    ctorIndexedVecApp, replaySuccApp,
    Expr.instantiate1_eq, Expr.instantiate1'] using
      indexedVecValidationConsUniverseLoopTail

theorem indexedVecValidationConsUniverseLoopN :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecValidationConsAfterParam 1 999
      indexedVecCtorValidationContext = .ok () := by
  rw [show 999 = 998 + 1 by rfl]
  rw [indexedVecValidationConsAfterParamExplicitShape]
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[1]? = none by
    simp [indexedVecValidationStatsParams]]
  simp only [ReaderT.bind, Bind.bind, AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationNatEnsureTypeM]
  simp only [Except.bind]
  rw [if_pos (show AddInductive.constructorUniverseSemanticGe
      indexedVecCandidateInductiveStats.resultLevel
      (Expr.sort (.succ .zero)).sortLevel! = true from by
    simp [Expr.sortLevel!, AddInductive.constructorUniverseSemanticGe,
      indexedVecCandidateInductiveStats_resultLevel,
      AddInductive.levelStructGe])]
  rw [AddInductive.withLocalDecl_apply]
  simpa [indexedVecValidationNContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.consumeTypeAnnotations,
    indexedVecValidationConsAfterN,
    ctorIndexedVecApp, replaySuccApp,
    indexedVecValidationNExpr,
    AddInductive.Context.freshExpr,
    Expr.instantiate1_eq, Expr.instantiate1'] using
      indexedVecValidationConsUniverseLoopHead

theorem indexedVecValidationConsUniverseLoop :
    AddInductive.checkConstructorUniverseSemantics.loop
      indexedVecCandidateInductiveStats indexedVecKernelCons.type 0
      indexedVecCtorValidationContext.fuel.inductiveFuel
      indexedVecCtorValidationContext = .ok () := by
  rw [show indexedVecCtorValidationContext.fuel.inductiveFuel =
      999 + 1 by rfl]
  rw [show indexedVecKernelCons.type = consCtorTypeRaw by
    simpa [indexedVecKernelCons] using consInfoTypeShape]
  unfold consCtorTypeRaw
  unfold AddInductive.checkConstructorUniverseSemantics.loop
  simp only
  rw [show indexedVecCandidateInductiveStats.params[0]? =
      some indexedVecValidationAlpha by
    simp [indexedVecValidationStatsParams]]
  simpa [indexedVecValidationConsAfterParam] using
    indexedVecValidationConsUniverseLoopN

theorem indexedVecValidationNilUniverseRun :
    AddInductive.checkConstructorUniverseSemantics
      indexedVecCandidateInductiveStats indexedVecKernelNil.type
      indexedVecCtorValidationContext = .ok () := by
  unfold AddInductive.checkConstructorUniverseSemantics
  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure] using indexedVecValidationNilUniverseLoop

theorem indexedVecValidationConsUniverseRun :
    AddInductive.checkConstructorUniverseSemantics
      indexedVecCandidateInductiveStats indexedVecKernelCons.type
      indexedVecCtorValidationContext = .ok () := by
  unfold AddInductive.checkConstructorUniverseSemantics
  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure] using indexedVecValidationConsUniverseLoop

/-- Both source-ordered `IndexedVec` constructors pass the executable verified
universe gate. -/
theorem indexedVecValidationCheckConstructorUniverseSemantics :
    AddInductive.checkConstructorUniverseListSemantics
      indexedVecCandidateInductiveStats indexedVecKernelType.ctors
      indexedVecCtorValidationContext = .ok () := by
  unfold AddInductive.checkConstructorUniverseListSemantics
  simp only [indexedVecKernelType, ReaderT.bind, Bind.bind]
  rw [indexedVecValidationNilUniverseRun]
  simp only [Except.bind]
  unfold AddInductive.checkConstructorUniverseListSemantics
  simp only [ReaderT.bind, Bind.bind]
  rw [indexedVecValidationConsUniverseRun]
  rfl

theorem indexedVecValidationGetEnvM :
    TypeChecker.M.run indexedVecCtorValidationContext.env
        indexedVecCtorValidationContext.safety
        indexedVecCtorValidationContext.lctx
        indexedVecCtorValidationContext.lparams
        indexedVecCtorValidationContext.fuel TypeChecker.getEnv =
      .ok ctorEnv := by
  rfl

theorem indexedVecValidationEmptyDoesNotContainNil :
    (∅ : NameSet).contains indexedVecKernelNil.name = false := by
  simp +decide

theorem indexedVecValidationNilSetDoesNotContainCons :
    ((∅ : NameSet).insert indexedVecKernelNil.name).contains
      indexedVecKernelCons.name = false := by
  simp only [indexedVecKernelNil, indexedVecKernelCons,
    indexedVecNilInfo, indexedVecConsInfo,
    ConstantInfo.name, ConstantInfo.toConstantVal,
    NameSet.contains, NameSet.insert]
  rw [Std.TreeSet.contains_insert (t := (∅ : NameSet))]
  simp +decide

set_option linter.unusedSimpArgs false in
theorem indexedVecValidationCheckConstructors :
    AddInductive.checkConstructors #[indexedVecKernelType]
      indexedVecCandidateInductiveStats false
      indexedVecCtorValidationContext = .ok () := by
  unfold AddInductive.checkConstructors
  simp only [ReaderT.bind, Bind.bind]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationGetEnvM]
  simp only [Except.bind]
  unfold AddInductive.checkConstructorsLoop AddInductive.checkConstructorFold
  simp only [indexedVecKernelType, List.toList_toArray,
    ReaderT.bind, Bind.bind, Except.bind]
  rw [indexedVecValidationEmptyDoesNotContainNil]
  simp only [Bool.false_eq_true, if_false,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [indexedVecNilNoMVarNoFVar]
  simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure, AddInductive.liftExcept_apply]
  rw [AddInductive.withEmptyLocalContext_apply]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationNilRootCheckTypeM]
  unfold AddInductive.checkConstructorType
  simp only [Except.bind, readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure]
  rw [indexedVecValidationNilLoop]
  unfold AddInductive.checkConstructorFold
  simp only [Except.bind, ReaderT.pure, Pure.pure, Except.pure]
  rw [indexedVecValidationNilSetDoesNotContainCons]
  simp only [Bool.false_eq_true, if_false,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [indexedVecConsNoMVarNoFVar]
  simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure, AddInductive.liftExcept_apply]
  rw [AddInductive.withEmptyLocalContext_apply]
  rw [AddInductive.liftTypeChecker_apply]
  rw [indexedVecValidationConsRootCheckTypeM]
  unfold AddInductive.checkConstructorType
  simp only [Except.bind, readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure]
  rw [indexedVecValidationConsLoop]
  unfold AddInductive.checkConstructorFold
  rfl

/-- The complete one-parameter, one-index IndexedVec request produces the
exact ordered family/nil/cons normalization candidate. -/
theorem indexedVecNormalizationCandidateProduced :
    AddInductive.buildNormalizationCandidate 1
        [indexedVecKernelType] 0 false
        indexedVecFamilyCandidateContext =
      .ok indexedVecNormalizationCandidate := by
  unfold AddInductive.buildNormalizationCandidate
  rw [indexedVec_checkInductiveTypes]
  simp only [ReaderT.bind, Bind.bind]
  rw [show
    (withReader (fun _ : AddInductive.Context =>
        { indexedVecFamilyCandidateContext with lctx := {} })
      (AddInductive.normalizeCandidateFamilyTypeList
        [indexedVecKernelType])) indexedVecFamilyCandidate.trace.terminalContext =
      .ok (.cons indexedVecFamilyListCandidate.familyType .nil) by
    simpa using indexedVecFamilyTypeListCandidateProduced]
  simp only [Except.bind]
  rw [indexedVecDeclareFromTerminal]
  unfold AddInductive.withEnv
  change (ReaderT.bind
      (AddInductive.checkConstructors #[indexedVecKernelType]
        indexedVecCandidateInductiveStats false)
      (fun _ => ReaderT.bind
        (fun _ : AddInductive.Context =>
          AddInductive.normalizeCandidateFamilyList
            (.cons indexedVecFamilyListCandidate.familyType .nil)
            ctorContext)
        (fun families => pure
          (⟨families⟩ : AddInductive.NormalizationCandidate
            [indexedVecKernelType]))))
      indexedVecCtorValidationContext = _
  simp only [ReaderT.bind, Bind.bind]
  rw [indexedVecValidationCheckConstructors]
  simp only [Except.bind]
  rw [indexedVecFamilyListCandidateProduced]
  rfl

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecNormalizationCandidateProduced [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

end Ix.Theory.Named.InductiveReplayFixtures
