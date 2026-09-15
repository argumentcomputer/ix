/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.IndexedVecConstructors

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta
open Ix.Theory.Named.InductiveFixtures

namespace IndexedVecConsReplay






def replayInsert (state : TypeChecker.State) (e type : Expr) :
    TypeChecker.State :=
  { state with inferTypeC := state.inferTypeC.insert e type }

open private mkLevelIMaxCore mkLevelMaxCore from Lean.Level in
@[simp] theorem replayMkLevelIMaxSuccParamSelf :
    mkLevelIMax' (.succ (.param `u)) (.succ (.param `u)) =
      .succ (.param `u) := by
  simp [mkLevelIMax', mkLevelIMaxCore, mkLevelMax', mkLevelMaxCore]

def replayFirstApp (alpha : Expr) : Expr :=
  .app (.const ``IndexedVec [.param `u]) alpha

@[simp] theorem replayAppBeqFVar (fn arg : Expr) (id : FVarId) :
    ((.app fn arg : Expr) == .fvar id) = false := by
  change Expr.eqv (.app fn arg) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem replayFVarBeqApp (id : FVarId) (fn arg : Expr) :
    ((.fvar id : Expr) == .app fn arg) = false := by
  change Expr.eqv (.fvar id) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem replayConstBeqApp
    (name : Name) (levels : List Level) (fn arg : Expr) :
    ((.const name levels : Expr) == .app fn arg) = false := by
  change Expr.eqv (.const name levels) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem replayAppBeqConst
    (fn arg : Expr) (name : Name) (levels : List Level) :
    ((.app fn arg : Expr) == .const name levels) = false := by
  change Expr.eqv (.app fn arg) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem replayIndexedVecConstBeqSucc :
    ((.const ``IndexedVec [.param `u] : Expr) ==
      .const ``Nat.succ []) = false := by
  change Expr.eqv (.const ``IndexedVec [.param `u])
    (.const ``Nat.succ []) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv']

@[simp] theorem replayAlphaBeqN :
    ((consAlphaExpr : Expr) == consNExpr) = false := by
  change Expr.eqv consAlphaExpr consNExpr = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', consAlphaExpr, consNExpr, consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId, NameGenerator.next, NameGenerator.curr]

@[simp] theorem replayAlphaIdBeqNId :
    ((.fvar consAlphaId : Expr) == .fvar consNId) = false := by
  simpa using replayAlphaBeqN

theorem replayInferFirstAppFVarCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (id : FVarId)
    (hfamily : state.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none)
    (halpha : (replayInsert state
      (.const ``IndexedVec [.param `u]) indexedVecInfo.type).inferTypeC[
        (.fvar id : Expr)]? = none)
    (happ : state.inferTypeC[replayFirstApp (.fvar id)]? = none)
    (hfind : lctx.find? id = some (.cdecl index id name
      (.sort (.succ (.param `u))) bi kind)) :
    TypeChecker.Inner.inferType' (replayFirstApp (.fvar id)) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (vecFamilyTail,
          replayInsert
            (replayInsert
              (replayInsert state
                (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
              (.fvar id) (.sort (.succ (.param `u))))
            (replayFirstApp (.fvar id)) vecFamilyTail) := by
  have hfamilyRun := inferTypeFamilyCore fuel lctx state hfamily
  have halphaRun := inferTypeFVarCore fuel lctx
    (replayInsert state (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
    id (.sort (.succ (.param `u))) halpha hfind
  have happRun := inferAppCoreOf fuel (tcContext lctx)
    state
    (replayInsert state (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
    (replayInsert
      (replayInsert state (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
      (.fvar id) (.sort (.succ (.param `u))))
    (.const ``IndexedVec [.param `u]) (.fvar id)
    (.sort (.succ (.param `u))) vecFamilyTail `α .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    happ
    (by simpa [replayInsert, indexedVecInfoTypeShape] using hfamilyRun)
    (by simpa [replayInsert] using halphaRun)
    (by rfl)
  simpa [replayInsert, replayFirstApp, vecFamilyTail,
    Expr.instantiate1'] using happRun

def replaySuccApp (n : Expr) : Expr :=
  .app (.const ``Nat.succ []) n

@[simp] theorem replayFirstAppBeqSuccApp (alpha n : Expr) :
    (replayFirstApp alpha == replaySuccApp n) = false := by
  change Expr.eqv (replayFirstApp alpha) (replaySuccApp n) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', replayFirstApp, replaySuccApp]

@[simp] theorem replayFirstAppBeqSuccLiteral (alpha n : Expr) :
    (replayFirstApp alpha == .app (.const ``Nat.succ []) n) = false := by
  simpa [replaySuccApp] using replayFirstAppBeqSuccApp alpha n

theorem replayInferSuccFVarCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (id : FVarId)
    (hsucc : state.inferTypeC[(.const ``Nat.succ [] : Expr)]? = none)
    (hn : (replayInsert state (.const ``Nat.succ [])
      (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)).inferTypeC[
        (.fvar id : Expr)]? = none)
    (happ : state.inferTypeC[replaySuccApp (.fvar id)]? = none)
    (hfind : lctx.find? id = some (.cdecl index id name
      (.const ``Nat []) bi kind)) :
    TypeChecker.Inner.inferType' (replaySuccApp (.fvar id)) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.const ``Nat [],
          replayInsert
            (replayInsert
              (replayInsert state (.const ``Nat.succ [])
                (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
              (.fvar id) (.const ``Nat []))
            (replaySuccApp (.fvar id)) (.const ``Nat [])) := by
  have hsuccRun := inferTypeSuccCore fuel lctx state hsucc
  have hnRun := inferTypeFVarCore fuel lctx
    (replayInsert state (.const ``Nat.succ [])
      (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
    id (.const ``Nat []) hn hfind
  have happRun := inferAppCoreOf fuel (tcContext lctx)
    state
    (replayInsert state (.const ``Nat.succ [])
      (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
    (replayInsert
      (replayInsert state (.const ``Nat.succ [])
        (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
      (.fvar id) (.const ``Nat []))
    (.const ``Nat.succ []) (.fvar id) (.const ``Nat [])
    (.const ``Nat []) `n .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    happ
    (by simpa [replayInsert] using hsuccRun)
    (by simpa [replayInsert] using hnRun)
    (by rfl)
  simpa [replayInsert, replaySuccApp, Expr.instantiate1_eq,
    Expr.instantiate1'] using happRun

theorem replayInferIndexedVecAppCore
    (fuel : Nat) (lctx : LocalContext)
    (state stateFn stateArg : TypeChecker.State)
    (alpha indexExpr : Expr)
    (hclosed : (ctorIndexedVecApp alpha indexExpr).hasLooseBVars = false)
    (hcache : state.inferTypeC[ctorIndexedVecApp alpha indexExpr]? = none)
    (hfn : TypeChecker.Inner.inferType' (replayFirstApp alpha) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (vecFamilyTail, stateFn))
    (harg : TypeChecker.Inner.inferType' indexExpr false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) stateFn =
        .ok (.const ``Nat [], stateArg))
    (heager : indexExpr.isAppOfArity ``eagerReduce 2 = false) :
    TypeChecker.Inner.inferType' (ctorIndexedVecApp alpha indexExpr) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.sort (.succ (.param `u)),
          replayInsert stateArg (ctorIndexedVecApp alpha indexExpr)
            (.sort (.succ (.param `u)))) := by
  have h := inferAppCoreOf fuel (tcContext lctx) state stateFn stateArg
    (replayFirstApp alpha) indexExpr (.const ``Nat [])
    (.sort (.succ (.param `u))) vecIndexName .default
    hclosed hcache
    (by simpa [replayFirstApp, vecFamilyTail] using hfn) harg heager
  simpa [replayInsert, ctorIndexedVecApp, replayFirstApp,
    vecFamilyTail, Expr.instantiate1_eq, Expr.instantiate1'] using h

theorem replayInferTypeCachedCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (e type : Expr)
    (hclosed : e.hasLooseBVars = false)
    (hcache : state.inferTypeC[e]? = some type) :
    TypeChecker.Inner.inferType' e false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (type, state) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache]

theorem replayInferFirstAppAlphaCachedCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (alphaId : FVarId)
    (halpha : state.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))))
    (hfamily : state.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none)
    (happ : state.inferTypeC[replayFirstApp (.fvar alphaId)]? = none) :
    TypeChecker.Inner.inferType' (replayFirstApp (.fvar alphaId)) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (vecFamilyTail,
          replayInsert
            (replayInsert state
              (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
            (replayFirstApp (.fvar alphaId)) vecFamilyTail) := by
  let familyState := replayInsert state
    (.const ``IndexedVec [.param `u]) indexedVecInfo.type
  have hfamilyRun := inferTypeFamilyCore fuel lctx state hfamily
  have halphaCache : familyState.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))) := by
    simp only [familyState, replayInsert, Std.HashMap.getElem?_insert]
    rw [constBeqFVar]
    exact halpha
  have halphaRun := replayInferTypeCachedCore fuel lctx familyState
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange']) halphaCache
  have hrun := inferAppCoreOf fuel (tcContext lctx)
    state familyState familyState
    (.const ``IndexedVec [.param `u]) (.fvar alphaId)
    (.sort (.succ (.param `u))) vecFamilyTail `α .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    happ
    (by simpa [familyState, replayInsert, indexedVecInfoTypeShape] using
      hfamilyRun)
    halphaRun (by rfl)
  simpa [familyState, replayInsert, replayFirstApp, vecFamilyTail,
    Expr.instantiate1'] using hrun

theorem replayInferTailDomainAlphaCachedCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (alphaId nId : FVarId)
    (halpha : state.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))))
    (hfamily : state.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none)
    (hfirstApp : state.inferTypeC[
      replayFirstApp (.fvar alphaId)]? = none)
    (hn : (replayInsert
      (replayInsert state (.const ``IndexedVec [.param `u])
        indexedVecInfo.type)
      (replayFirstApp (.fvar alphaId)) vecFamilyTail).inferTypeC[
        (.fvar nId : Expr)]? = none)
    (htail : state.inferTypeC[
      ctorIndexedVecApp (.fvar alphaId) (.fvar nId)]? = none)
    (hfind : lctx.find? nId = some (.cdecl index nId name
      (.const ``Nat []) bi kind)) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId) (.fvar nId)) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.sort (.succ (.param `u)),
          replayInsert
            (replayInsert
              (replayInsert
                (replayInsert state (.const ``IndexedVec [.param `u])
                  indexedVecInfo.type)
                (replayFirstApp (.fvar alphaId)) vecFamilyTail)
              (.fvar nId) (.const ``Nat []))
            (ctorIndexedVecApp (.fvar alphaId) (.fvar nId))
            (.sort (.succ (.param `u)))) := by
  let firstState := replayInsert
    (replayInsert state (.const ``IndexedVec [.param `u])
      indexedVecInfo.type)
    (replayFirstApp (.fvar alphaId)) vecFamilyTail
  let nState := replayInsert firstState (.fvar nId) (.const ``Nat [])
  have hfirstRun := replayInferFirstAppAlphaCachedCore fuel lctx state
    alphaId halpha hfamily hfirstApp
  have hnRun := inferTypeFVarCore fuel lctx firstState nId
    (.const ``Nat []) hn hfind
  have hrun := replayInferIndexedVecAppCore fuel lctx state firstState nState
    (.fvar alphaId) (.fvar nId)
    (by simp [ctorIndexedVecApp, Expr.hasLooseBVars,
      Expr.looseBVarRange'])
    htail
    (by simpa [firstState] using hfirstRun)
    (by simpa [firstState, nState, replayInsert] using hnRun)
    (by rfl)
  simpa [firstState, nState, replayInsert] using hrun

theorem replayInferSuccFVarCachedCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (id : FVarId)
    (hsucc : state.inferTypeC[(.const ``Nat.succ [] : Expr)]? = none)
    (hn : state.inferTypeC[(.fvar id : Expr)]? = some (.const ``Nat []))
    (happ : state.inferTypeC[replaySuccApp (.fvar id)]? = none) :
    TypeChecker.Inner.inferType' (replaySuccApp (.fvar id)) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.const ``Nat [],
          replayInsert
            (replayInsert state (.const ``Nat.succ [])
              (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
            (replaySuccApp (.fvar id)) (.const ``Nat [])) := by
  let succState := replayInsert state (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)
  have hsuccRun := inferTypeSuccCore fuel lctx state hsucc
  have hnCache : succState.inferTypeC[(.fvar id : Expr)]? =
      some (.const ``Nat []) := by
    simp only [succState, replayInsert, Std.HashMap.getElem?_insert]
    rw [constBeqFVar]
    exact hn
  have hnRun := replayInferTypeCachedCore fuel lctx succState
    (.fvar id) (.const ``Nat [])
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange']) hnCache
  have happRun := inferAppCoreOf fuel (tcContext lctx)
    state succState succState
    (.const ``Nat.succ []) (.fvar id) (.const ``Nat [])
    (.const ``Nat []) `n .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    happ
    (by simpa [succState, replayInsert] using hsuccRun)
    hnRun (by rfl)
  simpa [succState, replayInsert, replaySuccApp,
    Expr.instantiate1_eq, Expr.instantiate1'] using happRun

theorem replayInferIndexedVecSuccFromCacheCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (alphaId nId : FVarId)
    (hfirst : state.inferTypeC[replayFirstApp (.fvar alphaId)]? =
      some vecFamilyTail)
    (hsucc : state.inferTypeC[(.const ``Nat.succ [] : Expr)]? = none)
    (hn : state.inferTypeC[(.fvar nId : Expr)]? = some (.const ``Nat []))
    (hsuccApp : state.inferTypeC[replaySuccApp (.fvar nId)]? = none)
    (hresult : state.inferTypeC[
      ctorIndexedVecApp (.fvar alphaId) (replaySuccApp (.fvar nId))]? = none) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId) (replaySuccApp (.fvar nId))) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.sort (.succ (.param `u)),
          replayInsert
            (replayInsert
              (replayInsert state (.const ``Nat.succ [])
                (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
              (replaySuccApp (.fvar nId)) (.const ``Nat []))
            (ctorIndexedVecApp (.fvar alphaId)
              (replaySuccApp (.fvar nId)))
            (.sort (.succ (.param `u)))) := by
  let succState := replayInsert state (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)
  let succAppState := replayInsert succState
    (replaySuccApp (.fvar nId)) (.const ``Nat [])
  have hfirstRun := replayInferTypeCachedCore fuel lctx state
    (replayFirstApp (.fvar alphaId)) vecFamilyTail
    (by simp [replayFirstApp, Expr.hasLooseBVars,
      Expr.looseBVarRange']) hfirst
  have hsuccRun := replayInferSuccFVarCachedCore fuel lctx state nId
    hsucc hn hsuccApp
  have h := replayInferIndexedVecAppCore fuel lctx state state succAppState
    (.fvar alphaId) (replaySuccApp (.fvar nId))
    (by simp [ctorIndexedVecApp, replaySuccApp,
      Expr.hasLooseBVars, Expr.looseBVarRange'])
    hresult hfirstRun
    (by simpa [succState, succAppState] using hsuccRun)
    (by rfl)
  simpa [succState, succAppState, replayInsert] using h

def consHeadFirstAppState : TypeChecker.State :=
  replayInsert
    (replayInsert
      (replayInsert ({} : TypeChecker.State)
        (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
      consAlphaExpr (.sort (.succ (.param `u))))
    (replayFirstApp consAlphaExpr) vecFamilyTail

def consHeadNState : TypeChecker.State :=
  replayInsert consHeadFirstAppState consNExpr (.const ``Nat [])

def consTailDomainFinalState : TypeChecker.State :=
  replayInsert consHeadNState consTailDomain
    (.sort (.succ (.param `u)))

theorem replayInferConsHeadFirstApp (fuel : Nat) :
    TypeChecker.Inner.inferType' (replayFirstApp consAlphaExpr) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State) =
        .ok (vecFamilyTail, consHeadFirstAppState) := by
  simpa [consHeadFirstAppState, consAlphaExprShape] using
    (replayInferFirstAppFVarCore fuel consHeadContext.lctx
      ({} : TypeChecker.State) consAlphaId
      (by simp)
      (by simp [replayInsert])
      (by simp [replayFirstApp])
      consAlphaFindInHead)

theorem replayInferConsHeadN (fuel : Nat) :
    TypeChecker.Inner.inferType' consNExpr false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consHeadContext.lctx) consHeadFirstAppState =
        .ok (.const ``Nat [], consHeadNState) := by
  simpa [consHeadNState, consNExprShape, replayInsert] using
    (inferTypeFVarCore fuel consHeadContext.lctx
      consHeadFirstAppState consNId (.const ``Nat [])
      (index := 1) (name := consNName) (bi := .implicit)
      (kind := .default)
      (by simp [consHeadFirstAppState, replayInsert, replayFirstApp])
      consNFindInHead)

theorem replayInferConsTailDomainCore (fuel : Nat) :
    TypeChecker.Inner.inferType' consTailDomain false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)), consTailDomainFinalState) := by
  simpa [consTailDomainFinalState, consTailDomain,
    ctorIndexedVecApp, replayFirstApp] using
    (replayInferIndexedVecAppCore fuel consHeadContext.lctx
      ({} : TypeChecker.State) consHeadFirstAppState consHeadNState
      consAlphaExpr consNExpr
      (by simp [ctorIndexedVecApp, consAlphaExprShape,
        consNExprShape, Expr.hasLooseBVars, Expr.looseBVarRange'])
      (by simp [ctorIndexedVecApp, consAlphaExprShape, consNExprShape])
      (replayInferConsHeadFirstApp fuel) (replayInferConsHeadN fuel) (by rfl))

theorem replayInferConsTailDomain :
    TypeChecker.Inner.inferType consTailDomain false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)), consTailDomainFinalState) := by
  change TypeChecker.Inner.inferType' consTailDomain false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State) = _
  exact replayInferConsTailDomainCore 9999

theorem replayConsTailDomainCheckTypeM :
    TypeChecker.M.run ctorEnv .safe consHeadContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType consTailDomain) =
        .ok (.sort (.succ (.param `u))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType consTailDomain false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State)) = _
  rw [replayInferConsTailDomain]
  rfl

def consTailFirstAppState : TypeChecker.State :=
  replayInsert
    (replayInsert
      (replayInsert ({} : TypeChecker.State)
        (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
      consAlphaExpr (.sort (.succ (.param `u))))
    (replayFirstApp consAlphaExpr) vecFamilyTail

def consTailSuccState : TypeChecker.State :=
  replayInsert
    (replayInsert
      (replayInsert consTailFirstAppState (.const ``Nat.succ [])
        (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
      consNExpr (.const ``Nat []))
    (replaySuccApp consNExpr) (.const ``Nat [])

def consTerminalFinalState : TypeChecker.State :=
  replayInsert consTailSuccState consTerminal
    (.sort (.succ (.param `u)))

theorem replayInferConsTailFirstApp :
    TypeChecker.Inner.inferType' (replayFirstApp consAlphaExpr) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consTailContext.lctx) ({} : TypeChecker.State) =
        .ok (vecFamilyTail, consTailFirstAppState) := by
  simpa [consTailFirstAppState, consAlphaExprShape] using
    (replayInferFirstAppFVarCore 9999 consTailContext.lctx
      ({} : TypeChecker.State) consAlphaId
      (by simp)
      (by simp [replayInsert])
      (by simp [replayFirstApp])
      consAlphaFindInTail)

theorem replayInferConsTailSucc :
    TypeChecker.Inner.inferType' (replaySuccApp consNExpr) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consTailContext.lctx) consTailFirstAppState =
        .ok (.const ``Nat [], consTailSuccState) := by
  simpa [consTailSuccState, consNExprShape] using
    (replayInferSuccFVarCore 9999 consTailContext.lctx
      consTailFirstAppState consNId
      (by simp [consTailFirstAppState, replayInsert, replayFirstApp])
      (by simp [consTailFirstAppState, replayInsert,
        replayFirstApp])
      (by simp [consTailFirstAppState, replayInsert, replaySuccApp])
      consNFindInTail)

theorem replayInferConsTerminal :
    TypeChecker.Inner.inferType consTerminal false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consTailContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)), consTerminalFinalState) := by
  change TypeChecker.Inner.inferType' consTerminal false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consTailContext.lctx) ({} : TypeChecker.State) = _
  simpa [consTerminalFinalState, consTerminal,
    ctorIndexedVecApp, replayFirstApp, replaySuccApp] using
    (replayInferIndexedVecAppCore 9999 consTailContext.lctx
      ({} : TypeChecker.State) consTailFirstAppState consTailSuccState
      consAlphaExpr (replaySuccApp consNExpr)
      (by simp [ctorIndexedVecApp, replaySuccApp,
        Expr.hasLooseBVars, Expr.looseBVarRange'])
      (by simp [ctorIndexedVecApp, replaySuccApp])
      replayInferConsTailFirstApp replayInferConsTailSucc
      (by rfl))

theorem replayConsTerminalCheckTypeM :
    TypeChecker.M.run ctorEnv .safe consTailContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType consTerminal) =
        .ok (.sort (.succ (.param `u))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType consTerminal false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consTailContext.lctx) ({} : TypeChecker.State)) = _
  rw [replayInferConsTerminal]
  rfl

theorem replayConsTailDomainWhnfM :
    TypeChecker.M.run ctorEnv .safe consHeadContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.whnf consTailDomain) =
        .ok consTailDomain := by
  simpa [consTailDomain, ctorIndexedVecApp] using
    (ctorIndexedVecWhnfM consHeadContext.lctx consAlphaExpr consNExpr)

theorem replayConsTerminalWhnfM :
    TypeChecker.M.run ctorEnv .safe consTailContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.whnf consTerminal) =
        .ok consTerminal := by
  simpa [consTerminal, ctorIndexedVecApp, replaySuccApp] using
    (ctorIndexedVecWhnfM consTailContext.lctx consAlphaExpr
      (replaySuccApp consNExpr))

theorem replayConsRootWhnfM :
    TypeChecker.M.run ctorEnv .safe {} [`u] ({} : FuelConfig)
    (TypeChecker.whnf indexedVecConsInfo.type) =
      .ok indexedVecConsInfo.type := by rfl

theorem replayConsAfterAlphaWhnfM :
    TypeChecker.M.run ctorEnv .safe consAlphaContext.lctx [`u]
    ({} : FuelConfig) (TypeChecker.whnf consAfterAlpha) =
      .ok consAfterAlpha := by rfl

theorem replayConsAfterNWhnfM :
    TypeChecker.M.run ctorEnv .safe consNContext.lctx [`u]
    ({} : FuelConfig) (TypeChecker.whnf consAfterN) =
      .ok consAfterN := by rfl

theorem replayConsAfterHeadWhnfM :
    TypeChecker.M.run ctorEnv .safe consHeadContext.lctx [`u]
    ({} : FuelConfig) (TypeChecker.whnf consAfterHead) =
      .ok consAfterHead := by rfl

def consAfterHeadCheckTailId : FVarId :=
  ⟨consTailDomainFinalState.ngen.curr⟩

def consAfterHeadCheckLctx : LocalContext :=
  consHeadContext.lctx.mkLocalDecl consAfterHeadCheckTailId
    consTailName consTailDomain .default

def consAfterHeadCheckState : TypeChecker.State :=
  { consTailDomainFinalState with
    ngen := consTailDomainFinalState.ngen.next }

@[simp] theorem replayTailDomainBeqFirstApp :
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId) ==
      replayFirstApp (.fvar consAlphaId)) = false := by
  change Expr.eqv
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId))
    (replayFirstApp (.fvar consAlphaId)) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replayFirstApp]

@[simp] theorem replayTailDomainBeqSuccApp :
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId) ==
      replaySuccApp (.fvar consNId)) = false := by
  change Expr.eqv
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId))
    (replaySuccApp (.fvar consNId)) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replaySuccApp]

@[simp] theorem replayTailDomainBeqTerminal :
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId) ==
      ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consNId))) = false := by
  change Expr.eqv
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId))
    (ctorIndexedVecApp (.fvar consAlphaId)
      (replaySuccApp (.fvar consNId))) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replaySuccApp]

@[simp] theorem replayFirstAppBeqTerminal :
    (replayFirstApp (.fvar consAlphaId) ==
      ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consNId))) = false := by
  change Expr.eqv (replayFirstApp (.fvar consAlphaId))
    (ctorIndexedVecApp (.fvar consAlphaId)
      (replaySuccApp (.fvar consNId))) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replayFirstApp, replaySuccApp]

@[simp] theorem replayTailDomainLiteralBeqFirstApp :
    (((.const ``IndexedVec [.param `u] : Expr).app (.fvar consAlphaId)).app
        (.fvar consNId) ==
      (.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)) = false := by
  simpa [ctorIndexedVecApp, replayFirstApp] using
    replayTailDomainBeqFirstApp

@[simp] theorem replayTailDomainLiteralBeqSuccApp :
    (((.const ``IndexedVec [.param `u] : Expr).app (.fvar consAlphaId)).app
        (.fvar consNId) ==
      (.const ``Nat.succ [] : Expr).app (.fvar consNId)) = false := by
  simpa [ctorIndexedVecApp, replaySuccApp] using
    replayTailDomainBeqSuccApp

@[simp] theorem replayFirstAppLiteralBeqSuccApp :
    ((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId) ==
      (.const ``Nat.succ [] : Expr).app (.fvar consNId)) = false := by
  simpa only [replayFirstApp, replaySuccApp] using
    (replayFirstAppBeqSuccApp (.fvar consAlphaId) (.fvar consNId))

@[simp] theorem replayTailDomainLiteralBeqTerminal :
    (((.const ``IndexedVec [.param `u] : Expr).app (.fvar consAlphaId)).app
        (.fvar consNId) ==
      ((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app
        ((.const ``Nat.succ [] : Expr).app (.fvar consNId))) = false := by
  simpa [ctorIndexedVecApp, replaySuccApp] using
    replayTailDomainBeqTerminal

@[simp] theorem replayFirstAppLiteralBeqTerminal :
    ((.const ``IndexedVec [.param `u] : Expr).app (.fvar consAlphaId) ==
      ((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app
        ((.const ``Nat.succ [] : Expr).app (.fvar consNId))) = false := by
  simpa [ctorIndexedVecApp, replayFirstApp, replaySuccApp] using
    replayFirstAppBeqTerminal

theorem consAfterHeadCheckFirstCache :
    consAfterHeadCheckState.inferTypeC[
      replayFirstApp (.fvar consAlphaId)]? = some vecFamilyTail := by
  change consTailDomainFinalState.inferTypeC[
    replayFirstApp (.fvar consAlphaId)]? = some vecFamilyTail
  unfold consTailDomainFinalState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (consTailDomain == replayFirstApp (.fvar consAlphaId)) =
      false by
    simpa only [consTailDomain, ctorIndexedVecApp,
      consAlphaExprShape, consNExprShape] using
      replayTailDomainBeqFirstApp]
  simp only [Bool.false_eq_true, if_false]
  unfold consHeadNState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (consNExpr == replayFirstApp (.fvar consAlphaId)) = false by
    simp [consNExprShape, replayFirstApp]]
  simp only [Bool.false_eq_true, if_false]
  unfold consHeadFirstAppState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (replayFirstApp consAlphaExpr ==
      replayFirstApp (.fvar consAlphaId)) = true by simp]
  rfl

theorem consAfterHeadCheckNCache :
    consAfterHeadCheckState.inferTypeC[(.fvar consNId : Expr)]? =
      some (.const ``Nat []) := by
  change consTailDomainFinalState.inferTypeC[(.fvar consNId : Expr)]? =
    some (.const ``Nat [])
  unfold consTailDomainFinalState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (consTailDomain == (.fvar consNId : Expr)) = false by
    simpa only [consTailDomain, consAlphaExprShape, consNExprShape] using
      (replayAppBeqFVar
        ((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)) (.fvar consNId) consNId)]
  simp only [Bool.false_eq_true, if_false]
  unfold consHeadNState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (consNExpr == (.fvar consNId : Expr)) = true by simp]
  rfl

theorem consAfterHeadCheckSuccMiss :
    consAfterHeadCheckState.inferTypeC[(.const ``Nat.succ [] : Expr)]? =
      none := by
  simp [consAfterHeadCheckState, consTailDomainFinalState, consHeadNState, consHeadFirstAppState,
    replayInsert, consTailDomain, replayFirstApp]

theorem consAfterHeadCheckSuccAppMiss :
    consAfterHeadCheckState.inferTypeC[
      replaySuccApp (.fvar consNId)]? = none := by
  simp [consAfterHeadCheckState, consTailDomainFinalState, consHeadNState, consHeadFirstAppState,
    replayInsert, consTailDomain, replayFirstApp, replaySuccApp]

theorem consAfterHeadCheckTerminalMiss :
    consAfterHeadCheckState.inferTypeC[
      ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consNId))]? = none := by
  simp [consAfterHeadCheckState, consTailDomainFinalState, consHeadNState, consHeadFirstAppState,
    replayInsert, consTailDomain, ctorIndexedVecApp, replayFirstApp, replaySuccApp]

def consAfterHeadCheckSuccState : TypeChecker.State :=
  replayInsert consAfterHeadCheckState (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)

def consAfterHeadCheckSuccAppState : TypeChecker.State :=
  replayInsert consAfterHeadCheckSuccState
    (replaySuccApp (.fvar consNId)) (.const ``Nat [])

def consAfterHeadCheckTerminalState : TypeChecker.State :=
  replayInsert consAfterHeadCheckSuccAppState
    (ctorIndexedVecApp (.fvar consAlphaId)
      (replaySuccApp (.fvar consNId)))
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterHeadTerminal :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consNId))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterHeadCheckLctx) consAfterHeadCheckState =
        .ok (.sort (.succ (.param `u)),
          consAfterHeadCheckTerminalState) := by
  simpa [consAfterHeadCheckSuccState,
    consAfterHeadCheckSuccAppState,
    consAfterHeadCheckTerminalState] using
    (replayInferIndexedVecSuccFromCacheCore 9998 consAfterHeadCheckLctx
      consAfterHeadCheckState consAlphaId consNId
      consAfterHeadCheckFirstCache consAfterHeadCheckSuccMiss
      consAfterHeadCheckNCache consAfterHeadCheckSuccAppMiss
      consAfterHeadCheckTerminalMiss)

theorem replayConsAfterHeadCheckTypeM :
    TypeChecker.M.run ctorEnv .safe consHeadContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType consAfterHead) =
        .ok (.sort (.succ (.param `u))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType consAfterHead false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State)) = _
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' consAfterHead false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State)) = _
  unfold consAfterHead consTailDomain TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', TypeChecker.Inner.inferForall,
    TypeChecker.Inner.inferForall.loop, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show TypeChecker.Inner.inferType'
      (.app
        (.app (.const ``IndexedVec [.param `u]) (.fvar consAlphaId))
        (.fvar consNId)) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consHeadContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)), consTailDomainFinalState) by
    simpa [consTailDomain, ctorIndexedVecApp] using
      replayInferConsTailDomainCore 9998]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp [Expr.instantiate1']
  have hterminal :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)).app
          ((.const ``Nat.succ [] : Expr).app (.fvar consNId))) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consAfterHeadCheckLctx) consAfterHeadCheckState =
          .ok (.sort (.succ (.param `u)),
            consAfterHeadCheckTerminalState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app
        ((.const ``Nat.succ [] : Expr).app (.fvar consNId))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterHeadCheckLctx) consAfterHeadCheckState = _
    simpa [ctorIndexedVecApp, replaySuccApp] using
      replayInferConsAfterHeadTerminal
  simp only [consAfterHeadCheckLctx, consAfterHeadCheckTailId,
    consAfterHeadCheckState, consTailDomain, consAlphaExprShape,
    consNExprShape, tcContext] at hterminal
  simp only [tcContext]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hterminal]
  simp only [ensureSortExact]
  simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]
  rfl

/-! The two-binder suffix beginning at the `head` field. -/

def consAfterNHeadDomainState : TypeChecker.State :=
  replayInsert ({} : TypeChecker.State) consAlphaExpr
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterNHeadDomain (fuel : Nat) :
    TypeChecker.Inner.inferType' consAlphaExpr false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consNContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          consAfterNHeadDomainState) := by
  simpa [consAfterNHeadDomainState, replayInsert,
    consAlphaExprShape] using
    (inferTypeFVarCore fuel consNContext.lctx ({} : TypeChecker.State)
      consAlphaId (.sort (.succ (.param `u)))
      (index := 0) (name := consAlphaName) (bi := .implicit)
      (kind := .default) (by simp) consAlphaFindInN)

def consAfterNCheckHeadId : FVarId :=
  ⟨consAfterNHeadDomainState.ngen.curr⟩

def consAfterNCheckLctx : LocalContext :=
  consNContext.lctx.mkLocalDecl consAfterNCheckHeadId
    consHeadName consAlphaExpr .default

def consAfterNCheckState : TypeChecker.State :=
  { consAfterNHeadDomainState with
    ngen := consAfterNHeadDomainState.ngen.next }

theorem consAfterNCheckHeadFresh :
    consNContext.lctx.find? consAfterNCheckHeadId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consAfterNCheckHeadId) consNContextWF
  rw [h]
  simp [consAfterNCheckHeadId, consAfterNHeadDomainState, replayInsert, consNContext,
    consAlphaContext, consRootContext, ctorContext, consAlphaId, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl, LocalContext.toList,
    LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]
  intro x hx
  change some x ∈
    (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at hx
  rw [PersistentArray.toList'_empty] at hx
  simp at hx

theorem consAfterNCheckLctxWF : consAfterNCheckLctx.WF := by
  simpa [consAfterNCheckLctx] using
    (LocalContext.WF.mkLocalDecl consNContextWF consAfterNCheckHeadFresh)

theorem consAfterNCheckNFind :
    consAfterNCheckLctx.find? consNId =
      some (.cdecl 1 consNId consNName (.const ``Nat [])
        .implicit .default) := by
  rw [consAfterNCheckLctxWF.find?_eq_find?_toList]
  simp [consAfterNCheckLctx, consAfterNCheckHeadId, consAfterNHeadDomainState, replayInsert,
    consNContext, consAlphaContext, consRootContext, ctorContext, consAlphaId, consNId,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl,
    LocalContext.toList, LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

theorem consAfterNCheckAlphaCache :
    consAfterNCheckState.inferTypeC[(.fvar consAlphaId : Expr)]? =
      some (.sort (.succ (.param `u))) := by
  change consAfterNHeadDomainState.inferTypeC[
    (.fvar consAlphaId : Expr)]? = some (.sort (.succ (.param `u)))
  unfold consAfterNHeadDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (consAlphaExpr == (.fvar consAlphaId : Expr)) = true by simp]
  rfl

theorem consAfterNCheckFamilyMiss :
    consAfterNCheckState.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none := by
  simp [consAfterNCheckState, consAfterNHeadDomainState, replayInsert]

theorem consAfterNCheckFirstAppMiss :
    consAfterNCheckState.inferTypeC[
      replayFirstApp (.fvar consAlphaId)]? = none := by
  simp [consAfterNCheckState, consAfterNHeadDomainState,
    replayInsert, replayFirstApp]

def consAfterNCheckFirstAppState : TypeChecker.State :=
  replayInsert
    (replayInsert consAfterNCheckState
      (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
    (replayFirstApp (.fvar consAlphaId)) vecFamilyTail

theorem consAfterNCheckNMiss :
    consAfterNCheckFirstAppState.inferTypeC[(.fvar consNId : Expr)]? =
      none := by
  simp [consAfterNCheckFirstAppState, consAfterNCheckState,
    consAfterNHeadDomainState, replayInsert, replayFirstApp]

theorem consAfterNCheckTailMiss :
    consAfterNCheckState.inferTypeC[
      ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId)]? = none := by
  simp [consAfterNCheckState, consAfterNHeadDomainState,
    replayInsert, ctorIndexedVecApp]

def consAfterNCheckNState : TypeChecker.State :=
  replayInsert consAfterNCheckFirstAppState
    (.fvar consNId) (.const ``Nat [])

def consAfterNCheckTailDomainState : TypeChecker.State :=
  replayInsert consAfterNCheckNState
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId))
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterNTailDomain (fuel : Nat) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId)) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consAfterNCheckLctx) consAfterNCheckState =
        .ok (.sort (.succ (.param `u)),
          consAfterNCheckTailDomainState) := by
  simpa [consAfterNCheckFirstAppState, consAfterNCheckNState,
    consAfterNCheckTailDomainState] using
    (replayInferTailDomainAlphaCachedCore fuel consAfterNCheckLctx
      consAfterNCheckState consAlphaId consNId
      consAfterNCheckAlphaCache consAfterNCheckFamilyMiss
      consAfterNCheckFirstAppMiss consAfterNCheckNMiss
      consAfterNCheckTailMiss consAfterNCheckNFind)

def consAfterNCheckTailId : FVarId :=
  ⟨consAfterNCheckTailDomainState.ngen.curr⟩

def consAfterNCheckTailLctx : LocalContext :=
  consAfterNCheckLctx.mkLocalDecl consAfterNCheckTailId
    consTailName
    (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId)) .default

def consAfterNCheckTailState : TypeChecker.State :=
  { consAfterNCheckTailDomainState with
    ngen := consAfterNCheckTailDomainState.ngen.next }

theorem consAfterNCheckTailFirstCache :
    consAfterNCheckTailState.inferTypeC[
      replayFirstApp (.fvar consAlphaId)]? = some vecFamilyTail := by
  change consAfterNCheckTailDomainState.inferTypeC[
    replayFirstApp (.fvar consAlphaId)]? = some vecFamilyTail
  unfold consAfterNCheckTailDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [replayTailDomainBeqFirstApp]
  simp only [Bool.false_eq_true, if_false]
  unfold consAfterNCheckNState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show ((.fvar consNId : Expr) ==
      replayFirstApp (.fvar consAlphaId)) = false by
    simpa only [replayFirstApp] using
      (replayFVarBeqApp consNId
        (.const ``IndexedVec [.param `u]) (.fvar consAlphaId))]
  simp only [Bool.false_eq_true, if_false]
  unfold consAfterNCheckFirstAppState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consAfterNCheckTailNCache :
    consAfterNCheckTailState.inferTypeC[(.fvar consNId : Expr)]? =
      some (.const ``Nat []) := by
  change consAfterNCheckTailDomainState.inferTypeC[
    (.fvar consNId : Expr)]? = some (.const ``Nat [])
  unfold consAfterNCheckTailDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (ctorIndexedVecApp (.fvar consAlphaId) (.fvar consNId) ==
      (.fvar consNId : Expr)) = false by
    simpa only [ctorIndexedVecApp] using
      (replayAppBeqFVar
        ((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)) (.fvar consNId) consNId)]
  simp only [Bool.false_eq_true, if_false]
  unfold consAfterNCheckNState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consAfterNCheckTailSuccMiss :
    consAfterNCheckTailState.inferTypeC[
      (.const ``Nat.succ [] : Expr)]? = none := by
  simp [consAfterNCheckTailState, consAfterNCheckTailDomainState, consAfterNCheckNState,
    consAfterNCheckFirstAppState, consAfterNCheckState, consAfterNHeadDomainState, replayInsert,
    ctorIndexedVecApp, replayFirstApp]

theorem consAfterNCheckTailSuccAppMiss :
    consAfterNCheckTailState.inferTypeC[
      replaySuccApp (.fvar consNId)]? = none := by
  simp [consAfterNCheckTailState, consAfterNCheckTailDomainState, consAfterNCheckNState,
    consAfterNCheckFirstAppState, consAfterNCheckState, consAfterNHeadDomainState, replayInsert,
    ctorIndexedVecApp, replayFirstApp, replaySuccApp]

theorem consAfterNCheckTailTerminalMiss :
    consAfterNCheckTailState.inferTypeC[
      ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consNId))]? = none := by
  simp [consAfterNCheckTailState, consAfterNCheckTailDomainState, consAfterNCheckNState,
    consAfterNCheckFirstAppState, consAfterNCheckState, consAfterNHeadDomainState, replayInsert,
    ctorIndexedVecApp, replayFirstApp, replaySuccApp]

def consAfterNCheckSuccState : TypeChecker.State :=
  replayInsert consAfterNCheckTailState (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)

def consAfterNCheckSuccAppState : TypeChecker.State :=
  replayInsert consAfterNCheckSuccState
    (replaySuccApp (.fvar consNId)) (.const ``Nat [])

def consAfterNCheckTerminalState : TypeChecker.State :=
  replayInsert consAfterNCheckSuccAppState
    (ctorIndexedVecApp (.fvar consAlphaId)
      (replaySuccApp (.fvar consNId)))
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterNTerminal (fuel : Nat) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consNId))) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consAfterNCheckTailLctx) consAfterNCheckTailState =
        .ok (.sort (.succ (.param `u)),
          consAfterNCheckTerminalState) := by
  simpa [consAfterNCheckSuccState, consAfterNCheckSuccAppState,
    consAfterNCheckTerminalState] using
    (replayInferIndexedVecSuccFromCacheCore fuel
      consAfterNCheckTailLctx consAfterNCheckTailState
      consAlphaId consNId consAfterNCheckTailFirstCache
      consAfterNCheckTailSuccMiss consAfterNCheckTailNCache
      consAfterNCheckTailSuccAppMiss consAfterNCheckTailTerminalMiss)

theorem replayConsAfterNCheckTypeM :
    TypeChecker.M.run ctorEnv .safe consNContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType consAfterN) =
        .ok (.sort (.succ (.param `u))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType consAfterN false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consNContext.lctx) ({} : TypeChecker.State)) = _
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' consAfterN false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consNContext.lctx) ({} : TypeChecker.State)) = _
  unfold consAfterN TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show TypeChecker.Inner.inferType'
      (.fvar consAlphaId) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consNContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          consAfterNHeadDomainState) by
    simpa [consAlphaExprShape] using
      replayInferConsAfterNHeadDomain 9998]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp [Expr.instantiate1']
  have htail :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)).app (.fvar consNId)) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consAfterNCheckLctx) consAfterNCheckState =
          .ok (.sort (.succ (.param `u)),
            consAfterNCheckTailDomainState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app (.fvar consNId)) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterNCheckLctx) consAfterNCheckState = _
    simpa [ctorIndexedVecApp] using
      replayInferConsAfterNTailDomain 9998
  simp only [consAfterNCheckLctx, consAfterNCheckHeadId,
    consAfterNCheckState, consAlphaExprShape, tcContext] at htail
  simp only [tcContext]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [htail]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp only []
  have hterminal :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)).app
          ((.const ``Nat.succ [] : Expr).app (.fvar consNId))) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consAfterNCheckTailLctx) consAfterNCheckTailState =
          .ok (.sort (.succ (.param `u)),
            consAfterNCheckTerminalState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app
        ((.const ``Nat.succ [] : Expr).app (.fvar consNId))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterNCheckTailLctx) consAfterNCheckTailState = _
    simpa [ctorIndexedVecApp, replaySuccApp] using
      replayInferConsAfterNTerminal 9998
  simp only [consAfterNCheckTailLctx, consAfterNCheckTailId,
    consAfterNCheckTailState, consAfterNCheckLctx,
    consAfterNCheckHeadId, consAlphaExprShape,
    ctorIndexedVecApp, tcContext] at hterminal
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hterminal]
  simp only [ensureSortExact]
  simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]
  rfl

/-! The three-binder suffix beginning at the `n` index. -/

open private mkLevelIMaxCore mkLevelMaxCore from Lean.Level in
@[simp] theorem replayMkLevelIMaxSuccZeroSuccParam :
    mkLevelIMax' (.succ .zero) (.succ (.param `u)) =
      .succ (.param `u) := by
  simp [mkLevelIMax', mkLevelIMaxCore, mkLevelMax', mkLevelMaxCore, Level.isNeverZero, Level.isZero,
    Level.isExplicit, Level.hasMVar', Level.hasParam', Level.getOffset, Level.getOffsetAux]

def consAfterAlphaNatState : TypeChecker.State :=
  replayInsert ({} : TypeChecker.State) (.const ``Nat [])
    (.sort (.succ .zero))

theorem replayInferConsAfterAlphaNat (fuel : Nat) :
    TypeChecker.Inner.inferType' (.const ``Nat []) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consAlphaContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), consAfterAlphaNatState) := by
  simpa [consAfterAlphaNatState, replayInsert] using
    (inferTypeNatCore fuel consAlphaContext.lctx
      ({} : TypeChecker.State) (by simp))

def consAfterAlphaCheckNId : FVarId :=
  ⟨consAfterAlphaNatState.ngen.curr⟩

def consAfterAlphaCheckNLctx : LocalContext :=
  consAlphaContext.lctx.mkLocalDecl consAfterAlphaCheckNId
    consNName (.const ``Nat []) .implicit

def consAfterAlphaCheckNState : TypeChecker.State :=
  { consAfterAlphaNatState with
    ngen := consAfterAlphaNatState.ngen.next }

theorem consAfterAlphaCheckNFresh :
    consAlphaContext.lctx.find? consAfterAlphaCheckNId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consAfterAlphaCheckNId) consAlphaContextWF
  rw [h]
  simp [consAfterAlphaCheckNId, consAfterAlphaNatState, replayInsert, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl, LocalContext.toList,
    LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]
  intro x hx
  change some x ∈
    (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at hx
  rw [PersistentArray.toList'_empty] at hx
  simp at hx

theorem consAfterAlphaCheckNLctxWF : consAfterAlphaCheckNLctx.WF := by
  simpa [consAfterAlphaCheckNLctx] using
    (LocalContext.WF.mkLocalDecl consAlphaContextWF
      consAfterAlphaCheckNFresh)

theorem consAfterAlphaCheckAlphaFind :
    consAfterAlphaCheckNLctx.find? consAlphaId =
      some (.cdecl 0 consAlphaId consAlphaName
        (.sort (.succ (.param `u))) .implicit .default) := by
  rw [consAfterAlphaCheckNLctxWF.find?_eq_find?_toList]
  simp [consAfterAlphaCheckNLctx, consAfterAlphaCheckNId, consAfterAlphaNatState, replayInsert,
    consAlphaContext, consRootContext, ctorContext, consAlphaId, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl, LocalContext.toList,
    LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

theorem consAfterAlphaCheckAlphaMiss :
    consAfterAlphaCheckNState.inferTypeC[
      (.fvar consAlphaId : Expr)]? = none := by
  simp [consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert]

def consAfterAlphaHeadDomainState : TypeChecker.State :=
  replayInsert consAfterAlphaCheckNState (.fvar consAlphaId)
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterAlphaHeadDomain (fuel : Nat) :
    TypeChecker.Inner.inferType' (.fvar consAlphaId) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consAfterAlphaCheckNLctx) consAfterAlphaCheckNState =
        .ok (.sort (.succ (.param `u)),
          consAfterAlphaHeadDomainState) := by
  simpa [consAfterAlphaHeadDomainState, replayInsert] using
    (inferTypeFVarCore fuel consAfterAlphaCheckNLctx
      consAfterAlphaCheckNState consAlphaId
      (.sort (.succ (.param `u)))
      consAfterAlphaCheckAlphaMiss consAfterAlphaCheckAlphaFind)

def consAfterAlphaCheckHeadId : FVarId :=
  ⟨consAfterAlphaHeadDomainState.ngen.curr⟩

def consAfterAlphaCheckHeadLctx : LocalContext :=
  consAfterAlphaCheckNLctx.mkLocalDecl consAfterAlphaCheckHeadId
    consHeadName (.fvar consAlphaId) .default

def consAfterAlphaCheckHeadState : TypeChecker.State :=
  { consAfterAlphaHeadDomainState with
    ngen := consAfterAlphaHeadDomainState.ngen.next }

theorem consAfterAlphaCheckHeadFresh :
    consAfterAlphaCheckNLctx.find? consAfterAlphaCheckHeadId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consAfterAlphaCheckHeadId) consAfterAlphaCheckNLctxWF
  rw [h]
  simp [consAfterAlphaCheckHeadId, consAfterAlphaHeadDomainState, consAfterAlphaCheckNState,
    consAfterAlphaCheckNId, consAfterAlphaNatState, replayInsert, consAfterAlphaCheckNLctx,
    consAlphaContext, consRootContext, ctorContext, consAlphaId, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl, LocalContext.toList,
    LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]
  intro x hx
  change some x ∈
    (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at hx
  rw [PersistentArray.toList'_empty] at hx
  simp at hx

theorem consAfterAlphaCheckHeadLctxWF :
    consAfterAlphaCheckHeadLctx.WF := by
  simpa [consAfterAlphaCheckHeadLctx] using
    (LocalContext.WF.mkLocalDecl consAfterAlphaCheckNLctxWF
      consAfterAlphaCheckHeadFresh)

theorem consAfterAlphaCheckNFind :
    consAfterAlphaCheckHeadLctx.find? consAfterAlphaCheckNId =
      some (.cdecl 1 consAfterAlphaCheckNId consNName
        (.const ``Nat []) .implicit .default) := by
  rw [consAfterAlphaCheckHeadLctxWF.find?_eq_find?_toList]
  simp [consAfterAlphaCheckHeadLctx, consAfterAlphaCheckHeadId, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaCheckNLctx, consAfterAlphaCheckNId,
    consAfterAlphaNatState, replayInsert, consAlphaContext, consRootContext, ctorContext,
    consAlphaId, AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId,
    LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId, NameGenerator.next,
    NameGenerator.curr]

theorem consAfterAlphaCheckAlphaCache :
    consAfterAlphaCheckHeadState.inferTypeC[
      (.fvar consAlphaId : Expr)]? =
        some (.sort (.succ (.param `u))) := by
  change consAfterAlphaHeadDomainState.inferTypeC[
    (.fvar consAlphaId : Expr)]? =
      some (.sort (.succ (.param `u)))
  unfold consAfterAlphaHeadDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

@[simp] theorem replayNatConstBeqIndexedVec :
    ((.const ``Nat [] : Expr) ==
      .const ``IndexedVec [.param `u]) = false := by
  change Expr.eqv (.const ``Nat [])
    (.const ``IndexedVec [.param `u]) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem replayAlphaIdBeqAfterAlphaNId :
    ((.fvar consAlphaId : Expr) ==
      .fvar consAfterAlphaCheckNId) = false := by
  change Expr.eqv (.fvar consAlphaId)
    (.fvar consAfterAlphaCheckNId) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', consAlphaId, consAfterAlphaCheckNId, consAfterAlphaNatState, replayInsert,
    consRootContext, ctorContext, AddInductive.Context.freshFVarId, NameGenerator.curr]

theorem consAfterAlphaCheckFamilyMiss :
    consAfterAlphaCheckHeadState.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none := by
  simp [consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState, replayInsert]

theorem consAfterAlphaCheckFirstAppMiss :
    consAfterAlphaCheckHeadState.inferTypeC[
      replayFirstApp (.fvar consAlphaId)]? = none := by
  simp [consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert, replayFirstApp]

def consAfterAlphaCheckFirstAppState : TypeChecker.State :=
  replayInsert
    (replayInsert consAfterAlphaCheckHeadState
      (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
    (replayFirstApp (.fvar consAlphaId)) vecFamilyTail

theorem consAfterAlphaCheckNMiss :
    consAfterAlphaCheckFirstAppState.inferTypeC[
      (.fvar consAfterAlphaCheckNId : Expr)]? = none := by
  simp [consAfterAlphaCheckFirstAppState,
    consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert, replayFirstApp]

theorem consAfterAlphaCheckTailMiss :
    consAfterAlphaCheckHeadState.inferTypeC[
      ctorIndexedVecApp (.fvar consAlphaId)
        (.fvar consAfterAlphaCheckNId)]? = none := by
  simp [consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert, ctorIndexedVecApp]

def consAfterAlphaCheckNInferState : TypeChecker.State :=
  replayInsert consAfterAlphaCheckFirstAppState
    (.fvar consAfterAlphaCheckNId) (.const ``Nat [])

def consAfterAlphaCheckTailDomainState : TypeChecker.State :=
  replayInsert consAfterAlphaCheckNInferState
    (ctorIndexedVecApp (.fvar consAlphaId)
      (.fvar consAfterAlphaCheckNId))
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterAlphaTailDomain (fuel : Nat) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consAlphaId)
        (.fvar consAfterAlphaCheckNId)) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consAfterAlphaCheckHeadLctx)
      consAfterAlphaCheckHeadState =
        .ok (.sort (.succ (.param `u)),
          consAfterAlphaCheckTailDomainState) := by
  simpa [consAfterAlphaCheckFirstAppState,
    consAfterAlphaCheckNInferState,
    consAfterAlphaCheckTailDomainState] using
    (replayInferTailDomainAlphaCachedCore fuel
      consAfterAlphaCheckHeadLctx consAfterAlphaCheckHeadState
      consAlphaId consAfterAlphaCheckNId
      consAfterAlphaCheckAlphaCache consAfterAlphaCheckFamilyMiss
      consAfterAlphaCheckFirstAppMiss consAfterAlphaCheckNMiss
      consAfterAlphaCheckTailMiss consAfterAlphaCheckNFind)

def consAfterAlphaCheckTailId : FVarId :=
  ⟨consAfterAlphaCheckTailDomainState.ngen.curr⟩

def consAfterAlphaCheckTailLctx : LocalContext :=
  consAfterAlphaCheckHeadLctx.mkLocalDecl consAfterAlphaCheckTailId
    consTailName
    (ctorIndexedVecApp (.fvar consAlphaId)
      (.fvar consAfterAlphaCheckNId)) .default

def consAfterAlphaCheckTailState : TypeChecker.State :=
  { consAfterAlphaCheckTailDomainState with
    ngen := consAfterAlphaCheckTailDomainState.ngen.next }

@[simp] theorem replayAfterAlphaNIdBeqAlphaId :
    ((.fvar consAfterAlphaCheckNId : Expr) ==
      .fvar consAlphaId) = false := by
  change Expr.eqv (.fvar consAfterAlphaCheckNId)
    (.fvar consAlphaId) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', consAlphaId, consAfterAlphaCheckNId, consAfterAlphaNatState, replayInsert,
    consRootContext, ctorContext, AddInductive.Context.freshFVarId, NameGenerator.curr]

@[simp] theorem replayNatConstBeqSucc :
    ((.const ``Nat [] : Expr) == .const ``Nat.succ []) = false := by
  change Expr.eqv (.const ``Nat []) (.const ``Nat.succ []) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem replayIndexedVecAppBeqFirstApp
    (alpha index : Expr) :
    (ctorIndexedVecApp alpha index == replayFirstApp alpha) = false := by
  change Expr.eqv (ctorIndexedVecApp alpha index)
    (replayFirstApp alpha) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replayFirstApp]

@[simp] theorem replayIndexedVecAppBeqSuccApp
    (alpha n : Expr) :
    (ctorIndexedVecApp alpha n == replaySuccApp n) = false := by
  change Expr.eqv (ctorIndexedVecApp alpha n)
    (replaySuccApp n) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replaySuccApp]

@[simp] theorem replayIndexedVecAppBeqIndexedVecSucc
    (alpha : Expr) (id : FVarId) :
    (ctorIndexedVecApp alpha (.fvar id) ==
      ctorIndexedVecApp alpha (replaySuccApp (.fvar id))) = false := by
  change Expr.eqv (ctorIndexedVecApp alpha (.fvar id))
    (ctorIndexedVecApp alpha (replaySuccApp (.fvar id))) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replaySuccApp]

@[simp] theorem replayFirstAppBeqIndexedVecSucc
    (alpha n : Expr) :
    (replayFirstApp alpha ==
      ctorIndexedVecApp alpha (replaySuccApp n)) = false := by
  change Expr.eqv (replayFirstApp alpha)
    (ctorIndexedVecApp alpha (replaySuccApp n)) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', ctorIndexedVecApp, replayFirstApp, replaySuccApp]

@[simp] theorem replayIndexedVecLiteralBeqSuccApp
    (alpha n : Expr) :
    (((.const ``IndexedVec [.param `u] : Expr).app alpha).app n ==
      (.const ``Nat.succ [] : Expr).app n) = false := by
  simpa [ctorIndexedVecApp, replaySuccApp] using
    replayIndexedVecAppBeqSuccApp alpha n

@[simp] theorem replayFirstAppLiteralGenericBeqSuccApp
    (alpha n : Expr) :
    ((.const ``IndexedVec [.param `u] : Expr).app alpha ==
      (.const ``Nat.succ [] : Expr).app n) = false := by
  simpa [replayFirstApp, replaySuccApp] using
    replayFirstAppBeqSuccApp alpha n

@[simp] theorem replayIndexedVecLiteralFVarBeqTerminal
    (alpha : Expr) (id : FVarId) :
    (((.const ``IndexedVec [.param `u] : Expr).app alpha).app
        (.fvar id) ==
      ((.const ``IndexedVec [.param `u] : Expr).app alpha).app
        ((.const ``Nat.succ [] : Expr).app (.fvar id))) = false := by
  simpa [ctorIndexedVecApp, replaySuccApp] using
    replayIndexedVecAppBeqIndexedVecSucc alpha id

@[simp] theorem replayFirstAppLiteralGenericBeqTerminal
    (alpha : Expr) (id : FVarId) :
    ((.const ``IndexedVec [.param `u] : Expr).app alpha ==
      ((.const ``IndexedVec [.param `u] : Expr).app alpha).app
        ((.const ``Nat.succ [] : Expr).app (.fvar id))) = false := by
  simpa [ctorIndexedVecApp, replayFirstApp, replaySuccApp] using
    replayFirstAppBeqIndexedVecSucc alpha (.fvar id)

theorem consAfterAlphaCheckTailFirstCache :
    consAfterAlphaCheckTailState.inferTypeC[
      replayFirstApp (.fvar consAlphaId)]? = some vecFamilyTail := by
  change consAfterAlphaCheckTailDomainState.inferTypeC[
    replayFirstApp (.fvar consAlphaId)]? = some vecFamilyTail
  unfold consAfterAlphaCheckTailDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [replayIndexedVecAppBeqFirstApp]
  simp only [Bool.false_eq_true, if_false]
  unfold consAfterAlphaCheckNInferState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show ((.fvar consAfterAlphaCheckNId : Expr) ==
      replayFirstApp (.fvar consAlphaId)) = false by
    exact replayFVarBeqApp consAfterAlphaCheckNId
      (.const ``IndexedVec [.param `u]) (.fvar consAlphaId)]
  simp only [Bool.false_eq_true, if_false]
  unfold consAfterAlphaCheckFirstAppState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consAfterAlphaCheckTailNCache :
    consAfterAlphaCheckTailState.inferTypeC[
      (.fvar consAfterAlphaCheckNId : Expr)]? =
        some (.const ``Nat []) := by
  change consAfterAlphaCheckTailDomainState.inferTypeC[
    (.fvar consAfterAlphaCheckNId : Expr)]? =
      some (.const ``Nat [])
  unfold consAfterAlphaCheckTailDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (ctorIndexedVecApp (.fvar consAlphaId)
      (.fvar consAfterAlphaCheckNId) ==
      (.fvar consAfterAlphaCheckNId : Expr)) = false by
    exact replayAppBeqFVar
      ((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId))
      (.fvar consAfterAlphaCheckNId) consAfterAlphaCheckNId]
  simp only [Bool.false_eq_true, if_false]
  unfold consAfterAlphaCheckNInferState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consAfterAlphaCheckTailSuccMiss :
    consAfterAlphaCheckTailState.inferTypeC[
      (.const ``Nat.succ [] : Expr)]? = none := by
  simp [consAfterAlphaCheckTailState,
    consAfterAlphaCheckTailDomainState,
    consAfterAlphaCheckNInferState,
    consAfterAlphaCheckFirstAppState,
    consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert, ctorIndexedVecApp, replayFirstApp]

theorem consAfterAlphaCheckTailSuccAppMiss :
    consAfterAlphaCheckTailState.inferTypeC[
      replaySuccApp (.fvar consAfterAlphaCheckNId)]? = none := by
  simp [consAfterAlphaCheckTailState,
    consAfterAlphaCheckTailDomainState,
    consAfterAlphaCheckNInferState,
    consAfterAlphaCheckFirstAppState,
    consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert, ctorIndexedVecApp, replayFirstApp, replaySuccApp]

theorem consAfterAlphaCheckTailTerminalMiss :
    consAfterAlphaCheckTailState.inferTypeC[
      ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consAfterAlphaCheckNId))]? = none := by
  simp [consAfterAlphaCheckTailState,
    consAfterAlphaCheckTailDomainState,
    consAfterAlphaCheckNInferState,
    consAfterAlphaCheckFirstAppState,
    consAfterAlphaCheckHeadState, consAfterAlphaHeadDomainState,
    consAfterAlphaCheckNState, consAfterAlphaNatState,
    replayInsert, ctorIndexedVecApp, replayFirstApp, replaySuccApp]

def consAfterAlphaCheckSuccState : TypeChecker.State :=
  replayInsert consAfterAlphaCheckTailState (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)

def consAfterAlphaCheckSuccAppState : TypeChecker.State :=
  replayInsert consAfterAlphaCheckSuccState
    (replaySuccApp (.fvar consAfterAlphaCheckNId)) (.const ``Nat [])

def consAfterAlphaCheckTerminalState : TypeChecker.State :=
  replayInsert consAfterAlphaCheckSuccAppState
    (ctorIndexedVecApp (.fvar consAlphaId)
      (replaySuccApp (.fvar consAfterAlphaCheckNId)))
    (.sort (.succ (.param `u)))

theorem replayInferConsAfterAlphaTerminal (fuel : Nat) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consAlphaId)
        (replaySuccApp (.fvar consAfterAlphaCheckNId))) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consAfterAlphaCheckTailLctx)
      consAfterAlphaCheckTailState =
        .ok (.sort (.succ (.param `u)),
          consAfterAlphaCheckTerminalState) := by
  simpa [consAfterAlphaCheckSuccState,
    consAfterAlphaCheckSuccAppState,
    consAfterAlphaCheckTerminalState] using
    (replayInferIndexedVecSuccFromCacheCore fuel
      consAfterAlphaCheckTailLctx consAfterAlphaCheckTailState
      consAlphaId consAfterAlphaCheckNId
      consAfterAlphaCheckTailFirstCache
      consAfterAlphaCheckTailSuccMiss
      consAfterAlphaCheckTailNCache
      consAfterAlphaCheckTailSuccAppMiss
      consAfterAlphaCheckTailTerminalMiss)

theorem replayConsAfterAlphaCheckTypeM :
    TypeChecker.M.run ctorEnv .safe consAlphaContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType consAfterAlpha) =
        .ok (.sort (.succ (.param `u))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType consAfterAlpha false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consAlphaContext.lctx) ({} : TypeChecker.State)) = _
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' consAfterAlpha false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consAlphaContext.lctx) ({} : TypeChecker.State)) = _
  unfold consAfterAlpha TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show TypeChecker.Inner.inferType'
      (.const ``Nat []) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAlphaContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), consAfterAlphaNatState) by
    exact replayInferConsAfterAlphaNat 9998]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp only [Expr.instantiate1']
  have hhead :
      TypeChecker.Inner.inferType (.fvar consAlphaId) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consAfterAlphaCheckNLctx)
        consAfterAlphaCheckNState =
          .ok (.sort (.succ (.param `u)),
            consAfterAlphaHeadDomainState) := by
    change TypeChecker.Inner.inferType' (.fvar consAlphaId) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterAlphaCheckNLctx)
      consAfterAlphaCheckNState = _
    exact replayInferConsAfterAlphaHeadDomain 9998
  simp only [consAfterAlphaCheckNLctx, consAfterAlphaCheckNId,
    consAfterAlphaCheckNState, tcContext] at hhead
  simp only [tcContext]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hhead]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp [Expr.instantiate1']
  have htail :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)).app
          (.fvar consAfterAlphaCheckNId)) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consAfterAlphaCheckHeadLctx)
        consAfterAlphaCheckHeadState =
          .ok (.sort (.succ (.param `u)),
            consAfterAlphaCheckTailDomainState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app
        (.fvar consAfterAlphaCheckNId)) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterAlphaCheckHeadLctx)
      consAfterAlphaCheckHeadState = _
    simpa [ctorIndexedVecApp] using
      replayInferConsAfterAlphaTailDomain 9998
  simp only [consAfterAlphaCheckHeadLctx,
    consAfterAlphaCheckHeadId, consAfterAlphaCheckHeadState,
    consAfterAlphaCheckNLctx, consAfterAlphaCheckNId,
    tcContext] at htail
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [htail]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp
  have hterminal :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consAlphaId)).app
          ((.const ``Nat.succ [] : Expr).app
            (.fvar consAfterAlphaCheckNId))) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consAfterAlphaCheckTailLctx)
        consAfterAlphaCheckTailState =
          .ok (.sort (.succ (.param `u)),
            consAfterAlphaCheckTerminalState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consAlphaId)).app
        ((.const ``Nat.succ [] : Expr).app
          (.fvar consAfterAlphaCheckNId))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consAfterAlphaCheckTailLctx)
      consAfterAlphaCheckTailState = _
    simpa [ctorIndexedVecApp, replaySuccApp] using
      replayInferConsAfterAlphaTerminal 9998
  simp only [consAfterAlphaCheckTailLctx,
    consAfterAlphaCheckTailId, consAfterAlphaCheckTailState,
    consAfterAlphaCheckHeadLctx, consAfterAlphaCheckHeadId,
    consAfterAlphaCheckNLctx, consAfterAlphaCheckNId,
    ctorIndexedVecApp, tcContext] at hterminal
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hterminal]
  simp only [ensureSortExact]
  simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]
  rfl

/-! The complete four-binder constructor type. -/

def consRootCheckAlphaId : FVarId :=
  ⟨nilRootSortState.ngen.curr⟩

def consRootCheckAlphaLctx : LocalContext :=
  consRootContext.lctx.mkLocalDecl consRootCheckAlphaId
    consAlphaName (.sort (.succ (.param `u))) .implicit

def consRootCheckAlphaState : TypeChecker.State :=
  { nilRootSortState with ngen := nilRootSortState.ngen.next }

theorem replayInferConsRootSort :
    TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consRootContext.lctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.succ (.param `u))),
          nilRootSortState) := by
  simpa [consRootContext, ctorContext] using nilRootSortCore

theorem consRootCheckAlphaFresh :
    consRootContext.lctx.find? consRootCheckAlphaId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consRootCheckAlphaId) LocalContext.WF.nil
  change
    ({ fvarIdToDecl := PersistentHashMap.empty,
       decls := PersistentArray.empty,
       auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
      consRootCheckAlphaId = none
  rw [h]
  simp [LocalContext.toList]

theorem consRootCheckAlphaLctxWF : consRootCheckAlphaLctx.WF := by
  change (({} : LocalContext).mkLocalDecl consRootCheckAlphaId
    consAlphaName (.sort (.succ (.param `u))) .implicit).WF
  exact LocalContext.WF.mkLocalDecl LocalContext.WF.nil (by
    have h := LocalContext.WF.find?_eq_find?_toList
      (fv := consRootCheckAlphaId) LocalContext.WF.nil
    change
      ({ fvarIdToDecl := PersistentHashMap.empty,
         decls := PersistentArray.empty,
         auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
        consRootCheckAlphaId = none
    rw [h]
    simp [LocalContext.toList])

theorem consRootCheckAlphaFind :
    consRootCheckAlphaLctx.find? consRootCheckAlphaId =
      some (.cdecl 0 consRootCheckAlphaId consAlphaName
        (.sort (.succ (.param `u))) .implicit .default) := by
  rw [consRootCheckAlphaLctxWF.find?_eq_find?_toList]
  simp [consRootCheckAlphaLctx, consRootCheckAlphaId, consRootContext, ctorContext,
    nilRootSortState, LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId,
    NameGenerator.curr]

theorem consRootCheckNatMiss :
    consRootCheckAlphaState.inferTypeC[
      (.const ``Nat [] : Expr)]? = none := by
  simp [consRootCheckAlphaState, nilRootSortState]

def consRootCheckNatState : TypeChecker.State :=
  replayInsert consRootCheckAlphaState (.const ``Nat [])
    (.sort (.succ .zero))

theorem replayInferConsRootNat (fuel : Nat) :
    TypeChecker.Inner.inferType' (.const ``Nat []) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consRootCheckAlphaLctx) consRootCheckAlphaState =
        .ok (.sort (.succ .zero), consRootCheckNatState) := by
  simpa [consRootCheckNatState, replayInsert] using
    (inferTypeNatCore fuel consRootCheckAlphaLctx
      consRootCheckAlphaState consRootCheckNatMiss)

def consRootCheckNId : FVarId :=
  ⟨consRootCheckNatState.ngen.curr⟩

def consRootCheckNLctx : LocalContext :=
  consRootCheckAlphaLctx.mkLocalDecl consRootCheckNId
    consNName (.const ``Nat []) .implicit

def consRootCheckNState : TypeChecker.State :=
  { consRootCheckNatState with ngen := consRootCheckNatState.ngen.next }

theorem consRootCheckNFresh :
    consRootCheckAlphaLctx.find? consRootCheckNId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consRootCheckNId) consRootCheckAlphaLctxWF
  rw [h]
  simp [consRootCheckNId, consRootCheckNatState, consRootCheckAlphaState, consRootCheckAlphaLctx,
    consRootCheckAlphaId, nilRootSortState, replayInsert, consRootContext, ctorContext,
    LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId, NameGenerator.next,
    NameGenerator.curr]
  intro x hx
  change some x ∈
    (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at hx
  rw [PersistentArray.toList'_empty] at hx
  simp at hx

theorem consRootCheckNLctxWF : consRootCheckNLctx.WF := by
  simpa [consRootCheckNLctx] using
    (LocalContext.WF.mkLocalDecl consRootCheckAlphaLctxWF
      consRootCheckNFresh)

theorem consRootCheckAlphaFindInN :
    consRootCheckNLctx.find? consRootCheckAlphaId =
      some (.cdecl 0 consRootCheckAlphaId consAlphaName
        (.sort (.succ (.param `u))) .implicit .default) := by
  rw [consRootCheckNLctxWF.find?_eq_find?_toList]
  simp [consRootCheckNLctx, consRootCheckNId, consRootCheckNatState, consRootCheckAlphaState,
    consRootCheckAlphaLctx, consRootCheckAlphaId, nilRootSortState, replayInsert, consRootContext,
    ctorContext, LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId,
    NameGenerator.next, NameGenerator.curr]

theorem consRootCheckAlphaMiss :
    consRootCheckNState.inferTypeC[
      (.fvar consRootCheckAlphaId : Expr)]? = none := by
  simp [consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState, replayInsert]

def consRootCheckHeadDomainState : TypeChecker.State :=
  replayInsert consRootCheckNState (.fvar consRootCheckAlphaId)
    (.sort (.succ (.param `u)))

theorem replayInferConsRootHeadDomain (fuel : Nat) :
    TypeChecker.Inner.inferType' (.fvar consRootCheckAlphaId) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consRootCheckNLctx) consRootCheckNState =
        .ok (.sort (.succ (.param `u)),
          consRootCheckHeadDomainState) := by
  simpa [consRootCheckHeadDomainState, replayInsert] using
    (inferTypeFVarCore fuel consRootCheckNLctx consRootCheckNState
      consRootCheckAlphaId (.sort (.succ (.param `u)))
      consRootCheckAlphaMiss consRootCheckAlphaFindInN)

def consRootCheckHeadId : FVarId :=
  ⟨consRootCheckHeadDomainState.ngen.curr⟩

def consRootCheckHeadLctx : LocalContext :=
  consRootCheckNLctx.mkLocalDecl consRootCheckHeadId
    consHeadName (.fvar consRootCheckAlphaId) .default

def consRootCheckHeadState : TypeChecker.State :=
  { consRootCheckHeadDomainState with
    ngen := consRootCheckHeadDomainState.ngen.next }

theorem consRootCheckHeadFresh :
    consRootCheckNLctx.find? consRootCheckHeadId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consRootCheckHeadId) consRootCheckNLctxWF
  rw [h]
  simp [consRootCheckHeadId, consRootCheckHeadDomainState, consRootCheckNState, consRootCheckNId,
    consRootCheckNatState, consRootCheckAlphaState, consRootCheckAlphaLctx, consRootCheckAlphaId,
    nilRootSortState, replayInsert, consRootCheckNLctx, consRootContext, ctorContext,
    LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId, NameGenerator.next,
    NameGenerator.curr]
  intro x hx
  change some x ∈
    (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at hx
  rw [PersistentArray.toList'_empty] at hx
  simp at hx

theorem consRootCheckHeadLctxWF : consRootCheckHeadLctx.WF := by
  simpa [consRootCheckHeadLctx] using
    (LocalContext.WF.mkLocalDecl consRootCheckNLctxWF
      consRootCheckHeadFresh)

theorem consRootCheckNFind :
    consRootCheckHeadLctx.find? consRootCheckNId =
      some (.cdecl 1 consRootCheckNId consNName
        (.const ``Nat []) .implicit .default) := by
  rw [consRootCheckHeadLctxWF.find?_eq_find?_toList]
  simp [consRootCheckHeadLctx, consRootCheckHeadId, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNLctx, consRootCheckNId, consRootCheckNatState,
    consRootCheckAlphaState, consRootCheckAlphaLctx, consRootCheckAlphaId, nilRootSortState,
    replayInsert, consRootContext, ctorContext, LocalContext.mkLocalDecl, LocalContext.toList,
    LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

@[simp] theorem replayConsRootAlphaIdBeqNId :
    ((.fvar consRootCheckAlphaId : Expr) ==
      .fvar consRootCheckNId) = false := by
  change Expr.eqv (.fvar consRootCheckAlphaId)
    (.fvar consRootCheckNId) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', consRootCheckAlphaId, consRootCheckNId,
    consRootCheckNatState, consRootCheckAlphaState,
    nilRootSortState, replayInsert,
    NameGenerator.next, NameGenerator.curr]

@[simp] theorem replayConsRootNIdBeqAlphaId :
    ((.fvar consRootCheckNId : Expr) ==
      .fvar consRootCheckAlphaId) = false := by
  change Expr.eqv (.fvar consRootCheckNId)
    (.fvar consRootCheckAlphaId) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', consRootCheckAlphaId, consRootCheckNId,
    consRootCheckNatState, consRootCheckAlphaState,
    nilRootSortState, replayInsert,
    NameGenerator.next, NameGenerator.curr]

theorem consRootCheckAlphaCache :
    consRootCheckHeadState.inferTypeC[
      (.fvar consRootCheckAlphaId : Expr)]? =
        some (.sort (.succ (.param `u))) := by
  change consRootCheckHeadDomainState.inferTypeC[
    (.fvar consRootCheckAlphaId : Expr)]? =
      some (.sort (.succ (.param `u)))
  unfold consRootCheckHeadDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consRootCheckFamilyMiss :
    consRootCheckHeadState.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none := by
  simp [consRootCheckHeadState, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState, replayInsert]

theorem consRootCheckFirstAppMiss :
    consRootCheckHeadState.inferTypeC[
      replayFirstApp (.fvar consRootCheckAlphaId)]? = none := by
  simp [consRootCheckHeadState, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState,
    replayInsert, replayFirstApp]

def consRootCheckFirstAppState : TypeChecker.State :=
  replayInsert
    (replayInsert consRootCheckHeadState
      (.const ``IndexedVec [.param `u]) indexedVecInfo.type)
    (replayFirstApp (.fvar consRootCheckAlphaId)) vecFamilyTail

theorem consRootCheckNMiss :
    consRootCheckFirstAppState.inferTypeC[
      (.fvar consRootCheckNId : Expr)]? = none := by
  simp [consRootCheckFirstAppState, consRootCheckHeadState,
    consRootCheckHeadDomainState, consRootCheckNState,
    consRootCheckNatState, consRootCheckAlphaState,
    nilRootSortState, replayInsert, replayFirstApp]

theorem consRootCheckTailMiss :
    consRootCheckHeadState.inferTypeC[
      ctorIndexedVecApp (.fvar consRootCheckAlphaId)
        (.fvar consRootCheckNId)]? = none := by
  simp [consRootCheckHeadState, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState,
    replayInsert, ctorIndexedVecApp]

def consRootCheckNInferState : TypeChecker.State :=
  replayInsert consRootCheckFirstAppState
    (.fvar consRootCheckNId) (.const ``Nat [])

def consRootCheckTailDomainState : TypeChecker.State :=
  replayInsert consRootCheckNInferState
    (ctorIndexedVecApp (.fvar consRootCheckAlphaId)
      (.fvar consRootCheckNId))
    (.sort (.succ (.param `u)))

theorem replayInferConsRootTailDomain (fuel : Nat) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consRootCheckAlphaId)
        (.fvar consRootCheckNId)) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consRootCheckHeadLctx) consRootCheckHeadState =
        .ok (.sort (.succ (.param `u)),
          consRootCheckTailDomainState) := by
  simpa [consRootCheckFirstAppState, consRootCheckNInferState,
    consRootCheckTailDomainState] using
    (replayInferTailDomainAlphaCachedCore fuel
      consRootCheckHeadLctx consRootCheckHeadState
      consRootCheckAlphaId consRootCheckNId
      consRootCheckAlphaCache consRootCheckFamilyMiss
      consRootCheckFirstAppMiss consRootCheckNMiss
      consRootCheckTailMiss consRootCheckNFind)

def consRootCheckTailId : FVarId :=
  ⟨consRootCheckTailDomainState.ngen.curr⟩

def consRootCheckTailLctx : LocalContext :=
  consRootCheckHeadLctx.mkLocalDecl consRootCheckTailId
    consTailName
    (ctorIndexedVecApp (.fvar consRootCheckAlphaId)
      (.fvar consRootCheckNId)) .default

def consRootCheckTailState : TypeChecker.State :=
  { consRootCheckTailDomainState with
    ngen := consRootCheckTailDomainState.ngen.next }

theorem consRootCheckTailFirstCache :
    consRootCheckTailState.inferTypeC[
      replayFirstApp (.fvar consRootCheckAlphaId)]? =
        some vecFamilyTail := by
  change consRootCheckTailDomainState.inferTypeC[
    replayFirstApp (.fvar consRootCheckAlphaId)]? = some vecFamilyTail
  unfold consRootCheckTailDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [replayIndexedVecAppBeqFirstApp]
  simp only [Bool.false_eq_true, if_false]
  unfold consRootCheckNInferState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show ((.fvar consRootCheckNId : Expr) ==
      replayFirstApp (.fvar consRootCheckAlphaId)) = false by
    exact replayFVarBeqApp consRootCheckNId
      (.const ``IndexedVec [.param `u])
      (.fvar consRootCheckAlphaId)]
  simp only [Bool.false_eq_true, if_false]
  unfold consRootCheckFirstAppState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consRootCheckTailNCache :
    consRootCheckTailState.inferTypeC[
      (.fvar consRootCheckNId : Expr)]? = some (.const ``Nat []) := by
  change consRootCheckTailDomainState.inferTypeC[
    (.fvar consRootCheckNId : Expr)]? = some (.const ``Nat [])
  unfold consRootCheckTailDomainState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [show (ctorIndexedVecApp (.fvar consRootCheckAlphaId)
      (.fvar consRootCheckNId) ==
      (.fvar consRootCheckNId : Expr)) = false by
    exact replayAppBeqFVar
      ((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consRootCheckAlphaId))
      (.fvar consRootCheckNId) consRootCheckNId]
  simp only [Bool.false_eq_true, if_false]
  unfold consRootCheckNInferState replayInsert
  rw [Std.HashMap.getElem?_insert]
  rw [beq_self_eq_true]
  rfl

theorem consRootCheckTailSuccMiss :
    consRootCheckTailState.inferTypeC[
      (.const ``Nat.succ [] : Expr)]? = none := by
  simp [consRootCheckTailState, consRootCheckTailDomainState,
    consRootCheckNInferState, consRootCheckFirstAppState,
    consRootCheckHeadState, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState,
    replayInsert, ctorIndexedVecApp, replayFirstApp]

theorem consRootCheckTailSuccAppMiss :
    consRootCheckTailState.inferTypeC[
      replaySuccApp (.fvar consRootCheckNId)]? = none := by
  simp [consRootCheckTailState, consRootCheckTailDomainState,
    consRootCheckNInferState, consRootCheckFirstAppState,
    consRootCheckHeadState, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState,
    replayInsert, ctorIndexedVecApp, replayFirstApp, replaySuccApp]

theorem consRootCheckTailTerminalMiss :
    consRootCheckTailState.inferTypeC[
      ctorIndexedVecApp (.fvar consRootCheckAlphaId)
        (replaySuccApp (.fvar consRootCheckNId))]? = none := by
  simp [consRootCheckTailState, consRootCheckTailDomainState,
    consRootCheckNInferState, consRootCheckFirstAppState,
    consRootCheckHeadState, consRootCheckHeadDomainState,
    consRootCheckNState, consRootCheckNatState,
    consRootCheckAlphaState, nilRootSortState,
    replayInsert, ctorIndexedVecApp, replayFirstApp, replaySuccApp]

def consRootCheckSuccState : TypeChecker.State :=
  replayInsert consRootCheckTailState (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)

def consRootCheckSuccAppState : TypeChecker.State :=
  replayInsert consRootCheckSuccState
    (replaySuccApp (.fvar consRootCheckNId)) (.const ``Nat [])

def consRootCheckTerminalState : TypeChecker.State :=
  replayInsert consRootCheckSuccAppState
    (ctorIndexedVecApp (.fvar consRootCheckAlphaId)
      (replaySuccApp (.fvar consRootCheckNId)))
    (.sort (.succ (.param `u)))

theorem replayInferConsRootTerminal (fuel : Nat) :
    TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar consRootCheckAlphaId)
        (replaySuccApp (.fvar consRootCheckNId))) false
      (TypeChecker.Methods.withFuel fuel)
      (tcContext consRootCheckTailLctx) consRootCheckTailState =
        .ok (.sort (.succ (.param `u)),
          consRootCheckTerminalState) := by
  simpa [consRootCheckSuccState, consRootCheckSuccAppState,
    consRootCheckTerminalState] using
    (replayInferIndexedVecSuccFromCacheCore fuel
      consRootCheckTailLctx consRootCheckTailState
      consRootCheckAlphaId consRootCheckNId
      consRootCheckTailFirstCache consRootCheckTailSuccMiss
      consRootCheckTailNCache consRootCheckTailSuccAppMiss
      consRootCheckTailTerminalMiss)

open private mkLevelIMaxCore mkLevelMaxCore from Lean.Level in
@[simp] theorem replayMkLevelIMaxSuccSuccParamSuccParam :
    mkLevelIMax' (.succ (.succ (.param `u)))
      (.succ (.param `u)) = .succ (.succ (.param `u)) := by
  simp [mkLevelIMax', mkLevelIMaxCore, mkLevelMax', mkLevelMaxCore,
    Level.isNeverZero, Level.isZero, Level.isExplicit,
    Level.hasMVar', Level.hasParam', Level.getOffset,
    Level.getOffsetAux, Level.getLevelOffset]

theorem replayConsRootCheckTypeM :
    TypeChecker.M.run ctorEnv .safe consRootContext.lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType indexedVecConsInfo.type) =
        .ok (.sort (.succ (.succ (.param `u)))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType indexedVecConsInfo.type false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext consRootContext.lctx) ({} : TypeChecker.State)) = _
  rw [consInfoTypeShape]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' consCtorTypeRaw false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext consRootContext.lctx) ({} : TypeChecker.State)) = _
  unfold consCtorTypeRaw consNTypeRaw consHeadTypeRaw
    consTailTypeRaw consTerminalRaw TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferForall, TypeChecker.Inner.inferForall.loop,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [replayInferConsRootSort]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp [Expr.instantiate1']
  have hnat :
      TypeChecker.Inner.inferType (.const ``Nat []) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consRootCheckAlphaLctx) consRootCheckAlphaState =
          .ok (.sort (.succ .zero), consRootCheckNatState) := by
    change TypeChecker.Inner.inferType' (.const ``Nat []) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consRootCheckAlphaLctx) consRootCheckAlphaState = _
    exact replayInferConsRootNat 9998
  simp only [consRootCheckAlphaLctx, consRootCheckAlphaId,
    consRootCheckAlphaState, tcContext] at hnat
  simp only [tcContext]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hnat]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp [Expr.instantiate1']
  have hhead :
      TypeChecker.Inner.inferType (.fvar consRootCheckAlphaId) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consRootCheckNLctx) consRootCheckNState =
          .ok (.sort (.succ (.param `u)),
            consRootCheckHeadDomainState) := by
    change TypeChecker.Inner.inferType'
      (.fvar consRootCheckAlphaId) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consRootCheckNLctx) consRootCheckNState = _
    exact replayInferConsRootHeadDomain 9998
  simp only [consRootCheckNLctx, consRootCheckNId,
    consRootCheckNState, consRootCheckAlphaLctx,
    consRootCheckAlphaId, tcContext] at hhead
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hhead]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp
  have htail :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consRootCheckAlphaId)).app
          (.fvar consRootCheckNId)) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consRootCheckHeadLctx) consRootCheckHeadState =
          .ok (.sort (.succ (.param `u)),
            consRootCheckTailDomainState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consRootCheckAlphaId)).app
        (.fvar consRootCheckNId)) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consRootCheckHeadLctx) consRootCheckHeadState = _
    simpa [ctorIndexedVecApp] using
      replayInferConsRootTailDomain 9998
  simp only [consRootCheckHeadLctx, consRootCheckHeadId,
    consRootCheckHeadState, consRootCheckNLctx, consRootCheckNId,
    consRootCheckAlphaLctx, consRootCheckAlphaId,
    tcContext] at htail
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [htail]
  simp only [ensureSortExact]
  rw [withLocalDeclEq]
  simp
  have hterminal :
      TypeChecker.Inner.inferType
        (((.const ``IndexedVec [.param `u] : Expr).app
          (.fvar consRootCheckAlphaId)).app
          ((.const ``Nat.succ [] : Expr).app
            (.fvar consRootCheckNId))) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext consRootCheckTailLctx) consRootCheckTailState =
          .ok (.sort (.succ (.param `u)),
            consRootCheckTerminalState) := by
    change TypeChecker.Inner.inferType'
      (((.const ``IndexedVec [.param `u] : Expr).app
        (.fvar consRootCheckAlphaId)).app
        ((.const ``Nat.succ [] : Expr).app
          (.fvar consRootCheckNId))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext consRootCheckTailLctx) consRootCheckTailState = _
    simpa [ctorIndexedVecApp, replaySuccApp] using
      replayInferConsRootTerminal 9998
  simp only [consRootCheckTailLctx, consRootCheckTailId,
    consRootCheckTailState, consRootCheckHeadLctx,
    consRootCheckHeadId, consRootCheckNLctx, consRootCheckNId,
    consRootCheckAlphaLctx, consRootCheckAlphaId,
    ctorIndexedVecApp, tcContext] at hterminal
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hterminal]
  simp only [ensureSortExact]
  simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]
  rfl

/-! ## Source-indexed candidate trace -/

def consAlphaAnnotations :
    AddInductive.CandidateTypeAnnotations
      (.sort (.succ (.param `u))) where
  consumed := .sort (.succ (.param `u))
  trace := .identity _

def consNatAnnotations :
    AddInductive.CandidateTypeAnnotations (.const ``Nat []) where
  consumed := .const ``Nat []
  trace := .identity _

def consHeadAnnotations :
    AddInductive.CandidateTypeAnnotations consAlphaExpr where
  consumed := consAlphaExpr
  trace := .identity _

def consTailAnnotations :
    AddInductive.CandidateTypeAnnotations consTailDomain where
  consumed := consTailDomain
  trace := .identity _

theorem consAlphaAnnotationTraceBuild :
    AddInductive.CandidateTypeAnnotationTrace.build
      (.sort (.succ (.param `u))) =
        ⟨.sort (.succ (.param `u)), .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build]

theorem consNatAnnotationTraceBuild :
    AddInductive.CandidateTypeAnnotationTrace.build (.const ``Nat []) =
      ⟨.const ``Nat [], .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build]

theorem consHeadAnnotationTraceBuild :
    AddInductive.CandidateTypeAnnotationTrace.build consAlphaExpr =
      ⟨consAlphaExpr, .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build,
    consAlphaExprShape]

theorem consTailAnnotationTraceBuild :
    AddInductive.CandidateTypeAnnotationTrace.build consTailDomain =
      ⟨consTailDomain, .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build, consTailDomain]

theorem consAlphaAnnotationsBuild :
    AddInductive.buildCandidateTypeAnnotations
      (.sort (.succ (.param `u))) = .ok consAlphaAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [consAlphaAnnotationTraceBuild]
  rfl

theorem consNatAnnotationsBuild :
    AddInductive.buildCandidateTypeAnnotations (.const ``Nat []) =
      .ok consNatAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [consNatAnnotationTraceBuild]
  rfl

theorem consHeadAnnotationsBuild :
    AddInductive.buildCandidateTypeAnnotations consAlphaExpr =
      .ok consHeadAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [consHeadAnnotationTraceBuild]
  rfl

theorem consTailAnnotationsBuild :
    AddInductive.buildCandidateTypeAnnotations consTailDomain =
      .ok consTailAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [consTailAnnotationTraceBuild]
  rfl

theorem consAlphaAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨consRootContext, (.sort (.succ (.param `u))),
        consAlphaAnnotations.consumed⟩ := by
  simpa [consAlphaAnnotations] using
    (candidateIsDefEqSelfValid consRootContext
      (.sort (.succ (.param `u))) 9999 rfl)

theorem consNatAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨consAlphaContext, (.const ``Nat []),
        consNatAnnotations.consumed⟩ := by
  simpa [consNatAnnotations] using
    (candidateIsDefEqSelfValid consAlphaContext
      (.const ``Nat []) 9999 rfl)

theorem consHeadAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨consNContext, consAlphaExpr,
        consHeadAnnotations.consumed⟩ := by
  simpa [consHeadAnnotations] using
    (candidateIsDefEqSelfValid consNContext consAlphaExpr 9999 rfl)

theorem consTailAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨consHeadContext, consTailDomain,
        consTailAnnotations.consumed⟩ := by
  simpa [consTailAnnotations] using
    (candidateIsDefEqSelfValid consHeadContext consTailDomain 9999 rfl)

theorem consRootCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consRootContext, indexedVecConsInfo.type,
        .sort (.succ (.succ (.param `u)))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consRootContext, ctorContext] using
    replayConsRootCheckTypeM

theorem consRootWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consRootContext, indexedVecConsInfo.type,
        indexedVecConsInfo.type⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consRootContext, ctorContext] using replayConsRootWhnfM

theorem consAfterAlphaCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consAlphaContext, consAfterAlpha,
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl] using
    replayConsAfterAlphaCheckTypeM

theorem consAfterAlphaWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consAlphaContext, consAfterAlpha, consAfterAlpha⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl] using
    replayConsAfterAlphaWhnfM

theorem consAfterNCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consNContext, consAfterN, .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consNContext, consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl] using
    replayConsAfterNCheckTypeM

theorem consAfterNWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consNContext, consAfterN, consAfterN⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consNContext, consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl] using
    replayConsAfterNWhnfM

theorem consAfterHeadCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consHeadContext, consAfterHead,
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    replayConsAfterHeadCheckTypeM

theorem consAfterHeadWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consHeadContext, consAfterHead, consAfterHead⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    replayConsAfterHeadWhnfM

theorem consTerminalCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consTailContext, consTerminal,
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consTailContext, consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    replayConsTerminalCheckTypeM

theorem consTerminalWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consTailContext, consTerminal, consTerminal⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consTailContext, consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    replayConsTerminalWhnfM

theorem consAlphaDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consRootContext, (.sort (.succ (.param `u))),
        .sort (.succ (.succ (.param `u)))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consRootContext, nilCandidateContext, ctorContext] using
    nilDomainCheckValid

theorem consAlphaDomainWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consRootContext, (.sort (.succ (.param `u))),
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consRootContext, nilCandidateContext, ctorContext] using
    nilDomainWhnfValid

theorem consNatDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consAlphaContext, (.const ``Nat []),
        .sort (.succ .zero)⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl] using
    ctorNatCheckTypeM consAlphaContext.lctx

theorem consNatDomainWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consAlphaContext, (.const ``Nat []), (.const ``Nat [])⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl] using
    ctorNatWhnfM consAlphaContext.lctx

theorem consHeadDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consNContext, consAlphaExpr,
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consAlphaExprShape, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    (ctorFVarCheckTypeM consNContext.lctx consAlphaId
      (.sort (.succ (.param `u))) consAlphaFindInN)

theorem consHeadDomainWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consNContext, consAlphaExpr, consAlphaExpr⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consAlphaExprShape, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    (ctorFVarWhnfM consNContext.lctx consAlphaId consAlphaFindInN)

theorem consTailDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨consHeadContext, consTailDomain,
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    replayConsTailDomainCheckTypeM

theorem consTailDomainWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨consHeadContext, consTailDomain, consTailDomain⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl] using
    replayConsTailDomainWhnfM

def consAlphaDomainCandidateTrace :
    AddInductive.CandidateExprTrace consRootContext
      (.sort (.succ (.param `u))) :=
  .terminal consRootContext (.sort (.succ (.param `u)))
    (.sort (.succ (.succ (.param `u))))
    (.sort (.succ (.param `u)))
    consAlphaDomainCheckValid consAlphaDomainWhnfValid

def consNatDomainCandidateTrace :
    AddInductive.CandidateExprTrace consAlphaContext
      (.const ``Nat []) :=
  .terminal consAlphaContext (.const ``Nat [])
    (.sort (.succ .zero)) (.const ``Nat [])
    consNatDomainCheckValid consNatDomainWhnfValid

def consHeadDomainCandidateTrace :
    AddInductive.CandidateExprTrace consNContext consAlphaExpr :=
  .terminal consNContext consAlphaExpr
    (.sort (.succ (.param `u))) consAlphaExpr
    consHeadDomainCheckValid consHeadDomainWhnfValid

def consTailDomainCandidateTrace :
    AddInductive.CandidateExprTrace consHeadContext consTailDomain :=
  .terminal consHeadContext consTailDomain
    (.sort (.succ (.param `u))) consTailDomain
    consTailDomainCheckValid consTailDomainWhnfValid

def consTerminalCandidateTrace :
    AddInductive.CandidateExprTrace consTailContext
      (consAfterHead.bindingBody!.instantiate1
        consHeadContext.freshExpr) :=
  .terminal consTailContext
    (consAfterHead.bindingBody!.instantiate1 consHeadContext.freshExpr)
    (.sort (.succ (.param `u))) consTerminal
    (by simpa only [consTerminalShape] using consTerminalCheckValid)
    (by simpa only [consTerminalShape] using consTerminalWhnfValid)

def consAfterHeadCandidateTrace :
    AddInductive.CandidateExprTrace consHeadContext
      (consAfterN.bindingBody!.instantiate1 consNContext.freshExpr) :=
  .forallE consHeadContext
    (consAfterN.bindingBody!.instantiate1 consNContext.freshExpr)
    (.sort (.succ (.param `u))) consTailName consTailDomain
    consAfterHead.bindingBody! .default consHeadContextFresh
    consTailAnnotations consTailAnnotationsEq
    (by simpa only [consAfterHeadShape] using consAfterHeadCheckValid)
    (by
      simpa [consAfterN, consAfterHead, consTailDomain,
        consAlphaExpr, consNExpr, consRootContext, consAlphaContext,
        consNContext, ctorContext, AddInductive.Context.pushLocalDecl,
        AddInductive.Context.freshExpr, Expr.bindingBody!,
        Expr.instantiate1_eq, Expr.instantiate1',
        Expr.liftLooseBVars_zero] using
        consAfterHeadWhnfValid)
    consTailDomainCandidateTrace consTerminalCandidateTrace

def consAfterNCandidateTrace :
    AddInductive.CandidateExprTrace consNContext
      (consAfterAlpha.bindingBody!.instantiate1
        consAlphaContext.freshExpr) :=
  .forallE consNContext
    (consAfterAlpha.bindingBody!.instantiate1
      consAlphaContext.freshExpr)
    (.sort (.succ (.param `u))) consHeadName consAlphaExpr
    consAfterN.bindingBody! .default consNContextFresh
    consHeadAnnotations consHeadAnnotationsEq
    (by simpa only [consAfterNShape] using consAfterNCheckValid)
    (by
      simpa [consAfterAlpha, consAfterN, consAlphaExpr, consNExpr,
        consRootContext, consAlphaContext, ctorContext,
        AddInductive.Context.pushLocalDecl,
        AddInductive.Context.freshExpr, Expr.bindingBody!,
        Expr.instantiate1_eq, Expr.instantiate1',
        Expr.liftLooseBVars_zero] using
        consAfterNWhnfValid)
    consHeadDomainCandidateTrace consAfterHeadCandidateTrace

def consAfterAlphaCandidateTrace :
    AddInductive.CandidateExprTrace consAlphaContext
      (consNTypeRaw.instantiate1 consRootContext.freshExpr) :=
  .forallE consAlphaContext
    (consNTypeRaw.instantiate1 consRootContext.freshExpr)
    (.sort (.succ (.param `u))) consNName (.const ``Nat [])
    consAfterAlpha.bindingBody! .implicit consAlphaContextFresh
    consNatAnnotations consNatAnnotationsEq
    (by simpa only [consAfterAlphaShape] using consAfterAlphaCheckValid)
    (by
      simpa [consNTypeRaw, consHeadTypeRaw, consTailTypeRaw,
        consTerminalRaw, consAfterAlpha, consAlphaExpr,
        consRootContext, ctorContext, AddInductive.Context.freshExpr,
        Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1',
        Expr.liftLooseBVars_zero] using
        consAfterAlphaWhnfValid)
    consNatDomainCandidateTrace consAfterNCandidateTrace

def consCandidateTrace :
    AddInductive.CandidateExprTrace consRootContext
      indexedVecConsInfo.type :=
  .forallE consRootContext indexedVecConsInfo.type
    (.sort (.succ (.succ (.param `u)))) consAlphaName
    (.sort (.succ (.param `u))) consNTypeRaw .implicit consRootFresh
    consAlphaAnnotations consAlphaAnnotationsEq consRootCheckValid
    (by
      simpa [consInfoTypeShape, consCtorTypeRaw] using consRootWhnfValid)
    consAlphaDomainCandidateTrace consAfterAlphaCandidateTrace

def consCandidate : AddInductive.CandidateExpr indexedVecConsInfo.type :=
  ⟨consRootContext, consCandidateTrace⟩

theorem consCandidate_view_eq :
    consCandidate.view = indexedVecConsInfo.type := by
  have habstract (context : AddInductive.Context) (e : Expr) :
      e.abstract #[context.freshExpr] =
        Expr.abstract1 context.freshFVarId e := by
    rw [show #[context.freshExpr] =
      ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
    simp only [Expr.abstract_eq, Expr.abstractList]
  simp only [consCandidate, AddInductive.CandidateExpr.view,
    consCandidateTrace, consAlphaDomainCandidateTrace,
    consNatDomainCandidateTrace, consHeadDomainCandidateTrace,
    consTailDomainCandidateTrace, consTerminalCandidateTrace,
    consAfterHeadCandidateTrace, consAfterNCandidateTrace,
    consAfterAlphaCandidateTrace, AddInductive.CandidateExprTrace.view]
  rw [habstract, habstract, habstract, habstract]
  rw [consInfoTypeShape]
  simp [consCtorTypeRaw, consNTypeRaw, consHeadTypeRaw,
    consTailTypeRaw, consTerminalRaw, consTerminal, consTailDomain,
    consAlphaExpr, consNExpr,
    consRootContext, consAlphaContext, ctorContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId,
    Expr.abstract1, NameGenerator.next, NameGenerator.curr]

/-- The retained `cons` candidate preserves all four Pi nodes, their domains,
and the terminal recursive result under the exact instantiated contexts. -/
theorem consCandidate_identity :
    TypeChecker.CandidateExprIdentity consCandidate.trace := by
  change TypeChecker.CandidateExprIdentity consCandidateTrace
  unfold consCandidateTrace
  refine .forallE (name := consAlphaName) (binderInfo := .implicit)
    (body := consNTypeRaw) (annotations := consAlphaAnnotations)
    consAlphaDomainCandidateTrace consAfterAlphaCandidateTrace
    (by simpa [consCtorTypeRaw] using consInfoTypeShape)
    rfl (.terminal rfl) ?_
  · unfold consAfterAlphaCandidateTrace
    refine .forallE (name := consNName) (binderInfo := .implicit)
      (body := consAfterAlpha.bindingBody!)
      (annotations := consNatAnnotations)
      consNatDomainCandidateTrace consAfterNCandidateTrace
      (by rw [consAfterAlphaShape]; rfl) rfl (.terminal rfl) ?_
    · unfold consAfterNCandidateTrace
      refine .forallE (name := consHeadName) (binderInfo := .default)
        (body := consAfterN.bindingBody!)
        (annotations := consHeadAnnotations)
        consHeadDomainCandidateTrace consAfterHeadCandidateTrace
        (by rw [consAfterNShape]; rfl) rfl (.terminal rfl) ?_
      · unfold consAfterHeadCandidateTrace
        refine .forallE (name := consTailName) (binderInfo := .default)
          (body := consAfterHead.bindingBody!)
          (annotations := consTailAnnotations)
          consTailDomainCandidateTrace consTerminalCandidateTrace
          (by rw [consAfterHeadShape]; rfl) rfl (.terminal rfl) ?_
        · unfold consTerminalCandidateTrace
          exact .terminal (by
            simpa only [Expr.instantiate1_eq] using consTerminalShape.symm)

theorem consAlphaDomainCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop consRootContext
      (.sort (.succ (.param `u))) (fuel + 1) =
        .ok consAlphaDomainCandidateTrace := by
  simpa only [consAlphaDomainCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      consRootContext (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u))))
      (.sort (.succ (.param `u))) fuel
      consAlphaDomainCheckValid consAlphaDomainWhnfValid rfl

theorem consNatDomainCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop consAlphaContext
      (.const ``Nat []) (fuel + 1) =
        .ok consNatDomainCandidateTrace := by
  simpa only [consNatDomainCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      consAlphaContext (.const ``Nat []) (.sort (.succ .zero))
      (.const ``Nat []) fuel consNatDomainCheckValid
      consNatDomainWhnfValid rfl

theorem consHeadDomainCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop consNContext consAlphaExpr
      (fuel + 1) = .ok consHeadDomainCandidateTrace := by
  simpa only [consHeadDomainCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      consNContext consAlphaExpr (.sort (.succ (.param `u)))
      consAlphaExpr fuel consHeadDomainCheckValid
      consHeadDomainWhnfValid (by rw [consAlphaExprShape]; rfl)

theorem consTailDomainCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop consHeadContext consTailDomain
      (fuel + 1) = .ok consTailDomainCandidateTrace := by
  simpa only [consTailDomainCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      consHeadContext consTailDomain (.sort (.succ (.param `u)))
      consTailDomain fuel consTailDomainCheckValid
      consTailDomainWhnfValid (by rfl)

theorem consTerminalCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop consTailContext
      (consAfterHead.bindingBody!.instantiate1
        consHeadContext.freshExpr) (fuel + 1) =
        .ok consTerminalCandidateTrace := by
  simpa only [consTerminalCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      consTailContext
      (consAfterHead.bindingBody!.instantiate1 consHeadContext.freshExpr)
      (.sort (.succ (.param `u))) consTerminal fuel
      (by simpa only [consTerminalShape] using consTerminalCheckValid)
      (by simpa only [consTerminalShape] using consTerminalWhnfValid)
      (by rfl)

theorem consAfterHeadCandidateTraceLoop :
    AddInductive.buildCandidateExpr.loop consHeadContext
      (consAfterN.bindingBody!.instantiate1 consNContext.freshExpr) 997 =
        .ok consAfterHeadCandidateTrace := by
  rw [show 997 = 996 + 1 by rfl]
  simpa only [consAfterHeadCandidateTrace, consTailContext,
    consTailAnnotations] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := consHeadContext)
      (e := consAfterN.bindingBody!.instantiate1 consNContext.freshExpr)
      (inferred := .sort (.succ (.param `u))) (fuel := 996)
      (name := consTailName) (domain := consTailDomain)
      (body := consAfterHead.bindingBody!) (binderInfo := .default)
      (hfresh := consHeadContextFresh)
      (annotations := consTailAnnotations)
      (hannotations := consTailAnnotationsBuild)
      (hannotationsEq := consTailAnnotationsEq)
      (hcheck := by
        simpa only [consAfterHeadShape] using consAfterHeadCheckValid)
      (hrun := by
        simpa [consAfterN, consAfterHead, consTailDomain,
          consAlphaExpr, consNExpr, consRootContext, consAlphaContext,
          consNContext, ctorContext, AddInductive.Context.pushLocalDecl,
          AddInductive.Context.freshExpr, Expr.bindingBody!,
          Expr.instantiate1_eq, Expr.instantiate1',
          Expr.liftLooseBVars_zero] using
          consAfterHeadWhnfValid)
      (domainCandidate := consTailDomainCandidateTrace)
      (bodyCandidate := consTerminalCandidateTrace)
      (hdomain := by
        simpa using consTailDomainCandidateTraceLoop 995)
      (hbody := by
        simpa [consTailContext, consTailAnnotations] using
          consTerminalCandidateTraceLoop 995))

theorem consAfterNCandidateTraceLoop :
    AddInductive.buildCandidateExpr.loop consNContext
      (consAfterAlpha.bindingBody!.instantiate1
        consAlphaContext.freshExpr) 998 =
        .ok consAfterNCandidateTrace := by
  rw [show 998 = 997 + 1 by rfl]
  simpa only [consAfterNCandidateTrace, consHeadContext,
    consHeadAnnotations] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := consNContext)
      (e := consAfterAlpha.bindingBody!.instantiate1
        consAlphaContext.freshExpr)
      (inferred := .sort (.succ (.param `u))) (fuel := 997)
      (name := consHeadName) (domain := consAlphaExpr)
      (body := consAfterN.bindingBody!) (binderInfo := .default)
      (hfresh := consNContextFresh)
      (annotations := consHeadAnnotations)
      (hannotations := consHeadAnnotationsBuild)
      (hannotationsEq := consHeadAnnotationsEq)
      (hcheck := by
        simpa only [consAfterNShape] using consAfterNCheckValid)
      (hrun := by
        simpa [consAfterAlpha, consAfterN, consAlphaExpr, consNExpr,
          consRootContext, consAlphaContext, ctorContext,
          AddInductive.Context.pushLocalDecl,
          AddInductive.Context.freshExpr, Expr.bindingBody!,
          Expr.instantiate1_eq, Expr.instantiate1',
          Expr.liftLooseBVars_zero] using
          consAfterNWhnfValid)
      (domainCandidate := consHeadDomainCandidateTrace)
      (bodyCandidate := consAfterHeadCandidateTrace)
      (hdomain := by
        simpa using consHeadDomainCandidateTraceLoop 996)
      (hbody := by
        simpa [consHeadContext, consHeadAnnotations] using
          consAfterHeadCandidateTraceLoop))

theorem consAfterAlphaCandidateTraceLoop :
    AddInductive.buildCandidateExpr.loop consAlphaContext
      (consNTypeRaw.instantiate1 consRootContext.freshExpr) 999 =
        .ok consAfterAlphaCandidateTrace := by
  rw [show 999 = 998 + 1 by rfl]
  simpa only [consAfterAlphaCandidateTrace, consNContext,
    consNatAnnotations] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := consAlphaContext)
      (e := consNTypeRaw.instantiate1 consRootContext.freshExpr)
      (inferred := .sort (.succ (.param `u))) (fuel := 998)
      (name := consNName) (domain := .const ``Nat [])
      (body := consAfterAlpha.bindingBody!) (binderInfo := .implicit)
      (hfresh := consAlphaContextFresh)
      (annotations := consNatAnnotations)
      (hannotations := consNatAnnotationsBuild)
      (hannotationsEq := consNatAnnotationsEq)
      (hcheck := by
        simpa only [consAfterAlphaShape] using consAfterAlphaCheckValid)
      (hrun := by
        simpa [consNTypeRaw, consHeadTypeRaw, consTailTypeRaw,
          consTerminalRaw, consAfterAlpha, consAlphaExpr,
          consRootContext, ctorContext, AddInductive.Context.freshExpr,
          Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1',
          Expr.liftLooseBVars_zero] using
          consAfterAlphaWhnfValid)
      (domainCandidate := consNatDomainCandidateTrace)
      (bodyCandidate := consAfterNCandidateTrace)
      (hdomain := by
        simpa using consNatDomainCandidateTraceLoop 997)
      (hbody := by
        simpa [consNContext, consNatAnnotations] using
          consAfterNCandidateTraceLoop))

theorem consCandidateTraceLoop :
    AddInductive.buildCandidateExpr.loop consRootContext
      indexedVecConsInfo.type consRootContext.fuel.inductiveFuel =
        .ok consCandidateTrace := by
  change AddInductive.buildCandidateExpr.loop consRootContext
    indexedVecConsInfo.type (999 + 1) = _
  simpa only [consCandidateTrace, consAlphaContext,
    consAlphaAnnotations] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := consRootContext) (e := indexedVecConsInfo.type)
      (inferred := .sort (.succ (.succ (.param `u)))) (fuel := 999)
      (name := consAlphaName)
      (domain := .sort (.succ (.param `u)))
      (body := consNTypeRaw) (binderInfo := .implicit)
      (hfresh := consRootFresh)
      (annotations := consAlphaAnnotations)
      (hannotations := consAlphaAnnotationsBuild)
      (hannotationsEq := consAlphaAnnotationsEq)
      (hcheck := consRootCheckValid)
      (hrun := by
        simpa [consInfoTypeShape, consCtorTypeRaw] using consRootWhnfValid)
      (domainCandidate := consAlphaDomainCandidateTrace)
      (bodyCandidate := consAfterAlphaCandidateTrace)
      (hdomain := by
        simpa using consAlphaDomainCandidateTraceLoop 998)
      (hbody := by
        simpa [consAlphaContext, consAlphaAnnotations] using
          consAfterAlphaCandidateTraceLoop))

theorem consCandidateProduced :
    AddInductive.buildCandidateExpr indexedVecConsInfo.type
      consRootContext = .ok consCandidate := by
  unfold AddInductive.buildCandidateExpr
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [consCandidateTraceLoop]
  rfl

def indexedVecNilConstructorCandidate :
    AddInductive.CandidateConstructor indexedVecKernelNil where
  type := nilCandidate

def indexedVecConsConstructorCandidate :
    AddInductive.CandidateConstructor indexedVecKernelCons where
  type := consCandidate

def indexedVecFamilyListCandidate :
    AddInductive.CandidateFamily indexedVecKernelType where
  familyType := ⟨indexedVecFamilyCandidate⟩
  constructors :=
    .cons indexedVecNilConstructorCandidate
      (.cons indexedVecConsConstructorCandidate .nil)

def indexedVecNormalizationCandidate :
    AddInductive.NormalizationCandidate [indexedVecKernelType] where
  families := .cons indexedVecFamilyListCandidate .nil

/-- Source-indexed evidence for the complete `IndexedVec` family-type list. -/
theorem indexedVecFamilyTypeListProduced :
    AddInductive.CandidateFamilyTypeListProduced
      indexedVecFamilyCandidateContext
      (.cons indexedVecFamilyListCandidate.familyType .nil) := by
  exact .cons (by
    unfold AddInductive.normalizeCandidateFamilyType
    simp only [ReaderT.bind, Bind.bind]
    simp only [indexedVecKernelType]
    rw [indexedVecFamily_candidateTrace]
    rfl) .nil

theorem indexedVecFamilyTypeListCandidateProduced :
    (withReader (fun c : AddInductive.Context => { c with lctx := {} })
        (AddInductive.normalizeCandidateFamilyTypeList
          [indexedVecKernelType])) indexedVecFamilyCandidateContext =
      .ok (.cons indexedVecFamilyListCandidate.familyType .nil) := by
  change AddInductive.normalizeCandidateFamilyTypeList
    [indexedVecKernelType] indexedVecFamilyCandidateContext = _
  exact indexedVecFamilyTypeListProduced.normalize

/-- The two constructor positions are assembled in source order.  The
dependent list indices rule out truncating, swapping, or reusing either
constructor proof. -/
theorem indexedVecConstructorListProduced :
    AddInductive.CandidateConstructorListProduced ctorContext
      indexedVecFamilyListCandidate.constructors := by
  have hnil : AddInductive.buildCandidateExpr indexedVecNilInfo.type
      ctorContext = .ok nilCandidate := by
    simpa [nilCandidateContext] using nilCandidateProduced
  have hcons : AddInductive.buildCandidateExpr indexedVecConsInfo.type
      ctorContext = .ok consCandidate := by
    simpa [consRootContext] using consCandidateProduced
  exact .cons (by
    unfold AddInductive.normalizeCandidateConstructor
    simp only [ReaderT.bind, Bind.bind]
    simp only [indexedVecKernelNil]
    rw [hnil]
    rfl) (.cons (by
      unfold AddInductive.normalizeCandidateConstructor
      simp only [ReaderT.bind, Bind.bind]
      simp only [indexedVecKernelCons]
      rw [hcons]
      rfl) .nil)

theorem indexedVecConstructorListCandidateProduced :
    AddInductive.normalizeCandidateConstructorList
        indexedVecKernelType.ctors ctorContext =
      .ok indexedVecFamilyListCandidate.constructors := by
  exact indexedVecConstructorListProduced.normalize

/-- Source-indexed evidence for complete family assembly after constructor
normalization. -/
theorem indexedVecFamilyListProduced :
    AddInductive.CandidateFamilyListProduced ctorContext
      (.cons indexedVecFamilyListCandidate.familyType .nil)
      indexedVecNormalizationCandidate.families := by
  exact .cons indexedVecConstructorListProduced .nil

theorem indexedVecFamilyListCandidateProduced :
    AddInductive.normalizeCandidateFamilyList
        (.cons indexedVecFamilyListCandidate.familyType .nil)
        ctorContext =
      .ok indexedVecNormalizationCandidate.families := by
  exact indexedVecFamilyListProduced.normalize

end IndexedVecConsReplay

end Ix.Theory.Named.InductiveReplayFixtures
