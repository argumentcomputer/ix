/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.IndexedVecCandidate

/-!
# IndexedVec constructor normalization candidates

Exact ordinary-checker and candidate-producer traces for the real `nil` and
`cons` constructor metadata, staged in the post-family kernel environment.
This module extends the family-validation seam proved in
`IndexedVecCandidate` toward the complete normalization candidate used by the
certified inductive-generation path.
-/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta
open Ix.Theory.Named.InductiveFixtures

def ctorEnv : Kernel.Environment :=
  -- `declareInductiveTypes` preserves the input environment header while
  -- inserting the raw family constant.  Use that exact staged header so this
  -- environment is not merely lookup-equivalent to the producer result.
  Kernel.Environment.ofConstants `_indexedVecCandidate indexedVecTypeMap

def ctorContext : AddInductive.Context where
  env := ctorEnv
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

theorem type_lookup_family :
    ctorEnv.find? ``IndexedVec = some indexedVecInfo := by
  change indexedVecTypeMap.find?' ``IndexedVec = some indexedVecInfo
  rw [indexedVecTypeMap_wf.find?'_eq_find?, indexedVecTypeMap,
    natMap_wf.find?_insert]
  rfl

theorem type_lookup_nat : ctorEnv.find? ``Nat = some natInfo := by
  change indexedVecTypeMap.find?' ``Nat = some natInfo
  rw [indexedVecTypeMap_wf.find?'_eq_find?, indexedVecTypeMap,
    natMap_wf.find?_insert, nat_type_map_lookup]
  simp +decide

theorem nat_zero_map_lookup :
    natMap.find? ``Nat.zero = some natZeroInfo := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert]
  rfl

theorem type_lookup_zero :
    ctorEnv.find? ``Nat.zero = some natZeroInfo := by
  change indexedVecTypeMap.find?' ``Nat.zero = some natZeroInfo
  rw [indexedVecTypeMap_wf.find?'_eq_find?, indexedVecTypeMap,
    natMap_wf.find?_insert, nat_zero_map_lookup]
  simp +decide

theorem type_lookup_succ :
    ctorEnv.find? ``Nat.succ = some natSuccInfo := by
  change indexedVecTypeMap.find?' ``Nat.succ = some natSuccInfo
  rw [indexedVecTypeMap_wf.find?'_eq_find?, indexedVecTypeMap,
    natMap_wf.find?_insert, nat_succ_map_lookup]
  simp +decide

@[simp] theorem type_get_family :
    ctorEnv.get ``IndexedVec = .ok indexedVecInfo := by
  unfold Kernel.Environment.get
  rw [type_lookup_family]
  rfl

@[simp] theorem type_get_nat : ctorEnv.get ``Nat = .ok natInfo := by
  unfold Kernel.Environment.get
  rw [type_lookup_nat]
  rfl

@[simp] theorem type_get_zero :
    ctorEnv.get ``Nat.zero = .ok natZeroInfo := by
  unfold Kernel.Environment.get
  rw [type_lookup_zero]
  rfl

@[simp] theorem type_get_succ :
    ctorEnv.get ``Nat.succ = .ok natSuccInfo := by
  unfold Kernel.Environment.get
  rw [type_lookup_succ]
  rfl

def tcContext (lctx : LocalContext := {}) : TypeChecker.Context where
  env := ctorEnv
  lctx := lctx
  lparams := [`u]

@[simp] theorem checkLevelSuccParam (lctx) :
    TypeChecker.Inner.checkLevel (tcContext lctx)
      (.succ (.param `u)) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, tcContext,
    Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem checkLevelParam (lctx) :
    TypeChecker.Inner.checkLevel (tcContext lctx) (.param `u) =
      .ok () := by
  simp [TypeChecker.Inner.checkLevel, tcContext,
    Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem indexedVecInfoLevelParams :
    indexedVecInfo.levelParams = [`u] := rfl

@[simp] theorem indexedVecInfoIsUnsafe :
    indexedVecInfo.isUnsafe = false := rfl

@[simp] theorem indexedVecInfoInstantiate :
    indexedVecInfo.instantiateTypeLevelParams [.param `u] =
      indexedVecInfo.type := by
  rw [ConstantInfo.instantiateTypeLevelParams,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq]
  simp [indexedVecInfo, ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParamsCore', Level.substParams']

@[simp] theorem inferConstantFamily (lctx) :
    TypeChecker.Inner.inferConstant (tcContext lctx) ``IndexedVec
      [.param `u] false = .ok indexedVecInfo.type := by
  unfold TypeChecker.Inner.inferConstant
  simp only [tcContext]
  rw [type_get_family]
  simp only [Bind.bind, Except.bind]
  rw [show indexedVecInfo.levelParams.length = 1 by rfl]
  simp
  rw [show TypeChecker.Inner.checkLevel
      ({ env := ctorEnv, lctx := lctx, lparams := [`u] } :
        TypeChecker.Context) (.param `u) = .ok () by
    simpa [tcContext] using checkLevelParam lctx]
  simp [indexedVecInfo, Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] theorem inferConstantNat (lctx) :
    TypeChecker.Inner.inferConstant (tcContext lctx) ``Nat [] false =
      .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.Inner.inferConstant
  simp [tcContext, natInfo,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] theorem inferConstantZero (lctx) :
    TypeChecker.Inner.inferConstant (tcContext lctx) ``Nat.zero [] false =
      .ok (.const ``Nat []) := by
  unfold TypeChecker.Inner.inferConstant
  simp [tcContext, natZeroInfo,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] theorem inferConstantSucc (lctx) :
    TypeChecker.Inner.inferConstant (tcContext lctx) ``Nat.succ [] false =
      .ok (.forallE `n (.const ``Nat []) (.const ``Nat []) .default) := by
  unfold TypeChecker.Inner.inferConstant
  simp [tcContext, natSuccInfo,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem selfDefEq (e : Expr) fuel context state :
    TypeChecker.Inner.isDefEq e e (TypeChecker.Methods.withFuel fuel)
      context state = .ok (true, state) := by
  unfold TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl _)]
  rfl

@[simp] theorem constBeqFVar (name : Name) (levels : List Level)
    (id : FVarId) :
    ((.const name levels : Expr) == .fvar id) = false := by
  change Expr.eqv (.const name levels) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem sortBeqFVar (level : Level) (id : FVarId) :
    ((.sort level : Expr) == .fvar id) = false := by
  change Expr.eqv (.sort level) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem fvarBeqConst (id : FVarId) (name : Name)
    (levels : List Level) :
    ((.fvar id : Expr) == .const name levels) = false := by
  change Expr.eqv (.fvar id) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem sortBeqApp (level : Level) (fn arg : Expr) :
    ((.sort level : Expr) == .app fn arg) = false := by
  change Expr.eqv (.sort level) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem indexedVecConstBeqZero :
    ((.const ``IndexedVec [.param `u] : Expr) ==
      .const ``Nat.zero []) = false := by
  change Expr.eqv (.const ``IndexedVec [.param `u])
    (.const ``Nat.zero []) = false
  rw [Expr.eqv_eq]
  rfl

theorem withLocalDeclEq
    {α} (name : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → TypeChecker.RecM α)
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    (withLocalDecl (m := TypeChecker.RecM) name bi ty k)
      methods context state =
        k (.fvar ⟨state.ngen.curr⟩) methods
          { context with lctx :=
              context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name ty bi }
          { state with ngen := state.ngen.next } := rfl

def nilRootSortState : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeC := ({} : TypeChecker.State).inferTypeC.insert
      (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u)))) }

def nilAlphaId : FVarId :=
  ⟨nilRootSortState.ngen.curr⟩

def nilAlphaLctx : LocalContext :=
  ({} : LocalContext).mkLocalDecl nilAlphaId `α
    (.sort (.succ (.param `u))) .implicit

def nilBodyInitialState : TypeChecker.State :=
  { nilRootSortState with ngen := nilRootSortState.ngen.next }

theorem nilAlphaFind :
    nilAlphaLctx.find? nilAlphaId =
      some (.cdecl 0 nilAlphaId `α
        (.sort (.succ (.param `u))) .implicit .default) := by
  have hfresh : ({} : LocalContext).find? nilAlphaId = none := by
    have h := LocalContext.WF.find?_eq_find?_toList
      (fv := nilAlphaId) LocalContext.WF.nil
    change
      ({ fvarIdToDecl := PersistentHashMap.empty,
         decls := PersistentArray.empty,
         auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
        nilAlphaId = none
    rw [h]
    simp [LocalContext.toList]
  have hwf : nilAlphaLctx.WF := by
    change (({} : LocalContext).mkLocalDecl nilAlphaId `α
      (.sort (.succ (.param `u))) .implicit).WF
    exact LocalContext.WF.mkLocalDecl LocalContext.WF.nil hfresh
  rw [hwf.find?_eq_find?_toList]
  simp only [nilAlphaLctx]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  rw [show ({} : LocalContext).decls.size = 0 by rfl]
  change
    (if nilAlphaId == nilAlphaId then
      some (LocalDecl.cdecl 0 nilAlphaId `α
        (.sort (.succ (.param `u))) .implicit .default)
    else none) = _
  rw [beq_self_eq_true]
  rfl

example :
    TypeChecker.Inner.inferFVar (tcContext nilAlphaLctx) nilAlphaId =
      .ok (.sort (.succ (.param `u))) := by
  unfold TypeChecker.Inner.inferFVar
  simp [tcContext, nilAlphaFind, LocalDecl.type,
    Pure.pure, Except.pure]

theorem inferTypeFamilyCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache : state.inferTypeC[
      (.const ``IndexedVec [.param `u] : Expr)]? = none) :
    TypeChecker.Inner.inferType'
      (.const ``IndexedVec [.param `u]) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (indexedVecInfo.type,
          { state with inferTypeC :=
              (state.inferTypeC.insert
                (.const ``IndexedVec [.param `u]) indexedVecInfo.type) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    inferConstantFamily, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem inferTypeFVarCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (id : FVarId) (type : Expr)
    (hcache : state.inferTypeC[(.fvar id : Expr)]? = none)
    (hfind : lctx.find? id = some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType' (.fvar id) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (type, { state with inferTypeC :=
          (state.inferTypeC.insert (.fvar id) type) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    TypeChecker.Inner.inferFVar, tcContext, hfind,
    LocalDecl.type, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem inferTypeZeroCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat.zero [] : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.const ``Nat [], { state with inferTypeC :=
          (state.inferTypeC.insert (.const ``Nat.zero []) (.const ``Nat [])) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    inferConstantZero, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem inferTypeNatCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat [] : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.const ``Nat []) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.sort (.succ .zero), { state with inferTypeC :=
          (state.inferTypeC.insert (.const ``Nat [])
            (.sort (.succ .zero))) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    inferConstantNat, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem inferTypeSuccCore
    (fuel : Nat) (lctx : LocalContext) (state : TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat.succ [] : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.const ``Nat.succ []) false
      (TypeChecker.Methods.withFuel fuel) (tcContext lctx) state =
        .ok (.forallE `n (.const ``Nat []) (.const ``Nat []) .default,
          { state with inferTypeC :=
            (state.inferTypeC.insert (.const ``Nat.succ [])
              (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    inferConstantSucc, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

@[simp] theorem ensureForallExact
    (name : Name) (domain body : Expr) (bi : BinderInfo)
    (source : Expr) (fuel : Nat) (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    TypeChecker.Inner.ensureForallCore (.forallE name domain body bi)
      source (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.forallE name domain body bi, state) := by
  rfl

theorem inferAppCoreOf
    (fuel : Nat) (context : TypeChecker.Context)
    (state stateFn stateArg : TypeChecker.State)
    (fn arg domain body : Expr) (name : Name) (bi : BinderInfo)
    (hclosed : (.app fn arg : Expr).hasLooseBVars = false)
    (hcache : state.inferTypeC[(.app fn arg : Expr)]? = none)
    (hfn : TypeChecker.Inner.inferType' fn false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.forallE name domain body bi, stateFn))
    (harg : TypeChecker.Inner.inferType' arg false
      (TypeChecker.Methods.withFuel fuel) context stateFn =
        .ok (domain, stateArg))
    (heager : arg.isAppOfArity ``eagerReduce 2 = false) :
    TypeChecker.Inner.inferType' (.app fn arg) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (body.instantiate1 arg,
          { stateArg with inferTypeC :=
              (stateArg.inferTypeC.insert
                (.app fn arg) (body.instantiate1 arg)) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache, hfn, harg, heager, selfDefEq, Expr.instantiate1_eq, Bind.bind,
    ReaderT.bind, StateT.bind, Except.bind]

theorem inferTypeForallCore
    (fuel : Nat) (context : TypeChecker.Context)
    (state finalState : TypeChecker.State)
    (name : Name) (domain body result : Expr) (bi : BinderInfo)
    (hclosed : (.forallE name domain body bi : Expr).hasLooseBVars = false)
    (hcache : state.inferTypeC[(.forallE name domain body bi : Expr)]? = none)
    (hforall : TypeChecker.Inner.inferForall
      (.forallE name domain body bi) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, finalState)) :
    TypeChecker.Inner.inferType'
      (.forallE name domain body bi) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, { finalState with inferTypeC :=
          (finalState.inferTypeC.insert
            (.forallE name domain body bi) result) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache, hforall, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

def nilBodyExpr : Expr :=
  .app (.app (.const ``IndexedVec [.param `u]) (.fvar nilAlphaId))
    (.const ``Nat.zero [])

def vecIndexName : Name :=
  indexedVecInfo.type.bindingBody!.bindingName!

def vecFamilyTail : Expr :=
  .forallE vecIndexName (.const ``Nat [])
    (.sort (.succ (.param `u))) .default

theorem indexedVecInfoTypeShape :
    indexedVecInfo.type =
      .forallE `α (.sort (.succ (.param `u))) vecFamilyTail .default := by
  rfl

@[simp] theorem vecFamilyTailInstantiate (arg : Expr) :
    vecFamilyTail.instantiate1 arg = vecFamilyTail := by
  simp [vecFamilyTail, Expr.instantiate1_eq, Expr.instantiate1']

def nilFamilyState : TypeChecker.State :=
  { nilBodyInitialState with inferTypeC :=
      (nilBodyInitialState.inferTypeC.insert
        (.const ``IndexedVec [.param `u]) indexedVecInfo.type) }

def nilAlphaState : TypeChecker.State :=
  { nilFamilyState with inferTypeC :=
      (nilFamilyState.inferTypeC.insert (.fvar nilAlphaId)
        (.sort (.succ (.param `u)))) }

def nilFirstApp : Expr :=
  .app (.const ``IndexedVec [.param `u]) (.fvar nilAlphaId)

def nilFirstAppState : TypeChecker.State :=
  { nilAlphaState with inferTypeC :=
      (nilAlphaState.inferTypeC.insert nilFirstApp vecFamilyTail) }

def nilZeroState : TypeChecker.State :=
  { nilFirstAppState with inferTypeC :=
      (nilFirstAppState.inferTypeC.insert (.const ``Nat.zero [])
        (.const ``Nat [])) }

theorem inferNilFamily :
    TypeChecker.Inner.inferType'
      (.const ``IndexedVec [.param `u]) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext nilAlphaLctx) nilBodyInitialState =
        .ok (indexedVecInfo.type, nilFamilyState) := by
  simpa [nilFamilyState] using
    (inferTypeFamilyCore 9998 nilAlphaLctx nilBodyInitialState (by
      simp [nilBodyInitialState, nilRootSortState]))

theorem inferNilAlpha :
    TypeChecker.Inner.inferType' (.fvar nilAlphaId) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext nilAlphaLctx) nilFamilyState =
        .ok (.sort (.succ (.param `u)), nilAlphaState) := by
  simpa [nilAlphaState] using
    (inferTypeFVarCore 9998 nilAlphaLctx nilFamilyState nilAlphaId
      (.sort (.succ (.param `u))) (index := 0) (name := `α)
      (bi := .implicit) (kind := .default) (by
        simp [nilFamilyState, nilBodyInitialState, nilRootSortState]) nilAlphaFind)

theorem inferNilFirstApp :
    TypeChecker.Inner.inferType' nilFirstApp false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext nilAlphaLctx) nilBodyInitialState =
        .ok (vecFamilyTail, nilFirstAppState) := by
  have h := inferAppCoreOf 9998 (tcContext nilAlphaLctx)
    nilBodyInitialState nilFamilyState nilAlphaState
    (.const ``IndexedVec [.param `u]) (.fvar nilAlphaId)
    (.sort (.succ (.param `u))) vecFamilyTail `α .default
    (by
      simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    (by
      simp [nilBodyInitialState, nilRootSortState])
    (by simpa [indexedVecInfoTypeShape] using inferNilFamily)
    inferNilAlpha (by rfl)
  simpa [nilFirstApp, nilFirstAppState, vecFamilyTail,
    Expr.instantiate1'] using h

theorem inferNilZero :
    TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext nilAlphaLctx) nilFirstAppState =
        .ok (.const ``Nat [], nilZeroState) := by
  simpa [nilZeroState] using
    (inferTypeZeroCore 9998 nilAlphaLctx nilFirstAppState (by
      simp [nilFirstAppState, nilAlphaState, nilFamilyState, nilBodyInitialState, nilRootSortState,
        nilFirstApp]))

theorem inferNilBodyExists : ∃ finalState,
    TypeChecker.Inner.inferType nilBodyExpr false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilAlphaLctx) nilBodyInitialState =
        .ok (.sort (.succ (.param `u)), finalState) := by
  refine ⟨{ nilZeroState with inferTypeC :=
    (nilZeroState.inferTypeC.insert nilBodyExpr
      (.sort (.succ (.param `u)))) }, ?_⟩
  change TypeChecker.Inner.inferType' nilBodyExpr false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext nilAlphaLctx) nilBodyInitialState = _
  have h := inferAppCoreOf 9998 (tcContext nilAlphaLctx)
    nilBodyInitialState nilFirstAppState nilZeroState
    nilFirstApp (.const ``Nat.zero []) (.const ``Nat [])
    (.sort (.succ (.param `u))) vecIndexName .default
    (by simp [nilFirstApp, Expr.hasLooseBVars, Expr.looseBVarRange'])
    (by simp [nilBodyInitialState, nilRootSortState])
    (by simpa [vecFamilyTail] using inferNilFirstApp)
    inferNilZero (by rfl)
  simpa [nilBodyExpr, nilFirstApp,
    Expr.instantiate1_eq, Expr.instantiate1'] using h

theorem nilOuterWithLocalDecl
    {α} (k : Expr → TypeChecker.RecM α)
    (methods : TypeChecker.Methods) :
    (withLocalDecl (m := TypeChecker.RecM) `α .implicit
      (.sort (.succ (.param `u))) k)
        methods (tcContext ({} : LocalContext)) nilRootSortState =
      k (.fvar nilAlphaId) methods (tcContext nilAlphaLctx)
        nilBodyInitialState := by
  simpa [nilAlphaId, nilAlphaLctx, nilBodyInitialState, tcContext] using
    (withLocalDeclEq `α .implicit (.sort (.succ (.param `u))) k methods
      (tcContext ({} : LocalContext)) nilRootSortState)

@[simp] theorem ensureSortExact
    (level : Level) (source : Expr) (fuel : Nat)
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    TypeChecker.Inner.ensureSortCore (.sort level) source
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.sort level, state) := by
  rfl

theorem nilRootSortCore :
    TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9998)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.succ (.param `u))), nilRootSortState) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    nilRootSortState, checkLevelSuccParam,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

def nilCtorBodyRaw : Expr :=
  .app (.app (.const ``IndexedVec [.param `u]) (.bvar 0))
    (.const ``Nat.zero [])

def nilCtorTypeRaw : Expr :=
  .forallE `α (.sort (.succ (.param `u))) nilCtorBodyRaw .implicit

def nilCtorInferredLevel : Level :=
  mkLevelIMax' (.succ (.succ (.param `u))) (.succ (.param `u))

theorem nilInfoTypeShape : indexedVecNilInfo.type = nilCtorTypeRaw := by
  rfl

theorem nilRootInferForallExists : ∃ finalState,
    TypeChecker.Inner.inferForall nilCtorTypeRaw false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State) =
        .ok (.sort nilCtorInferredLevel, finalState) := by
  obtain ⟨finalState, hbody⟩ := inferNilBodyExists
  refine ⟨finalState, ?_⟩
  unfold TypeChecker.Inner.inferForall
  simp only [TypeChecker.Inner.inferForall.loop, nilCtorTypeRaw]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev #[] =
      .sort (.succ (.param `u)) by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show TypeChecker.Inner.inferType
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State) =
        TypeChecker.Inner.inferType'
          (.sort (.succ (.param `u))) false
          (TypeChecker.Methods.withFuel 9998)
          (tcContext ({} : LocalContext)) ({} : TypeChecker.State) by rfl]
  rw [nilRootSortCore]
  simp only
  rw [ensureSortExact]
  simp only
  rw [nilOuterWithLocalDecl]
  simp only [TypeChecker.Inner.inferForall.loop, nilCtorBodyRaw]
  rw [show
      (((.const ``IndexedVec [.param `u] : Expr).app (.bvar 0)).app
        (.const ``Nat.zero [])).instantiateRev
      (#[] |>.push (.fvar nilAlphaId)) = nilBodyExpr by
    simp [nilBodyExpr, nilAlphaId, Expr.instantiateRev_eq, Expr.instantiate_eq, Expr.instantiate1',
      Expr.liftLooseBVars_zero]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hbody]
  simp only
  rw [ensureSortExact]
  simp [nilCtorInferredLevel, Expr.sortLevel!, Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]

theorem inferNilRootExists : ∃ finalState,
    TypeChecker.Inner.inferType indexedVecNilInfo.type false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State) =
        .ok (.sort nilCtorInferredLevel, finalState) := by
  obtain ⟨state, hforall⟩ := nilRootInferForallExists
  refine ⟨{ state with inferTypeC :=
    (state.inferTypeC.insert indexedVecNilInfo.type
      (.sort nilCtorInferredLevel)) }, ?_⟩
  change TypeChecker.Inner.inferType' indexedVecNilInfo.type false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State) = _
  rw [nilInfoTypeShape]
  exact inferTypeForallCore 9999 (tcContext ({} : LocalContext))
    ({} : TypeChecker.State) state `α
    (.sort (.succ (.param `u))) nilCtorBodyRaw
    (.sort nilCtorInferredLevel) .implicit
    (by simp [nilCtorBodyRaw, Expr.hasLooseBVars,
      Expr.looseBVarRange'])
    (by simp) hforall

theorem nilRootCheckTypeM :
    TypeChecker.M.run ctorEnv .safe {} [`u] {}
      (TypeChecker.checkType indexedVecNilInfo.type) =
      .ok (.sort nilCtorInferredLevel) := by
  obtain ⟨finalState, hroot⟩ := inferNilRootExists
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType indexedVecNilInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        (tcContext {}) ({} : TypeChecker.State)) = _
  rw [hroot]
  rfl

def nilCandidateContext : AddInductive.Context := ctorContext

def nilCandidateBodyContext : AddInductive.Context :=
  nilCandidateContext.pushLocalDecl `α .implicit
    (.sort (.succ (.param `u)))

def nilCandidateBody : Expr :=
  nilCtorBodyRaw.instantiate1 nilCandidateContext.freshExpr

theorem nilStandaloneSortCore :
    TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.succ (.param `u))), nilRootSortState) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    nilRootSortState, checkLevelSuccParam,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem nilRootWhnfM :
    TypeChecker.M.run nilCandidateContext.env nilCandidateContext.safety
      nilCandidateContext.lctx nilCandidateContext.lparams
      nilCandidateContext.fuel
      (TypeChecker.whnf indexedVecNilInfo.type) =
        .ok indexedVecNilInfo.type := by
  rfl

theorem nilDomainCheckTypeM :
    TypeChecker.M.run nilCandidateContext.env nilCandidateContext.safety
      nilCandidateContext.lctx nilCandidateContext.lparams
      nilCandidateContext.fuel
      (TypeChecker.checkType (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.succ (.param `u)))) := by
  obtain ⟨finalState, hroot⟩ :=
    show ∃ finalState,
      TypeChecker.Inner.inferType (.sort (.succ (.param `u))) false
        (TypeChecker.Methods.withFuel 10000)
        (tcContext ({} : LocalContext)) ({} : TypeChecker.State) =
          .ok (.sort (.succ (.succ (.param `u))), finalState) by
      refine ⟨nilRootSortState, ?_⟩
      change TypeChecker.Inner.inferType'
        (.sort (.succ (.param `u))) false
        (TypeChecker.Methods.withFuel 9999)
        (tcContext ({} : LocalContext)) ({} : TypeChecker.State) = _
      exact nilStandaloneSortCore
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext ({} : LocalContext)) ({} : TypeChecker.State)) = _
  rw [hroot]
  rfl

theorem nilDomainWhnfM :
    TypeChecker.M.run nilCandidateContext.env nilCandidateContext.safety
      nilCandidateContext.lctx nilCandidateContext.lparams
      nilCandidateContext.fuel
      (TypeChecker.whnf (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.param `u))) := by
  rfl

def nilCandidateAlphaId : FVarId :=
  nilCandidateContext.freshFVarId

def nilCandidateAlphaLctx : LocalContext :=
  ({} : LocalContext).mkLocalDecl nilCandidateAlphaId `α
    (.sort (.succ (.param `u))) .implicit

theorem nilCandidateFresh :
    ({} : LocalContext).find? nilCandidateAlphaId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := nilCandidateAlphaId) LocalContext.WF.nil
  change
    ({ fvarIdToDecl := PersistentHashMap.empty,
       decls := PersistentArray.empty,
       auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
      nilCandidateAlphaId = none
  rw [h]
  simp [LocalContext.toList]

theorem nilCandidateAlphaFind :
    nilCandidateAlphaLctx.find? nilCandidateAlphaId =
      some (.cdecl 0 nilCandidateAlphaId `α
        (.sort (.succ (.param `u))) .implicit .default) := by
  have hwf : nilCandidateAlphaLctx.WF := by
    change (({} : LocalContext).mkLocalDecl nilCandidateAlphaId `α
      (.sort (.succ (.param `u))) .implicit).WF
    exact LocalContext.WF.mkLocalDecl LocalContext.WF.nil
      nilCandidateFresh
  rw [hwf.find?_eq_find?_toList]
  simp only [nilCandidateAlphaLctx]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  rw [show ({} : LocalContext).decls.size = 0 by rfl]
  change
    (if nilCandidateAlphaId == nilCandidateAlphaId then
      some (LocalDecl.cdecl 0 nilCandidateAlphaId `α
        (.sort (.succ (.param `u))) .implicit .default)
    else none) = _
  rw [beq_self_eq_true]
  rfl

def nilCandidateFirstApp : Expr :=
  .app (.const ``IndexedVec [.param `u]) (.fvar nilCandidateAlphaId)

def nilCandidateBodyExpr : Expr :=
  .app nilCandidateFirstApp (.const ``Nat.zero [])

theorem nilCandidateBodyShape :
    nilCandidateBody = nilCandidateBodyExpr := by
  simp [nilCandidateBody, nilCtorBodyRaw, nilCandidateBodyExpr,
    nilCandidateFirstApp, nilCandidateAlphaId,
    AddInductive.Context.freshExpr,
    Expr.instantiate1_eq, Expr.instantiate1']

def nilCandidateFamilyState : TypeChecker.State :=
  { ({} : TypeChecker.State) with inferTypeC :=
      (({} : TypeChecker.State).inferTypeC.insert
        (.const ``IndexedVec [.param `u]) indexedVecInfo.type) }

def nilCandidateAlphaState : TypeChecker.State :=
  { nilCandidateFamilyState with inferTypeC :=
      (nilCandidateFamilyState.inferTypeC.insert
        (.fvar nilCandidateAlphaId) (.sort (.succ (.param `u)))) }

def nilCandidateFirstAppState : TypeChecker.State :=
  { nilCandidateAlphaState with inferTypeC :=
      (nilCandidateAlphaState.inferTypeC.insert
        nilCandidateFirstApp vecFamilyTail) }

def nilCandidateZeroState : TypeChecker.State :=
  { nilCandidateFirstAppState with inferTypeC :=
      (nilCandidateFirstAppState.inferTypeC.insert
        (.const ``Nat.zero []) (.const ``Nat [])) }

theorem inferNilCandidateFamily :
    TypeChecker.Inner.inferType'
      (.const ``IndexedVec [.param `u]) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) =
        .ok (indexedVecInfo.type, nilCandidateFamilyState) := by
  simpa [nilCandidateFamilyState] using
    (inferTypeFamilyCore 9999 nilCandidateAlphaLctx
      ({} : TypeChecker.State) (by simp))

theorem inferNilCandidateAlpha :
    TypeChecker.Inner.inferType' (.fvar nilCandidateAlphaId) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) nilCandidateFamilyState =
        .ok (.sort (.succ (.param `u)), nilCandidateAlphaState) := by
  simpa [nilCandidateAlphaState] using
    (inferTypeFVarCore 9999 nilCandidateAlphaLctx
      nilCandidateFamilyState nilCandidateAlphaId
      (.sort (.succ (.param `u)))
      (by simp [nilCandidateFamilyState]) nilCandidateAlphaFind)

theorem inferNilCandidateFirstApp :
    TypeChecker.Inner.inferType' nilCandidateFirstApp false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) =
        .ok (vecFamilyTail, nilCandidateFirstAppState) := by
  have h := inferAppCoreOf 9999 (tcContext nilCandidateAlphaLctx)
    ({} : TypeChecker.State) nilCandidateFamilyState
    nilCandidateAlphaState (.const ``IndexedVec [.param `u])
    (.fvar nilCandidateAlphaId) (.sort (.succ (.param `u)))
    vecFamilyTail `α .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    (by simp) inferNilCandidateFamily
    (by simpa [indexedVecInfoTypeShape] using inferNilCandidateAlpha)
    (by rfl)
  simpa [nilCandidateFirstApp, nilCandidateFirstAppState,
    indexedVecInfoTypeShape, vecFamilyTail,
    Expr.instantiate1'] using h

theorem inferNilCandidateZero :
    TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) nilCandidateFirstAppState =
        .ok (.const ``Nat [], nilCandidateZeroState) := by
  simpa [nilCandidateZeroState] using
    (inferTypeZeroCore 9999 nilCandidateAlphaLctx
      nilCandidateFirstAppState (by
        simp [nilCandidateFirstAppState, nilCandidateAlphaState, nilCandidateFamilyState,
          nilCandidateFirstApp]))

theorem inferNilCandidateBodyExists : ∃ finalState,
    TypeChecker.Inner.inferType nilCandidateBody false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)), finalState) := by
  refine ⟨{ nilCandidateZeroState with inferTypeC :=
    (nilCandidateZeroState.inferTypeC.insert nilCandidateBodyExpr
      (.sort (.succ (.param `u)))) }, ?_⟩
  change TypeChecker.Inner.inferType' nilCandidateBody false
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) = _
  rw [nilCandidateBodyShape]
  have h := inferAppCoreOf 9999 (tcContext nilCandidateAlphaLctx)
    ({} : TypeChecker.State) nilCandidateFirstAppState
    nilCandidateZeroState nilCandidateFirstApp (.const ``Nat.zero [])
    (.const ``Nat []) (.sort (.succ (.param `u))) vecIndexName .default
    (by simp [nilCandidateFirstApp, Expr.hasLooseBVars, Expr.looseBVarRange'])
    (by simp) inferNilCandidateFirstApp
    inferNilCandidateZero (by rfl)
  simpa [nilCandidateBodyExpr, nilCandidateFirstApp,
    Expr.instantiate1_eq, Expr.instantiate1'] using h

theorem nilCandidateBodyCheckTypeM :
    TypeChecker.M.run nilCandidateBodyContext.env
      nilCandidateBodyContext.safety nilCandidateBodyContext.lctx
      nilCandidateBodyContext.lparams nilCandidateBodyContext.fuel
      (TypeChecker.checkType nilCandidateBody) =
        .ok (.sort (.succ (.param `u))) := by
  obtain ⟨finalState, hbody⟩ := inferNilCandidateBodyExists
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType nilCandidateBody false
      (TypeChecker.Methods.withFuel 10000)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State)) = _
  rw [hbody]
  rfl

theorem nilCandidateBodyGetAppFn :
    nilCandidateBody.getAppFn =
      .const ``IndexedVec [.param `u] := by
  rw [nilCandidateBodyShape]
  rfl

theorem nilRecMBind
    {α β} (x : TypeChecker.RecM α)
    (f : α → TypeChecker.RecM β) (methods context state) :
    (x >>= f) methods context state =
      match x methods context state with
      | .error e => .error e
      | .ok (a, state') => f a methods context state' := by
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  cases h : x methods context state with
  | error => rfl
  | ok value => cases value; rfl

@[simp] theorem nilRecMGetEnv (methods context state) :
    (liftM TypeChecker.getEnv :
      TypeChecker.RecM Kernel.Environment) methods context state =
        .ok (context.env, state) := rfl

@[simp] theorem nilRecMGet (methods context state) :
    (get : TypeChecker.RecM TypeChecker.State)
      methods context state = .ok (state, state) := rfl

@[simp] theorem nilRecMPure
    {α} (a : α) (methods context state) :
    (pure a : TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

theorem nilCandidateInductiveReduceRec
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    inductiveReduceRec ctorEnv nilCandidateBody
        (fun e => TypeChecker.Inner.whnf e)
        (fun e => TypeChecker.Inner.inferType e)
        TypeChecker.Inner.isDefEq
        TypeChecker.Inner.isNeverProp
        methods (tcContext nilCandidateAlphaLctx) state =
      .ok (none, state) := by
  unfold inductiveReduceRec
  rw [nilCandidateBodyGetAppFn]
  simp only
  rw [type_lookup_family]
  rfl

theorem nilCandidateReduceRecursor
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.reduceRecursor nilCandidateBody
      methods (tcContext nilCandidateAlphaLctx) state =
        .ok (none, state) := by
  unfold TypeChecker.Inner.reduceRecursor
  have hquot : ctorEnv.quotInit = false := by rfl
  simp only [nilRecMBind, nilRecMGetEnv]
  rw [show (tcContext nilCandidateAlphaLctx).env = ctorEnv by rfl]
  rw [hquot]
  simp only [Bool.false_eq_true, if_false, nilRecMBind]
  rw [nilCandidateInductiveReduceRec methods state]
  rfl

@[simp] theorem nilCandidateWhnfCoreFamily (n state) :
    TypeChecker.Inner.whnfCore
      (.const ``IndexedVec [.param `u]) false
      (TypeChecker.Methods.withFuel (n + 1))
      (tcContext nilCandidateAlphaLctx) state =
        .ok (.const ``IndexedVec [.param `u], state) := by
  rfl

theorem nilCandidateWhnfCoreInitial (n : Nat) :
    TypeChecker.Inner.whnfCore' nilCandidateBody false
      (TypeChecker.Methods.withFuel (n + 1))
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) =
        .ok (nilCandidateBody, ({} : TypeChecker.State)) := by
  rw [nilCandidateBodyShape]
  change TypeChecker.Inner.whnfCore'
    (.app (.app (.const ``IndexedVec [.param `u])
      (.fvar nilCandidateAlphaId)) (.const ``Nat.zero []))
    false (TypeChecker.Methods.withFuel (n + 1))
    (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) = _
  unfold TypeChecker.Inner.whnfCore'
  simp only [nilRecMBind, nilRecMGet, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [nilRecMBind]
  rw [show
    (Expr.app
      (Expr.app (Expr.const ``IndexedVec [.param `u])
        (Expr.fvar nilCandidateAlphaId))
      (Expr.const ``Nat.zero [])).getAppFn =
        (Expr.const ``IndexedVec [.param `u]) by rfl]
  rw [nilCandidateWhnfCoreFamily n ({} : TypeChecker.State)]
  simp [nilCandidateBodyExpr, nilCandidateFirstApp, Expr.structuralEq, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rw [show
    .app (.app (.const ``IndexedVec [.param `u])
      (.fvar nilCandidateAlphaId)) (.const ``Nat.zero []) =
        nilCandidateBody by
    symm; exact nilCandidateBodyShape]
  rw [nilCandidateReduceRecursor]
  rfl

@[simp] theorem nilCandidateReduceNative
    (env : Kernel.Environment) (methods : TypeChecker.Methods)
    (state : TypeChecker.State) :
    (liftM (TypeChecker.Inner.reduceNative env nilCandidateBody) :
      TypeChecker.RecM (Option Expr))
        methods (tcContext nilCandidateAlphaLctx) state =
      .ok (none, state) := by
  rw [nilCandidateBodyShape]
  simp [TypeChecker.Inner.reduceNative, nilCandidateBodyExpr,
    nilCandidateFirstApp, Expr.structuralEq]

@[simp] theorem nilCandidateReduceNat
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.reduceNat nilCandidateBody
        methods (tcContext nilCandidateAlphaLctx) state =
      .ok (none, state) := by
  rw [nilCandidateBodyShape]
  simp [TypeChecker.Inner.reduceNat, nilCandidateBodyExpr, nilCandidateFirstApp,
    Expr.getAppNumArgs_eq, Expr.getAppArgsRevList]

theorem nilCandidateIsDeltaFamily :
    TypeChecker.Inner.isDelta ctorEnv
      (.const ``IndexedVec [.param `u]) = none := by
  unfold TypeChecker.Inner.isDelta
  rw [show
    (Expr.const ``IndexedVec [.param `u]).getAppFn =
      Expr.const ``IndexedVec [.param `u] by rfl]
  simp only
  rw [type_lookup_family]
  simp [indexedVecInfo, ConstantInfo.deltaValue?]

theorem nilCandidateUnfoldFamily
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.unfoldDefinitionCore
      (.const ``IndexedVec [.param `u])
      methods (tcContext nilCandidateAlphaLctx) state =
        .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinitionCore
  simp only [nilRecMBind, nilRecMGetEnv]
  rw [show (tcContext nilCandidateAlphaLctx).env = ctorEnv by rfl]
  rw [nilCandidateIsDeltaFamily]
  rfl

theorem nilCandidateUnfoldBody
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.unfoldDefinition nilCandidateBody
      methods (tcContext nilCandidateAlphaLctx) state =
        .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinition
  rw [show nilCandidateBody.isApp = true by
    rw [nilCandidateBodyShape]
    rfl]
  simp only [if_true]
  rw [nilCandidateBodyGetAppFn]
  simp only [nilRecMBind]
  rw [nilCandidateUnfoldFamily]
  rfl

theorem nilCandidateWhnfLoop :
    TypeChecker.Inner.whnf'.loop nilCandidateBody 100000
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) =
        .ok (nilCandidateBody, ({} : TypeChecker.State)) := by
  rw [show 100000 = 99999 + 1 by rfl]
  unfold TypeChecker.Inner.whnf'.loop
  rw [show 9999 = 9998 + 1 by rfl]
  simp only [nilRecMBind, nilRecMGetEnv]
  rw [nilCandidateWhnfCoreInitial 9998]
  simp only []
  rw [nilCandidateReduceNative]
  simp only [nilRecMBind]
  rw [nilCandidateReduceNat]
  simp only [nilRecMBind]
  rw [nilCandidateUnfoldBody]
  rfl

theorem nilCandidateBodyWhnfM :
    TypeChecker.M.run nilCandidateBodyContext.env
      nilCandidateBodyContext.safety nilCandidateBodyContext.lctx
      nilCandidateBodyContext.lparams nilCandidateBodyContext.fuel
      (TypeChecker.whnf nilCandidateBody) = .ok nilCandidateBody := by
  rw [nilCandidateBodyShape]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf'
      (.app (.app (.const ``IndexedVec [.param `u])
        (.fvar nilCandidateAlphaId)) (.const ``Nat.zero []))
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State)) =
        .ok (.app (.app (.const ``IndexedVec [.param `u])
          (.fvar nilCandidateAlphaId)) (.const ``Nat.zero []))
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show
    (if (tcContext nilCandidateAlphaLctx).eagerReduce then
      (tcContext nilCandidateAlphaLctx).fuel.whnfEager
    else (tcContext nilCandidateAlphaLctx).fuel.whnf) = 100000 by rfl]
  rw [show
    TypeChecker.Inner.whnf'.loop
      (.app (.app (.const ``IndexedVec [.param `u])
        (.fvar nilCandidateAlphaId)) (.const ``Nat.zero [])) 100000
      (TypeChecker.Methods.withFuel 9999)
      (tcContext nilCandidateAlphaLctx) ({} : TypeChecker.State) =
        .ok (.app (.app (.const ``IndexedVec [.param `u])
          (.fvar nilCandidateAlphaId)) (.const ``Nat.zero []),
          ({} : TypeChecker.State)) by
    simpa [nilCandidateBodyShape, nilCandidateBodyExpr,
      nilCandidateFirstApp] using nilCandidateWhnfLoop]
  simp [Functor.map, StateT.map, Except.map]

def nilDomainAnnotations :
    AddInductive.CandidateTypeAnnotations
      (.sort (.succ (.param `u))) where
  consumed := .sort (.succ (.param `u))
  trace := .identity _

theorem nilDomainAnnotationTraceBuild :
    AddInductive.CandidateTypeAnnotationTrace.build
      (.sort (.succ (.param `u))) =
        ⟨.sort (.succ (.param `u)), .identity _⟩ := by
  simp [AddInductive.CandidateTypeAnnotationTrace.build]

theorem nilDomainAnnotationsBuild :
    AddInductive.buildCandidateTypeAnnotations
      (.sort (.succ (.param `u))) = .ok nilDomainAnnotations := by
  unfold AddInductive.buildCandidateTypeAnnotations
  rw [nilDomainAnnotationTraceBuild]
  rfl

theorem nilDomainAnnotationsEq :
    AddInductive.CandidateIsDefEqStep.Valid
      ⟨nilCandidateContext, (.sort (.succ (.param `u))),
        nilDomainAnnotations.consumed⟩ := by
  simpa [nilDomainAnnotations] using
    (candidateIsDefEqSelfValid nilCandidateContext
      (.sort (.succ (.param `u))) 9999 rfl)

theorem nilCandidateContextFresh :
    nilCandidateContext.lctx.find?
      nilCandidateContext.freshFVarId = none := by
  change ({} : LocalContext).find? nilCandidateAlphaId = none
  exact nilCandidateFresh

theorem nilRootCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨nilCandidateContext, indexedVecNilInfo.type,
        .sort nilCtorInferredLevel⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid,
    nilCandidateContext, ctorContext] using nilRootCheckTypeM

theorem nilRootWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨nilCandidateContext, indexedVecNilInfo.type,
        indexedVecNilInfo.type⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid,
    nilCandidateContext, ctorContext] using nilRootWhnfM

theorem nilDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨nilCandidateContext, (.sort (.succ (.param `u))),
        .sort (.succ (.succ (.param `u)))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid] using
    nilDomainCheckTypeM

theorem nilDomainWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨nilCandidateContext, (.sort (.succ (.param `u))),
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid] using nilDomainWhnfM

theorem nilBodyCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨nilCandidateBodyContext, nilCandidateBody,
        .sort (.succ (.param `u))⟩ := by
  simpa [AddInductive.CandidateCheckTypeStep.Valid] using
    nilCandidateBodyCheckTypeM

theorem nilBodyWhnfValid :
    AddInductive.CandidateWhnfStep.Valid
      ⟨nilCandidateBodyContext, nilCandidateBody,
        nilCandidateBody⟩ := by
  simpa [AddInductive.CandidateWhnfStep.Valid] using
    nilCandidateBodyWhnfM

def nilDomainCandidateTrace :
    AddInductive.CandidateExprTrace nilCandidateContext
      (.sort (.succ (.param `u))) :=
  .terminal nilCandidateContext (.sort (.succ (.param `u)))
    (.sort (.succ (.succ (.param `u))))
    (.sort (.succ (.param `u)))
    nilDomainCheckValid nilDomainWhnfValid

def nilBodyCandidateTrace :
    AddInductive.CandidateExprTrace nilCandidateBodyContext
      (nilCtorBodyRaw.instantiate1 nilCandidateContext.freshExpr) :=
  .terminal nilCandidateBodyContext
    (nilCtorBodyRaw.instantiate1 nilCandidateContext.freshExpr)
    (.sort (.succ (.param `u))) nilCandidateBody
    (by simpa [nilCandidateBody] using nilBodyCheckValid)
    (by simpa [nilCandidateBody] using nilBodyWhnfValid)

def nilCandidateTrace :
    AddInductive.CandidateExprTrace nilCandidateContext
      indexedVecNilInfo.type :=
  .forallE nilCandidateContext indexedVecNilInfo.type
    (.sort nilCtorInferredLevel) `α
    (.sort (.succ (.param `u))) nilCtorBodyRaw .implicit
    nilCandidateContextFresh nilDomainAnnotations
    nilDomainAnnotationsEq nilRootCheckValid
    (by simpa [nilInfoTypeShape, nilCtorTypeRaw] using nilRootWhnfValid)
    nilDomainCandidateTrace nilBodyCandidateTrace

def nilCandidate : AddInductive.CandidateExpr indexedVecNilInfo.type :=
  ⟨nilCandidateContext, nilCandidateTrace⟩

theorem nilCandidate_view_eq :
    nilCandidate.view = indexedVecNilInfo.type := by
  have habstract (context : AddInductive.Context) (e : Expr) :
      e.abstract #[context.freshExpr] =
        Expr.abstract1 context.freshFVarId e := by
    rw [show #[context.freshExpr] =
      ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
    simp only [Expr.abstract_eq, Expr.abstractList]
  simp only [nilCandidate, AddInductive.CandidateExpr.view,
    nilCandidateTrace, nilDomainCandidateTrace, nilBodyCandidateTrace,
    AddInductive.CandidateExprTrace.view]
  rw [habstract]
  rw [nilInfoTypeShape]
  simp [nilCandidateBody, nilCtorTypeRaw, nilCtorBodyRaw,
    Expr.instantiate1_eq, Expr.instantiate1', Expr.abstract1,
    nilCandidateContext, ctorContext,
    AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId,
    NameGenerator.curr]

/-- The retained `nil` candidate is identity-normalizing at its root, domain,
and instantiated result. -/
theorem nilCandidate_identity :
    TypeChecker.CandidateExprIdentity nilCandidate.trace := by
  change TypeChecker.CandidateExprIdentity nilCandidateTrace
  unfold nilCandidateTrace
  refine .forallE (name := `α) (binderInfo := .implicit)
    (body := nilCtorBodyRaw) (annotations := nilDomainAnnotations)
    nilDomainCandidateTrace nilBodyCandidateTrace
    (by simpa [nilCtorTypeRaw] using nilInfoTypeShape)
    rfl (.terminal rfl) (.terminal (by rfl))

theorem nilDomainCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop nilCandidateContext
      (.sort (.succ (.param `u))) (fuel + 1) =
        .ok nilDomainCandidateTrace := by
  simpa only [nilDomainCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      nilCandidateContext (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u))))
      (.sort (.succ (.param `u))) fuel
      nilDomainCheckValid nilDomainWhnfValid rfl

theorem nilBodyCandidateTraceLoop (fuel : Nat) :
    AddInductive.buildCandidateExpr.loop nilCandidateBodyContext
      (nilCtorBodyRaw.instantiate1 nilCandidateContext.freshExpr)
      (fuel + 1) = .ok nilBodyCandidateTrace := by
  simpa only [nilBodyCandidateTrace] using
    AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      nilCandidateBodyContext
      (nilCtorBodyRaw.instantiate1 nilCandidateContext.freshExpr)
      (.sort (.succ (.param `u))) nilCandidateBody fuel
      (by simpa [nilCandidateBody] using nilBodyCheckValid)
      (by simpa [nilCandidateBody] using nilBodyWhnfValid)
      (by rw [nilCandidateBodyShape]; rfl)

theorem nilCandidateTraceLoop :
    AddInductive.buildCandidateExpr.loop nilCandidateContext
      indexedVecNilInfo.type nilCandidateContext.fuel.inductiveFuel =
        .ok nilCandidateTrace := by
  change AddInductive.buildCandidateExpr.loop nilCandidateContext
    indexedVecNilInfo.type (999 + 1) = _
  simpa only [nilCandidateTrace, nilCandidateBodyContext] using
    (AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := nilCandidateContext)
      (e := indexedVecNilInfo.type)
      (inferred := .sort nilCtorInferredLevel)
      (fuel := 999) (name := `α)
      (domain := .sort (.succ (.param `u)))
      (body := nilCtorBodyRaw) (binderInfo := .implicit)
      (hfresh := nilCandidateContextFresh)
      (annotations := nilDomainAnnotations)
      (hannotations := nilDomainAnnotationsBuild)
      (hannotationsEq := nilDomainAnnotationsEq)
      (hcheck := nilRootCheckValid)
      (hrun := by
        simpa [nilInfoTypeShape, nilCtorTypeRaw] using nilRootWhnfValid)
      (domainCandidate := nilDomainCandidateTrace)
      (bodyCandidate := nilBodyCandidateTrace)
      (hdomain := by
        simpa using nilDomainCandidateTraceLoop 998)
      (hbody := by
        simpa [nilCandidateBodyContext, nilDomainAnnotations] using
          nilBodyCandidateTraceLoop 998))

theorem nilCandidateProduced :
    AddInductive.buildCandidateExpr indexedVecNilInfo.type
      nilCandidateContext = .ok nilCandidate := by
  unfold AddInductive.buildCandidateExpr
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [nilCandidateTraceLoop]
  rfl

/-! ## `IndexedVec.cons` source and candidate contexts -/

def consAlphaName : Name :=
  indexedVecConsInfo.type.bindingName!

def consNName : Name :=
  indexedVecConsInfo.type.bindingBody!.bindingName!

def consHeadName : Name :=
  indexedVecConsInfo.type.bindingBody!.bindingBody!.bindingName!

def consTailName : Name :=
  indexedVecConsInfo.type.bindingBody!.bindingBody!.bindingBody!.bindingName!

def consTerminalRaw : Expr :=
  .app (.app (.const ``IndexedVec [.param `u]) (.bvar 3))
    (.app (.const ``Nat.succ []) (.bvar 2))

def consTailTypeRaw : Expr :=
  .forallE consTailName
    (.app (.app (.const ``IndexedVec [.param `u]) (.bvar 2)) (.bvar 1))
    consTerminalRaw .default

def consHeadTypeRaw : Expr :=
  .forallE consHeadName (.bvar 1) consTailTypeRaw .default

def consNTypeRaw : Expr :=
  .forallE consNName (.const ``Nat []) consHeadTypeRaw .implicit

def consCtorTypeRaw : Expr :=
  .forallE consAlphaName (.sort (.succ (.param `u)))
    consNTypeRaw .implicit

theorem consInfoTypeShape :
    indexedVecConsInfo.type = consCtorTypeRaw := by
  rfl

def consRootContext : AddInductive.Context := ctorContext

def consAlphaId : FVarId := consRootContext.freshFVarId

def consAlphaExpr : Expr := consRootContext.freshExpr

def consAlphaContext : AddInductive.Context :=
  consRootContext.pushLocalDecl consAlphaName .implicit
    (.sort (.succ (.param `u)))

def consNId : FVarId := consAlphaContext.freshFVarId

def consNExpr : Expr := consAlphaContext.freshExpr

def consNContext : AddInductive.Context :=
  consAlphaContext.pushLocalDecl consNName .implicit (.const ``Nat [])

def consHeadId : FVarId := consNContext.freshFVarId

def consHeadExpr : Expr := consNContext.freshExpr

def consAfterAlpha : Expr :=
  .forallE consNName (.const ``Nat [])
    (.forallE consHeadName consAlphaExpr
      (.forallE consTailName
        (.app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr)
          (.bvar 1))
        (.app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr)
          (.app (.const ``Nat.succ []) (.bvar 2)))
        .default)
      .default)
    .implicit

def consAfterN : Expr :=
  .forallE consHeadName consAlphaExpr
    (.forallE consTailName
      (.app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr)
        consNExpr)
      (.app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr)
        (.app (.const ``Nat.succ []) consNExpr))
      .default)
    .default

def consHeadContext : AddInductive.Context :=
  consNContext.pushLocalDecl consHeadName .default consAlphaExpr

def consTailId : FVarId := consHeadContext.freshFVarId

def consTailExpr : Expr := consHeadContext.freshExpr

def consTailDomain : Expr :=
  .app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr) consNExpr

def consAfterHead : Expr :=
  .forallE consTailName consTailDomain
    (.app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr)
      (.app (.const ``Nat.succ []) consNExpr))
    .default

def consTailContext : AddInductive.Context :=
  consHeadContext.pushLocalDecl consTailName .default consTailDomain

def consTerminal : Expr :=
  .app (.app (.const ``IndexedVec [.param `u]) consAlphaExpr)
    (.app (.const ``Nat.succ []) consNExpr)

@[simp] theorem consLiftLooseBVarsFVar
    (id : FVarId) (s d : Nat) :
    (Expr.fvar id).liftLooseBVars' s d = .fvar id := by
  rfl

@[simp] theorem consInstantiateFVar
    (id : FVarId) (a : Expr) (k : Nat) :
    (Expr.fvar id).instantiate1' a k = .fvar id := by
  rfl

theorem consAfterAlphaShape :
    consNTypeRaw.instantiate1 consRootContext.freshExpr =
      consAfterAlpha := by
  simp [consNTypeRaw, consHeadTypeRaw, consTailTypeRaw, consTerminalRaw, consAfterAlpha,
    consAlphaExpr, consRootContext, ctorContext, AddInductive.Context.freshExpr,
    Expr.instantiate1_eq, Expr.instantiate1']

theorem consAfterNShape :
    consAfterAlpha.bindingBody!.instantiate1
      consAlphaContext.freshExpr = consAfterN := by
  simp [consAfterAlpha, consAfterN, consAlphaExpr, consNExpr, consRootContext, consAlphaContext,
    ctorContext, AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem consAfterHeadShape :
    consAfterN.bindingBody!.instantiate1
      consNContext.freshExpr = consAfterHead := by
  simp [consAfterN, consAfterHead, consTailDomain, consAlphaExpr, consNExpr, consRootContext,
    consAlphaContext, consNContext, ctorContext, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem consTerminalShape :
    consAfterHead.bindingBody!.instantiate1
      consHeadContext.freshExpr = consTerminal := by
  simp [consAfterHead, consTerminal, consAlphaExpr, consNExpr, consRootContext, consAlphaContext,
    consNContext, consHeadContext, ctorContext, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

@[simp] theorem consAlphaExprShape :
    consAlphaExpr = .fvar consAlphaId := by
  rfl

@[simp] theorem consNExprShape :
    consNExpr = .fvar consNId := by
  rfl

@[simp] theorem consHeadExprShape :
    consHeadExpr = .fvar consHeadId := by
  rfl

@[simp] theorem consTailExprShape :
    consTailExpr = .fvar consTailId := by
  rfl

theorem consRootFresh :
    consRootContext.lctx.find? consRootContext.freshFVarId = none := by
  simpa [consRootContext, nilCandidateContext] using nilCandidateContextFresh

theorem consAlphaContextWF : consAlphaContext.lctx.WF := by
  change (({} : LocalContext).mkLocalDecl
    consRootContext.freshFVarId consAlphaName
    (.sort (.succ (.param `u))) .implicit).WF
  exact LocalContext.WF.mkLocalDecl LocalContext.WF.nil (by
    have h := LocalContext.WF.find?_eq_find?_toList
      (fv := consRootContext.freshFVarId) LocalContext.WF.nil
    change
      ({ fvarIdToDecl := PersistentHashMap.empty,
         decls := PersistentArray.empty,
         auxDeclToFullName := Std.TreeMap.empty } : LocalContext).find?
        consRootContext.freshFVarId = none
    rw [h]
    simp [LocalContext.toList])

theorem consAlphaContextFresh :
    consAlphaContext.lctx.find? consAlphaContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consAlphaContext.freshFVarId) consAlphaContextWF
  rw [h]
  simp only [consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  intro heq
  injection heq with hname
  injection hname with hidx
  omega

theorem consNContextWF : consNContext.lctx.WF := by
  simpa [consNContext, AddInductive.Context.pushLocalDecl] using
    (LocalContext.WF.mkLocalDecl consAlphaContextWF consAlphaContextFresh)

theorem consNContextFresh :
    consNContext.lctx.find? consNContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consNContext.freshFVarId) consNContextWF
  rw [h]
  simp only [consNContext, consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList, LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  constructor <;> intro heq
  · injection heq with hname
    injection hname with hidx
    omega
  · injection heq with hname
    injection hname with hidx
    omega

theorem consHeadContextWF : consHeadContext.lctx.WF := by
  simpa [consHeadContext, AddInductive.Context.pushLocalDecl] using
    (LocalContext.WF.mkLocalDecl consNContextWF consNContextFresh)

theorem consHeadContextFresh :
    consHeadContext.lctx.find? consHeadContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := consHeadContext.freshFVarId) consHeadContextWF
  rw [h]
  simp only [consHeadContext, consNContext, consAlphaContext,
    consRootContext, ctorContext, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList, LocalContext.mkLocalDecl_toList,
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

theorem consTailContextWF : consTailContext.lctx.WF := by
  simpa [consTailContext, AddInductive.Context.pushLocalDecl] using
    (LocalContext.WF.mkLocalDecl consHeadContextWF consHeadContextFresh)

theorem consAlphaFindInHead :
    consHeadContext.lctx.find? consAlphaId =
      some (.cdecl 0 consAlphaId consAlphaName
        (.sort (.succ (.param `u))) .implicit .default) := by
  rw [consHeadContextWF.find?_eq_find?_toList]
  simp [consHeadContext, consNContext, consAlphaContext, consRootContext, ctorContext, consAlphaId,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl,
    LocalContext.toList, LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

theorem consAlphaFindInN :
    consNContext.lctx.find? consAlphaId =
      some (.cdecl 0 consAlphaId consAlphaName
        (.sort (.succ (.param `u))) .implicit .default) := by
  rw [consNContextWF.find?_eq_find?_toList]
  simp [consNContext, consAlphaContext, consRootContext, ctorContext, consAlphaId,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl,
    LocalContext.toList, LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

theorem consNFindInHead :
    consHeadContext.lctx.find? consNId =
      some (.cdecl 1 consNId consNName (.const ``Nat [])
        .implicit .default) := by
  rw [consHeadContextWF.find?_eq_find?_toList]
  simp [consHeadContext, consNContext, consAlphaContext, consRootContext, ctorContext, consAlphaId,
    consNId, AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId,
    LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId, NameGenerator.next,
    NameGenerator.curr]

theorem consAlphaFindInTail :
    consTailContext.lctx.find? consAlphaId =
      some (.cdecl 0 consAlphaId consAlphaName
        (.sort (.succ (.param `u))) .implicit .default) := by
  rw [consTailContextWF.find?_eq_find?_toList]
  simp [consTailContext, consHeadContext, consNContext, consAlphaContext, consRootContext,
    ctorContext, consAlphaId, AddInductive.Context.pushLocalDecl, AddInductive.Context.freshFVarId,
    LocalContext.mkLocalDecl, LocalContext.toList, LocalDecl.fvarId, NameGenerator.next,
    NameGenerator.curr]

theorem consNFindInTail :
    consTailContext.lctx.find? consNId =
      some (.cdecl 1 consNId consNName (.const ``Nat [])
        .implicit .default) := by
  rw [consTailContextWF.find?_eq_find?_toList]
  simp [consTailContext, consHeadContext, consNContext, consAlphaContext, consRootContext,
    ctorContext, consAlphaId, consNId, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId, LocalContext.mkLocalDecl, LocalContext.toList,
    LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

/-! ## Reusable post-family atom observations -/

theorem ctorNatCheckTypeM (lctx : LocalContext) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType (.const ``Nat [])) =
        .ok (.sort (.succ .zero)) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType (.const ``Nat []) false
      (TypeChecker.Methods.withFuel 10000) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.const ``Nat []) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [inferTypeNatCore 9999 lctx ({} : TypeChecker.State)
    (by simp)]
  rfl

theorem ctorUnfoldNat (lctx methods state) :
    TypeChecker.Inner.unfoldDefinition (.const ``Nat [])
      methods (tcContext lctx) state = .ok (none, state) := by
  change TypeChecker.Inner.unfoldDefinitionCore (.const ``Nat [])
    methods (tcContext lctx) state = _
  simp [TypeChecker.Inner.unfoldDefinitionCore,
    TypeChecker.Inner.isDelta, Expr.getAppFn, tcContext,
    type_lookup_nat, natInfo, ConstantInfo.deltaValue?,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem ctorWhnfLoopNat (lctx methods state n) :
    TypeChecker.Inner.whnf'.loop (.const ``Nat []) (n + 1)
      methods (tcContext lctx) state =
        .ok (.const ``Nat [], state) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [ctorUnfoldNat]

theorem ctorNatWhnfM (lctx : LocalContext) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.whnf (.const ``Nat [])) =
        .ok (.const ``Nat []) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf' (.const ``Nat [])
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show
    (if (tcContext lctx).eagerReduce then
      (tcContext lctx).fuel.whnfEager
    else (tcContext lctx).fuel.whnf) = 100000 by rfl]
  rw [show 100000 = 99999 + 1 by rfl]
  rw [ctorWhnfLoopNat]
  simp [Functor.map, StateT.map, Except.map]

theorem ctorFVarCheckTypeM
    (lctx : LocalContext) (id : FVarId) (type : Expr)
    (hfind : lctx.find? id = some (.cdecl index id name type bi kind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType (.fvar id)) = .ok type := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType (.fvar id) false
      (TypeChecker.Methods.withFuel 10000) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.fvar id) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [inferTypeFVarCore 9999 lctx ({} : TypeChecker.State)
    id type (by simp) hfind]
  rfl

theorem ctorFVarWhnfM
    (lctx : LocalContext) (id : FVarId)
    (hfind : lctx.find? id = some (.cdecl index id name type bi kind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.whnf (.fvar id)) = .ok (.fvar id) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf' (.fvar id)
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.whnf'
  simp only [nilRecMBind]
  rw [show (getLCtx : TypeChecker.RecM LocalContext)
    (TypeChecker.Methods.withFuel 9999)
    (tcContext lctx) ({} : TypeChecker.State) =
      .ok (lctx, ({} : TypeChecker.State)) by rfl]
  simp [TypeChecker.Inner.isLetFVar, hfind]
  rfl

/-! A uniform WHNF observation for opaque applications of the inserted
`IndexedVec` family. -/

def ctorIndexedVecApp (alpha index : Expr) : Expr :=
  .app (.app (.const ``IndexedVec [.param `u]) alpha) index

@[simp] theorem ctorIndexedVecAppGetAppFn (alpha index : Expr) :
    (ctorIndexedVecApp alpha index).getAppFn =
      .const ``IndexedVec [.param `u] := by
  rfl

theorem ctorIndexedVecInductiveReduceRec
    {m : Type → Type} [Monad m]
    (alpha index : Expr) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool) (isNeverProp : Expr → m Bool) :
    inductiveReduceRec ctorEnv (ctorIndexedVecApp alpha index)
      whnf inferType isDefEq isNeverProp = pure none := by
  unfold inductiveReduceRec
  rw [ctorIndexedVecAppGetAppFn]
  simp only
  rw [type_lookup_family]
  rfl

theorem ctorIndexedVecReduceRecursor
    (lctx : LocalContext) (alpha index : Expr)
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.reduceRecursor (ctorIndexedVecApp alpha index)
      methods (tcContext lctx) state =
        .ok (none, state) := by
  unfold TypeChecker.Inner.reduceRecursor
  have hquot : ctorEnv.quotInit = false := by rfl
  simp only [nilRecMBind, nilRecMGetEnv]
  rw [show (tcContext lctx).env = ctorEnv by rfl]
  rw [hquot]
  simp only [Bool.false_eq_true, if_false, nilRecMBind]
  rw [ctorIndexedVecInductiveReduceRec]
  rfl

@[simp] theorem ctorIndexedVecWhnfCoreFamily
    (lctx : LocalContext) (n : Nat) (state : TypeChecker.State) :
    TypeChecker.Inner.whnfCore
      (.const ``IndexedVec [.param `u]) false
      (TypeChecker.Methods.withFuel (n + 1)) (tcContext lctx) state =
        .ok (.const ``IndexedVec [.param `u], state) := by
  rfl

theorem ctorIndexedVecWhnfCoreInitial
    (lctx : LocalContext) (alpha index : Expr) (n : Nat) :
    TypeChecker.Inner.whnfCore' (ctorIndexedVecApp alpha index)
      false (TypeChecker.Methods.withFuel (n + 1))
      (tcContext lctx) ({} : TypeChecker.State) =
        .ok (ctorIndexedVecApp alpha index, ({} : TypeChecker.State)) := by
  unfold ctorIndexedVecApp TypeChecker.Inner.whnfCore'
  simp only [nilRecMBind, nilRecMGet, Std.HashMap.getElem?_empty]
  rw [Expr.withRevApp_eq]
  simp only [nilRecMBind]
  rw [show
    (Expr.app (Expr.app (Expr.const ``IndexedVec [.param `u]) alpha)
      index).getAppFn = Expr.const ``IndexedVec [.param `u] by rfl]
  rw [ctorIndexedVecWhnfCoreFamily lctx n ({} : TypeChecker.State)]
  simp [Expr.structuralEq, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show
    Expr.app (Expr.app (Expr.const ``IndexedVec [.param `u]) alpha)
      index = ctorIndexedVecApp alpha index by rfl]
  rw [ctorIndexedVecReduceRecursor]
  rfl

@[simp] theorem ctorIndexedVecReduceNative
    (lctx : LocalContext) (env : Kernel.Environment)
    (alpha index : Expr) (methods : TypeChecker.Methods)
    (state : TypeChecker.State) :
    (liftM (TypeChecker.Inner.reduceNative env
      (ctorIndexedVecApp alpha index)) :
        TypeChecker.RecM (Option Expr))
      methods (tcContext lctx) state = .ok (none, state) := by
  cases index <;>
    simp [ctorIndexedVecApp, TypeChecker.Inner.reduceNative, Expr.structuralEq]

@[simp] theorem ctorIndexedVecReduceNat
    (lctx : LocalContext) (alpha index : Expr)
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.reduceNat (ctorIndexedVecApp alpha index)
      methods (tcContext lctx) state = .ok (none, state) := by
  simp [ctorIndexedVecApp, TypeChecker.Inner.reduceNat, Expr.getAppNumArgs_eq,
    Expr.getAppArgsRevList]

theorem ctorIndexedVecUnfoldFamily
    (lctx : LocalContext) (methods : TypeChecker.Methods)
    (state : TypeChecker.State) :
    TypeChecker.Inner.unfoldDefinitionCore
      (.const ``IndexedVec [.param `u]) methods (tcContext lctx) state =
        .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinitionCore
  simp only [nilRecMBind, nilRecMGetEnv]
  rw [show (tcContext lctx).env = ctorEnv by rfl]
  rw [nilCandidateIsDeltaFamily]
  rfl

theorem ctorIndexedVecUnfold
    (lctx : LocalContext) (alpha index : Expr)
    (methods : TypeChecker.Methods) (state : TypeChecker.State) :
    TypeChecker.Inner.unfoldDefinition (ctorIndexedVecApp alpha index)
      methods (tcContext lctx) state = .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinition
  rw [show (ctorIndexedVecApp alpha index).isApp = true by rfl]
  simp only [if_true]
  rw [ctorIndexedVecAppGetAppFn]
  simp only [nilRecMBind]
  rw [ctorIndexedVecUnfoldFamily]
  rfl

theorem ctorIndexedVecWhnfLoop
    (lctx : LocalContext) (alpha index : Expr) :
    TypeChecker.Inner.whnf'.loop (ctorIndexedVecApp alpha index) 100000
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State) =
        .ok (ctorIndexedVecApp alpha index, ({} : TypeChecker.State)) := by
  rw [show 100000 = 99999 + 1 by rfl]
  unfold TypeChecker.Inner.whnf'.loop
  rw [show 9999 = 9998 + 1 by rfl]
  simp only [nilRecMBind, nilRecMGetEnv]
  rw [ctorIndexedVecWhnfCoreInitial lctx alpha index 9998]
  simp only []
  rw [ctorIndexedVecReduceNative]
  simp only [nilRecMBind]
  rw [ctorIndexedVecReduceNat]
  simp only [nilRecMBind]
  rw [ctorIndexedVecUnfold]
  rfl

theorem ctorIndexedVecWhnfM
    (lctx : LocalContext) (alpha index : Expr) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.whnf (ctorIndexedVecApp alpha index)) =
        .ok (ctorIndexedVecApp alpha index) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf' (ctorIndexedVecApp alpha index)
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  unfold ctorIndexedVecApp
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show
    (if (tcContext lctx).eagerReduce then
      (tcContext lctx).fuel.whnfEager
    else (tcContext lctx).fuel.whnf) = 100000 by rfl]
  have hloop := ctorIndexedVecWhnfLoop lctx alpha index
  simp only [ctorIndexedVecApp] at hloop
  rw [hloop]
  simp [Functor.map, StateT.map, Except.map]

end Ix.Theory.Named.InductiveReplayFixtures
