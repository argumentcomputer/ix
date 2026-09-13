/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.Environment.InductiveFixtures

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta
open Ix.Theory.Named.InductiveFixtures

def indexedVecKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_indexedVecCandidate natMap

def indexedVecFamilyCandidateContext :
    Ix.Theory.Named.AddInductive.Context where
  env := indexedVecKernelEnv
  lparams := indexedVecInfo.levelParams
  safety := .safe
  allowPrimitive := false

private theorem indexedVecKernel_lookup_nat :
    indexedVecKernelEnv.find? ``Nat = some natInfo := by
  change natMap.find?' ``Nat = some natInfo
  rw [natMap_wf.find?'_eq_find?, nat_type_map_lookup]

private theorem indexedVecKernel_lookup_zero :
    indexedVecKernelEnv.find? ``Nat.zero = some natZeroInfo := by
  change natMap.find?' ``Nat.zero = some natZeroInfo
  rw [natMap_wf.find?'_eq_find?, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert]
  rfl

private theorem indexedVecKernel_lookup_succ :
    indexedVecKernelEnv.find? ``Nat.succ = some natSuccInfo := by
  change natMap.find?' ``Nat.succ = some natSuccInfo
  rw [natMap_wf.find?'_eq_find?, nat_succ_map_lookup]

@[simp] private theorem indexedVecKernel_get_nat :
    indexedVecKernelEnv.get ``Nat = .ok natInfo := by
  simp only [Kernel.Environment.get, indexedVecKernel_lookup_nat,
    Pure.pure, Except.pure]

@[simp] private theorem indexedVecKernel_get_zero :
    indexedVecKernelEnv.get ``Nat.zero = .ok natZeroInfo := by
  simp only [Kernel.Environment.get, indexedVecKernel_lookup_zero,
    Pure.pure, Except.pure]

@[simp] private theorem indexedVecKernel_get_succ :
    indexedVecKernelEnv.get ``Nat.succ = .ok natSuccInfo := by
  simp only [Kernel.Environment.get, indexedVecKernel_lookup_succ,
    Pure.pure, Except.pure]

private def indexedVecParamName : Name :=
  indexedVecInfo.type.bindingName!

private def indexedVecIndexName : Name :=
  indexedVecInfo.type.bindingBody!.bindingName!

private def indexedVecParamCandidateContext :
    Ix.Theory.Named.AddInductive.Context :=
  indexedVecFamilyCandidateContext.pushLocalDecl
    indexedVecParamName .default (.sort (.succ (.param `u)))

private def indexedVecIndexCandidateContext :
    Ix.Theory.Named.AddInductive.Context :=
  indexedVecParamCandidateContext.pushLocalDecl
    indexedVecIndexName .default (.const ``Nat [])

private def indexedVecInnerKernel : Expr :=
  .forallE indexedVecIndexName (.const ``Nat [])
    (.sort (.succ (.param `u))) .default

private def indexedVecTerminalKernel : Expr :=
  .sort (.succ (.param `u))

@[simp] private theorem indexedVecInnerKernel_instantiate1 (arg : Expr) :
    indexedVecInnerKernel.instantiate1 arg = indexedVecInnerKernel := by
  simp [indexedVecInnerKernel, Expr.instantiate1_eq, Expr.instantiate1']

@[simp] private theorem indexedVecTerminalKernel_instantiate1 (arg : Expr) :
    indexedVecTerminalKernel.instantiate1 arg =
      indexedVecTerminalKernel := by
  simp [indexedVecTerminalKernel, Expr.instantiate1_eq,
    Expr.instantiate1']

@[simp] private theorem indexedVecInfo_levelParams :
    indexedVecInfo.levelParams = [`u] := rfl

/-- Reflexive binder-domain equality is an exact successful ordinary-checker
run in any candidate context with positive recursive fuel. -/
theorem candidateIsDefEqSelfValid
    (context : Ix.Theory.Named.AddInductive.Context) (e : Expr)
    (fuel : Nat) (hfuel : context.fuel.recDepth = fuel + 1) :
    Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.Valid ⟨context, e, e⟩ := by
  unfold Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.Valid
  unfold Ix.Theory.Named.TypeChecker.M.run Ix.Theory.Named.TypeChecker.isDefEq
    Ix.Theory.Named.TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hfuel]
  change Except.map (fun x : Bool × Ix.Theory.Named.TypeChecker.State => x.1)
      (Ix.Theory.Named.TypeChecker.Inner.isDefEq e e
        (Ix.Theory.Named.TypeChecker.Methods.withFuel (fuel + 1))
        context.toTypeChecker ({} : Ix.Theory.Named.TypeChecker.State)) = .ok true
  unfold Ix.Theory.Named.TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl e)]
  rfl

def indexedVecTypeCheckerContext
    (lctx : LocalContext) : Ix.Theory.Named.TypeChecker.Context where
  env := indexedVecKernelEnv
  lctx := lctx
  lparams := [`u]

@[simp] private theorem indexedVecFamily_checkLevel :
    Ix.Theory.Named.TypeChecker.Inner.checkLevel
      indexedVecFamilyCandidateContext.toTypeChecker
        (.succ (.param `u)) = .ok () := by
  simp [Ix.Theory.Named.TypeChecker.Inner.checkLevel,
    indexedVecFamilyCandidateContext, indexedVecInfo,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker,
    Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] private theorem indexedVec_checkLevel
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.checkLevel
      (indexedVecTypeCheckerContext lctx)
      (.succ (.param `u)) = .ok () := by
  simp [Ix.Theory.Named.TypeChecker.Inner.checkLevel,
    indexedVecTypeCheckerContext,
    Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] private theorem indexedVecRecMGet (methods context state) :
    (get : Ix.Theory.Named.TypeChecker.RecM Ix.Theory.Named.TypeChecker.State)
        methods context state = .ok (state, state) := rfl

@[simp] private theorem indexedVecRecMReadContext
    (methods context state) :
    (readThe Ix.Theory.Named.TypeChecker.Context :
        Ix.Theory.Named.TypeChecker.RecM Ix.Theory.Named.TypeChecker.Context)
      methods context state = .ok (context, state) := rfl

@[simp] private theorem indexedVecRecMModify
    (f : Ix.Theory.Named.TypeChecker.State → Ix.Theory.Named.TypeChecker.State)
    (methods context state) :
    (modify f : Ix.Theory.Named.TypeChecker.RecM PUnit)
      methods context state = .ok (.unit, f state) := rfl

@[simp] private theorem indexedVecRecMPure
    {α} (a : α) (methods context state) :
    (pure a : Ix.Theory.Named.TypeChecker.RecM α)
      methods context state = .ok (a, state) := rfl

@[simp] private theorem indexedVecRecMBind
    {α β} (x : Ix.Theory.Named.TypeChecker.RecM α)
    (f : α → Ix.Theory.Named.TypeChecker.RecM β)
    (methods context state) :
    (x >>= f) methods context state =
      match x methods context state with
      | .error e => .error e
      | .ok (a, state') => f a methods context state' := by
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  cases h : x methods context state with
  | error => rfl
  | ok value => cases value; rfl

@[simp] private theorem indexedVecRecMLiftExceptOk
    {α} (a : α) (methods context state) :
    (liftM (.ok a : Except Kernel.Exception α) :
      Ix.Theory.Named.TypeChecker.RecM α) methods context state =
        .ok (a, state) := rfl

@[simp] private theorem indexedVecGetNGen
    (context : Ix.Theory.Named.TypeChecker.Context)
    (state : Ix.Theory.Named.TypeChecker.State) :
    (getNGen : Ix.Theory.Named.TypeChecker.M NameGenerator) context state =
      .ok (state.ngen, state) := rfl

@[simp] private theorem indexedVecSetNGen
    (ngen : NameGenerator) (context : Ix.Theory.Named.TypeChecker.Context)
    (state : Ix.Theory.Named.TypeChecker.State) :
    (setNGen ngen : Ix.Theory.Named.TypeChecker.M PUnit) context state =
      .ok (.unit, { state with ngen }) := rfl

@[simp] private theorem indexedVecMPure
    {α} (a : α) (context : Ix.Theory.Named.TypeChecker.Context)
    (state : Ix.Theory.Named.TypeChecker.State) :
    (pure a : Ix.Theory.Named.TypeChecker.M α) context state =
      .ok (a, state) := rfl

@[simp] private theorem indexedVecRecMWithReader
    {α} (f : LocalContext → LocalContext)
    (x : Ix.Theory.Named.TypeChecker.RecM α)
    (methods : Ix.Theory.Named.TypeChecker.Methods)
    (context : Ix.Theory.Named.TypeChecker.Context)
    (state : Ix.Theory.Named.TypeChecker.State) :
    (MonadWithReaderOf.withReader (m := Ix.Theory.Named.TypeChecker.RecM) f x)
      methods context state =
        x methods { context with lctx := f context.lctx } state := rfl

private theorem indexedVecWithLocalDecl
    {α} (name : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → Ix.Theory.Named.TypeChecker.RecM α)
    (methods : Ix.Theory.Named.TypeChecker.Methods)
    (context : Ix.Theory.Named.TypeChecker.Context)
    (state : Ix.Theory.Named.TypeChecker.State) :
    (withLocalDecl (m := Ix.Theory.Named.TypeChecker.RecM) name bi ty k)
      methods context state =
        k (.fvar ⟨state.ngen.curr⟩) methods
          { context with lctx :=
              (context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name ty bi) }
          { state with ngen := state.ngen.next } := rfl

@[simp] private theorem indexedVecEnsureSort
    (u : Level) (source : Expr)
    (methods : Ix.Theory.Named.TypeChecker.Methods)
    (context : Ix.Theory.Named.TypeChecker.Context)
    (state : Ix.Theory.Named.TypeChecker.State) :
    Ix.Theory.Named.TypeChecker.Inner.ensureSortCore (.sort u) source
      methods context state = .ok (.sort u, state) := by
  rfl

private theorem indexedVecInferTypeFuel
    (n e inferOnly context state) :
    Ix.Theory.Named.TypeChecker.Inner.inferType e inferOnly
      (Ix.Theory.Named.TypeChecker.Methods.withFuel (n + 1)) context state =
        Ix.Theory.Named.TypeChecker.Inner.inferType' e inferOnly
          (Ix.Theory.Named.TypeChecker.Methods.withFuel n) context state := rfl

@[simp] private theorem indexedVecInferTypeSortCore
    (n : Nat) (lctx : LocalContext)
    (state : Ix.Theory.Named.TypeChecker.State)
    (hcache : state.inferTypeC[(.sort (.succ (.param `u)) : Expr)]? = none) :
    Ix.Theory.Named.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx)
      state =
        .ok (.sort (.succ (.succ (.param `u))),
          { state with inferTypeC :=
              (state.inferTypeC.insert (.sort (.succ (.param `u)))
                (.sort (.succ (.succ (.param `u))))) }) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem indexedVecInferTypeSortCachedCore
    (n : Nat) (lctx : LocalContext)
    (state : Ix.Theory.Named.TypeChecker.State)
    (hcache : state.inferTypeC[(.sort (.succ (.param `u)) : Expr)]? =
      some (.sort (.succ (.succ (.param `u))))) :
    Ix.Theory.Named.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx)
      state = .ok (.sort (.succ (.succ (.param `u))), state) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache]

@[simp] private theorem indexedVecInferConstantNat
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferConstant
      (indexedVecTypeCheckerContext lctx) ``Nat [] false =
        .ok (.sort (.succ .zero)) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferConstant
  simp [indexedVecTypeCheckerContext, indexedVecKernel_get_nat,
    natInfo, ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams', Bind.bind, Except.bind,
    Pure.pure, Except.pure]

@[simp] theorem indexedVecPreFamilyInferConstantZero
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferConstant
      (indexedVecTypeCheckerContext lctx) ``Nat.zero [] false =
        .ok (.const ``Nat []) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferConstant
  simp [indexedVecTypeCheckerContext, indexedVecKernel_get_zero,
    natZeroInfo, ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] theorem indexedVecPreFamilyInferConstantSucc
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferConstant
      (indexedVecTypeCheckerContext lctx) ``Nat.succ [] false =
        .ok (.forallE `n (.const ``Nat []) (.const ``Nat []) .default) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferConstant
  simp [indexedVecTypeCheckerContext, indexedVecKernel_get_succ,
    natSuccInfo, ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] private theorem indexedVecInferTypeNatCore
    (n : Nat) (lctx : LocalContext)
    (state : Ix.Theory.Named.TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat [] : Expr)]? = none) :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx)
      state =
        .ok (.sort (.succ .zero),
          { state with inferTypeC :=
              (state.inferTypeC.insert (.const ``Nat [])
                (.sort (.succ .zero))) }) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    indexedVecInferConstantNat,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem indexedVecPreFamilyInferTypeFVarCore
    (n : Nat) (lctx : LocalContext)
    (state : Ix.Theory.Named.TypeChecker.State) (id : FVarId) (type : Expr)
    (hcache : state.inferTypeC[(.fvar id : Expr)]? = none)
    (hfind : lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.fvar id) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx) state =
        .ok (type, { state with inferTypeC :=
          state.inferTypeC.insert (.fvar id) type }) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    Ix.Theory.Named.TypeChecker.Inner.inferFVar,
    indexedVecTypeCheckerContext, hfind, LocalDecl.type,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem indexedVecPreFamilyInferTypeZeroCore
    (n : Nat) (lctx : LocalContext)
    (state : Ix.Theory.Named.TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat.zero [] : Expr)]? = none) :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx) state =
        .ok (.const ``Nat [], { state with inferTypeC :=
          (state.inferTypeC.insert (.const ``Nat.zero [])
            (.const ``Nat [])) }) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    indexedVecPreFamilyInferConstantZero,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem indexedVecPreFamilyInferTypeSuccCore
    (n : Nat) (lctx : LocalContext)
    (state : Ix.Theory.Named.TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat.succ [] : Expr)]? = none) :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat.succ []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx) state =
        .ok (.forallE `n (.const ``Nat []) (.const ``Nat []) .default,
          { state with inferTypeC := (state.inferTypeC.insert
            (.const ``Nat.succ [])
            (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)) }) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    indexedVecPreFamilyInferConstantSucc,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private def indexedVecRootSortState : Ix.Theory.Named.TypeChecker.State :=
  { ({} : Ix.Theory.Named.TypeChecker.State) with inferTypeC :=
      (({} : Ix.Theory.Named.TypeChecker.State).inferTypeC.insert
        (.sort (.succ (.param `u)))
        (.sort (.succ (.succ (.param `u))))) }

@[simp] private theorem indexedVecRootSortCore :
    Ix.Theory.Named.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecRootSortState) := by
  simpa [indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecRootSortState] using
      (indexedVecInferTypeSortCore 9998 ({} : LocalContext)
        ({} : Ix.Theory.Named.TypeChecker.State) Std.HashMap.getElem?_empty)

private def indexedVecParamLctx : LocalContext :=
  ({} : LocalContext).mkLocalDecl
    ⟨indexedVecRootSortState.ngen.curr⟩ indexedVecParamName
    (.sort (.succ (.param `u))) .default

private def indexedVecAfterParamState : Ix.Theory.Named.TypeChecker.State :=
  { indexedVecRootSortState with
    ngen := indexedVecRootSortState.ngen.next }

private def indexedVecNatState : Ix.Theory.Named.TypeChecker.State :=
  { indexedVecAfterParamState with
    inferTypeC := indexedVecAfterParamState.inferTypeC.insert
      (.const ``Nat []) (.sort (.succ .zero)) }

private def indexedVecIndexLctx : LocalContext :=
  indexedVecParamLctx.mkLocalDecl
    ⟨indexedVecNatState.ngen.curr⟩ indexedVecIndexName
    (.const ``Nat []) .default

private def indexedVecAfterIndexState : Ix.Theory.Named.TypeChecker.State :=
  { indexedVecNatState with ngen := indexedVecNatState.ngen.next }

private theorem indexedVecOuterWithLocalDecl
    {α} (k : Expr → Ix.Theory.Named.TypeChecker.RecM α)
    (methods : Ix.Theory.Named.TypeChecker.Methods) :
    (withLocalDecl (m := Ix.Theory.Named.TypeChecker.RecM)
      indexedVecParamName .default (.sort (.succ (.param `u))) k)
        methods indexedVecFamilyCandidateContext.toTypeChecker
          indexedVecRootSortState =
      k (.fvar ⟨indexedVecRootSortState.ngen.curr⟩) methods
        { indexedVecFamilyCandidateContext.toTypeChecker with
          lctx := indexedVecParamLctx }
        indexedVecAfterParamState := by
  simpa [indexedVecParamLctx, indexedVecAfterParamState,
    indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker] using
    (indexedVecWithLocalDecl indexedVecParamName .default
      (.sort (.succ (.param `u))) k methods
      indexedVecFamilyCandidateContext.toTypeChecker indexedVecRootSortState)

private theorem indexedVecInnerWithLocalDecl
    {α} (k : Expr → Ix.Theory.Named.TypeChecker.RecM α)
    (methods : Ix.Theory.Named.TypeChecker.Methods) :
    (withLocalDecl (m := Ix.Theory.Named.TypeChecker.RecM)
      indexedVecIndexName .default (.const ``Nat []) k)
        methods
          { indexedVecFamilyCandidateContext.toTypeChecker with
            lctx := indexedVecParamLctx }
          indexedVecNatState =
      k (.fvar ⟨indexedVecNatState.ngen.curr⟩) methods
        { indexedVecFamilyCandidateContext.toTypeChecker with
          lctx := indexedVecIndexLctx }
        indexedVecAfterIndexState := by
  simpa [indexedVecIndexLctx, indexedVecAfterIndexState] using
    (indexedVecWithLocalDecl indexedVecIndexName .default
      (.const ``Nat []) k methods
      { indexedVecFamilyCandidateContext.toTypeChecker with
        lctx := indexedVecParamLctx }
      indexedVecNatState)

@[simp] private theorem indexedVecNat_beq_sort :
    ((.const ``Nat [] : Expr) == .sort (.succ (.param `u))) = false := by
  change Expr.eqv (.const ``Nat []) (.sort (.succ (.param `u))) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem indexedVecAfterIndexState_sort_cache :
    indexedVecAfterIndexState.inferTypeC[
      (.sort (.succ (.param `u)) : Expr)]? =
        some (.sort (.succ (.succ (.param `u)))) := by
  change
    (((({} : Ix.Theory.Named.InferCache).insert
      (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u))))).insert
      (.const ``Nat []) (.sort (.succ .zero)))[
        (.sort (.succ (.param `u)) : Expr)]?) = _
  rw [Std.HashMap.getElem?_insert, indexedVecNat_beq_sort]
  exact Std.HashMap.getElem?_insert_self

@[simp] private theorem indexedVecParamNatCore :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      { indexedVecFamilyCandidateContext.toTypeChecker with
        lctx := indexedVecParamLctx }
      indexedVecAfterParamState =
        .ok (.sort (.succ .zero), indexedVecNatState) := by
  simpa [indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecAfterParamState, indexedVecRootSortState,
    indexedVecNatState] using
      (indexedVecInferTypeNatCore 9998 indexedVecParamLctx
        indexedVecAfterParamState (by
          simp [indexedVecAfterParamState, indexedVecRootSortState]))

@[simp] private theorem indexedVecTerminalSortCore :
    Ix.Theory.Named.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      { indexedVecFamilyCandidateContext.toTypeChecker with
        lctx := indexedVecIndexLctx }
      indexedVecAfterIndexState =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecAfterIndexState) := by
  simpa [indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecAfterIndexState, indexedVecNatState,
    indexedVecAfterParamState, indexedVecRootSortState] using
      (indexedVecInferTypeSortCachedCore 9998 indexedVecIndexLctx
        indexedVecAfterIndexState indexedVecAfterIndexState_sort_cache)

private def indexedVecFamilyInferredLevel : Level :=
  mkLevelIMax' (.succ (.succ (.param `u)))
    (mkLevelIMax' (.succ .zero) (.succ (.succ (.param `u))))

private theorem indexedVecFamilyInferForall :
    Ix.Theory.Named.TypeChecker.Inner.inferForall
      (.forallE indexedVecParamName (.sort (.succ (.param `u)))
        (.forallE indexedVecIndexName (.const ``Nat [])
          (.sort (.succ (.param `u))) .default) .default)
      false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort indexedVecFamilyInferredLevel,
          indexedVecAfterIndexState) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferForall
  simp only [Ix.Theory.Named.TypeChecker.Inner.inferForall.loop]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev #[] =
      .sort (.succ (.param `u)) by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecRootSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecOuterWithLocalDecl]
  rw [show
    (.const ``Nat [] : Expr).instantiateRev
        (#[] |>.push (.fvar ⟨indexedVecRootSortState.ngen.curr⟩)) =
      .const ``Nat [] by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
          Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecParamNatCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecInnerWithLocalDecl]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev
        ((#[] |>.push
          (.fvar ⟨indexedVecRootSortState.ngen.curr⟩)).push
          (.fvar ⟨indexedVecNatState.ngen.curr⟩)) =
      .sort (.succ (.param `u)) by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
          Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecTerminalSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp [indexedVecFamilyInferredLevel, Expr.sortLevel!,
    Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]

private def indexedVecFamilyCheckedState : Ix.Theory.Named.TypeChecker.State :=
  { indexedVecAfterIndexState with
    inferTypeC := indexedVecAfterIndexState.inferTypeC.insert
      (.forallE indexedVecParamName (.sort (.succ (.param `u)))
        (.forallE indexedVecIndexName (.const ``Nat [])
          (.sort (.succ (.param `u))) .default) .default)
      (.sort indexedVecFamilyInferredLevel) }

private theorem indexedVecFamilyCheckTypeInner :
    Ix.Theory.Named.TypeChecker.Inner.inferType indexedVecInfo.type false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort indexedVecFamilyInferredLevel,
          indexedVecFamilyCheckedState) := by
  change Ix.Theory.Named.TypeChecker.Inner.inferType'
    (.forallE indexedVecParamName (.sort (.succ (.param `u)))
      (.forallE indexedVecIndexName (.const ``Nat [])
        (.sort (.succ (.param `u))) .default) .default)
    false (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
    indexedVecFamilyCandidateContext.toTypeChecker
    ({} : Ix.Theory.Named.TypeChecker.State) = _
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    indexedVecFamilyInferForall, indexedVecFamilyCheckedState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem indexedVecFamily_whnfM :
    Ix.Theory.Named.TypeChecker.M.run
      indexedVecFamilyCandidateContext.env
      indexedVecFamilyCandidateContext.safety
      indexedVecFamilyCandidateContext.lctx
      indexedVecFamilyCandidateContext.lparams
      indexedVecFamilyCandidateContext.fuel
      (Ix.Theory.Named.TypeChecker.whnf indexedVecInfo.type) =
        .ok indexedVecInfo.type := by
  rfl

private theorem indexedVecSort_checkTypeM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.checkType (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.succ (.param `u)))) := by
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.inferType
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  rw [indexedVecInferTypeFuel 9999]
  rw [indexedVecInferTypeSortCore 9999 lctx
    ({} : Ix.Theory.Named.TypeChecker.State) Std.HashMap.getElem?_empty]
  rfl

private theorem indexedVecSort_whnfM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.whnf (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.param `u))) := by
  rfl

private theorem indexedVecNat_checkTypeM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.checkType (.const ``Nat [])) =
        .ok (.sort (.succ .zero)) := by
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.inferType (.const ``Nat []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  rw [indexedVecInferTypeFuel 9999]
  rw [indexedVecInferTypeNatCore 9999 lctx
    ({} : Ix.Theory.Named.TypeChecker.State) Std.HashMap.getElem?_empty]
  rfl

private theorem indexedVecUnfoldNat (lctx methods state) :
    Ix.Theory.Named.TypeChecker.Inner.unfoldDefinition (.const ``Nat [])
      methods (indexedVecTypeCheckerContext lctx) state =
        .ok (none, state) := by
  change Ix.Theory.Named.TypeChecker.Inner.unfoldDefinitionCore
    (.const ``Nat []) methods (indexedVecTypeCheckerContext lctx) state = _
  simp [Ix.Theory.Named.TypeChecker.Inner.unfoldDefinitionCore,
    Ix.Theory.Named.TypeChecker.Inner.isDelta, Expr.getAppFn,
    indexedVecTypeCheckerContext, indexedVecKernel_lookup_nat,
    natInfo, ConstantInfo.deltaValue?,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem indexedVecWhnfLoopNat (lctx methods state n) :
    Ix.Theory.Named.TypeChecker.Inner.whnf'.loop (.const ``Nat []) (n + 1)
      methods (indexedVecTypeCheckerContext lctx) state =
        .ok (.const ``Nat [], state) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.whnf'.loop
  simp [indexedVecUnfoldNat]

private theorem indexedVecNat_whnfM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.whnf (.const ``Nat [])) =
        .ok (.const ``Nat []) := by
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.whnf' (.const ``Nat [])
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  unfold Ix.Theory.Named.TypeChecker.Inner.whnf'
  simp
  rw [show
    (if (indexedVecTypeCheckerContext lctx).eagerReduce then
      (indexedVecTypeCheckerContext lctx).fuel.whnfEager
    else (indexedVecTypeCheckerContext lctx).fuel.whnf) = 100000 by rfl]
  rw [show 100000 = 99999 + 1 by rfl]
  rw [indexedVecWhnfLoopNat]
  simp [Functor.map, StateT.map, Except.map]

private def indexedVecInnerInferredLevel : Level :=
  mkLevelIMax' (.succ .zero) (.succ (.succ (.param `u)))

private def indexedVecInnerNatState : Ix.Theory.Named.TypeChecker.State :=
  { ({} : Ix.Theory.Named.TypeChecker.State) with
    inferTypeC := ({} : Ix.Theory.Named.TypeChecker.State).inferTypeC.insert
      (.const ``Nat []) (.sort (.succ .zero)) }

private def indexedVecInnerCheckerLctx : LocalContext :=
  indexedVecParamCandidateContext.lctx.mkLocalDecl
    ⟨indexedVecInnerNatState.ngen.curr⟩ indexedVecIndexName
    (.const ``Nat []) .default

private def indexedVecInnerAfterIndexState :
    Ix.Theory.Named.TypeChecker.State :=
  { indexedVecInnerNatState with
    ngen := indexedVecInnerNatState.ngen.next }

private def indexedVecInnerSortState : Ix.Theory.Named.TypeChecker.State :=
  { indexedVecInnerAfterIndexState with
    inferTypeC := indexedVecInnerAfterIndexState.inferTypeC.insert
      (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u)))) }

private def indexedVecInnerCheckedState : Ix.Theory.Named.TypeChecker.State :=
  { indexedVecInnerSortState with
    inferTypeC := indexedVecInnerSortState.inferTypeC.insert
      indexedVecInnerKernel (.sort indexedVecInnerInferredLevel) }

@[simp] private theorem indexedVecInnerNatCore :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort (.succ .zero), indexedVecInnerNatState) := by
  simpa [indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecInnerNatState] using
      (indexedVecInferTypeNatCore 9998
        indexedVecParamCandidateContext.lctx
        ({} : Ix.Theory.Named.TypeChecker.State) Std.HashMap.getElem?_empty)

private theorem indexedVecInnerCheckerWithLocalDecl
    {α} (k : Expr → Ix.Theory.Named.TypeChecker.RecM α)
    (methods : Ix.Theory.Named.TypeChecker.Methods) :
    (withLocalDecl (m := Ix.Theory.Named.TypeChecker.RecM)
      indexedVecIndexName .default (.const ``Nat []) k)
        methods indexedVecParamCandidateContext.toTypeChecker
          indexedVecInnerNatState =
      k (.fvar ⟨indexedVecInnerNatState.ngen.curr⟩) methods
        { indexedVecParamCandidateContext.toTypeChecker with
          lctx := indexedVecInnerCheckerLctx }
        indexedVecInnerAfterIndexState := by
  simpa [indexedVecInnerCheckerLctx,
    indexedVecInnerAfterIndexState,
    indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker] using
      (indexedVecWithLocalDecl indexedVecIndexName .default
        (.const ``Nat []) k methods
        indexedVecParamCandidateContext.toTypeChecker
        indexedVecInnerNatState)

@[simp] private theorem indexedVecInnerTerminalSortCore :
    Ix.Theory.Named.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      { indexedVecParamCandidateContext.toTypeChecker with
        lctx := indexedVecInnerCheckerLctx }
      indexedVecInnerAfterIndexState =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecInnerSortState) := by
  simpa [indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
    Ix.Theory.Named.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecInnerAfterIndexState, indexedVecInnerNatState,
    indexedVecInnerSortState] using
      (indexedVecInferTypeSortCore 9998 indexedVecInnerCheckerLctx
        indexedVecInnerAfterIndexState (by
          simp [indexedVecInnerAfterIndexState,
            indexedVecInnerNatState]))

private theorem indexedVecInnerInferForall :
    Ix.Theory.Named.TypeChecker.Inner.inferForall indexedVecInnerKernel false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort indexedVecInnerInferredLevel,
          indexedVecInnerSortState) := by
  unfold indexedVecInnerKernel
  unfold Ix.Theory.Named.TypeChecker.Inner.inferForall
  simp only [Ix.Theory.Named.TypeChecker.Inner.inferForall.loop]
  rw [show (.const ``Nat [] : Expr).instantiateRev #[] =
    .const ``Nat [] by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecInnerNatCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecInnerCheckerWithLocalDecl]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev
      (#[] |>.push (.fvar ⟨indexedVecInnerNatState.ngen.curr⟩)) =
        .sort (.succ (.param `u)) by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
        Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecInnerTerminalSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp [indexedVecInnerInferredLevel, Expr.sortLevel!,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure]

private theorem indexedVecInner_checkTypeM :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe
      indexedVecParamCandidateContext.lctx [`u] ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.checkType indexedVecInnerKernel) =
        .ok (.sort indexedVecInnerInferredLevel) := by
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.inferType indexedVecInnerKernel false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.inferType' indexedVecInnerKernel false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [indexedVecInnerKernel, Expr.hasLooseBVars,
    Expr.looseBVarRange',
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show
    Ix.Theory.Named.TypeChecker.Inner.inferForall
      (.forallE indexedVecIndexName (.const ``Nat [])
        (.sort (.succ (.param `u))) .default)
      false (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort indexedVecInnerInferredLevel,
          indexedVecInnerSortState) by
      simpa [indexedVecInnerKernel] using indexedVecInnerInferForall]
  rfl

/-! The constructor pre-family replay runs after family analysis has added its
parameter and index locals, but before `IndexedVec` itself is present in the
kernel environment.  The following executions expose the family-free pieces
of the family candidate proof for an arbitrary local context. -/

def indexedVecPreFamilyIndexTelescope : Expr :=
  .forallE indexedVecIndexName (.const ``Nat [])
    (.sort (.succ (.param `u))) .default

theorem indexedVecPreFamilyIndexTelescope_eq :
    indexedVecPreFamilyIndexTelescope = indexedVecInfo.type.bindingBody! := by
  rfl

theorem indexedVecPreFamilySortCheckTypeM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.checkType
        (.sort (.succ (.param `u)))) =
      .ok (.sort (.succ (.succ (.param `u)))) :=
  indexedVecSort_checkTypeM lctx

theorem indexedVecPreFamilyNatCheckTypeM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.checkType (.const ``Nat [])) =
      .ok (.sort (.succ .zero)) :=
  indexedVecNat_checkTypeM lctx

@[simp] private theorem indexedVecInferConstantNatOnly
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferConstant
      (indexedVecTypeCheckerContext lctx) ``Nat [] true =
        .ok (.sort (.succ .zero)) := by
  unfold Ix.Theory.Named.TypeChecker.Inner.inferConstant
  simp [indexedVecTypeCheckerContext, indexedVecKernel_get_nat, natInfo, ConstantInfo.levelParams,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams, Expr.instantiateLevelParams_eq,
    Expr.instantiateLevelParamsCore', Level.substParams', Bind.bind, Except.bind, Pure.pure,
    Except.pure]

private def indexedVecPreFamilyNatInferOnlyState :
    Ix.Theory.Named.TypeChecker.State :=
  { ({} : Ix.Theory.Named.TypeChecker.State) with
    inferTypeI := ({} : Ix.Theory.Named.TypeChecker.State).inferTypeI.insert
      (.const ``Nat []) (.sort (.succ .zero)) }

private theorem indexedVecPreFamilyNatInferOnly
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferType (.const ``Nat []) true
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort (.succ .zero),
          indexedVecPreFamilyNatInferOnlyState) := by
  change Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat []) true
    (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
    (indexedVecTypeCheckerContext lctx)
    ({} : Ix.Theory.Named.TypeChecker.State) = _
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [indexedVecPreFamilyNatInferOnlyState,
    Expr.hasLooseBVars, Expr.looseBVarRange',
    indexedVecInferConstantNatOnly, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem indexedVecPreFamilyNatEnsureTypeM (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.ensureType (.const ``Nat [])) =
        .ok (.sort (.succ .zero)) := by
  unfold Ix.Theory.Named.TypeChecker.ensureType Ix.Theory.Named.TypeChecker.inferType
    Ix.Theory.Named.TypeChecker.ensureSort Ix.Theory.Named.TypeChecker.RecM.run
    Ix.Theory.Named.TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show Ix.Theory.Named.TypeChecker.Inner.inferType (.const ``Nat []) true
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      { env := indexedVecKernelEnv
        lctx := lctx
        safety := .safe
        lparams := [`u]
        fuel := ({} : FuelConfig) }
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort (.succ .zero),
          indexedVecPreFamilyNatInferOnlyState) by
    simpa [indexedVecTypeCheckerContext] using
      indexedVecPreFamilyNatInferOnly lctx]
  rfl

private def indexedVecPreFamilyIndexCheckerLctx
    (lctx : LocalContext) : LocalContext :=
  lctx.mkLocalDecl ⟨indexedVecInnerNatState.ngen.curr⟩
    indexedVecIndexName (.const ``Nat []) .default

private theorem indexedVecPreFamilyIndexNatCore (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort (.succ .zero), indexedVecInnerNatState) := by
  simp [indexedVecInnerNatState]

private theorem indexedVecPreFamilyIndexWithLocalDecl
    (lctx : LocalContext)
    {α} (k : Expr → Ix.Theory.Named.TypeChecker.RecM α)
    (methods : Ix.Theory.Named.TypeChecker.Methods) :
    (withLocalDecl (m := Ix.Theory.Named.TypeChecker.RecM)
      indexedVecIndexName .default (.const ``Nat []) k)
        methods (indexedVecTypeCheckerContext lctx)
          indexedVecInnerNatState =
      k (.fvar ⟨indexedVecInnerNatState.ngen.curr⟩) methods
        { indexedVecTypeCheckerContext lctx with
          lctx := indexedVecPreFamilyIndexCheckerLctx lctx }
        indexedVecInnerAfterIndexState := by
  simpa [indexedVecPreFamilyIndexCheckerLctx,
    indexedVecInnerAfterIndexState, indexedVecTypeCheckerContext] using
    (indexedVecWithLocalDecl indexedVecIndexName .default
      (.const ``Nat []) k methods (indexedVecTypeCheckerContext lctx)
      indexedVecInnerNatState)

private theorem indexedVecPreFamilyIndexSortCore (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9998)
      { indexedVecTypeCheckerContext lctx with
        lctx := indexedVecPreFamilyIndexCheckerLctx lctx }
      indexedVecInnerAfterIndexState =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecInnerSortState) := by
  simpa [indexedVecPreFamilyIndexCheckerLctx,
    indexedVecInnerAfterIndexState, indexedVecInnerNatState,
    indexedVecInnerSortState, indexedVecTypeCheckerContext] using
    (indexedVecInferTypeSortCore 9998
      (indexedVecPreFamilyIndexCheckerLctx lctx)
      indexedVecInnerAfterIndexState (by
        simp [indexedVecInnerAfterIndexState,
          indexedVecInnerNatState]))

private theorem indexedVecPreFamilyIndexInferForall
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.Inner.inferForall
      indexedVecPreFamilyIndexTelescope false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort indexedVecInnerInferredLevel,
          indexedVecInnerSortState) := by
  unfold indexedVecPreFamilyIndexTelescope
  unfold Ix.Theory.Named.TypeChecker.Inner.inferForall
  simp only [Ix.Theory.Named.TypeChecker.Inner.inferForall.loop]
  rw [show (.const ``Nat [] : Expr).instantiateRev #[] =
    .const ``Nat [] by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecPreFamilyIndexNatCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecPreFamilyIndexWithLocalDecl]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev
      (#[] |>.push (.fvar ⟨indexedVecInnerNatState.ngen.curr⟩)) =
        .sort (.succ (.param `u)) by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
        Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecPreFamilyIndexSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp [indexedVecInnerInferredLevel, Expr.sortLevel!,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure]

theorem indexedVecPreFamilyIndexTelescopeCheckTypeM
    (lctx : LocalContext) :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.checkType
        indexedVecPreFamilyIndexTelescope) =
      .ok (.sort indexedVecInnerInferredLevel) := by
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.inferType'
      indexedVecPreFamilyIndexTelescope false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  unfold Ix.Theory.Named.TypeChecker.Inner.inferType'
  simp [indexedVecPreFamilyIndexTelescope, Expr.hasLooseBVars,
    Expr.looseBVarRange', Bind.bind, ReaderT.bind, StateT.bind,
    Except.bind]
  rw [show
    Ix.Theory.Named.TypeChecker.Inner.inferForall
      (.forallE indexedVecIndexName (.const ``Nat [])
        (.sort (.succ (.param `u))) .default)
      false (Ix.Theory.Named.TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : Ix.Theory.Named.TypeChecker.State) =
        .ok (.sort indexedVecInnerInferredLevel,
          indexedVecInnerSortState) by
      simpa [indexedVecPreFamilyIndexTelescope] using
        indexedVecPreFamilyIndexInferForall lctx]
  rfl

private theorem indexedVecInner_whnfM :
    Ix.Theory.Named.TypeChecker.M.run indexedVecKernelEnv .safe
      indexedVecParamCandidateContext.lctx [`u] ({} : FuelConfig)
      (Ix.Theory.Named.TypeChecker.whnf indexedVecInnerKernel) =
        .ok indexedVecInnerKernel := by
  rfl

private theorem indexedVecFamilyCandidateFresh :
    indexedVecFamilyCandidateContext.lctx.find?
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

private theorem indexedVecParamCandidateFresh :
    indexedVecParamCandidateContext.lctx.find?
      indexedVecParamCandidateContext.freshFVarId = none := by
  have hroot := indexedVecFamilyCandidateFresh
  have hwf : indexedVecParamCandidateContext.lctx.WF := by
    change (({} : LocalContext).mkLocalDecl
      indexedVecFamilyCandidateContext.freshFVarId
      indexedVecParamName (.sort (.succ (.param `u))) .default).WF
    exact LocalContext.WF.mkLocalDecl LocalContext.WF.nil (by
      simpa [indexedVecFamilyCandidateContext] using hroot)
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecParamCandidateContext.freshFVarId) hwf
  rw [h]
  simp only [indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
    Ix.Theory.Named.AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  intro heq
  injection heq with hname
  injection hname with hidx
  omega

private theorem indexedVecFamily_checkTypeM :
    Ix.Theory.Named.TypeChecker.M.run
      indexedVecFamilyCandidateContext.env
      indexedVecFamilyCandidateContext.safety
      indexedVecFamilyCandidateContext.lctx
      indexedVecFamilyCandidateContext.lparams
      indexedVecFamilyCandidateContext.fuel
      (Ix.Theory.Named.TypeChecker.checkType indexedVecInfo.type) =
        .ok (.sort indexedVecFamilyInferredLevel) := by
  change Except.map
    (fun x : Expr × Ix.Theory.Named.TypeChecker.State => x.1)
    (Ix.Theory.Named.TypeChecker.Inner.inferType indexedVecInfo.type false
      (Ix.Theory.Named.TypeChecker.Methods.withFuel 10000)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Ix.Theory.Named.TypeChecker.State)) = _
  rw [indexedVecFamilyCheckTypeInner]
  rfl

private def indexedVecParamAnnotations :
    Ix.Theory.Named.AddInductive.CandidateTypeAnnotations
      indexedVecTerminalKernel where
  consumed := indexedVecTerminalKernel
  trace := .identity _

private def indexedVecIndexAnnotations :
    Ix.Theory.Named.AddInductive.CandidateTypeAnnotations (.const ``Nat []) where
  consumed := .const ``Nat []
  trace := .identity _

private theorem indexedVecParamAnnotationTrace_build :
    Ix.Theory.Named.AddInductive.CandidateTypeAnnotationTrace.build
      indexedVecTerminalKernel =
        ⟨indexedVecTerminalKernel, .identity _⟩ := by
  simp [Ix.Theory.Named.AddInductive.CandidateTypeAnnotationTrace.build,
    indexedVecTerminalKernel]

private theorem indexedVecIndexAnnotationTrace_build :
    Ix.Theory.Named.AddInductive.CandidateTypeAnnotationTrace.build
      (.const ``Nat []) = ⟨.const ``Nat [], .identity _⟩ := by
  simp [Ix.Theory.Named.AddInductive.CandidateTypeAnnotationTrace.build]

private theorem indexedVecParamAnnotations_build :
    Ix.Theory.Named.AddInductive.buildCandidateTypeAnnotations
      indexedVecTerminalKernel = .ok indexedVecParamAnnotations := by
  unfold Ix.Theory.Named.AddInductive.buildCandidateTypeAnnotations
  rw [indexedVecParamAnnotationTrace_build]
  rfl

private theorem indexedVecIndexAnnotations_build :
    Ix.Theory.Named.AddInductive.buildCandidateTypeAnnotations
      (.const ``Nat []) = .ok indexedVecIndexAnnotations := by
  unfold Ix.Theory.Named.AddInductive.buildCandidateTypeAnnotations
  rw [indexedVecIndexAnnotationTrace_build]
  rfl

private theorem indexedVecParamAnnotations_match :
    indexedVecParamAnnotations.Matches :=
  Ix.Theory.Named.AddInductive.CandidateTypeAnnotations.matches_of_build
    indexedVecParamAnnotations indexedVecParamAnnotations_build

private theorem indexedVecIndexAnnotations_match :
    indexedVecIndexAnnotations.Matches :=
  Ix.Theory.Named.AddInductive.CandidateTypeAnnotations.matches_of_build
    indexedVecIndexAnnotations indexedVecIndexAnnotations_build

private theorem indexedVecParamAnnotationsEq :
    Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.Valid
      ⟨indexedVecFamilyCandidateContext, indexedVecTerminalKernel,
        indexedVecParamAnnotations.consumed⟩ := by
  simpa [indexedVecParamAnnotations] using
    (candidateIsDefEqSelfValid indexedVecFamilyCandidateContext
      indexedVecTerminalKernel 9999 rfl)

private theorem indexedVecIndexAnnotationsEq :
    Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.Valid
      ⟨indexedVecParamCandidateContext, (.const ``Nat []),
        indexedVecIndexAnnotations.consumed⟩ := by
  simpa [indexedVecIndexAnnotations] using
    (candidateIsDefEqSelfValid indexedVecParamCandidateContext
      (.const ``Nat []) 9999 rfl)

private def indexedVecParamDomainCandidateTrace :
    Ix.Theory.Named.AddInductive.CandidateExprTrace
      indexedVecFamilyCandidateContext indexedVecTerminalKernel :=
  .terminal indexedVecFamilyCandidateContext indexedVecTerminalKernel
    (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateCheckTypeStep.Valid,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        indexedVecTerminalKernel] using
          indexedVecSort_checkTypeM
            indexedVecFamilyCandidateContext.lctx)
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateWhnfStep.Valid,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        indexedVecTerminalKernel] using
          indexedVecSort_whnfM indexedVecFamilyCandidateContext.lctx)

private def indexedVecIndexDomainCandidateTrace :
    Ix.Theory.Named.AddInductive.CandidateExprTrace
      indexedVecParamCandidateContext (.const ``Nat []) :=
  .terminal indexedVecParamCandidateContext (.const ``Nat [])
    (.sort (.succ .zero)) (.const ``Nat [])
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateCheckTypeStep.Valid,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Ix.Theory.Named.AddInductive.Context.pushLocalDecl] using
          indexedVecNat_checkTypeM indexedVecParamCandidateContext.lctx)
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateWhnfStep.Valid,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Ix.Theory.Named.AddInductive.Context.pushLocalDecl] using
          indexedVecNat_whnfM indexedVecParamCandidateContext.lctx)

private def indexedVecTerminalCandidateTrace :
    Ix.Theory.Named.AddInductive.CandidateExprTrace
      indexedVecIndexCandidateContext
      (indexedVecTerminalKernel.instantiate1
        indexedVecParamCandidateContext.freshExpr) :=
  .terminal indexedVecIndexCandidateContext
    (indexedVecTerminalKernel.instantiate1
      indexedVecParamCandidateContext.freshExpr)
    (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateCheckTypeStep.Valid,
        indexedVecIndexCandidateContext,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
        indexedVecTerminalKernel] using
          indexedVecSort_checkTypeM indexedVecIndexCandidateContext.lctx)
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateWhnfStep.Valid,
        indexedVecIndexCandidateContext,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
        indexedVecTerminalKernel] using
          indexedVecSort_whnfM indexedVecIndexCandidateContext.lctx)

private def indexedVecInnerCandidateTrace :
    Ix.Theory.Named.AddInductive.CandidateExprTrace
      indexedVecParamCandidateContext
      (indexedVecInnerKernel.instantiate1
        indexedVecFamilyCandidateContext.freshExpr) :=
  .forallE indexedVecParamCandidateContext
    (indexedVecInnerKernel.instantiate1
      indexedVecFamilyCandidateContext.freshExpr)
    (.sort indexedVecInnerInferredLevel)
    indexedVecIndexName (.const ``Nat []) indexedVecTerminalKernel
    .default indexedVecParamCandidateFresh indexedVecIndexAnnotations
    indexedVecIndexAnnotationsEq
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateCheckTypeStep.Valid,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
        indexedVecInnerKernel, indexedVecTerminalKernel,
        Expr.instantiate1'] using
          indexedVecInner_checkTypeM)
    (by
      simpa [Ix.Theory.Named.AddInductive.CandidateWhnfStep.Valid,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
        indexedVecInnerKernel, indexedVecTerminalKernel,
        Expr.instantiate1'] using
          indexedVecInner_whnfM)
    indexedVecIndexDomainCandidateTrace indexedVecTerminalCandidateTrace

private def indexedVecFamilyCandidateTrace :
    Ix.Theory.Named.AddInductive.CandidateExprTrace
      indexedVecFamilyCandidateContext indexedVecInfo.type :=
  .forallE indexedVecFamilyCandidateContext indexedVecInfo.type
    (.sort indexedVecFamilyInferredLevel)
    indexedVecParamName indexedVecTerminalKernel indexedVecInnerKernel
    .default indexedVecFamilyCandidateFresh indexedVecParamAnnotations
    indexedVecParamAnnotationsEq
    indexedVecFamily_checkTypeM
    (by
      change Ix.Theory.Named.TypeChecker.M.run
        indexedVecFamilyCandidateContext.env
        indexedVecFamilyCandidateContext.safety
        indexedVecFamilyCandidateContext.lctx
        indexedVecFamilyCandidateContext.lparams
        indexedVecFamilyCandidateContext.fuel
        (Ix.Theory.Named.TypeChecker.whnf indexedVecInfo.type) =
          .ok indexedVecInfo.type
      exact indexedVecFamily_whnfM)
    indexedVecParamDomainCandidateTrace indexedVecInnerCandidateTrace

def indexedVecFamilyCandidate :
    Ix.Theory.Named.AddInductive.CandidateExpr indexedVecInfo.type :=
  ⟨indexedVecFamilyCandidateContext, indexedVecFamilyCandidateTrace⟩

theorem indexedVecFamilyCandidate_view_eq :
    indexedVecFamilyCandidate.view = indexedVecInfo.type := by
  have habstract (context : Ix.Theory.Named.AddInductive.Context) (e : Expr) :
      e.abstract #[context.freshExpr] =
        Expr.abstract1 context.freshFVarId e := by
    rw [show #[context.freshExpr] =
      ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
    simp only [Expr.abstract_eq, Expr.abstractList]
  simp only [indexedVecFamilyCandidate,
    Ix.Theory.Named.AddInductive.CandidateExpr.view,
    indexedVecFamilyCandidateTrace,
    indexedVecInnerCandidateTrace, indexedVecParamDomainCandidateTrace,
    indexedVecIndexDomainCandidateTrace, indexedVecTerminalCandidateTrace,
    Ix.Theory.Named.AddInductive.CandidateExprTrace.view]
  rw [habstract, habstract]
  simp [Expr.abstract1, indexedVecTerminalKernel,
    indexedVecFamilyCandidateContext,
    Ix.Theory.Named.AddInductive.Context.pushLocalDecl,
    Ix.Theory.Named.AddInductive.Context.freshFVarId,
    NameGenerator.next, NameGenerator.curr,
    indexedVecInfo, ConstantInfo.type, ConstantInfo.toConstantVal]
  constructor <;> rfl

/-- Every retained family-type candidate node preserves its kernel source.
This is the structural premise used by the semantic spine interpreter; it is
stronger than the root `view` equality because it covers both Pi domains and
the instantiated body under their exact candidate contexts. -/
theorem indexedVecFamilyCandidate_identity :
    Ix.Theory.Named.TypeChecker.CandidateExprIdentity
      indexedVecFamilyCandidate.trace := by
  change Ix.Theory.Named.TypeChecker.CandidateExprIdentity
    indexedVecFamilyCandidateTrace
  unfold indexedVecFamilyCandidateTrace
  refine .forallE (name := indexedVecParamName) (binderInfo := .default)
    (body := indexedVecInnerKernel)
    (annotations := indexedVecParamAnnotations)
    indexedVecParamDomainCandidateTrace indexedVecInnerCandidateTrace
    ?_ rfl (.terminal rfl) ?_
  · rfl
  · unfold indexedVecInnerCandidateTrace
    refine .forallE (name := indexedVecIndexName) (binderInfo := .default)
      (body := indexedVecTerminalKernel)
      (annotations := indexedVecIndexAnnotations)
      indexedVecIndexDomainCandidateTrace indexedVecTerminalCandidateTrace
      ?_ rfl (.terminal rfl) ?_
    · simpa only [Expr.instantiate1_eq, indexedVecInnerKernel,
        indexedVecTerminalKernel] using
        indexedVecInnerKernel_instantiate1
          indexedVecFamilyCandidateContext.freshExpr
    · exact .terminal (by
        simpa only [Expr.instantiate1_eq] using
          (indexedVecTerminalKernel_instantiate1
            indexedVecParamCandidateContext.freshExpr).symm)

private theorem indexedVecParamDomainCandidateTrace_loop (fuel : Nat) :
    Ix.Theory.Named.AddInductive.buildCandidateExpr.loop
      indexedVecFamilyCandidateContext indexedVecTerminalKernel
      (fuel + 1) = .ok indexedVecParamDomainCandidateTrace := by
  simpa only [indexedVecParamDomainCandidateTrace] using
    Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      indexedVecFamilyCandidateContext indexedVecTerminalKernel
      (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel fuel
      indexedVecParamDomainCandidateTrace.rootCheck.valid
      indexedVecParamDomainCandidateTrace.rootWhnf_valid rfl

private theorem indexedVecIndexDomainCandidateTrace_loop (fuel : Nat) :
    Ix.Theory.Named.AddInductive.buildCandidateExpr.loop
      indexedVecParamCandidateContext (.const ``Nat []) (fuel + 1) =
        .ok indexedVecIndexDomainCandidateTrace := by
  simpa only [indexedVecIndexDomainCandidateTrace] using
    Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      indexedVecParamCandidateContext (.const ``Nat [])
      (.sort (.succ .zero)) (.const ``Nat []) fuel
      indexedVecIndexDomainCandidateTrace.rootCheck.valid
      indexedVecIndexDomainCandidateTrace.rootWhnf_valid rfl

private theorem indexedVecTerminalCandidateTrace_loop (fuel : Nat) :
    Ix.Theory.Named.AddInductive.buildCandidateExpr.loop
      indexedVecIndexCandidateContext
      (indexedVecTerminalKernel.instantiate1
        indexedVecParamCandidateContext.freshExpr)
      (fuel + 1) = .ok indexedVecTerminalCandidateTrace := by
  simpa only [indexedVecTerminalCandidateTrace] using
    Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      indexedVecIndexCandidateContext
      (indexedVecTerminalKernel.instantiate1
        indexedVecParamCandidateContext.freshExpr)
      (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel fuel
      indexedVecTerminalCandidateTrace.rootCheck.valid
      indexedVecTerminalCandidateTrace.rootWhnf_valid rfl

private theorem indexedVecInnerCandidateTrace_loop :
    Ix.Theory.Named.AddInductive.buildCandidateExpr.loop
      indexedVecParamCandidateContext
      (indexedVecInnerKernel.instantiate1
        indexedVecFamilyCandidateContext.freshExpr) 999 =
        .ok indexedVecInnerCandidateTrace := by
  rw [show 999 = 998 + 1 by rfl]
  simpa only [indexedVecInnerCandidateTrace,
    indexedVecIndexCandidateContext] using
    (Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := indexedVecParamCandidateContext)
      (e := indexedVecInnerKernel.instantiate1
        indexedVecFamilyCandidateContext.freshExpr)
      (inferred := .sort indexedVecInnerInferredLevel)
      (fuel := 998) (name := indexedVecIndexName)
      (domain := .const ``Nat []) (body := indexedVecTerminalKernel)
      (binderInfo := .default) (hfresh := indexedVecParamCandidateFresh)
      (annotations := indexedVecIndexAnnotations)
      (hannotations := indexedVecIndexAnnotations_build)
      (hannotationsEq := indexedVecIndexAnnotationsEq)
      (hcheck := indexedVecInnerCandidateTrace.rootCheck.valid)
      (hrun := indexedVecInnerCandidateTrace.rootWhnf_valid)
      (domainCandidate := indexedVecIndexDomainCandidateTrace)
      (bodyCandidate := indexedVecTerminalCandidateTrace)
      (hdomain := by
        simpa using indexedVecIndexDomainCandidateTrace_loop 997)
      (hbody := by
        simpa [indexedVecIndexCandidateContext,
          indexedVecIndexAnnotations] using
          indexedVecTerminalCandidateTrace_loop 997))

private theorem indexedVecFamilyCandidateTrace_loop :
    Ix.Theory.Named.AddInductive.buildCandidateExpr.loop
      indexedVecFamilyCandidateContext indexedVecInfo.type
      indexedVecFamilyCandidateContext.fuel.inductiveFuel =
        .ok indexedVecFamilyCandidateTrace := by
  change Ix.Theory.Named.AddInductive.buildCandidateExpr.loop
    indexedVecFamilyCandidateContext indexedVecInfo.type (999 + 1) = _
  simpa only [indexedVecFamilyCandidateTrace,
    indexedVecParamCandidateContext] using
    (Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := indexedVecFamilyCandidateContext)
      (e := indexedVecInfo.type)
      (inferred := .sort indexedVecFamilyInferredLevel)
      (fuel := 999) (name := indexedVecParamName)
      (domain := indexedVecTerminalKernel) (body := indexedVecInnerKernel)
      (binderInfo := .default) (hfresh := indexedVecFamilyCandidateFresh)
      (annotations := indexedVecParamAnnotations)
      (hannotations := indexedVecParamAnnotations_build)
      (hannotationsEq := indexedVecParamAnnotationsEq)
      (hcheck := indexedVecFamilyCandidateTrace.rootCheck.valid)
      (hrun := indexedVecFamilyCandidateTrace.rootWhnf_valid)
      (domainCandidate := indexedVecParamDomainCandidateTrace)
      (bodyCandidate := indexedVecInnerCandidateTrace)
      (hdomain := by
        simpa using indexedVecParamDomainCandidateTrace_loop 998)
      (hbody := by
        simpa [indexedVecParamCandidateContext,
          indexedVecParamAnnotations, indexedVecTerminalKernel] using
          indexedVecInnerCandidateTrace_loop))

/-- The executable candidate traversal preserves the real IndexedVec family
telescope and classifies its first binder as a parameter and its second as an
index in the subsequent family-validation pass. -/
theorem indexedVecFamily_candidateTrace :
    Ix.Theory.Named.AddInductive.buildCandidateExpr indexedVecInfo.type
      indexedVecFamilyCandidateContext = .ok indexedVecFamilyCandidate := by
  unfold Ix.Theory.Named.AddInductive.buildCandidateExpr
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [indexedVecFamilyCandidateTrace_loop]
  rfl

/-- The executable IndexedVec family candidate retains its parameter and
index binders in order. -/
theorem indexedVecFamilyCandidate_spineLength :
    indexedVecFamilyCandidate.trace.spineLength = 2 := by
  rfl

theorem indexedVecFamilyCandidate_validationAnnotations :
    indexedVecFamilyCandidate.trace.validationAnnotations := by
  exact ⟨indexedVecParamAnnotations_match,
    indexedVecIndexAnnotations_match, trivial⟩

theorem indexedVecFamilyCandidate_terminalResult :
    indexedVecFamilyCandidate.trace.terminalResult =
      .sort (.succ (.param `u)) := by
  rfl

def indexedVecKernelNil : Constructor where
  name := indexedVecNilInfo.name
  type := indexedVecNilInfo.type

def indexedVecKernelCons : Constructor where
  name := indexedVecConsInfo.name
  type := indexedVecConsInfo.type

def indexedVecKernelType : InductiveType where
  name := indexedVecInfo.name
  type := indexedVecInfo.type
  ctors := [indexedVecKernelNil, indexedVecKernelCons]

def indexedVecCandidateInductiveStats :
    Ix.Theory.Named.AddInductive.InductiveStats :=
  indexedVecFamilyCandidate.trace.singletonCandidateInductiveStats
    indexedVecKernelType 1 (.succ (.param `u))

private theorem indexedVecFamily_data_hasExprMVar_false :
    indexedVecInfo.type.data.hasExprMVar = false := by
  change indexedVecInfo.type.hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem indexedVecFamily_data_hasLevelMVar_false :
    indexedVecInfo.type.data.hasLevelMVar = false := by
  change indexedVecInfo.type.hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  simp [indexedVecInfo, ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.hasLevelMVar', Level.hasMVar_eq, Level.hasMVar']

private theorem indexedVecFamily_data_hasFVar_false :
    indexedVecInfo.type.data.hasFVar = false := by
  change indexedVecInfo.type.hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem indexedVecFamily_hasMVar_false :
    indexedVecInfo.type.hasMVar = false := by
  change (indexedVecInfo.type.data.hasExprMVar ||
    indexedVecInfo.type.data.hasLevelMVar) = false
  rw [indexedVecFamily_data_hasExprMVar_false,
    indexedVecFamily_data_hasLevelMVar_false]
  rfl

private theorem indexedVecFamily_hasFVar_false :
    indexedVecInfo.type.hasFVar = false := by
  exact indexedVecFamily_data_hasFVar_false

private theorem indexedVecFamily_closed :
    indexedVecFamilyCandidateContext.env.checkNoMVarNoFVar
      indexedVecKernelType.name indexedVecKernelType.type = .ok () := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show indexedVecKernelType.type.hasMVar = false by
    simpa [indexedVecKernelType] using indexedVecFamily_hasMVar_false]
  rw [show indexedVecKernelType.type.hasFVar = false by
    simpa [indexedVecKernelType] using indexedVecFamily_hasFVar_false]
  rfl

private theorem indexedVecTerminal_ensureSortM :
    Ix.Theory.Named.TypeChecker.M.run
      indexedVecFamilyCandidate.trace.terminalContext.env
      indexedVecFamilyCandidate.trace.terminalContext.safety
      indexedVecFamilyCandidate.trace.terminalContext.lctx
      indexedVecFamilyCandidate.trace.terminalContext.lparams
      indexedVecFamilyCandidate.trace.terminalContext.fuel
      (Ix.Theory.Named.TypeChecker.ensureSort
        (.sort (.succ (.param `u)))) =
      .ok (.sort (.succ (.param `u))) := by
  rfl

/-- The real IndexedVec family telescope drives the complete singleton
family-validation pass with one parameter and one index. -/
theorem indexedVec_checkInductiveTypes
    (k : Ix.Theory.Named.AddInductive.InductiveStats →
      Ix.Theory.Named.AddInductive.M α) :
    Ix.Theory.Named.AddInductive.checkInductiveTypes 1
        #[indexedVecKernelType] k indexedVecFamilyCandidateContext =
      k indexedVecCandidateInductiveStats
        indexedVecFamilyCandidate.trace.terminalContext := by
  change Ix.Theory.Named.AddInductive.checkInductiveTypes 1
      #[indexedVecKernelType] k indexedVecFamilyCandidate.context =
    k indexedVecCandidateInductiveStats
      indexedVecFamilyCandidate.trace.terminalContext
  exact
    Ix.Theory.Named.AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      (indType := indexedVecKernelType)
      (candidate := indexedVecFamilyCandidate.trace)
      (nparams := 1) (resultLevel := .succ (.param `u)) (k := k)
      indexedVecFamily_closed (by decide) (by decide)
      ⟨indexedVecParamAnnotations_match,
        indexedVecIndexAnnotations_match, trivial⟩
      rfl indexedVecTerminal_ensureSortM

theorem indexedVecCandidateInductiveStats_nindices :
    indexedVecCandidateInductiveStats.nindices = #[1] := by
  rfl

theorem indexedVecCandidateInductiveStats_params :
    indexedVecCandidateInductiveStats.params =
    #[indexedVecFamilyCandidateContext.freshExpr] := by
  rfl

theorem indexedVecCandidateInductiveStats_resultLevel :
    indexedVecCandidateInductiveStats.resultLevel =
    .succ (.param `u) := by
  rfl

theorem indexedVecCandidateInductiveStats_indConsts :
    indexedVecCandidateInductiveStats.indConsts =
    #[.const ``IndexedVec [.param `u]] := by
  rfl

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.candidateIsDefEqSelfValid [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Syntax.structEq_eq]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecFamily_candidateTrace [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVec_checkInductiveTypes [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
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

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecCandidateInductiveStats_nindices [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecCandidateInductiveStats_params [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

end Ix.Theory.Named.InductiveReplayFixtures
