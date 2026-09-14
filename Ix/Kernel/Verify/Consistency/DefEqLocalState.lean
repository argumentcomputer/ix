/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.WhnfLocalState

/-!
# Structural local-state preservation for production conversion

Every direct definitional-equality phase preserves the local declarations,
fresh-variable bound and installed loader on success and error. The binder
and let cases first extend the context with the actual guarded allocation,
then restore it through production scope cleanup. Finite spine and structure
eta workers use induction; recursive method calls use the predecessor table.
Cache and equivalence-manager operations preserve this structural state,
without asserting the semantic correctness of their entries or answers.
-/

namespace Ix.Kernel.Consistency

theorem openLetWithFV_eq (name : Mode.anon.F Name) (type value body : KExpr .anon)
    (before : TcState .anon) :
    TcM.openLetWithFV name type value body before =
      if before.env.nextFVarId.toNat + 1 < UInt64.size then
        let fresh : FVarId := ⟨before.env.nextFVarId⟩
        let internedLocal := before.env.intern.internExpr (KExpr.mkFVar fresh name)
        let opened := instantiateRev body #[internedLocal.1] internedLocal.2
        .ok (opened.1, internedLocal.1, fresh) {before with
          env := {before.env with
            nextFVarId := before.env.nextFVarId + 1
            intern := opened.2}
          lctx := before.lctx.push fresh (.ldecl name type value)}
      else .error (.other "free-variable id space exhausted") before := by
  unfold TcM.openLetWithFV
  change EStateM.bind TcM.freshFVarId _ before = _
  rw [EStateM.bind, TcM.freshFVarId]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · simp only [room, if_true]
    rfl
  · simp only [room, if_false]

theorem PreservesLocalState.openLetWithFV
    (name : Mode.anon.F Name) (type value body : KExpr .anon) :
    PreservesLocalState (TcM.openLetWithFV name type value body) := by
  intro before valid
  rw [openLetWithFV_eq]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · rw [if_pos room]
    have increment : (before.env.nextFVarId + 1).toNat = before.env.nextFVarId.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt room]
    exact ⟨⟨valid.coherent.push valid.allocated.fresh, valid.allocated.push _ room, valid.loader⟩,
      by change before.env.nextFVarId.toNat ≤ (before.env.nextFVarId + 1).toNat
         rw [increment]; omega, .push _ (.refl _) valid.allocated.fresh, rfl⟩
  · rw [if_neg room]; exact .refl valid

namespace FramesLocalState

attribute [local local_state_frame] FramesLocalState.ctxAddrForLbr

attribute [local irreducible] TcM.intern TcM.runIntern
  RecM.whnf RecM.whnfCore RecM.whnfNoDelta RecM.whnfCoreForDefEq
  RecM.whnfNoDeltaForDefEq RecM.strLitToConstructor

@[local_state_frame] theorem isDefEqCall {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (left right : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqCall left right).run methods) := recursive.isDefEq left right

@[local_state_frame] theorem inferOnlyCall {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.inferOnlyCall term).run methods) := withInferOnly (recursive.infer term)

@[local_state_frame] theorem defEqCtxKey (left right : KExpr .anon) :
    FramesLocalState (TcM.defEqCtxKey left right) := ctxAddrForLbr _

@[local_state_frame] theorem withEquiv (update : EquivManager → α × EquivManager) :
    FramesLocalState (TcM.withEquiv (m := .anon) update) := by
  unfold TcM.withEquiv
  apply bind
  · apply modifyGet
    exact fun _ => ⟨Nat.le_refl _, .refl _, rfl⟩
  · intro manager
    local_state

@[local_state_frame] theorem quickBinder {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (name : Mode.anon.F Name)
    (bi : Mode.anon.F Lean.BinderInfo) (type1 body1 type2 body2 : KExpr .anon) :
    FramesLocalState ((RecM.quickBinder name bi type1 body1 type2 body2).run methods) := by
  unfold RecM.quickBinder
  local_state
  apply PreservesLocalState.withLctxScope
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply PreservesLocalState.bind (PreservesLocalState.openBinder name bi type1 body1)
  rintro ⟨opened, fresh⟩
  apply FramesLocalState.preserves
  local_state

@[local_state_frame] theorem tryDefEqWhnfLet {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (name : Mode.anon.F Name)
    (type1 value1 body1 type2 value2 body2 : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfLet name type1 value1 body1 type2 value2 body2).run methods) := by
  unfold RecM.tryDefEqWhnfLet
  local_state
  apply PreservesLocalState.withLctxScope
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply PreservesLocalState.bind (PreservesLocalState.openLetWithFV name type1 value1 body1)
  rintro ⟨opened, fv, fresh⟩
  apply FramesLocalState.preserves
  local_state

@[local_state_frame] theorem allDefEqSpineArgsList {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (pairs : List (KExpr .anon × KExpr .anon)) :
    FramesLocalState ((RecM.allDefEqSpineArgsList pairs).run methods) := by
  induction pairs with
  | nil => exact pure _
  | cons pair pairs ih =>
      rcases pair with ⟨left, right⟩
      rw [RecM.allDefEqSpineArgsList]
      local_state

@[local_state_frame] theorem tryEtaStructFields {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ind : KId .anon) (params : Nat)
    (term : KExpr .anon) (args : Array (KExpr .anon)) (fuel field : Nat) :
    FramesLocalState ((RecM.tryEtaStructFields ind params term args fuel field).run methods) := by
  induction fuel generalizing field with
  | zero => exact pure _
  | succ fuel ih =>
      rw [RecM.tryEtaStructFields]
      local_state

@[local_state_frame] theorem etaExpansionBaseLoop {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ind : KId .anon) (params : Nat)
    (args : Array (KExpr .anon)) (fuel field : Nat) (base : Option (KExpr .anon)) :
    FramesLocalState ((RecM.etaExpansionBaseLoop ind params args fuel field base).run methods) := by
  induction fuel generalizing field base with
  | zero =>
      rw [RecM.etaExpansionBaseLoop]
      exact pure _
  | succ fuel ih =>
      rw [RecM.etaExpansionBaseLoop]
      simp only [RecM.etaExpansionBaseAfterProjection]
      local_state
      all_goals unfold RecM.etaExpansionBaseAfterValue
      all_goals local_state


@[local_state_frame] theorem isNatLike {methods : Methods .anon}
    (e : KExpr .anon) :
    FramesLocalState ((RecM.isNatLike e).run methods) := by
  unfold RecM.isNatLike
  local_state

attribute [local irreducible] RecM.isNatLike

@[local_state_frame] theorem isNatZero {methods : Methods .anon}
    (e : KExpr .anon) :
    FramesLocalState ((RecM.isNatZero e).run methods) := by
  unfold RecM.isNatZero
  local_state

attribute [local irreducible] RecM.isNatZero

@[local_state_frame] theorem natSuccOf {methods : Methods .anon}
    (e : KExpr .anon) :
    FramesLocalState ((RecM.natSuccOf e).run methods) := by
  unfold RecM.natSuccOf
  local_state

attribute [local irreducible] RecM.natSuccOf

@[local_state_frame] theorem isBoolTrue {methods : Methods .anon}
    (e : KExpr .anon) :
    FramesLocalState ((RecM.isBoolTrue e).run methods) := by
  unfold RecM.isBoolTrue
  local_state

attribute [local irreducible] RecM.isBoolTrue

@[local_state_frame] theorem boolTrueReductionAllowed {methods : Methods .anon}
    (e : KExpr .anon) :
    FramesLocalState ((RecM.boolTrueReductionAllowed e).run methods) := by
  unfold RecM.boolTrueReductionAllowed
  local_state

attribute [local irreducible] RecM.boolTrueReductionAllowed

@[local_state_frame] theorem whnfIsBoolTrue {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (e : KExpr .anon) :
    FramesLocalState ((RecM.whnfIsBoolTrue e).run methods) := by
  unfold RecM.whnfIsBoolTrue
  local_state

attribute [local irreducible] RecM.whnfIsBoolTrue

@[local_state_frame] theorem isDelta {methods : Methods .anon}
    (id : KId .anon) :
    FramesLocalState ((RecM.isDelta id).run methods) := by
  unfold RecM.isDelta
  local_state

attribute [local irreducible] RecM.isDelta

@[local_state_frame] theorem classifyDeltaHead {methods : Methods .anon}
    (e : KExpr .anon) :
    FramesLocalState ((RecM.classifyDeltaHead e).run methods) := by
  unfold RecM.classifyDeltaHead
  local_state

attribute [local irreducible] RecM.classifyDeltaHead

@[local_state_frame] theorem isRegular {methods : Methods .anon}
    (id : KId .anon) :
    FramesLocalState ((RecM.isRegular id).run methods) := by
  unfold RecM.isRegular
  local_state

attribute [local irreducible] RecM.isRegular

@[local_state_frame] theorem defRankId {methods : Methods .anon}
    (id : KId .anon) :
    FramesLocalState ((RecM.defRankId id).run methods) := by
  unfold RecM.defRankId
  local_state

attribute [local irreducible] RecM.defRankId

@[local_state_frame] theorem rankDeltaHead {methods : Methods .anon}
    (head : Option (KId .anon)) :
    FramesLocalState ((RecM.rankDeltaHead head).run methods) := by
  unfold RecM.rankDeltaHead
  local_state

attribute [local irreducible] RecM.rankDeltaHead

@[local_state_frame] theorem quickDefEq {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.quickDefEq a b).run methods) := by
  unfold RecM.quickDefEq
  local_state

attribute [local irreducible] RecM.quickDefEq

@[local_state_frame] theorem finishDefEqLazyDeltaStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.finishDefEqLazyDeltaStep wa wb).run methods) := by
  unfold RecM.finishDefEqLazyDeltaStep
  local_state

attribute [local irreducible] RecM.finishDefEqLazyDeltaStep

@[local_state_frame] theorem defEqLazyDeltaStepAfterSameHeadMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa0 wb0 : KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStepAfterSameHeadMiss wa0 wb0).run methods) := by
  unfold RecM.defEqLazyDeltaStepAfterSameHeadMiss
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepAfterSameHeadMiss

@[local_state_frame] theorem defEqLazyDeltaStepWithLeftDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStepWithLeftDelta wa wb).run methods) := by
  unfold RecM.defEqLazyDeltaStepWithLeftDelta
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepWithLeftDelta

@[local_state_frame] theorem defEqLazyDeltaStepWithRightDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStepWithRightDelta wa wb).run methods) := by
  unfold RecM.defEqLazyDeltaStepWithRightDelta
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepWithRightDelta

@[local_state_frame] theorem allDefEqSpineArgs {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (pairs : Array (KExpr .anon × KExpr .anon)) :
    FramesLocalState ((RecM.allDefEqSpineArgs pairs).run methods) := by
  unfold RecM.allDefEqSpineArgs
  local_state

attribute [local irreducible] RecM.allDefEqSpineArgs

@[local_state_frame] theorem trySameHeadSpine {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.trySameHeadSpine a b).run methods) := by
  unfold RecM.trySameHeadSpine
  local_state

attribute [local irreducible] RecM.trySameHeadSpine

@[local_state_frame] theorem trySameHeadSpineSpeculative {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.trySameHeadSpineSpeculative a b).run methods) := by
  unfold RecM.trySameHeadSpineSpeculative
  local_state

attribute [local irreducible] RecM.trySameHeadSpineSpeculative

@[local_state_frame] theorem trySameHeadSpineCached {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (speculative : Bool) (left right : KExpr .anon) :
    FramesLocalState ((RecM.trySameHeadSpineCached speculative left right).run methods) := by
  unfold RecM.trySameHeadSpineCached
  local_state

attribute [local irreducible] RecM.trySameHeadSpineCached

@[local_state_frame] theorem defEqLazyDeltaStepWithEqualRank {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa0 wb0 : KExpr .anon)
    (aHead bHead : Option (KId .anon)) :
    FramesLocalState ((RecM.defEqLazyDeltaStepWithEqualRank wa0 wb0 aHead bHead).run methods) := by
  unfold RecM.defEqLazyDeltaStepWithEqualRank
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepWithEqualRank

@[local_state_frame] theorem defEqLazyDeltaStepAfterProjectionMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa0 wb0 : KExpr .anon)
    (aHead bHead : Option (KId .anon)) (aDelta bDelta : Bool) :
    FramesLocalState ((RecM.defEqLazyDeltaStepAfterProjectionMiss wa0 wb0 aHead bHead aDelta bDelta).run methods) := by
  unfold RecM.defEqLazyDeltaStepAfterProjectionMiss
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepAfterProjectionMiss

@[local_state_frame] theorem tryDefEqWhnfApp {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (f1 a1 f2 a2 : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfApp f1 a1 f2 a2).run methods) := by
  unfold RecM.tryDefEqWhnfApp
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfApp

@[local_state_frame] theorem tryDefEqWhnfStructural {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfStructural a b).run methods) := by
  unfold RecM.tryDefEqWhnfStructural
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfStructural

@[local_state_frame] theorem classifyPropTypeUncached {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ty : KExpr .anon) :
    FramesLocalState ((RecM.classifyPropTypeUncached ty).run methods) := by
  unfold RecM.classifyPropTypeUncached
  local_state

attribute [local irreducible] RecM.classifyPropTypeUncached

@[local_state_frame] theorem isPropType {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ty : KExpr .anon) :
    FramesLocalState ((RecM.isPropType ty).run methods) := by
  unfold RecM.isPropType
  local_state

attribute [local irreducible] RecM.isPropType

@[local_state_frame] theorem tryProofIrrel {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryProofIrrel a b).run methods) := by
  unfold RecM.tryProofIrrel
  local_state

attribute [local irreducible] RecM.tryProofIrrel

@[local_state_frame] theorem isDefEqWhnfAfterUnit {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnfAfterUnit a b).run methods) := by
  unfold RecM.isDefEqWhnfAfterUnit
  local_state

attribute [local irreducible] RecM.isDefEqWhnfAfterUnit

@[local_state_frame] theorem isUnitLikeInductive {methods : Methods .anon}
    (indId : KId .anon) :
    FramesLocalState ((RecM.isUnitLikeInductive indId).run methods) := by
  unfold RecM.isUnitLikeInductive
  local_state

attribute [local irreducible] RecM.isUnitLikeInductive

@[local_state_frame] theorem tryDefEqUnit {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqUnit a b).run methods) := by
  unfold RecM.tryDefEqUnit
  local_state

attribute [local irreducible] RecM.tryDefEqUnit

@[local_state_frame] theorem isDefEqWhnfAfterStructEta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnfAfterStructEta a b).run methods) := by
  unfold RecM.isDefEqWhnfAfterStructEta
  local_state

attribute [local irreducible] RecM.isDefEqWhnfAfterStructEta

@[local_state_frame] theorem isDefEqNatAfterLiteral {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqNatAfterLiteral a b).run methods) := by
  unfold RecM.isDefEqNatAfterLiteral
  local_state

attribute [local irreducible] RecM.isDefEqNatAfterLiteral

@[local_state_frame] theorem isDefEqNat {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqNat a b).run methods) := by
  unfold RecM.isDefEqNat
  local_state

attribute [local irreducible] RecM.isDefEqNat

@[local_state_frame] theorem tryDefEqWhnfNat {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfNat a b).run methods) := by
  unfold RecM.tryDefEqWhnfNat
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfNat

@[local_state_frame] theorem tryDefEqOffsetAfterCandidates {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqOffsetAfterCandidates a b).run methods) := by
  unfold RecM.tryDefEqOffsetAfterCandidates
  local_state

attribute [local irreducible] RecM.tryDefEqOffsetAfterCandidates

@[local_state_frame] theorem tryDefEqOffsetAfterZeroMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqOffsetAfterZeroMiss a b).run methods) := by
  unfold RecM.tryDefEqOffsetAfterZeroMiss
  local_state

attribute [local irreducible] RecM.tryDefEqOffsetAfterZeroMiss

@[local_state_frame] theorem tryDefEqOffsetAfterLiteral {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqOffsetAfterLiteral a b).run methods) := by
  unfold RecM.tryDefEqOffsetAfterLiteral
  local_state

attribute [local irreducible] RecM.tryDefEqOffsetAfterLiteral

@[local_state_frame] theorem tryDefEqOffset {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqOffset a b).run methods) := by
  unfold RecM.tryDefEqOffset
  local_state

attribute [local irreducible] RecM.tryDefEqOffset

@[local_state_frame] theorem tryStringLitExpansion {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (t s : KExpr .anon) :
    FramesLocalState ((RecM.tryStringLitExpansion t s).run methods) := by
  unfold RecM.tryStringLitExpansion
  local_state

attribute [local irreducible] RecM.tryStringLitExpansion

@[local_state_frame] theorem tryDefEqWhnfStringAfterGuard {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfStringAfterGuard a b).run methods) := by
  unfold RecM.tryDefEqWhnfStringAfterGuard
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfStringAfterGuard

@[local_state_frame] theorem tryDefEqWhnfString {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfString a b).run methods) := by
  unfold RecM.tryDefEqWhnfString
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfString

@[local_state_frame] theorem compareEtaExpansion {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (t s : KExpr .anon) (name : Mode.anon.F Name)
    (bi : Mode.anon.F Lean.BinderInfo) (ty : KExpr .anon) :
    FramesLocalState ((RecM.compareEtaExpansion t s name bi ty).run methods) := by
  unfold RecM.compareEtaExpansion
  local_state

attribute [local irreducible] RecM.compareEtaExpansion

@[local_state_frame] theorem tryEtaExpansionAfterGuard {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (t s : KExpr .anon) :
    FramesLocalState ((RecM.tryEtaExpansionAfterGuard t s).run methods) := by
  unfold RecM.tryEtaExpansionAfterGuard
  local_state

attribute [local irreducible] RecM.tryEtaExpansionAfterGuard

@[local_state_frame] theorem tryEtaExpansion {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (t s : KExpr .anon) :
    FramesLocalState ((RecM.tryEtaExpansion t s).run methods) := by
  unfold RecM.tryEtaExpansion
  local_state

attribute [local irreducible] RecM.tryEtaExpansion

@[local_state_frame] theorem tryDefEqWhnfEtaAfterGuard {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfEtaAfterGuard a b).run methods) := by
  unfold RecM.tryDefEqWhnfEtaAfterGuard
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfEtaAfterGuard

@[local_state_frame] theorem tryDefEqWhnfEta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfEta a b).run methods) := by
  unfold RecM.tryDefEqWhnfEta
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfEta

@[local_state_frame] theorem normalizeEtaStructSource {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (t : KExpr .anon) :
    FramesLocalState ((RecM.normalizeEtaStructSource t).run methods) := by
  unfold RecM.normalizeEtaStructSource
  local_state

attribute [local irreducible] RecM.normalizeEtaStructSource

@[local_state_frame] theorem etaExpansionBase {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (inductId : KId .anon) (numParams numFields : Nat)
    (args : Array (KExpr .anon)) :
    FramesLocalState ((RecM.etaExpansionBase inductId numParams numFields args).run methods) := by
  unfold RecM.etaExpansionBase
  local_state

attribute [local irreducible] RecM.etaExpansionBase

@[local_state_frame] theorem tryEtaStructAfterTypes {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (inductId : KId .anon) (numParams numFields : Nat)
    (tNorm : KExpr .anon) (sArgs : Array (KExpr .anon)) :
    FramesLocalState ((RecM.tryEtaStructAfterTypes inductId numParams numFields tNorm sArgs).run methods) := by
  unfold RecM.tryEtaStructAfterTypes
  local_state

attribute [local irreducible] RecM.tryEtaStructAfterTypes

@[local_state_frame] theorem tryEtaStructAfterConstructor {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (inductId : KId .anon)
    (numParams numFields : Nat) (tNorm s : KExpr .anon)
    (sArgs : Array (KExpr .anon)) :
    FramesLocalState ((RecM.tryEtaStructAfterConstructor inductId numParams numFields tNorm s sArgs).run methods) := by
  unfold RecM.tryEtaStructAfterConstructor
  local_state

attribute [local irreducible] RecM.tryEtaStructAfterConstructor

@[local_state_frame] theorem tryEtaStructAfterNormalization {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (tNorm s : KExpr .anon) :
    FramesLocalState ((RecM.tryEtaStructAfterNormalization tNorm s).run methods) := by
  unfold RecM.tryEtaStructAfterNormalization
  local_state

attribute [local irreducible] RecM.tryEtaStructAfterNormalization

@[local_state_frame] theorem tryEtaStruct {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (t s : KExpr .anon) :
    FramesLocalState ((RecM.tryEtaStruct t s).run methods) := by
  unfold RecM.tryEtaStruct
  local_state

attribute [local irreducible] RecM.tryEtaStruct

@[local_state_frame] theorem tryDefEqWhnfStructEta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqWhnfStructEta a b).run methods) := by
  unfold RecM.tryDefEqWhnfStructEta
  local_state

attribute [local irreducible] RecM.tryDefEqWhnfStructEta

@[local_state_frame] theorem isDefEqWhnfAfterString {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnfAfterString a b).run methods) := by
  unfold RecM.isDefEqWhnfAfterString
  local_state

attribute [local irreducible] RecM.isDefEqWhnfAfterString

@[local_state_frame] theorem isDefEqWhnfAfterEta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnfAfterEta a b).run methods) := by
  unfold RecM.isDefEqWhnfAfterEta
  local_state

attribute [local irreducible] RecM.isDefEqWhnfAfterEta

@[local_state_frame] theorem isDefEqWhnfAfterNat {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnfAfterNat a b).run methods) := by
  unfold RecM.isDefEqWhnfAfterNat
  local_state

attribute [local irreducible] RecM.isDefEqWhnfAfterNat

@[local_state_frame] theorem isDefEqWhnfAfterStructural {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnfAfterStructural a b).run methods) := by
  unfold RecM.isDefEqWhnfAfterStructural
  local_state

attribute [local irreducible] RecM.isDefEqWhnfAfterStructural

@[local_state_frame] theorem isDefEqWhnf {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqWhnf a b).run methods) := by
  unfold RecM.isDefEqWhnf
  local_state

attribute [local irreducible] RecM.isDefEqWhnf

@[local_state_frame] theorem etaExpansionBaseAfterValue {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (inductId : KId .anon) (numParams : Nat)
    (args : Array (KExpr .anon)) (fuel fieldIdx : Nat)
    (base : Option (KExpr .anon)) (value : KExpr .anon) :
    FramesLocalState ((RecM.etaExpansionBaseAfterValue inductId numParams args fuel fieldIdx base value).run methods) := by
  unfold RecM.etaExpansionBaseAfterValue
  local_state


@[local_state_frame] theorem etaExpansionBaseAfterProjection {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (inductId : KId .anon) (numParams : Nat)
    (args : Array (KExpr .anon)) (fuel fieldIdx : Nat)
    (base : Option (KExpr .anon)) (value : KExpr .anon) :
    FramesLocalState ((RecM.etaExpansionBaseAfterProjection inductId numParams args fuel fieldIdx base value).run methods) := by
  unfold RecM.etaExpansionBaseAfterProjection
  local_state


@[local_state_frame] theorem tryDefEqApp {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryDefEqApp a b).run methods) := by
  unfold RecM.tryDefEqApp
  local_state

attribute [local irreducible] RecM.tryDefEqApp

@[local_state_frame] theorem finishLazyDeltaReductionStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.finishLazyDeltaReductionStep a b).run methods) := by
  unfold RecM.finishLazyDeltaReductionStep
  local_state

attribute [local irreducible] RecM.finishLazyDeltaReductionStep

@[local_state_frame] theorem lazyDeltaReductionStepWithLeftDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.lazyDeltaReductionStepWithLeftDelta a b).run methods) := by
  unfold RecM.lazyDeltaReductionStepWithLeftDelta
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepWithLeftDelta

@[local_state_frame] theorem lazyDeltaReductionStepWithRightDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.lazyDeltaReductionStepWithRightDelta a b).run methods) := by
  unfold RecM.lazyDeltaReductionStepWithRightDelta
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepWithRightDelta

@[local_state_frame] theorem lazyDeltaReductionStepAfterSameHeadMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a0 b0 : KExpr .anon) :
    FramesLocalState ((RecM.lazyDeltaReductionStepAfterSameHeadMiss a0 b0).run methods) := by
  unfold RecM.lazyDeltaReductionStepAfterSameHeadMiss
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepAfterSameHeadMiss

@[local_state_frame] theorem lazyDeltaReductionStepWithEqualRank {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a0 b0 : KExpr .anon)
    (aId bId : KId .anon) :
    FramesLocalState ((RecM.lazyDeltaReductionStepWithEqualRank a0 b0 aId bId).run methods) := by
  unfold RecM.lazyDeltaReductionStepWithEqualRank
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepWithEqualRank

@[local_state_frame] theorem lazyDeltaReductionStepWithBothDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon)
    (aHead bHead : Option (KId .anon)) :
    FramesLocalState ((RecM.lazyDeltaReductionStepWithBothDelta a b aHead bHead).run methods) := by
  unfold RecM.lazyDeltaReductionStepWithBothDelta
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepWithBothDelta

@[local_state_frame] theorem tryUnfoldProjApp {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (e : KExpr .anon) :
    FramesLocalState ((RecM.tryUnfoldProjApp e).run methods) := by
  unfold RecM.tryUnfoldProjApp
  local_state

attribute [local irreducible] RecM.tryUnfoldProjApp

@[local_state_frame] theorem defEqLazyDeltaStepAfterDeltaClassification {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa0 wb0 : KExpr .anon)
    (aHead bHead : Option (KId .anon)) (aDelta bDelta : Bool) :
    FramesLocalState ((RecM.defEqLazyDeltaStepAfterDeltaClassification wa0 wb0 aHead bHead aDelta bDelta).run methods) := by
  unfold RecM.defEqLazyDeltaStepAfterDeltaClassification
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepAfterDeltaClassification

@[local_state_frame] theorem defEqLazyDeltaStepAfterAcceleratorMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa0 wb0 : KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStepAfterAcceleratorMiss wa0 wb0).run methods) := by
  unfold RecM.defEqLazyDeltaStepAfterAcceleratorMiss
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepAfterAcceleratorMiss

@[local_state_frame] theorem defEqLazyDeltaStepAfterNatMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa0 wb0 : KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStepAfterNatMiss wa0 wb0).run methods) := by
  unfold RecM.defEqLazyDeltaStepAfterNatMiss
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepAfterNatMiss

@[local_state_frame] theorem defEqLazyDeltaStepAfterOffsetMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (state : KExpr .anon × KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStepAfterOffsetMiss state).run methods) := by
  unfold RecM.defEqLazyDeltaStepAfterOffsetMiss
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStepAfterOffsetMiss

@[local_state_frame] theorem defEqLazyDeltaStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (state : KExpr .anon × KExpr .anon) :
    FramesLocalState ((RecM.defEqLazyDeltaStep state).run methods) := by
  unfold RecM.defEqLazyDeltaStep
  local_state

attribute [local irreducible] RecM.defEqLazyDeltaStep

@[local_state_frame] theorem runDefEqLazyDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.runDefEqLazyDelta wa wb).run methods) := by
  unfold RecM.runDefEqLazyDelta
  local_state

attribute [local irreducible] RecM.runDefEqLazyDelta

@[local_state_frame] theorem lazyDeltaReductionStepAfterActive {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a0 b0 : KExpr .anon)
    (aHead bHead : Option (KId .anon)) (aDelta bDelta : Bool) :
    FramesLocalState ((RecM.lazyDeltaReductionStepAfterActive a0 b0 aHead bHead aDelta bDelta).run methods) := by
  unfold RecM.lazyDeltaReductionStepAfterActive
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepAfterActive

@[local_state_frame] theorem lazyDeltaReductionStepAfterClassification {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a0 b0 : KExpr .anon)
    (aHead bHead : Option (KId .anon)) (aDelta bDelta : Bool) :
    FramesLocalState ((RecM.lazyDeltaReductionStepAfterClassification a0 b0 aHead bHead aDelta bDelta).run methods) := by
  unfold RecM.lazyDeltaReductionStepAfterClassification
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStepAfterClassification

@[local_state_frame] theorem lazyDeltaReductionStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a0 b0 : KExpr .anon) :
    FramesLocalState ((RecM.lazyDeltaReductionStep a0 b0).run methods) := by
  unfold RecM.lazyDeltaReductionStep
  local_state

attribute [local irreducible] RecM.lazyDeltaReductionStep

@[local_state_frame] theorem lazyDeltaProjReduction {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (structId : KId .anon) (field : UInt64)
    (a0 b0 : KExpr .anon) :
    FramesLocalState ((RecM.lazyDeltaProjReduction structId field a0 b0).run methods) := by
  unfold RecM.lazyDeltaProjReduction
  local_state

attribute [local irreducible] RecM.lazyDeltaProjReduction

@[local_state_frame] theorem tryStructuralCongruence {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.tryStructuralCongruence a b).run methods) := by
  unfold RecM.tryStructuralCongruence
  local_state

attribute [local irreducible] RecM.tryStructuralCongruence

@[local_state_frame] theorem isDefEqAfterLazyDeltaStopped {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqAfterLazyDeltaStopped wa wb).run methods) := by
  unfold RecM.isDefEqAfterLazyDeltaStopped
  local_state

attribute [local irreducible] RecM.isDefEqAfterLazyDeltaStopped

@[local_state_frame] theorem isDefEqInnerAfterProofIrrelevance {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterProofIrrelevance wa wb).run methods) := by
  unfold RecM.isDefEqInnerAfterProofIrrelevance
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterProofIrrelevance

@[local_state_frame] theorem isDefEqInnerAfterNoDeltaPass {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (wa wb : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterNoDeltaPass wa wb).run methods) := by
  unfold RecM.isDefEqInnerAfterNoDeltaPass
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterNoDeltaPass

@[local_state_frame] theorem isDefEqInnerAfterCorePass {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterCorePass a b).run methods) := by
  unfold RecM.isDefEqInnerAfterCorePass
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterCorePass

@[local_state_frame] theorem isDefEqInnerAfterStringExpansion {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterStringExpansion a b).run methods) := by
  unfold RecM.isDefEqInnerAfterStringExpansion
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterStringExpansion

@[local_state_frame] theorem isDefEqInnerAfterBoolTrue {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterBoolTrue a b).run methods) := by
  unfold RecM.isDefEqInnerAfterBoolTrue
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterBoolTrue

@[local_state_frame] theorem isDefEqInnerAfterFirstBoolGuardMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterFirstBoolGuardMiss a b).run methods) := by
  unfold RecM.isDefEqInnerAfterFirstBoolGuardMiss
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterFirstBoolGuardMiss

@[local_state_frame] theorem isDefEqInnerAfterQuick {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInnerAfterQuick a b).run methods) := by
  unfold RecM.isDefEqInnerAfterQuick
  local_state

attribute [local irreducible] RecM.isDefEqInnerAfterQuick

@[local_state_frame] theorem isDefEqInner {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEqInner a b).run methods) := by
  unfold RecM.isDefEqInner
  local_state

attribute [local irreducible] RecM.isDefEqInner

@[local_state_frame] theorem isDefEqAfterRootCacheMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) (aKey bKey : EqKey)
    (cacheKey : Address × Address × Address) (cheapMode : Bool) :
    FramesLocalState ((RecM.isDefEqAfterRootCacheMiss a b aKey bKey cacheKey cheapMode).run methods) := by
  unfold RecM.isDefEqAfterRootCacheMiss
  local_state

attribute [local irreducible] RecM.isDefEqAfterRootCacheMiss

@[local_state_frame] theorem isDefEqAfterDirectCacheMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) (eqCtx : Address)
    (aKey bKey : EqKey) (cacheKey : Address × Address × Address)
    (cheapMode : Bool) :
    FramesLocalState ((RecM.isDefEqAfterDirectCacheMiss a b eqCtx aKey bKey cacheKey cheapMode).run methods) := by
  unfold RecM.isDefEqAfterDirectCacheMiss
  local_state

attribute [local irreducible] RecM.isDefEqAfterDirectCacheMiss

@[local_state_frame] theorem isDefEq {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (a b : KExpr .anon) :
    FramesLocalState ((RecM.isDefEq a b).run methods) := by
  unfold RecM.isDefEq
  local_state

attribute [local irreducible] RecM.isDefEq

end FramesLocalState
end Ix.Kernel.Consistency
