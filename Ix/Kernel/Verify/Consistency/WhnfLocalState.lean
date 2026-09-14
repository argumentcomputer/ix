/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalStateTactic

/-!
# Structural local-state preservation for production reduction

The actual full, structural and no-delta WHNF drivers preserve the caller's
local declarations and installed loader and never decrease the fresh-variable
counter, on success and error. The proofs cover primitive reduction, String
expansion, projection, iota, recursor classification, caches, finite workers,
and cleanup. Only calls through the recursive method table require a frame
premise; every direct reduction helper is discharged here.

This is the structural state component of consistency. It does not assert
the semantic validity of a cached expression, reduction, or loaded declaration.
-/

namespace Ix.Kernel.Consistency

namespace FramesLocalState

-- Apply the proved intern effects without expanding the intern implementation
-- while elaborating a long sequence of requests.
attribute [local irreducible] TcM.intern TcM.runIntern

@[local_state_frame] theorem mkNatSucc {methods : Methods .anon}
    (pred : KExpr .anon) :
    FramesLocalState ((RecM.mkNatSucc pred).run methods) := by
  unfold RecM.mkNatSucc
  local_state

@[local_state_frame] theorem mkNatAdd {methods : Methods .anon}
    (left right : KExpr .anon) :
    FramesLocalState ((RecM.mkNatAdd left right).run methods) := by
  unfold RecM.mkNatAdd
  local_state

@[local_state_frame] theorem isNatBinArithAddr {methods : Methods .anon}
    (addr : Address) :
    FramesLocalState ((RecM.isNatBinArithAddr addr).run methods) := by
  unfold RecM.isNatBinArithAddr
  local_state

@[local_state_frame] theorem isNatBinPredAddr {methods : Methods .anon}
    (addr : Address) :
    FramesLocalState ((RecM.isNatBinPredAddr addr).run methods) := by
  unfold RecM.isNatBinPredAddr
  local_state

@[local_state_frame] theorem boolLitValue {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.boolLitValue term).run methods) := by
  unfold RecM.boolLitValue
  local_state

@[local_state_frame] theorem isNatStuckRecursorAddr {methods : Methods .anon}
    (addr : Address) :
    FramesLocalState ((RecM.isNatStuckRecursorAddr addr).run methods) := by
  unfold RecM.isNatStuckRecursorAddr
  local_state


@[local_state_frame] theorem unfoldConstValue {methods : Methods .anon} (head value : KExpr .anon)
    (levels : Array (KUniv .anon)) :
    FramesLocalState ((RecM.unfoldConstValue head value levels).run methods) := by
  unfold RecM.unfoldConstValue
  local_state

@[local_state_frame] theorem natToConstructor {methods : Methods .anon} (value : Nat) :
    FramesLocalState ((RecM.natToConstructor (m := .anon) value).run methods) := by
  unfold RecM.natToConstructor
  local_state

@[local_state_frame] theorem tryDeltaUnfold {methods : Methods .anon} (term : KExpr .anon) :
    FramesLocalState ((RecM.tryDeltaUnfold term).run methods) := by
  unfold RecM.tryDeltaUnfold
  local_state

@[local_state_frame] theorem pushLocal (type : KExpr .anon) : FramesLocalState (TcM.pushLocal type) :=
  fun _ _ => ⟨Nat.le_refl _, .refl _, rfl⟩

@[local_state_frame] theorem pushLet (type value : KExpr .anon) : FramesLocalState (TcM.pushLet type value) :=
  fun _ _ => ⟨Nat.le_refl _, .refl _, rfl⟩

@[local_state_frame] theorem popLocal : FramesLocalState (TcM.popLocal (m := .anon)) :=
  fun _ _ => ⟨Nat.le_refl _, .refl _, rfl⟩

@[local_state_frame] theorem saveDepth : FramesLocalState (TcM.saveDepth (m := .anon)) :=
  fun _ _ => .refl _

@[local_state_frame] theorem enterDispatch : FramesLocalState (RecM.enterDispatch (m := .anon)) := by
  apply ofWF
  intro before
  unfold RecM.enterDispatch
  apply TcM.WF.bind
    (Q₁ := fun observed after => observed = before ∧ after = before)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro observed after ⟨rfl, rfl⟩
  dsimp only
  split
  · exact TcM.WF.throw (fun _ => trivial)
  · exact TcM.WF.set (fun valid =>
      ⟨⟨valid.1.coherent, valid.1.allocated, valid.1.loader⟩,
        ⟨valid.2.counter, valid.2.context, valid.2.loader⟩⟩) (fun _ => trivial)

@[local_state_frame] theorem exitDispatch : FramesLocalState (RecM.exitDispatch (m := .anon)) :=
  fun _ _ => ⟨Nat.le_refl _, .refl _, rfl⟩

@[local_state_frame] theorem callIsDefEq {methods : Methods .anon} (recursive : MethodsLocalState methods)
    (left right : KExpr .anon) :
    FramesLocalState ((RecM.callIsDefEq left right).run methods) := by
  unfold RecM.callIsDefEq
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply bind enterDispatch
  intro _
  change FramesLocalState (_root_.tryFinally (methods.isDefEq left right) (RecM.exitDispatch (m := .anon)))
  exact tryFinally (recursive.isDefEq left right) exitDispatch

@[local_state_frame] theorem evalNatOffsetLiteralFuel {methods : Methods .anon} (fuel : Nat) (term : KExpr .anon) :
    FramesLocalState ((RecM.evalNatOffsetLiteralFuel fuel term).run methods) := by
  induction fuel generalizing term with
  | zero => exact pure _
  | succ fuel ih =>
      rw [RecM.evalNatOffsetLiteralFuel]
      local_state

@[local_state_frame] theorem natOffsetFuel {methods : Methods .anon} (fuel : Nat) (term : KExpr .anon) :
    FramesLocalState ((RecM.natOffsetFuel fuel term).run methods) := by
  induction fuel generalizing term with
  | zero => exact pure _
  | succ fuel ih =>
      have literal := evalNatOffsetLiteralFuel (methods := methods) fuel
      rw [RecM.natOffsetFuel]
      rcases spine : term.collectSpine with ⟨head, args⟩
      dsimp only
      cases head <;> dsimp only
      all_goals try exact pure _
      simp only [ReaderT.run_bind]
      apply bind (prims methods)
      intro primitives
      split
      · exact bind (ih _) (fun _ => pure _)
      · split
        · apply bind (literal _)
          intro result
          cases result with
          | none => exact pure _
          | some value => exact bind (ih _) (fun _ => pure _)
        · exact pure _

@[local_state_frame] theorem finishAppResult {methods : Methods .anon} (term : KExpr .anon)
    (args : Array (KExpr .anon)) (consumed : Nat) :
    FramesLocalState ((RecM.finishAppResult term args consumed).run methods) := by
  unfold RecM.finishAppResult
  local_state

@[local_state_frame] theorem tryReduceNativeMarker {methods : Methods .anon} (recursive : MethodsLocalState methods)
    (primitives : Primitives .anon) (isBool : Bool) (id : KId .anon) (levels : Array (KUniv .anon)) :
    FramesLocalState ((RecM.tryReduceNativeMarker primitives isBool id levels).run methods) := by
  unfold RecM.tryReduceNativeMarker
  local_state


@[local_state_frame] theorem strLitListToConstructor {methods : Methods .anon}
    (charOfNat cons : KExpr .anon) (chars : List Char) (tail : KExpr .anon) :
    FramesLocalState ((RecM.strLitListToConstructor charOfNat cons chars tail).run methods) := by
  induction chars generalizing tail with
  | nil => exact pure _
  | cons char chars ih =>
      rw [RecM.strLitListToConstructor]
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      exact bind (intern _) fun _ => bind (intern _) fun _ =>
        bind (intern _) fun _ => bind (intern _) ih

@[local_state_frame] theorem natOffset {methods : Methods .anon}
    (term : KExpr .anon) (depth : Nat) :
    FramesLocalState ((RecM.natOffset term depth).run methods) := by
  unfold RecM.natOffset
  local_state

@[local_state_frame] theorem natOffsetOrZero {methods : Methods .anon}
    (term : KExpr .anon) (depth : Nat) :
    FramesLocalState ((RecM.natOffsetOrZero term depth).run methods) := by
  unfold RecM.natOffsetOrZero
  local_state

@[local_state_frame] theorem evalNatOffsetLiteral {methods : Methods .anon}
    (term : KExpr .anon) (depth : Nat) :
    FramesLocalState ((RecM.evalNatOffsetLiteral term depth).run methods) := by
  unfold RecM.evalNatOffsetLiteral
  local_state

@[local_state_frame] theorem natOffsetDecompose {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.natOffsetDecompose term).run methods) := by
  unfold RecM.natOffsetDecompose
  local_state

@[local_state_frame] theorem natOffsetRebuild {methods : Methods .anon}
    (base : Option (KExpr .anon)) (offset : Nat) :
    FramesLocalState ((RecM.natOffsetRebuild base offset).run methods) := by
  unfold RecM.natOffsetRebuild
  local_state

@[local_state_frame] theorem strLitToConstructor {methods : Methods .anon}
    (value : String) :
    FramesLocalState ((RecM.strLitToConstructor value).run methods) := by
  unfold RecM.strLitToConstructor
  with_reducible refine bindRec (prims methods) ?_
  intro p
  refine bindTcM (intern (.mkConst p.charType #[])) ?_
  intro charType
  refine bindTcM (intern (.mkConst p.charOfNat #[])) ?_
  intro charOfNat
  refine bindTcM (intern (.mkConst p.stringOfList #[])) ?_
  intro stringMk
  refine bindTcM (intern (.mkConst p.listNil #[.mkZero])) ?_
  intro listNil
  refine bindTcM (intern (KExpr.mkApp listNil charType)) ?_
  intro nil
  refine bindTcM (intern (.mkConst p.listCons #[.mkZero])) ?_
  intro listCons
  refine bindTcM (intern (KExpr.mkApp listCons charType)) ?_
  intro cons
  refine bindRec (strLitListToConstructor charOfNat cons value.toList.reverse nil) ?_
  intro list
  exact liftRec (intern (KExpr.mkApp stringMk list))

@[local_state_frame] theorem internIntLit {methods : Methods .anon}
    (value : _root_.Int) :
    FramesLocalState ((RecM.internIntLit value).run methods) := by
  unfold RecM.internIntLit
  local_state

@[local_state_frame] theorem applyIotaArg {methods : Methods .anon}
    (term arg : KExpr .anon) (transient : Bool) :
    FramesLocalState ((RecM.applyIotaArg term arg transient).run methods) := by
  unfold RecM.applyIotaArg
  local_state

@[local_state_frame] theorem applyIotaArgs {methods : Methods .anon}
    (term : KExpr .anon) (args : Array (KExpr .anon)) (transient : Bool) :
    FramesLocalState ((RecM.applyIotaArgs term args transient).run methods) := by
  unfold RecM.applyIotaArgs
  local_state

@[local_state_frame] theorem applyIotaRule {methods : Methods .anon}
    (rule : RecRule .anon) (levels : Array (KUniv .anon))
    (recursor : IotaInfo .anon) (spine args : Array (KExpr .anon)) (fields : Nat) (transient : Bool) :
    FramesLocalState ((RecM.applyIotaRule rule levels recursor spine args fields transient).run methods) := by
  unfold RecM.applyIotaRule
  local_state

@[local_state_frame] theorem tryApplyIotaCtor {methods : Methods .anon}
    (recursor : IotaInfo .anon) (levels : Array (KUniv .anon))
    (spine args : Array (KExpr .anon)) (index fields : Nat) (transient : Bool) :
    FramesLocalState ((RecM.tryApplyIotaCtor recursor levels spine args index fields transient).run methods) := by
  unfold RecM.tryApplyIotaCtor
  local_state

@[local_state_frame] theorem isNatLiteralRecursorApp {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.isNatLiteralRecursorApp term).run methods) := by
  unfold RecM.isNatLiteralRecursorApp
  local_state

@[local_state_frame] theorem isTransientNatLiteralWork {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.isTransientNatLiteralWork term).run methods) := by
  unfold RecM.isTransientNatLiteralWork
  local_state

@[local_state_frame] theorem cleanupNatOffsetMajor {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.cleanupNatOffsetMajor term).run methods) := by
  unfold RecM.cleanupNatOffsetMajor
  local_state

@[local_state_frame] theorem projectDecidableFinValMinor {methods : Methods .anon}
    (id : KId .anon) (field : UInt64) (minor : KExpr .anon) :
    FramesLocalState ((RecM.projectDecidableFinValMinor id field minor).run methods) := by
  unfold RecM.projectDecidableFinValMinor
  local_state

@[local_state_frame] theorem tryReduceFinValDecidableRec {methods : Methods .anon}
    (id : KId .anon) (field : UInt64)
    (head : KExpr .anon) (args : Array (KExpr .anon)) :
    FramesLocalState ((RecM.tryReduceFinValDecidableRec id field head args).run methods) := by
  unfold RecM.tryReduceFinValDecidableRec
  local_state

@[local_state_frame] theorem tryReduceProjectionDefinition {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceProjectionDefinition term).run methods) := by
  unfold RecM.tryReduceProjectionDefinition
  local_state

@[local_state_frame] theorem natRecLiteralParts {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.natRecLiteralParts term).run methods) := by
  unfold RecM.natRecLiteralParts
  local_state

@[local_state_frame] theorem isStuckNatPredicateProbe {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.isStuckNatPredicateProbe term).run methods) := by
  unfold RecM.isStuckNatPredicateProbe
  local_state

@[local_state_frame] theorem bitvecOfNatArgs {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.bitvecOfNatArgs term).run methods) := by
  unfold RecM.bitvecOfNatArgs
  local_state

@[local_state_frame] theorem charOfNatExpr {methods : Methods .anon}
    (value : Nat) :
    FramesLocalState ((RecM.charOfNatExpr value).run methods) := by
  unfold RecM.charOfNatExpr
  local_state

@[local_state_frame] theorem tryReduceStringLiteral {methods : Methods .anon}
    (primitives : Primitives .anon) (id : KId .anon) (value : String) :
    FramesLocalState ((RecM.tryReduceStringLiteral primitives id value).run methods) := by
  unfold RecM.tryReduceStringLiteral
  local_state

@[local_state_frame] theorem tryReduceString {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceString term).run methods) := by
  unfold RecM.tryReduceString
  local_state

@[local_state_frame] theorem discoverBlockInductives {methods : Methods .anon}
    (block : KId .anon) :
    FramesLocalState ((RecM.discoverBlockInductives block).run methods) := by
  unfold RecM.discoverBlockInductives
  local_state

@[local_state_frame] theorem tryProjReduceTail {methods : Methods .anon}
    (id : KId .anon) (field : UInt64) (value : KExpr .anon) :
    FramesLocalState ((RecM.tryProjReduceTail id field value).run methods) := by
  unfold RecM.tryProjReduceTail
  local_state

@[local_state_frame] theorem tryProjPrepare {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (value : KExpr .anon) :
    FramesLocalState ((RecM.tryProjPrepare value).run methods) := by
  rw [RecM.tryProjPrepare_eq]
  local_state

@[local_state_frame] theorem tryProjReduce {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (id : KId .anon) (field : UInt64) (value : KExpr .anon) :
    FramesLocalState ((RecM.tryProjReduce id field value).run methods) := by
  rw [RecM.tryProjReduce_eq]
  local_state

@[local_state_frame] theorem tryProjAppReduce {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.tryProjAppReduce term flags).run methods) := by
  unfold RecM.tryProjAppReduce
  local_state

@[local_state_frame] theorem tryProjAppReduceFinished {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.tryProjAppReduceFinished term flags).run methods) := by
  unfold RecM.tryProjAppReduceFinished
  local_state


@[local_state_frame] theorem restoreDepthGo (saved fuel : Nat) :
    FramesLocalState (TcM.restoreDepth.go (m := .anon) saved fuel) := by
  induction fuel with
  | zero => exact pure _
  | succ fuel ih =>
      rw [TcM.restoreDepth.go]
      local_state

@[local_state_frame] theorem restoreDepth (saved : Nat) :
    FramesLocalState (TcM.restoreDepth (m := .anon) saved) := by
  unfold TcM.restoreDepth
  local_state

@[local_state_frame] theorem peelMajorForalls {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (fuel : Nat) (type : KExpr .anon) :
    FramesLocalState ((RecM.peelMajorForalls fuel type).run methods) := by
  induction fuel generalizing type with
  | zero => exact pure _
  | succ fuel ih =>
      rw [RecM.peelMajorForalls]
      local_state

@[local_state_frame] theorem scanMajorInductiveStep {methods : Methods .anon}
    (next : KExpr .anon → RecM .anon (KId .anon))
    (framed : ∀ type, FramesLocalState ((next type).run methods)) (type : KExpr .anon) :
    FramesLocalState ((RecM.scanMajorInductiveStep next type).run methods) := by
  unfold RecM.scanMajorInductiveStep
  local_state

@[local_state_frame] theorem scanMajorInductive {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (fuel : Nat) (type : KExpr .anon) :
    FramesLocalState ((RecM.scanMajorInductive fuel type).run methods) := by
  induction fuel generalizing type with
  | zero => exact throw _
  | succ fuel ih =>
      rw [RecM.scanMajorInductive, ReaderT.run_bind]
      exact bind (whnfRec recursive type) (scanMajorInductiveStep _ ih)

@[local_state_frame] theorem getMajorInductiveId {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (type : KExpr .anon) (skip : UInt64) :
    FramesLocalState ((RecM.getMajorInductiveId type skip).run methods) := by
  unfold RecM.getMajorInductiveId
  local_state

@[local_state_frame] theorem computeIsRecParamStepAfterWhnf {methods : Methods .anon}
    (type reduced : KExpr .anon) :
    FramesLocalState ((RecM.computeIsRecParamStepAfterWhnf type reduced).run methods) := by
  unfold RecM.computeIsRecParamStepAfterWhnf
  local_state

@[local_state_frame] theorem computeIsRecParamStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (type : KExpr .anon) :
    FramesLocalState ((RecM.computeIsRecParamStep type).run methods) := by
  unfold RecM.computeIsRecParamStep
  local_state

@[local_state_frame] theorem computeIsRecFieldStepAfterWhnf {methods : Methods .anon}
    (blocks : Array Address) (reduced : KExpr .anon) :
    FramesLocalState ((RecM.computeIsRecFieldStepAfterWhnf blocks reduced).run methods) := by
  unfold RecM.computeIsRecFieldStepAfterWhnf
  local_state

@[local_state_frame] theorem computeIsRecFieldStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (blocks : Array Address) (type : KExpr .anon) :
    FramesLocalState ((RecM.computeIsRecFieldStep blocks type).run methods) := by
  unfold RecM.computeIsRecFieldStep
  local_state

@[local_state_frame] theorem computeIsRecCtor {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (type : KExpr .anon)
    (params : Nat) (blocks : Array Address) :
    FramesLocalState ((RecM.computeIsRecCtor type params blocks).run methods) := by
  unfold RecM.computeIsRecCtor
  local_state

@[local_state_frame] theorem computeIsRec {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ctors : Array (KId .anon))
    (params : Nat) (blocks : Array Address) :
    FramesLocalState ((RecM.computeIsRec ctors params blocks).run methods) := by
  unfold RecM.computeIsRec
  local_state

@[local_state_frame] theorem cacheIsRec {methods : Methods .anon}
    (ind : KId .anon) (value : Bool) :
    FramesLocalState ((RecM.cacheIsRec ind value).run methods) := by
  unfold RecM.cacheIsRec
  local_state

@[local_state_frame] theorem eraseCachedIsRec {methods : Methods .anon} (ind : KId .anon) :
    FramesLocalState ((RecM.eraseCachedIsRec ind).run methods) := by
  unfold RecM.eraseCachedIsRec
  local_state

@[local_state_frame] theorem computedIsRecClassify {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ind : KId .anon) (ctors : Array (KId .anon))
    (params : Nat) (blocks : Array Address) :
    FramesLocalState ((RecM.computedIsRecClassify ind ctors params blocks).run methods) := by
  unfold RecM.computedIsRecClassify
  local_state

@[local_state_frame] theorem computedIsRecMiss {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ind : KId .anon) (params : UInt64)
    (ctors : Array (KId .anon)) (block : KId .anon) :
    FramesLocalState ((RecM.computedIsRecMiss ind params ctors block).run methods) := by
  unfold RecM.computedIsRecMiss
  local_state

@[local_state_frame] theorem computedIsRec {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ind : KId .anon) :
    FramesLocalState ((RecM.computedIsRec ind).run methods) := by
  unfold RecM.computedIsRec
  local_state

@[local_state_frame] theorem isStructLike {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (ind : KId .anon) :
    FramesLocalState ((RecM.isStructLike ind).run methods) := by
  unfold RecM.isStructLike
  local_state

@[local_state_frame] theorem finishStructEtaFields {methods : Methods .anon}
    (ind : KId .anon) (major : KExpr .anon) (fuel field : Nat) (result : KExpr .anon) :
    FramesLocalState ((RecM.finishStructEtaFields ind major fuel field result).run methods) := by
  induction fuel generalizing field result with
  | zero => exact pure _
  | succ fuel ih =>
      rw [RecM.finishStructEtaFields]
      local_state

@[local_state_frame] theorem finishStructEtaResult {methods : Methods .anon}
    (ind : KId .anon) (major rhs : KExpr .anon) (fields : UInt64)
    (prefixArgs trailing : Array (KExpr .anon)) :
    FramesLocalState ((RecM.finishStructEtaResult ind major rhs fields prefixArgs trailing).run methods) := by
  unfold RecM.finishStructEtaResult
  local_state

@[local_state_frame] theorem finishStructEtaAfterSort {methods : Methods .anon}
    (levels : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (recursor : IotaInfo .anon) (rule : RecRule .anon) (ind : KId .anon)
    (major sort : KExpr .anon) :
    FramesLocalState ((RecM.finishStructEtaAfterSort levels spine recursor rule ind major sort).run methods) := by
  unfold RecM.finishStructEtaAfterSort
  local_state

@[local_state_frame] theorem tryStructEtaAfterInductive {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (levels : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (recursor : IotaInfo .anon) (rule : RecRule .anon) (ind : KId .anon) :
    FramesLocalState ((RecM.tryStructEtaAfterInductive levels spine recursor rule ind).run methods) := by
  unfold RecM.tryStructEtaAfterInductive
  local_state

@[local_state_frame] theorem tryStructEtaIota {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (id : KId .anon) (recursor : IotaInfo .anon)
    (levels : Array (KUniv .anon)) (spine : Array (KExpr .anon)) :
    FramesLocalState ((RecM.tryStructEtaIota id recursor levels spine).run methods) := by
  unfold RecM.tryStructEtaIota
  local_state

@[local_state_frame] theorem verifyKSynthCandidate {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (type : KExpr .anon) (ctor : KId .anon) (levels : Array (KUniv .anon))
    (args : Array (KExpr .anon)) (params : Nat) :
    FramesLocalState ((RecM.verifyKSynthCandidate type ctor levels args params).run methods) := by
  unfold RecM.verifyKSynthCandidate
  local_state

@[local_state_frame] theorem selectKSynthCandidate {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (type : KExpr .anon) (head : KId .anon) (levels : Array (KUniv .anon))
    (args : Array (KExpr .anon)) (ind : KId .anon) (params : Nat) :
    FramesLocalState ((RecM.selectKSynthCandidate type head levels args ind params).run methods) := by
  unfold RecM.selectKSynthCandidate
  local_state

@[local_state_frame] theorem synthCtorWhenK {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (major : KExpr .anon) (id : KId .anon)
    (recursor : IotaInfo .anon) (levels : Array (KUniv .anon)) :
    FramesLocalState ((RecM.synthCtorWhenK major id recursor levels).run methods) := by
  unfold RecM.synthCtorWhenK
  local_state

@[local_state_frame] theorem tryIotaCtorOrStructEta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (id : KId .anon) (recursor : IotaInfo .anon)
    (levels : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (major : KExpr .anon) (transient : Bool) :
    FramesLocalState ((RecM.tryIotaCtorOrStructEta id recursor levels spine major transient).run methods) := by
  unfold RecM.tryIotaCtorOrStructEta
  local_state

@[local_state_frame] theorem tryIotaAfterCleanup {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (flags : WhnfFlags) (id : KId .anon) (recursor : IotaInfo .anon)
    (levels : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (major : KExpr .anon) (transient : Bool) :
    FramesLocalState ((RecM.tryIotaAfterCleanup flags id recursor levels spine major transient).run methods) := by
  unfold RecM.tryIotaAfterCleanup
  local_state

@[local_state_frame] theorem tryIotaAfterMajorWhnf {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (flags : WhnfFlags) (id : KId .anon) (recursor : IotaInfo .anon)
    (levels : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (major : KExpr .anon) :
    FramesLocalState ((RecM.tryIotaAfterMajorWhnf flags id recursor levels spine major).run methods) := by
  unfold RecM.tryIotaAfterMajorWhnf
  local_state

@[local_state_frame] theorem tryIotaWithFlags {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.tryIotaWithFlags term flags).run methods) := by
  unfold RecM.tryIotaWithFlags
  local_state


@[local_state_frame] theorem deltaUnfoldOne {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.deltaUnfoldOne term).run methods) := by
  unfold RecM.deltaUnfoldOne
  local_state

@[local_state_frame] theorem isNatSuccSpine {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.isNatSuccSpine term).run methods) := by
  unfold RecM.isNatSuccSpine
  local_state

@[local_state_frame] theorem recordNatSuccStuck {methods : Methods .anon}
    (visited : Array (Address × Address)) :
    FramesLocalState ((RecM.recordNatSuccStuck visited).run methods) := by
  unfold RecM.recordNatSuccStuck
  local_state

@[local_state_frame] theorem tryReduceNatSuccPeelMiss {methods : Methods .anon}
    (reduced current : KExpr .anon) (offset : Nat)
    (visited : Array (Address × Address)) (key : Address × Address) :
    FramesLocalState ((RecM.tryReduceNatSuccPeelMiss reduced current offset visited key).run methods) := by
  unfold RecM.tryReduceNatSuccPeelMiss
  local_state

@[local_state_frame] theorem tryReduceNatSuccPeelAfterKey {methods : Methods .anon}
    (reduced current : KExpr .anon) (offset : Nat)
    (visited : Array (Address × Address)) (key : Address × Address) :
    FramesLocalState ((RecM.tryReduceNatSuccPeelAfterKey reduced current offset visited key).run methods) := by
  unfold RecM.tryReduceNatSuccPeelAfterKey
  local_state

@[local_state_frame] theorem tryReduceNatSuccPeel {methods : Methods .anon}
    (reduced current : KExpr .anon) (offset : Nat)
    (visited : Array (Address × Address)) :
    FramesLocalState ((RecM.tryReduceNatSuccPeel reduced current offset visited).run methods) := by
  unfold RecM.tryReduceNatSuccPeel
  local_state

@[local_state_frame] theorem tryReduceNatSuccAfterWhnf {methods : Methods .anon}
    (reduced : KExpr .anon) (offset : Nat)
    (visited : Array (Address × Address)) :
    FramesLocalState ((RecM.tryReduceNatSuccAfterWhnf reduced offset visited).run methods) := by
  unfold RecM.tryReduceNatSuccAfterWhnf
  local_state

@[local_state_frame] theorem isNatSuccIhStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (step : KExpr .anon) :
    FramesLocalState ((RecM.isNatSuccIhStep step).run methods) := by
  unfold RecM.isNatSuccIhStep
  local_state

@[local_state_frame] theorem tryReduceNatSuccLinearRec {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (arg : KExpr .anon) (offset : Nat) :
    FramesLocalState ((RecM.tryReduceNatSuccLinearRec arg offset).run methods) := by
  unfold RecM.tryReduceNatSuccLinearRec
  local_state

@[local_state_frame] theorem tryReduceNatSuccIterStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (state : KExpr .anon × Nat × Array (Address × Address)) :
    FramesLocalState ((RecM.tryReduceNatSuccIterStep state).run methods) := by
  unfold RecM.tryReduceNatSuccIterStep
  local_state

@[local_state_frame] theorem tryReduceNatSuccIter {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (arg : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceNatSuccIter arg).run methods) := by
  unfold RecM.tryReduceNatSuccIter
  local_state

@[local_state_frame] theorem whnfNatReducerArg {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (arg : KExpr .anon) :
    FramesLocalState ((RecM.whnfNatReducerArg arg).run methods) := by
  unfold RecM.whnfNatReducerArg
  local_state

@[local_state_frame] theorem tryReduceNatPredicate {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (addr : Address) (args : Array (KExpr .anon)) :
    FramesLocalState ((RecM.tryReduceNatPredicate addr args).run methods) := by
  unfold RecM.tryReduceNatPredicate
  local_state

@[local_state_frame] theorem tryReduceNatWithSuccMode {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (mode : NatSuccMode) :
    FramesLocalState ((RecM.tryReduceNatWithSuccMode term mode).run methods) := by
  unfold RecM.tryReduceNatWithSuccMode
  local_state

@[local_state_frame] theorem tryReduceNat {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceNat term).run methods) := by
  unfold RecM.tryReduceNat
  local_state

@[local_state_frame] theorem tryNatOffsetStuck {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryNatOffsetStuck term).run methods) := by
  unfold RecM.tryNatOffsetStuck
  local_state

@[local_state_frame] theorem buildNatDecidableTrue {methods : Methods .anon}
    (primitives : Primitives .anon) (prop : KExpr .anon)
    (args : Array (KExpr .anon)) (proofFn : KId .anon) (level : KUniv .anon) :
    FramesLocalState ((RecM.buildNatDecidableTrue primitives prop args proofFn level).run methods) := by
  unfold RecM.buildNatDecidableTrue
  local_state

@[local_state_frame] theorem buildNatDecidableFalse {methods : Methods .anon}
    (primitives : Primitives .anon) (prop : KExpr .anon)
    (args : Array (KExpr .anon)) (proofFn : KId .anon) (level : KUniv .anon) :
    FramesLocalState ((RecM.buildNatDecidableFalse primitives prop args proofFn level).run methods) := by
  unfold RecM.buildNatDecidableFalse
  local_state

@[local_state_frame] theorem inferDecidableProp {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.inferDecidableProp term).run methods) := by
  unfold RecM.inferDecidableProp
  local_state

@[local_state_frame] theorem tryNormalizeIntDecidable {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (addr : Address) (args : Array (KExpr .anon)) :
    FramesLocalState ((RecM.tryNormalizeIntDecidable addr args).run methods) := by
  unfold RecM.tryNormalizeIntDecidable
  local_state

@[local_state_frame] theorem tryReduceDecidable {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceDecidable term).run methods) := by
  unfold RecM.tryReduceDecidable
  local_state

@[local_state_frame] theorem tryQuotReduce {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryQuotReduce term).run methods) := by
  unfold RecM.tryQuotReduce
  local_state


@[local_state_frame] theorem tryEvalNatValueForPredFuel {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (fuel : Nat) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryEvalNatValueForPredFuel fuel term).run methods) := by
  induction fuel generalizing term with
  | zero => exact pure _
  | succ fuel ih =>
      rw [RecM.tryEvalNatValueForPredFuel]
      local_state

@[local_state_frame] theorem tryEvalNatValueForPred {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (depth : Nat) :
    FramesLocalState ((RecM.tryEvalNatValueForPred term depth).run methods) := by
  unfold RecM.tryEvalNatValueForPred
  local_state

@[local_state_frame] theorem tryReduceBitvecToNat {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (value : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceBitvecToNat value).run methods) := by
  unfold RecM.tryReduceBitvecToNat
  local_state

@[local_state_frame] theorem bitvecToNatExpr {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (width value : KExpr .anon) :
    FramesLocalState ((RecM.bitvecToNatExpr width value).run methods) := by
  unfold RecM.bitvecToNatExpr
  local_state

@[local_state_frame] theorem tryReduceBitvecUlt {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (width left right : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceBitvecUlt width left right).run methods) := by
  unfold RecM.tryReduceBitvecUlt
  local_state

@[local_state_frame] theorem tryReduceBitvecLtProp {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (prop : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceBitvecLtProp prop).run methods) := by
  unfold RecM.tryReduceBitvecLtProp
  local_state

@[local_state_frame] theorem tryReduceBitvec {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceBitvec term).run methods) := by
  unfold RecM.tryReduceBitvec
  local_state

@[local_state_frame] theorem tryReduceNative {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.tryReduceNative term).run methods) := by
  unfold RecM.tryReduceNative
  local_state


@[local_state_frame] theorem whnfCoreWithFlagsStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.whnfCoreWithFlagsStep term flags).run methods) := by
  unfold RecM.whnfCoreWithFlagsStep
  local_state

@[local_state_frame] theorem whnfCoreWithFlagsUncached {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.whnfCoreWithFlagsUncached term flags).run methods) := by
  unfold RecM.whnfCoreWithFlagsUncached
  local_state

@[local_state_frame] theorem whnfCoreWithFlagsNonLeaf {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.whnfCoreWithFlagsNonLeaf term flags).run methods) := by
  unfold RecM.whnfCoreWithFlagsNonLeaf
  local_state

@[local_state_frame] theorem whnfCoreWithFlags {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.whnfCoreWithFlags term flags).run methods) := by
  unfold RecM.whnfCoreWithFlags
  local_state

@[local_state_frame] theorem whnfCore {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfCore term).run methods) := by
  unfold RecM.whnfCore
  local_state

@[local_state_frame] theorem whnfCoreForDefEq {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfCoreForDefEq term).run methods) := by
  unfold RecM.whnfCoreForDefEq
  local_state

@[local_state_frame] theorem whnfNoDeltaReducersStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (flags : WhnfFlags) (mode : NatSuccMode) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfNoDeltaReducersStep flags mode term).run methods) := by
  unfold RecM.whnfNoDeltaReducersStep
  local_state

@[local_state_frame] theorem whnfNoDeltaImplStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (flags : WhnfFlags) (mode : NatSuccMode) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfNoDeltaImplStep flags mode term).run methods) := by
  unfold RecM.whnfNoDeltaImplStep
  local_state

@[local_state_frame] theorem whnfNoDeltaImplUncached {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfNoDeltaImplUncached term flags mode).run methods) := by
  unfold RecM.whnfNoDeltaImplUncached
  local_state

@[local_state_frame] theorem whnfNoDeltaImplNonLeaf {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfNoDeltaImplNonLeaf term flags mode).run methods) := by
  unfold RecM.whnfNoDeltaImplNonLeaf
  local_state

@[local_state_frame] theorem whnfNoDeltaImpl {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfNoDeltaImpl term flags mode).run methods) := by
  unfold RecM.whnfNoDeltaImpl
  local_state

@[local_state_frame] theorem whnfNoDelta {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfNoDelta term).run methods) := by
  unfold RecM.whnfNoDelta
  local_state

@[local_state_frame] theorem whnfNoDeltaForDefEq {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfNoDeltaForDefEq term).run methods) := by
  unfold RecM.whnfNoDeltaForDefEq
  local_state

@[local_state_frame] theorem whnfWithNatSuccModeStep {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (mode : NatSuccMode) (state : KExpr .anon × Std.HashSet Address) :
    FramesLocalState ((RecM.whnfWithNatSuccModeStep mode state).run methods) := by
  unfold RecM.whnfWithNatSuccModeStep
  local_state

@[local_state_frame] theorem whnfWithNatSuccModeUncached {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfWithNatSuccModeUncached term mode).run methods) := by
  unfold RecM.whnfWithNatSuccModeUncached
  local_state

@[local_state_frame] theorem whnfWithNatSuccModePrefix {methods : Methods .anon}
    (term : KExpr .anon) :
    FramesLocalState ((RecM.whnfWithNatSuccModePrefix term).run methods) := by
  unfold RecM.whnfWithNatSuccModePrefix
  local_state

@[local_state_frame] theorem whnfWithNatSuccModeMissCharge {methods : Methods .anon}
     :
    FramesLocalState ((RecM.whnfWithNatSuccModeMissCharge (m := .anon)).run methods) := by
  unfold RecM.whnfWithNatSuccModeMissCharge
  local_state

@[local_state_frame] theorem whnfWithNatSuccModeNonLeaf {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfWithNatSuccModeNonLeaf term mode).run methods) := by
  unfold RecM.whnfWithNatSuccModeNonLeaf
  local_state

@[local_state_frame] theorem whnfWithNatSuccMode {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfWithNatSuccMode term mode).run methods) := by
  unfold RecM.whnfWithNatSuccMode
  local_state

@[local_state_frame] theorem whnf {methods : Methods .anon}
    (recursive : MethodsLocalState methods) (term : KExpr .anon) :
    FramesLocalState ((RecM.whnf term).run methods) := by
  unfold RecM.whnf
  local_state

end FramesLocalState
end Ix.Kernel.Consistency
