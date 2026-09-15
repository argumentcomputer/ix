/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InferenceLocalState
import Ix.Kernel.Verify.Monad

/-!
# Local-state effects of reduction and conversion control flow

Both outcomes preserve the caller's local declarations, allocation bound and
installed loader. These rules cover caught failures, cleanup, finite loops,
keys, fuel and policy scopes. Recursive callback frames describe a strictly
smaller method table. The reduction and conversion proofs compose these rules
to close each finite production table.
-/

namespace Ix.Kernel.Consistency

namespace FramesLocalState

theorem ofWF {action : TcM .anon α}
    (framed : ∀ before, TcM.WF
      (fun after => LocalStateInvariant after ∧ LocalStateFrame before after)
      before action (fun _ _ => True)) : FramesLocalState action := by
  intro before valid
  have result := framed before ⟨valid, .refl _⟩
  cases run : action before <;> rw [run] at result <;> exact result.1.2

theorem tryCatch {action : TcM .anon α} {handler : TcError .anon → TcM .anon α}
    (body : FramesLocalState action) (caught : ∀ error, FramesLocalState (handler error)) :
    FramesLocalState (tryCatch action handler) := by
  intro before valid
  have first := body before valid
  change match EStateM.tryCatch action handler before with
    | .ok _ after | .error _ after => LocalStateFrame before after
  cases run : action before with
  | ok value after =>
      rw [EStateM.tryCatch, run]
      simpa only [run] using first
  | error error middle =>
      rw [run] at first
      rw [EStateM.tryCatch, run]
      change match handler error middle with
        | .ok _ after | .error _ after => LocalStateFrame before after
      have next := caught error middle (first.invariant valid)
      cases finished : handler error middle <;> rw [finished] at next <;> exact first.trans next

private theorem tryFinally_eq (action : TcM .anon α) (cleanup : TcM .anon β)
    (before : TcState .anon) :
    tryFinally action cleanup before =
      match action before with
      | .ok value middle =>
          match cleanup middle with
          | .ok _ after => .ok value after
          | .error error after => .error error after
      | .error error middle =>
          match cleanup middle with
          | .ok _ after => .error error after
          | .error cleanupError after => .error cleanupError after := by
  unfold tryFinally
  change EStateM.map (fun value : α × β => value.1)
    (tryFinally' action (fun _ => cleanup)) before = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases run : action before <;> simp only [run] <;> cases finished : cleanup _ <;> rfl

theorem tryFinally {action : TcM .anon α} {cleanup : TcM .anon β}
    (body : FramesLocalState action) (clean : FramesLocalState cleanup) :
    FramesLocalState (tryFinally action cleanup) := by
  intro before valid
  rw [tryFinally_eq]
  have first := body before valid
  cases run : action before <;> rw [run] at first <;> dsimp only <;>
    have next := clean _ (first.invariant valid) <;>
    cases finished : cleanup _ <;> rw [finished] at next <;> exact first.trans next

theorem map (f : α → β) {action : TcM .anon α} (body : FramesLocalState action) :
    FramesLocalState (f <$> action) := by
  simpa only [map_eq_pure_bind] using bind body (fun value => pure (f value))

theorem modifyGet {f : TcState .anon → α × TcState .anon}
    (framed : ∀ before, LocalStateFrame before (f before).2) :
    FramesLocalState (MonadStateOf.modifyGet f : TcM .anon α) :=
  fun before _ => framed before

theorem tick : FramesLocalState (TcM.tick (m := .anon)) := by
  apply ofWF
  intro before
  apply TcM.WF.mono (TcM.tick.wf (fun state valid =>
    ⟨⟨valid.1.coherent, valid.1.allocated, valid.1.loader⟩,
      ⟨valid.2.counter, valid.2.context, valid.2.loader⟩⟩))
  · intros; trivial
  · intros; trivial

theorem stepTrace (tag : String) (payload : Unit → String) :
    FramesLocalState (TcM.stepTrace (m := .anon) tag payload) := by
  unfold TcM.stepTrace
  apply bind get
  intro state
  split <;> exact pure _

theorem bumpStats (update : TcState .anon → TcState .anon)
    (framed : ∀ before, LocalStateFrame before (update before)) :
    FramesLocalState (TcM.bumpStats update) := by
  unfold TcM.bumpStats
  apply bind get
  intro state
  split
  · exact modify update framed
  · exact pure _

theorem isLetVar (index : UInt64) : FramesLocalState (TcM.isLetVar (m := .anon) index) := by
  unfold TcM.isLetVar
  apply bind get
  intro state
  dsimp only
  split <;> exact pure _

theorem lookupLetVal (index : UInt64) : FramesLocalState (TcM.lookupLetVal (m := .anon) index) := by
  unfold TcM.lookupLetVal
  apply bind get
  intro state
  dsimp only
  split
  · exact pure _
  · split
    · exact pure _
    · exact bind (runIntern _) (fun _ => pure _)

theorem whnfKey (term : KExpr .anon) : FramesLocalState (TcM.whnfKey term) :=
  bind (ctxAddrForLbr term.lbr) (fun _ => pure _)

theorem tryGetBlock (id : KId .anon) : FramesLocalState (TcM.tryGetBlock id) := by
  unfold TcM.tryGetBlock
  apply bind get
  intro state
  split
  · exact pure _
  · exact bind (lazyIngressAddr id.addr) fun _ => bind get fun _ => pure _

theorem runBounded {methods : Methods .anon}
    {step : σ → RecM .anon (RecM.BoundedStep σ α)}
    (framed : ∀ state, FramesLocalState ((step state).run methods)) :
    ∀ fuel state, FramesLocalState ((RecM.runBounded step fuel state).run methods)
  | 0, _ => throw _
  | fuel + 1, state => by
      rw [RecM.runBounded, ReaderT.run_bind]
      apply bind (framed state)
      intro next
      cases next with
      | next value => exact runBounded framed fuel value
      | done value => exact pure _

theorem forInList {methods : Methods .anon} (items : List α) (initial : β)
    (step : α → β → RecM .anon (ForInStep β))
    (framed : ∀ item value, FramesLocalState ((step item value).run methods)) :
    FramesLocalState ((forIn items initial step).run methods) := by
  induction items generalizing initial with
  | nil => exact pure _
  | cons item rest ih =>
      rw [List.forIn_cons, ReaderT.run_bind]
      apply bind (framed item initial)
      intro next
      cases next with
      | done value => exact pure _
      | yield value => exact ih value

theorem forInRange {methods : Methods .anon} (range : Std.Legacy.Range) (initial : α)
    (step : Nat → α → RecM .anon (ForInStep α))
    (framed : ∀ index value, FramesLocalState ((step index value).run methods)) :
    FramesLocalState ((forIn range initial step).run methods) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList _ _ _ framed

theorem forInArray {methods : Methods .anon} (items : Array α) (initial : β)
    (step : α → β → RecM .anon (ForInStep β))
    (framed : ∀ item value, FramesLocalState ((step item value).run methods)) :
    FramesLocalState ((forIn items initial step).run methods) := by
  rcases items with ⟨items⟩
  rw [List.forIn_toArray]
  exact forInList _ _ _ framed

theorem withCheapRecursionDepth {methods : Methods .anon} {action : RecM .anon α}
    (body : FramesLocalState (action.run methods)) :
    FramesLocalState ((RecM.withCheapRecursionDepth action).run methods) := by
  unfold RecM.withCheapRecursionDepth
  simp only [ReaderT.run_bind]
  apply bind
  · apply modify; exact fun _ => ⟨Nat.le_refl _, .refl _, rfl⟩
  · intro _
    change FramesLocalState (_root_.tryFinally (action.run methods)
      (_root_.modify fun state => {state with cheapRecursionDepth := state.cheapRecursionDepth - 1}))
    apply tryFinally body
    apply modify; exact fun _ => ⟨Nat.le_refl _, .refl _, rfl⟩

end FramesLocalState

structure MethodsLocalState (methods : Methods .anon) : Prop where
  whnf : ∀ term, FramesLocalState (methods.whnf term)
  whnfCore : ∀ term, FramesLocalState (methods.whnfCore term)
  whnfMode : ∀ term mode, FramesLocalState (methods.whnfMode term mode)
  whnfCoreFlags : ∀ term flags, FramesLocalState (methods.whnfCoreFlags term flags)
  infer : ∀ term, FramesLocalState (methods.infer term)
  isDefEq : ∀ left right, FramesLocalState (methods.isDefEq left right)

namespace FramesLocalState

theorem whnfRec {methods : Methods .anon} (recursive : MethodsLocalState methods)
    (term : KExpr .anon) : FramesLocalState ((RecM.whnfRec term).run methods) := recursive.whnf term

theorem whnfModeRec {methods : Methods .anon} (recursive : MethodsLocalState methods)
    (term : KExpr .anon) (mode : NatSuccMode) :
    FramesLocalState ((RecM.whnfModeRec term mode).run methods) := recursive.whnfMode term mode

theorem whnfCoreFlagsRec {methods : Methods .anon} (recursive : MethodsLocalState methods)
    (term : KExpr .anon) (flags : WhnfFlags) :
    FramesLocalState ((RecM.whnfCoreFlagsRec term flags).run methods) := recursive.whnfCoreFlags term flags

theorem inferOnlyRec {methods : Methods .anon} (recursive : MethodsLocalState methods)
    (term : KExpr .anon) : FramesLocalState ((RecM.inferOnlyRec term).run methods) :=
  withInferOnly (recursive.infer term)

theorem tryOptional {methods : Methods .anon} {action : RecM .anon α}
    (body : FramesLocalState (action.run methods)) :
    FramesLocalState ((RecM.tryOptional action).run methods) := by
  unfold RecM.tryOptional RecM.try?
  exact tryCatch (bind body (fun value => pure (some value))) (fun _ => pure none)

end FramesLocalState
end Ix.Kernel.Consistency

namespace Ix.Kernel.Consistency.FramesLocalState

theorem pureRec {methods : Methods .anon} (value : α) :
    FramesLocalState ((Pure.pure value : RecM .anon α).run methods) := pure value

theorem throwRec {methods : Methods .anon} (error : TcError .anon) :
    FramesLocalState ((MonadExceptOf.throw error : RecM .anon α).run methods) := throw error

theorem throwExceptRec {methods : Methods .anon} (error : TcError .anon) :
    FramesLocalState ((MonadExcept.throw error : RecM .anon α).run methods) := throw error

theorem getRec {methods : Methods .anon} :
    FramesLocalState ((MonadState.get : RecM .anon (TcState .anon)).run methods) := get

theorem liftRec {methods : Methods .anon} {action : TcM .anon α}
    (body : FramesLocalState action) :
    FramesLocalState ((monadLift action : RecM .anon α).run methods) := body

theorem liftSelf {action : TcM .anon α} (body : FramesLocalState action) :
    FramesLocalState (monadLift action : TcM .anon α) := body

theorem mapRec {methods : Methods .anon} (f : α → β) {action : RecM .anon α}
    (body : FramesLocalState (action.run methods)) :
    FramesLocalState ((f <$> action).run methods) := map f body

theorem bindRead {methods : Methods .anon} {next : Methods .anon → RecM .anon α}
    (body : FramesLocalState ((next methods).run methods)) :
    FramesLocalState (((read : RecM .anon (Methods .anon)) >>= next).run methods) := body

theorem tryProbe {methods : Methods .anon} {action : RecM .anon α}
    (body : FramesLocalState (action.run methods)) :
    FramesLocalState ((RecM.try? action).run methods) := tryOptional body

theorem bindRec {methods : Methods .anon} {action : RecM .anon α} {next : α → RecM .anon β}
    (body : FramesLocalState (action.run methods))
    (rest : ∀ value, FramesLocalState ((next value).run methods)) :
    FramesLocalState ((action >>= next).run methods) := bind body rest

theorem bindTcM {methods : Methods .anon} {action : TcM .anon α}
    {next : α → RecM .anon β}
    (body : FramesLocalState action)
    (rest : ∀ value, FramesLocalState ((next value).run methods)) :
    FramesLocalState ((do let value ← action; next value : RecM .anon β).run methods) := by
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  exact bind body rest

theorem tryFinallyRec {methods : Methods .anon} {action : RecM .anon α} {cleanup : RecM .anon β}
    (body : FramesLocalState (action.run methods))
    (clean : FramesLocalState (cleanup.run methods)) :
    FramesLocalState ((_root_.tryFinally action cleanup).run methods) := by
  change FramesLocalState (_root_.tryFinally (action.run methods) (cleanup.run methods))
  exact tryFinally body clean

theorem tryCatchRec {methods : Methods .anon} {action : RecM .anon α}
    {handler : TcError .anon → RecM .anon α}
    (body : FramesLocalState (action.run methods))
    (caught : ∀ error, FramesLocalState ((handler error).run methods)) :
    FramesLocalState ((MonadExceptOf.tryCatch action handler).run methods) := tryCatch body caught

theorem tryCatchExceptRec {methods : Methods .anon} {action : RecM .anon α}
    {handler : TcError .anon → RecM .anon α}
    (body : FramesLocalState (action.run methods))
    (caught : ∀ error, FramesLocalState ((handler error).run methods)) :
    FramesLocalState ((MonadExcept.tryCatch action handler).run methods) := tryCatch body caught

theorem modifyRec {methods : Methods .anon} {f : TcState .anon → TcState .anon}
    (framed : ∀ before, LocalStateFrame before (f before)) :
    FramesLocalState ((_root_.modify f : RecM .anon PUnit).run methods) := modify f framed

theorem forInListTcM (items : List α) (initial : β) (step : α → β → TcM .anon (ForInStep β))
    (framed : ∀ item value, FramesLocalState (step item value)) :
    FramesLocalState (forIn items initial step) := by
  induction items generalizing initial with
  | nil => exact pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply bind (framed item initial)
      intro next
      cases next with
      | done value => exact pure _
      | yield value => exact ih value

end Ix.Kernel.Consistency.FramesLocalState
