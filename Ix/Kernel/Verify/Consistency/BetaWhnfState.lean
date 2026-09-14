/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.StructuralWhnfEntry
import Ix.Kernel.Verify.Whnf.Driver.CacheExecution

/-! Computed WHNF key, instrumentation, cache states, and terminal branches.
These operational primitives do not depend on a reduction trace. -/

namespace Ix.Kernel.Consistency

universe u v

/-- Compute exactly the context-digest memoization performed by a WHNF key. -/
def betaWhnfKey (source : KExpr .anon) (before : TcState .anon) :
    (Address × Address) × TcState .anon :=
  if source.lbr == 0 || before.ctx.isEmpty then
    ((source.addr, emptyCtxAddr), before)
  else
    let cacheKey := (before.ctxId, source.lbr)
    match before.ctxAddrCache[cacheKey]? with
    | some cached => ((source.addr, cached), before)
    | none =>
        let digest := TcM.ctxAddrForLbrUncached before source.lbr
        ((source.addr, digest), { before with ctxAddrCache := before.ctxAddrCache.insert cacheKey digest })

theorem betaWhnfKey_run (source : KExpr .anon) (before : TcState .anon) :
    TcM.whnfKey source before = .ok (betaWhnfKey source before).1 (betaWhnfKey source before).2 := by
  unfold TcM.whnfKey TcM.ctxAddrForLbr betaWhnfKey
  change EStateM.bind (fun state => EStateM.bind (get : TcM .anon (TcState .anon)) _ state) _ before = _
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  by_cases fast : (source.lbr == 0 || before.ctx.isEmpty) = true
  · simp only [if_pos fast]; rfl
  · simp only [if_neg fast]
    cases before.ctxAddrCache[(before.ctxId, source.lbr)]? <;> rfl

theorem betaWhnfKey_environment (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source before).2.env = before.env := by
  unfold betaWhnfKey
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem betaWhnfKey_context (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source before).2.lctx = before.lctx := by
  unfold betaWhnfKey
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem betaWhnfKey_native (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source before).2.inNativeReduce = before.inNativeReduce := by
  unfold betaWhnfKey
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Full WHNF's instrumentation changes only its optional call counter. -/
def betaWhnfPrefix (before : TcState .anon) : TcState .anon :=
  if before.stats then { before with whnfCalls := before.whnfCalls + 1 } else before

theorem betaWhnfPrefix_run (source : KExpr .anon) (before : TcState .anon) (methods : Methods .anon) :
    (RecM.whnfWithNatSuccModePrefix source).run methods before = .ok () (betaWhnfPrefix before) := by
  have traced : TcM.stepTrace "whnf+" (fun _ => TcM.addr8 source.addr) before = .ok () before := by
    unfold TcM.stepTrace
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
    simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
    split <;> rfl
  unfold RecM.whnfWithNatSuccModePrefix
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.stepTrace "whnf+" (fun _ => TcM.addr8 source.addr)) _ before = _
  rw [EStateM.bind, traced]
  change TcM.bumpStats (fun state => { state with whnfCalls := state.whnfCalls + 1 }) before = _
  unfold TcM.bumpStats betaWhnfPrefix
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  split <;> rfl

/-- The miss charge performs one shared-fuel decrement and optionally
increments its miss counter. -/
def betaWhnfCharge (before : TcState .anon) : TcState .anon :=
  if before.stats then
    { before with whnfMisses := before.whnfMisses + 1, recFuel := before.recFuel - 1 }
  else { before with recFuel := before.recFuel - 1 }

theorem betaWhnfCharge_run (before : TcState .anon) (methods : Methods .anon)
    (enough : (before.recFuel == 0) = false) :
    (RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods before =
      .ok () (betaWhnfCharge before) := by
  unfold RecM.whnfWithNatSuccModeMissCharge
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }))
    (fun _ => TcM.tick) before = _
  cases stats : before.stats
  · have bumped : TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }) before =
        .ok () before := by
      unfold TcM.bumpStats
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
      simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
      rw [if_neg (by simp only [stats, Bool.false_eq_true, not_false_eq_true])]; rfl
    rw [EStateM.bind, bumped]
    change TcM.tick before = _
    unfold TcM.tick betaWhnfCharge
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
    simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
    rw [enough, stats]; rfl
  · have bumped : TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }) before =
        .ok () { before with whnfMisses := before.whnfMisses + 1 } := by
      unfold TcM.bumpStats
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
      simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
      rw [if_pos stats]; rfl
    rw [EStateM.bind, bumped]
    change TcM.tick { before with whnfMisses := before.whnfMisses + 1 } = _
    unfold TcM.tick betaWhnfCharge
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ { before with whnfMisses := before.whnfMisses + 1 } = _
    simp only [EStateM.bind, show (get : TcM .anon (TcState .anon))
      { before with whnfMisses := before.whnfMisses + 1 } =
        .ok { before with whnfMisses := before.whnfMisses + 1 }
          { before with whnfMisses := before.whnfMisses + 1 } from rfl]
    rw [enough, stats]; rfl

/-- Constructors on which both public drivers and all their reducer tails
stop without recursive callbacks or source lookup. -/
inductive BetaWhnfTerminal : KExpr .anon → Prop
  | sort (level : KUniv .anon) (info : ExprInfo .anon) : BetaWhnfTerminal (.sort level info)
  | forallE (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
      (domain body : KExpr .anon) (info : ExprInfo .anon) : BetaWhnfTerminal (.all name bi domain body info)
  | lam (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
      (domain body : KExpr .anon) (info : ExprInfo .anon) : BetaWhnfTerminal (.lam name bi domain body info)

theorem BetaWhnfTerminal.noDelta_tail {source : KExpr .anon} (terminal : BetaWhnfTerminal source)
    (methods : Methods .anon) (before : TcState .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    (RecM.whnfNoDeltaReducersStep flags mode source).run methods before = .ok (.done source) before := by
  cases terminal <;>
    simp [RecM.whnfNoDeltaReducersStep, RecM.tryProjAppReduceFinished, RecM.tryProjAppReduce,
      RecM.tryReduceBitvec, RecM.tryReduceNatWithSuccMode, RecM.tryReduceNative,
      RecM.tryReduceString, RecM.tryReduceProjectionDefinition, RecM.tryQuotReduce,
      KExpr.collectSpine, KExpr.collectSpine.go, RecM.prims, ReaderT.run_bind]
  all_goals
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
    simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
    cases before.noAccel <;> rfl

theorem BetaWhnfTerminal.full_step {source result : KExpr .anon}
    (terminal : BetaWhnfTerminal result) {methods : Methods .anon} {before after : TcState .anon}
    (mode : NatSuccMode) (seen : Std.HashSet Address)
    (reduced : (RecM.whnfNoDeltaImpl source .FULL mode).run methods before = .ok result after) :
    (RecM.whnfWithNatSuccModeStep mode (source, seen)).run methods before = .ok (.done result) after := by
  unfold RecM.whnfWithNatSuccModeStep
  rw [ReaderT.run_bind]
  change EStateM.bind ((RecM.whnfNoDeltaImpl source .FULL mode).run methods) _ before = _
  rw [EStateM.bind, reduced]
  simp only
  by_cases repeated : seen.contains result.addr = true
  · rw [if_pos repeated]; rfl
  · rw [if_neg repeated]
    cases terminal <;>
      simp [RecM.tryReduceNative, RecM.tryReduceBitvec, RecM.tryReduceNatWithSuccMode,
        RecM.tryReduceDecidable, RecM.tryReduceString, RecM.tryNatOffsetStuck,
        RecM.natOffsetStuckHead, RecM.deltaUnfoldOne, RecM.tryDeltaUnfold,
        KExpr.collectSpine, KExpr.collectSpine.go, RecM.prims, ReaderT.run_bind]
    all_goals
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ after = _
      simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
      cases native : after.noAccel
      all_goals
        change EStateM.bind (get : TcM .anon (TcState .anon)) _ after = _
        simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
        simp only [native]
        rfl

private theorem bounded_done {α γ : Type} (step : α → RecM .anon (RecM.BoundedStep α γ))
    {methods : Methods .anon} {before after : TcState .anon} {source : α} {result : γ}
    (done : (step source).run methods before = .ok (.done result) after)
    {fuel : Nat} (enough : 0 < fuel) :
    (RecM.runBounded step fuel source).run methods before = .ok result after := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      rw [RecM.runBounded, ReaderT.run_bind]
      change EStateM.bind ((step source).run methods) _ before = _
      rw [EStateM.bind, done]
      rfl

theorem BetaWhnfTerminal.noDelta_uncached {source result : KExpr .anon}
    (terminal : BetaWhnfTerminal result) {methods : Methods .anon} {before after : TcState .anon}
    (flags : WhnfFlags) (mode : NatSuccMode)
    (reduced : (RecM.whnfCoreWithFlags source flags).run methods before = .ok result after) :
    (RecM.whnfNoDeltaImplUncached source flags mode).run methods before = .ok result after := by
  apply bounded_done (enough := by decide)
  unfold RecM.whnfNoDeltaImplStep
  rw [ReaderT.run_bind]
  change EStateM.bind ((RecM.whnfCoreWithFlags source flags).run methods) _ before = _
  rw [EStateM.bind, reduced]
  exact terminal.noDelta_tail methods after flags mode

theorem BetaWhnfTerminal.full_uncached {source result : KExpr .anon}
    (terminal : BetaWhnfTerminal result) {methods : Methods .anon} {before after : TcState .anon}
    (mode : NatSuccMode)
    (reduced : (RecM.whnfNoDeltaImpl source .FULL mode).run methods before = .ok result after) :
    (RecM.whnfWithNatSuccModeUncached source mode).run methods before = .ok result after :=
  bounded_done _ (terminal.full_step mode {} reduced) (by decide)

theorem betaWhnfKey_fuel (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source before).2.recFuel = before.recFuel := by
  unfold betaWhnfKey
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem betaWhnfPrefix_fields (before : TcState .anon) :
    (betaWhnfPrefix before).env = before.env ∧
      (betaWhnfPrefix before).lctx = before.lctx ∧
      (betaWhnfPrefix before).inNativeReduce = before.inNativeReduce ∧
      (betaWhnfPrefix before).recFuel = before.recFuel := by
  unfold betaWhnfPrefix
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem betaWhnfCharge_fields (before : TcState .anon) :
    (betaWhnfCharge before).env = before.env ∧
      (betaWhnfCharge before).lctx = before.lctx ∧
      (betaWhnfCharge before).inNativeReduce = before.inNativeReduce := by
  unfold betaWhnfCharge
  split <;> exact ⟨rfl, rfl, rfl⟩

end Ix.Kernel.Consistency
