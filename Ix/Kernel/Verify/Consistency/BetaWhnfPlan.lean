/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaPrefixPlan
import Ix.Kernel.Verify.Consistency.LetWhnfPlan
import Ix.Kernel.Verify.Consistency.BetaCoreCache
import Ix.Kernel.Verify.Consistency.BetaHeadStepPlan

/-! Raw beta and explicit-let paths compute production results and states independently of
the source-inference and semantic-origin derivations. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- A lambda already at the source spine uses the shared prefix operation. -/
structure BetaStepPlan {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term : AExpr β)
    extends BetaPrefixPlan resolve locals before where
  rawFunction : KExpr .anon
  rawArgument : KExpr .anon
  appInfo : ExprInfo .anon
  sourceEq : source = .app rawFunction rawArgument appInfo
  modelSource : term = (AExpr.lam condition domain inner).appN arguments
  spine : (KExpr.app rawFunction rawArgument appInfo).collectSpine =
    (.lam name bi rawDomain rawInner lambdaInfo, rawArguments)

namespace BetaStepPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {locals : List FVarId} {before : TcState .anon} {source : KExpr .anon} {term : AExpr β}

def output (step : BetaStepPlan resolve locals before source term) :
    KExpr .anon × InternTable .anon :=
  let walk := simulSubst step.rawBody step.consumed.reverse 0 before.env.intern
  internAppChain walk.1 (step.rawArguments.extract step.consumed.size step.rawArguments.size).toList walk.2

def result (step : BetaStepPlan resolve locals before source term) :
    KExpr .anon := step.output.1

def after (step : BetaStepPlan resolve locals before source term) :
    TcState .anon := { before with env := { before.env with intern := step.output.2 } }

def modelResult (step : BetaStepPlan resolve locals before source term) :
    AExpr β := AExpr.betaPrefix step.consumed.size (.lam step.condition step.domain step.inner) step.arguments

theorem entry (step : BetaStepPlan resolve locals before source term) : StructuralWhnfEntry source := by
  rw [step.sourceEq]
  exact .beta step.spine

theorem run (step : BetaStepPlan resolve locals before source term)
    (reductionFuel : Nat) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
      .ok (.next step.result) step.after := by
  simp only [step.sourceEq]
  apply RecM.whnfCoreWithFlagsStep_betaMany step.spine rfl step.peeling step.nonempty rfl
  rw [RecM.finishAppResult_eq_internAppChain]
  rfl

theorem sourceReading
    (step : BetaStepPlan resolve locals before source term) :
    readScopedExpr? resolve locals source = some term.erase := by
  simp only [step.sourceEq, step.modelSource]
  exact readScopedExpr?_collectSpine step.spine step.headReads step.argumentReads

theorem reading
    (step : BetaStepPlan resolve locals before source term)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals step.result = some step.modelResult.erase ∧ step.after.env.intern.WF :=
  step.toBetaPrefixPlan.reading coherent

theorem counts (plan : BetaStepPlan resolve locals before source term) :
    plan.consumed.size ≤ plan.inner.lambdaDepth + 1 ∧ plan.consumed.size ≤ plan.arguments.length :=
  plan.toBetaPrefixPlan.counts

end BetaStepPlan

mutual

/-- A finite structural-WHNF path. Its fuel is the actual method-table depth;
recursive head calls run at the predecessor depth and retain their cache effects. -/
inductive BetaWhnfTrace {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) :
    Nat → WhnfFlags → Nat → TcState .anon → KExpr .anon → AExpr β → TcState .anon → KExpr .anon → AExpr β → Type u
  | done {fuel flags before source term}
      (finished : (RecM.whnfCoreWithFlagsStep source flags).run (methodsN fuel) before =
        .ok (.done source) before) :
      BetaWhnfTrace resolve locals fuel flags 0 before source term before source term
  | next {fuel flags steps before after source result term target}
      (plan : BetaStepPlan resolve locals before source term)
      (rest : BetaWhnfTrace resolve locals (fuel + 1) flags
        steps plan.after plan.result plan.modelResult after result target) :
      BetaWhnfTrace resolve locals (fuel + 1) flags (steps + 1) before source term after result target
  | zeta {fuel flags steps before after source result term target}
      (plan : LetStepPlan before source)
      (rest : BetaWhnfTrace resolve locals fuel flags
        steps plan.after plan.result term after result target) :
      BetaWhnfTrace resolve locals fuel flags (steps + 1) before source term after result target
  | head {fuel flags steps before middle after source result term target}
      (plan : BetaHeadStepPlan resolve locals middle source term)
      (call : BetaHeadReduction resolve locals fuel flags
        before plan.rawHead plan.headTerm middle plan.rawLambda plan.modelLambda)
      (rest : BetaWhnfTrace resolve locals (fuel + 1) flags
        steps plan.after plan.result plan.modelResult after result target) :
      BetaWhnfTrace resolve locals (fuel + 1) flags (steps + 1) before source term after result target

/-- A recursive structural head call, including its full/cheap cache lookup.
A retained hit carries the producing call, so its meaning can be reconstructed. -/
inductive BetaHeadReduction {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId) :
    Nat → WhnfFlags → TcState .anon → KExpr .anon → AExpr β → TcState .anon → KExpr .anon → AExpr β → Type u
  | reduce {fuel flags steps before reduced source result term target}
      (path : BetaWhnfTrace resolve locals fuel flags steps
        (betaWhnfKey source before).2 source term reduced result target)
      (moving : 0 < steps)
      (enough : steps < maxWhnfCoreFuel.toNat)
      (miss : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = none) :
      BetaHeadReduction resolve locals fuel flags before source term
        (BetaCoreCache.write flags (betaWhnfKey source before).1 result reduced) result target
  | cached {fuel flags before source result term target originFuel originBefore originAfter}
      (origin : BetaHeadReduction resolve locals originFuel flags originBefore source term originAfter result target)
      (coherent : originBefore.env.intern.WF)
      (hit : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = some result) :
      BetaHeadReduction resolve locals fuel flags before source term (betaWhnfKey source before).2 result target

end

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

theorem BetaWhnfTrace.first {reductionFuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target) :
    0 < steps → StructuralWhnfEntry source :=
  match trace with
  | .done _ => fun impossible => False.elim (Nat.not_lt_zero _ impossible)
  | .next plan _ => fun _ => plan.entry
  | .zeta plan _ => fun _ => plan.entry
  | .head plan _ _ => fun _ => plan.entry

theorem BetaHeadReduction.entry {reductionFuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals reductionFuel flags before source term after result target) :
    StructuralWhnfEntry source :=
  match call with
  | .reduce path moving .. => path.first moving
  | .cached origin .. => origin.entry

mutual

theorem BetaWhnfTrace.run {reductionFuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target)
    {loopFuel : Nat} (enough : steps < loopFuel) :
    (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags) loopFuel source).run
      (methodsN reductionFuel) before = .ok result after :=
  match trace with
  | .done finished => by
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          rw [EStateM.bind, finished]
          rfl
  | .next step rest => by
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          rw [EStateM.bind, step.run _ flags]
          exact BetaWhnfTrace.run rest (by omega)
  | .zeta step rest => by
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          rw [EStateM.bind, step.run (methodsN reductionFuel) flags]
          exact BetaWhnfTrace.run rest (by omega)
  | .head plan call rest => by
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          rw [EStateM.bind, plan.run (BetaHeadReduction.run call)]
          exact BetaWhnfTrace.run rest (by omega)
termination_by structural trace

theorem BetaHeadReduction.run {reductionFuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals reductionFuel flags before source term after result target) :
    (RecM.whnfCoreWithFlags source flags).run (methodsN reductionFuel) before = .ok result after :=
  match call with
  | .reduce path moving enough miss => by
      exact BetaCoreCache.miss flags (path.first moving) miss (BetaWhnfTrace.run path enough)
  | .cached origin coherent hit => by exact BetaCoreCache.hit flags origin.entry hit
termination_by structural call

end

mutual

theorem BetaWhnfTrace.reading {reductionFuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ after.env.intern.WF :=
  match trace with
  | .done _ => by exact ⟨sourceReading, coherent⟩
  | .next step rest => by
      obtain ⟨reading, preserved⟩ := step.reading coherent
      exact BetaWhnfTrace.reading rest reading preserved
  | .zeta step rest => by
      obtain ⟨reading, preserved⟩ := step.reading sourceReading coherent
      exact BetaWhnfTrace.reading rest reading preserved
  | .head plan call rest => by
      obtain ⟨_, headCoherent⟩ := BetaHeadReduction.reading call plan.sourceHeadReads coherent
      obtain ⟨reading, preserved⟩ := plan.reading headCoherent
      exact BetaWhnfTrace.reading rest reading preserved
termination_by structural trace

theorem BetaHeadReduction.reading {reductionFuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals reductionFuel flags before source term after result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ after.env.intern.WF :=
  match call with
  | .reduce path moving enough miss => by
      obtain ⟨reads, preserved⟩ := BetaWhnfTrace.reading path sourceReading ((betaWhnfKey_environment _ _).symm ▸ coherent)
      exact ⟨reads, (BetaCoreCache.intern _ _ _ _).symm ▸ preserved⟩
  | .cached origin initial hit => by
      exact ⟨(BetaHeadReduction.reading origin sourceReading initial).1, (betaWhnfKey_environment _ _).symm ▸ coherent⟩
termination_by structural call

end

mutual

/-- Recursive structural reduction preserves inference state and every
surrounding cache key while retaining the actual head-call cache writes. -/
theorem BetaWhnfTrace.frame {reductionFuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target) :
    BetaCacheFrame before after :=
  match trace with
  | .done _ => by exact .refl _
  | .next step rest => by exact (BetaCacheFrame.intern _ _).trans (BetaWhnfTrace.frame rest)
  | .zeta step rest => by exact (BetaCacheFrame.intern _ _).trans (BetaWhnfTrace.frame rest)
  | .head plan call rest => by exact (BetaHeadReduction.frame call).trans ((BetaCacheFrame.intern _ _).trans (BetaWhnfTrace.frame rest))
termination_by structural trace

theorem BetaHeadReduction.frame {reductionFuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals reductionFuel flags before source term after result target) :
    BetaCacheFrame before after :=
  match call with
  | .reduce path moving enough miss => by
      exact (BetaCacheFrame.key _ _).trans ((BetaWhnfTrace.frame path).trans (BetaCoreCache.frame _ _ _ _))
  | .cached .. => by exact .key _ _
termination_by structural call

end

end Ix.Kernel.Consistency
