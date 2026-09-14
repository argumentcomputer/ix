/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SpineReading
import Ix.Kernel.Verify.Consistency.LetWhnfPlan

/-! Raw beta and explicit-let paths compute production results and states independently of
the source-inference and semantic-origin derivations. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Resources for one actual beta iteration. The raw output and next
state are computed below; no typing, reduction origin, or result reading is a field. -/
structure BetaStepPlan {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term : AExpr β) where
  rawFunction : KExpr .anon
  rawArgument : KExpr .anon
  appInfo : ExprInfo .anon
  sourceEq : source = .app rawFunction rawArgument appInfo
  name : Mode.anon.F Name
  bi : Mode.anon.F Lean.BinderInfo
  rawDomain : KExpr .anon
  rawInner : KExpr .anon
  lambdaInfo : ExprInfo .anon
  rawArguments : Array (KExpr .anon)
  rawBody : KExpr .anon
  consumed : Array (KExpr .anon)
  condition : Certified.PropWhen
  domain : AExpr β
  inner : AExpr β
  arguments : List (AExpr β)
  modelSource : term = (AExpr.lam condition domain inner).appN arguments
  spine : (KExpr.app rawFunction rawArgument appInfo).collectSpine =
    (.lam name bi rawDomain rawInner lambdaInfo, rawArguments)
  headReads : readScopedExpr? resolve locals (.lam name bi rawDomain rawInner lambdaInfo) =
    some (AExpr.lam condition domain inner).erase
  argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) = arguments.map (some ·.erase)
  peeling : RecM.consumeBetaLams (.lam name bi rawDomain rawInner lambdaInfo) rawArguments = (rawBody, consumed)
  nonempty : (!consumed.isEmpty) = true
  walkerBounds : SimulSubstBounds rawBody consumed.reverse 0
  walkerFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
    KExpr.SimulSubstReach consumed.reverse rawBody 0 term
  suffixFaithful : KExpr.CollisionFree fun term =>
    (simulSubst rawBody consumed.reverse 0 before.env.intern).2.ExprSupport term ∨
      term ∈ cheapBetaChainList (simulSubst rawBody consumed.reverse 0 before.env.intern).1
        (rawArguments.extract consumed.size rawArguments.size).toList

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
    readScopedExpr? resolve locals step.result = some step.modelResult.erase ∧ step.after.env.intern.WF := by
  obtain ⟨result, after, run, reading, _, preserved⟩ := beta_many_step_readScopedExpr?
    step.spine step.headReads step.argumentReads step.peeling step.nonempty before 0 .FULL
    step.walkerBounds coherent step.walkerFaithful step.suffixFaithful
  have actual := step.run 0 .FULL
  simp only [step.sourceEq] at actual
  rw [actual] at run
  cases run
  exact ⟨reading, preserved⟩

theorem counts (plan : BetaStepPlan resolve locals before source term) :
    plan.consumed.size ≤ plan.inner.lambdaDepth + 1 ∧ plan.consumed.size ≤ plan.arguments.length := by
  obtain ⟨peeled, _, rawBound⟩ := RecM.BetaPeel.of_consume plan.peeling
  obtain ⟨_, modelPeel, _⟩ := betaPeel_readScopedExpr? peeled plan.headReads
  have sizeAgrees : plan.rawArguments.size = plan.arguments.length := by
    have lengths := congrArg List.length plan.argumentReads
    simpa using lengths
  exact ⟨by simpa only [Array.length_toList, AExpr.lambdaDepth] using modelPeel.length_bound,
    sizeAgrees ▸ rawBound⟩

end BetaStepPlan

/-- A finite production path without semantic step origins. All intermediate
expressions and states are computed by its raw beta and let plans. -/
inductive BetaWhnfTrace {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (reductionFuel : Nat) (flags : WhnfFlags) :
    Nat → TcState .anon → KExpr .anon → AExpr β → TcState .anon → KExpr .anon → AExpr β → Type u
  | done {before source term}
      (finished : (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
        .ok (.done source) before) :
      BetaWhnfTrace resolve locals reductionFuel flags 0 before source term before source term
  | next {steps before after source result term target}
      (plan : BetaStepPlan resolve locals before source term)
      (rest : BetaWhnfTrace resolve locals reductionFuel flags
        steps plan.after plan.result plan.modelResult after result target) :
      BetaWhnfTrace resolve locals reductionFuel flags (steps + 1) before source term after result target
  | zeta {steps before after source result term target}
      (plan : LetStepPlan before source)
      (rest : BetaWhnfTrace resolve locals reductionFuel flags
        steps plan.after plan.result term after result target) :
      BetaWhnfTrace resolve locals reductionFuel flags (steps + 1) before source term after result target

namespace BetaWhnfTrace

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {reductionFuel steps : Nat} {flags : WhnfFlags} {before after : TcState .anon}
  {source result : KExpr .anon} {term target : AExpr β}

theorem run
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target)
    {loopFuel : Nat} (enough : steps < loopFuel) :
    (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags) loopFuel source).run
      (methodsN (reductionFuel + 1)) before = .ok result after := by
  induction trace generalizing loopFuel with
  | done finished =>
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          unfold EStateM.bind
          rw [finished]
          rfl
  | next step rest ih =>
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          unfold EStateM.bind
          rw [step.run reductionFuel flags]
          exact ih (by omega)
  | zeta step rest ih =>
      cases loopFuel with
      | zero => omega
      | succ loopFuel =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep _ flags).run _) _ _ = _
          unfold EStateM.bind
          rw [step.run (methodsN (reductionFuel + 1)) flags]
          exact ih (by omega)

theorem reading
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ after.env.intern.WF := by
  induction trace with
  | done => exact ⟨sourceReading, coherent⟩
  | next step rest ih =>
      obtain ⟨reading, preserved⟩ := step.reading coherent
      exact ih reading preserved
  | zeta step rest ih =>
      obtain ⟨reading, preserved⟩ := step.reading sourceReading coherent
      exact ih reading preserved

/-- A beta/let path changes only the intern table. All cache partitions,
locals, checking policies, and instrumentation fields retain their values. -/
theorem frame
    (trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target) :
    ∃ table, after = { before with env := { before.env with intern := table } } := by
  induction trace with
  | done => exact ⟨_, rfl⟩
  | next step rest ih =>
      obtain ⟨table, same⟩ := ih
      exact ⟨table, same⟩
  | zeta step rest ih =>
      obtain ⟨table, same⟩ := ih
      exact ⟨table, same⟩

end BetaWhnfTrace

end Ix.Kernel.Consistency
