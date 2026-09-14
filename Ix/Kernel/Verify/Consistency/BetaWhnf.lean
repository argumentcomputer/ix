/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTrace

/-! Finite beta traces for the actual structural-WHNF loop. Every next
state is computed by production's simultaneous substitution and suffix
interning, and the loop consumes the same fuel as `runBounded`. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Resources for one actual beta iteration. The raw output and next
state are computed below; no result reading or semantic equality is a field. -/
structure SynthesisBetaStep {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term type : AExpr β) where
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
  meaning : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term
    (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments) type
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

namespace SynthesisBetaStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
  {incomingBounds : List VLevel} {locals : List FVarId} {before : TcState .anon}
  {source : KExpr .anon} {term type : AExpr β}

def output (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    KExpr .anon × InternTable .anon :=
  let walk := simulSubst step.rawBody step.consumed.reverse 0 before.env.intern
  internAppChain walk.1 (step.rawArguments.extract step.consumed.size step.rawArguments.size).toList walk.2

def result (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    KExpr .anon := step.output.1

def after (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    TcState .anon := { before with env := { before.env with intern := step.output.2 } }

def modelResult (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    AExpr β := AExpr.betaPrefix step.consumed.size (.lam step.condition step.domain step.inner) step.arguments

theorem run (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
    (reductionFuel : Nat) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
      .ok (.next step.result) step.after := by
  simp only [step.sourceEq]
  apply RecM.whnfCoreWithFlagsStep_betaMany step.spine rfl step.peeling step.nonempty rfl
  rw [RecM.finishAppResult_eq_internAppChain]
  rfl

theorem sourceReading
    (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    readScopedExpr? resolve locals source = some term.erase := by
  simp only [step.sourceEq, step.modelSource]
  exact readScopedExpr?_collectSpine step.spine step.headReads step.argumentReads

theorem reading
    (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
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

end SynthesisBetaStep

/-- A complete finite beta path through structural WHNF. The final
iteration returns its input; every preceding iteration has a computed
substitution result and intern table, with no postulated intermediate check. -/
inductive SynthesisBetaWhnfTrace {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β) (locals : List FVarId)
    (reductionFuel : Nat) (flags : WhnfFlags) :
    Nat → TcState .anon → KExpr .anon → AExpr β → TcState .anon → KExpr .anon → AExpr β → Type u
  | done {before source term}
      (finished : (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
        .ok (.done source) before) :
      SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
        0 before source term before source term
  | next {steps before after source result term target type}
      (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
      (rest : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
        steps step.after step.result step.modelResult after result target) :
      SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
        (steps + 1) before source term after result target

namespace SynthesisBetaWhnfTrace

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
  {incomingBounds : List VLevel} {locals : List FVarId} {reductionFuel steps : Nat} {flags : WhnfFlags}
  {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}

def toBetaTrace {steps : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) {type : AExpr β}
    (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term target type :=
  match trace with
  | .done _ => .refl origin
  | .next step rest =>
      let first := SynthesisBetaTrace.atType origin step.meaning
      first.trans (rest.toBetaTrace (.reduced first))
termination_by structural trace

theorem run
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) {loopFuel : Nat} (enough : steps < loopFuel) :
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

theorem reading
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ after.env.intern.WF := by
  induction trace with
  | done => exact ⟨sourceReading, coherent⟩
  | next step rest ih =>
      obtain ⟨reading, preserved⟩ := step.reading coherent
      exact ih reading preserved

/-- The production loop returns the final beta result with the original
source's type and a coherent intern table. The finite path uses the real
loop bound and the same recursive method table at every iteration. -/
theorem uncached_sound
    (trace : SynthesisBetaWhnfTrace resolve incoming incomingContext incomingBounds entries context locals reductionFuel flags
      steps before source term after result target) {type : AExpr β}
    (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (enough : steps < maxWhnfCoreFuel.toNat) :
    (RecM.whnfCoreWithFlagsUncached source flags).run (methodsN (reductionFuel + 1)) before = .ok result after ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧ TypingClaim.{u,v} entries context target type ∧
      after.env.intern.WF := by
  obtain ⟨reading, preserved⟩ := trace.reading sourceReading coherent
  obtain ⟨converted, typed⟩ := (trace.toBetaTrace origin).sound formed
  exact ⟨trace.run enough, reading, converted, typed, preserved⟩

end SynthesisBetaWhnfTrace
end Ix.Kernel.Consistency
