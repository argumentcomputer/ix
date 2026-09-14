/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTrace
import Ix.Kernel.Verify.Consistency.BetaWhnfPlan

/-! Finite beta traces for the actual structural-WHNF loop. Every next
state is computed by production's simultaneous substitution and suffix
interning, and the loop consumes the same fuel as `runBounded`. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- A raw beta plan together with its derived source-checking evidence. -/
structure SynthesisBetaStep {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term type : AExpr β)
    extends BetaStepPlan resolve locals before source term where
  meaning : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term
    (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments) type

namespace SynthesisBetaStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
  {incomingBounds : List VLevel} {locals : List FVarId} {before : TcState .anon}
  {source : KExpr .anon} {term type : AExpr β}

def output (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.output

def result (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.result

def after (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.after

def modelResult (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :=
  step.toBetaStepPlan.modelResult

theorem run (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
    (reductionFuel : Nat) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (reductionFuel + 1)) before =
      .ok (.next step.result) step.after :=
  step.toBetaStepPlan.run reductionFuel flags

theorem sourceReading
    (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type) :
    readScopedExpr? resolve locals source = some term.erase :=
  step.toBetaStepPlan.sourceReading

theorem reading
    (step : SynthesisBetaStep resolve incoming incomingContext incomingBounds entries context locals before source term type)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals step.result = some step.modelResult.erase ∧ step.after.env.intern.WF :=
  step.toBetaStepPlan.reading coherent

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
