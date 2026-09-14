/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaStepConstruction
import Ix.Kernel.Verify.Consistency.BetaCacheExecution
import Ix.Kernel.Verify.Whnf.Driver.Success

/-! Recover finite beta traces from actual successful WHNF runs. Branch
coverage and finite representation data concern only computed raw syntax;
the execution supplies termination and the returned expression and state. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

theorem BetaWhnfTerminal.core_step {source : KExpr .anon} (terminal : BetaWhnfTerminal source)
    (methods : Methods .anon) (before : TcState .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run methods before = .ok (.done source) before := by
  cases terminal <;> rfl

namespace BetaWhnfSource

/-- At each computed beta step, retain only finite walker and hash bounds.
A non-beta branch must be one of the supported terminal constructors. The
zero-fuel case requires no successful result; success is supplied separately
by the actual production run. -/
def Resources : Nat → TcState .anon → KExpr .anon → Prop
  | 0, _, _ => True
  | fuel + 1, before, source =>
      if BetaStepSource.selected source then
        BetaStepSource.Resources source before ∧
          Resources fuel (BetaStepSource.after source before) (BetaStepSource.output source before).1
      else BetaWhnfTerminal source

theorem Resources.first {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    (resources : Resources fuel before source) (positive : 0 < fuel)
    (chosen : BetaStepSource.selected source = true) : BetaStepSource.Resources source before := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      exact (show BetaStepSource.Resources source before ∧
        Resources fuel (BetaStepSource.after source before) (BetaStepSource.output source before).1 from by
          simpa only [Resources, chosen, if_true] using resources).1

/-- The annotation and iteration count are outputs of reconstruction.
The trace's endpoints are the actual result and state of the bounded run. -/
structure Witness {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (reductionFuel loopFuel : Nat) (flags : WhnfFlags) (before : TcState .anon)
    (source : KExpr .anon) (term : AExpr β) (result : KExpr .anon) (after : TcState .anon) where
  steps : Nat
  target : AExpr β
  trace : BetaWhnfTrace resolve locals reductionFuel flags steps before source term after result target
  enough : steps < loopFuel
  terminal : BetaWhnfTerminal result
  moving : BetaStepSource.selected source = true → 0 < steps

/-- Successful execution determines the complete raw trace. No intermediate
readings, model expressions, step equations, or iteration count are inputs. -/
def construct {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {reductionFuel loopFuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (resources : Resources loopFuel before source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags)
      loopFuel source).run (methodsN (reductionFuel + 1)) before = .ok result after) :
    Witness resolve locals reductionFuel loopFuel flags before source term result after := by
  induction loopFuel generalizing before source term with
  | zero => cases accepted
  | succ loopFuel ih =>
      by_cases chosen : BetaStepSource.selected source = true
      · have data : BetaStepSource.Resources source before ∧
            Resources loopFuel (BetaStepSource.after source before) (BetaStepSource.output source before).1 := by
          simpa only [Resources, chosen, if_true] using resources
        let first := BetaStepSource.construct chosen reading data.1
        have nextResources : Resources loopFuel first.1.after first.1.result := by
          simpa only [first, BetaStepSource.construct_after, BetaStepSource.construct_result] using data.2
        obtain ⟨nextReading, nextCoherent⟩ := first.1.reading coherent
        rw [RecM.runBounded, ReaderT.run_bind] at accepted
        change EStateM.bind ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before = _ at accepted
        rw [EStateM.bind, first.1.run reductionFuel flags] at accepted
        let rest := ih nextResources nextReading nextCoherent accepted
        exact ⟨rest.steps + 1, rest.target, .next first.1 rest.trace,
          Nat.add_lt_add_right rest.enough 1, rest.terminal, fun _ => Nat.zero_lt_succ _⟩
      · have terminal : BetaWhnfTerminal source := by
          simpa [Resources, chosen] using resources
        have finished := terminal.core_step (methodsN (reductionFuel + 1)) before flags
        rw [RecM.runBounded, ReaderT.run_bind] at accepted
        change EStateM.bind ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before = _ at accepted
        rw [EStateM.bind, finished] at accepted
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj accepted
        exact ⟨0, term, .done finished, Nat.zero_lt_succ _, terminal,
          fun impossible => False.elim (chosen impossible)⟩

end BetaWhnfSource

/-- Successful structural WHNF on a miss supplies the uncached execution,
then source reconstruction supplies the full reduction and cache witness. -/
theorem BetaCoreExecution.exists_of_miss_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaStepSource.selected source = true)
    (resources : BetaWhnfSource.Resources maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (miss : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = none)
    (accepted : (RecM.whnfCore source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaCoreExecution resolve locals fuel before source term result target,
      execution.after = after := by
  let first := BetaStepSource.construct chosen reading (resources.first (by decide) chosen)
  have entry : RecM.whnfCore source = RecM.whnfCoreWithFlagsNonLeaf source .FULL := by
    rw [first.1.sourceEq]; rfl
  rw [entry] at accepted
  obtain ⟨reduced, rawRun, afterEq⟩ := RecM.whnfCoreWithFlagsNonLeaf_fullMiss_success rfl
    (betaWhnfKey_run source before) (first.1.not_transient _ _) miss accepted
  have initial : (betaWhnfKey source before).2.env.intern.WF := by
    simpa only [betaWhnfKey_environment] using coherent
  let reconstructed := BetaWhnfSource.construct resources reading initial rawRun
  let execution : BetaCoreExecution resolve locals fuel before source term result reconstructed.target :=
    .reduce reconstructed.trace (reconstructed.moving chosen) reconstructed.enough miss reconstructed.terminal
  exact ⟨reconstructed.target, execution, afterEq.symm⟩

end Ix.Kernel.Consistency
