/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaStepConstruction
import Ix.Kernel.Verify.Consistency.BetaHeadConstruction
import Ix.Kernel.Verify.Consistency.BetaHeadOrigin
import Ix.Kernel.Verify.Consistency.BetaCacheExecution
import Ix.Kernel.Verify.Whnf.Driver.Success

/-! Recover finite beta/let traces from actual successful WHNF runs. Branch
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

def selected (source : KExpr .anon) : Bool :=
  BetaStepSource.selected source || LetStepSource.selected source || BetaHeadStepSource.selected source

theorem selected_entry {source : KExpr .anon} (chosen : selected source = true) : StructuralWhnfEntry source := by
  by_cases beta : BetaStepSource.selected source = true
  · exact BetaStepSource.selected_entry beta
  · by_cases zeta : LetStepSource.selected source = true
    · exact LetStepSource.selected_entry zeta
    · exact BetaHeadStepSource.selected_entry (by simpa [selected, beta, zeta] using chosen)

/-- Raw resources follow actual method depth and loop fuel. Hits retain an
earlier producing call independently of its annotations; a head miss gets its
own bounded orbit. Successful callbacks require finite beta continuation
resources, without an intermediate inference or semantic typing premise. -/
def Resources {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (reductionFuel : Nat) (flags : WhnfFlags) (loopFuel : Nat)
    (before : TcState .anon) (source : KExpr .anon) : Prop :=
  match loopFuel with
  | 0 => True
  | loopFuel + 1 =>
      if BetaStepSource.selected source then
        BetaStepSource.Resources source before ∧
          Resources resolve locals reductionFuel flags loopFuel (BetaStepSource.after source before) (BetaStepSource.output source before).1
      else if LetStepSource.selected source then
        LetStepSource.Resources source before ∧
          Resources resolve locals reductionFuel flags loopFuel (LetStepSource.after source before) (LetStepSource.output source before).1
      else if BetaHeadStepSource.selected source then
        match reductionFuel with
        | 0 => True
        | fuel + 1 =>
            HeadOrigins (β := β) flags before source.collectSpine.1 ∧
            (BetaCoreCache.lookup flags (betaWhnfKey source.collectSpine.1 before).1
                (betaWhnfKey source.collectSpine.1 before).2 = none →
              Resources resolve locals fuel flags maxWhnfCoreFuel.toNat (betaWhnfKey source.collectSpine.1 before).2 source.collectSpine.1) ∧
            ∀ head middle,
              (RecM.whnfCoreWithFlags source.collectSpine.1 flags).run (methodsN fuel) before = .ok head middle →
                BetaPrefixSource.selected head = true ∧
                BetaPrefixSource.Resources head source.collectSpine.2 middle ∧
                Resources resolve locals (fuel + 1) flags loopFuel (BetaPrefixSource.after head source.collectSpine.2 middle)
                  (BetaPrefixSource.output head source.collectSpine.2 middle).1
      else BetaWhnfTerminal source
termination_by (reductionFuel, loopFuel)

theorem Resources.first {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {reductionFuel fuel : Nat} {flags : WhnfFlags} {before : TcState .anon} {source : KExpr .anon}
    (resources : Resources resolve locals reductionFuel flags fuel before source) (positive : 0 < fuel)
    (chosen : BetaStepSource.selected source = true) : BetaStepSource.Resources source before := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      rw [Resources.eq_def] at resources
      exact (show BetaStepSource.Resources source before ∧
        Resources resolve locals reductionFuel flags fuel (BetaStepSource.after source before) (BetaStepSource.output source before).1 from by
          simpa only [chosen, if_true] using resources).1

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
  moving : selected source = true → 0 < steps

/-- Successful execution determines both nested head calls and the outer
path. Each recursive callback uses the predecessor method table. -/
noncomputable def construct {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {reductionFuel loopFuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (resources : Resources resolve locals reductionFuel flags loopFuel before source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags)
      loopFuel source).run (methodsN reductionFuel) before = .ok result after) :
    Witness resolve locals reductionFuel loopFuel flags before source term result after := by
  cases loopFuel with
  | zero => cases accepted
  | succ loopFuel =>
      rw [Resources.eq_def] at resources
      by_cases chosen : BetaStepSource.selected source = true
      · cases reductionFuel with
        | zero =>
            exfalso
            obtain ⟨fn, arg, info, rfl⟩ := BetaStepSource.selected_app chosen
            obtain ⟨_, _, impossible⟩ := BetaHeadStepSource.head_of_success accepted
            cases impossible
        | succ fuel =>
            have data : BetaStepSource.Resources source before ∧
                Resources resolve locals (fuel + 1) flags loopFuel (BetaStepSource.after source before) (BetaStepSource.output source before).1 := by
              simpa only [chosen, if_true] using resources
            let first := BetaStepSource.construct chosen reading data.1
            have nextResources : Resources resolve locals (fuel + 1) flags loopFuel first.1.after first.1.result := by
              simpa only [first, BetaStepSource.construct_after, BetaStepSource.construct_result] using data.2
            obtain ⟨nextReading, nextCoherent⟩ := first.1.reading coherent
            rw [RecM.runBounded, ReaderT.run_bind] at accepted
            change EStateM.bind ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before = _ at accepted
            rw [EStateM.bind, first.1.run fuel flags] at accepted
            let rest := construct nextResources nextReading nextCoherent accepted
            exact ⟨rest.steps + 1, rest.target, .next first.1 rest.trace,
              Nat.add_lt_add_right rest.enough 1, rest.terminal, fun _ => Nat.zero_lt_succ _⟩
      · by_cases zeta : LetStepSource.selected source = true
        · have data : LetStepSource.Resources source before ∧
              Resources resolve locals reductionFuel flags loopFuel (LetStepSource.after source before) (LetStepSource.output source before).1 := by
            simpa [chosen, zeta] using resources
          let first := LetStepSource.construct zeta data.1
          have nextResources : Resources resolve locals reductionFuel flags loopFuel first.1.after first.1.result := by
            simpa only [first, LetStepSource.construct_after, LetStepSource.construct_result] using data.2
          obtain ⟨nextReading, nextCoherent⟩ := first.1.reading reading coherent
          rw [RecM.runBounded, ReaderT.run_bind] at accepted
          change EStateM.bind ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before = _ at accepted
          rw [EStateM.bind, first.1.run (methodsN reductionFuel) flags] at accepted
          let rest := construct nextResources nextReading nextCoherent accepted
          exact ⟨rest.steps + 1, rest.target, .zeta first.1 rest.trace,
            Nat.add_lt_add_right rest.enough 1, rest.terminal, fun _ => Nat.zero_lt_succ _⟩
        · by_cases headed : BetaHeadStepSource.selected source = true
          · cases reductionFuel with
            | zero =>
                exfalso
                obtain ⟨fn, arg, info, rfl⟩ := BetaHeadStepSource.selected_app headed
                obtain ⟨_, _, impossible⟩ := BetaHeadStepSource.head_of_success accepted
                cases impossible
            | succ fuel =>
                have data :
                    HeadOrigins (β := β) flags before source.collectSpine.1 ∧
                    (BetaCoreCache.lookup flags (betaWhnfKey source.collectSpine.1 before).1
                        (betaWhnfKey source.collectSpine.1 before).2 = none →
                      Resources resolve locals fuel flags maxWhnfCoreFuel.toNat
                        (betaWhnfKey source.collectSpine.1 before).2 source.collectSpine.1) ∧
                    ∀ head middle,
                      (RecM.whnfCoreWithFlags source.collectSpine.1 flags).run (methodsN fuel) before = .ok head middle →
                        BetaPrefixSource.selected head = true ∧
                        BetaPrefixSource.Resources head source.collectSpine.2 middle ∧
                        Resources resolve locals (fuel + 1) flags loopFuel (BetaPrefixSource.after head source.collectSpine.2 middle)
                          (BetaPrefixSource.output head source.collectSpine.2 middle).1 := by
                  simpa [chosen, zeta, headed] using resources
                have headChosen := BetaHeadStepSource.selected_head headed
                have headEntry := LetStepSource.selected_entry headChosen
                have parsed := AppSpineSource.reading reading
                have headCoherent : (betaWhnfKey source.collectSpine.1 before).2.env.intern.WF :=
                  (betaWhnfKey_environment _ _).symm ▸ coherent
                cases called : (RecM.whnfCoreWithFlags source.collectSpine.1 flags).run (methodsN fuel) before with
                | error error failed =>
                    exfalso
                    obtain ⟨fn, arg, info, rfl⟩ := BetaHeadStepSource.selected_app headed
                    obtain ⟨_, _, success⟩ := BetaHeadStepSource.head_of_success accepted
                    change (RecM.whnfCoreWithFlags (KExpr.app fn arg info).collectSpine.1 flags).run
                      (methodsN fuel) before = _ at success
                    rw [called] at success
                    cases success
                | ok head middle =>
                    have tailData := data.2.2 head middle called
                    let retained : Σ target, BetaHeadReduction resolve locals fuel flags before
                        source.collectSpine.1 (AppSpineSource.parts source term).1 middle head target := by
                      cases observed : BetaCoreCache.lookup flags (betaWhnfKey source.collectSpine.1 before).1
                          (betaWhnfKey source.collectSpine.1 before).2 with
                      | some cached =>
                          let call := data.1.replay (fuel := fuel) parsed.2.1 observed
                          have same := call.2.run
                          rw [called] at same
                          obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj same
                          exact call
                      | none =>
                          cases rawRun : (RecM.whnfCoreWithFlagsUncached source.collectSpine.1 flags).run
                              (methodsN fuel) (betaWhnfKey source.collectSpine.1 before).2 with
                          | error error failed =>
                              exfalso
                              obtain ⟨_, success, _⟩ := BetaCoreCache.miss_success flags headEntry observed called
                              rw [rawRun] at success
                              cases success
                          | ok returned rawAfter =>
                              let headPath := construct (data.2.1 observed) parsed.2.1 headCoherent rawRun
                              have moving : selected source.collectSpine.1 = true := by
                                simp [selected, headChosen]
                              let call := BetaHeadReduction.reduce headPath.trace
                                (headPath.moving moving) headPath.enough observed
                              have same := call.run
                              rw [called] at same
                              obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj same
                              exact ⟨headPath.target, call⟩
                    let call := retained.2
                    have headReading := (call.reading parsed.2.1 coherent).1
                    let built := BetaHeadStepSource.construct headed reading tailData.1 headReading tailData.2.1
                    have aligned : BetaHeadReduction resolve locals fuel flags before built.plan.rawHead built.plan.headTerm
                        middle built.plan.rawLambda built.plan.modelLambda := by
                      rw [built.sourceHead, built.sourceTerm, built.resultHead, built.resultTerm]
                      exact call
                    have nextResources : Resources resolve locals (fuel + 1) flags loopFuel built.plan.after built.plan.result := by
                      simpa only [built.after, built.result] using tailData.2.2
                    obtain ⟨nextReading, nextCoherent⟩ := built.plan.reading (call.reading parsed.2.1 coherent).2
                    rw [RecM.runBounded, ReaderT.run_bind] at accepted
                    change EStateM.bind ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before = _ at accepted
                    rw [EStateM.bind, built.plan.run aligned.run] at accepted
                    let rest := construct nextResources nextReading nextCoherent accepted
                    exact ⟨rest.steps + 1, rest.target, .head built.plan aligned rest.trace,
                      Nat.add_lt_add_right rest.enough 1, rest.terminal, fun _ => Nat.zero_lt_succ _⟩
          · have terminal : BetaWhnfTerminal source := by
              simpa [chosen, zeta, headed] using resources
            have finished := terminal.core_step (methodsN reductionFuel) before flags
            rw [RecM.runBounded, ReaderT.run_bind] at accepted
            change EStateM.bind ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before = _ at accepted
            rw [EStateM.bind, finished] at accepted
            obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj accepted
            exact ⟨0, term, .done finished, Nat.zero_lt_succ _, terminal,
              fun impossible => by simp [selected, chosen, zeta, headed] at impossible⟩
termination_by (reductionFuel, loopFuel)
decreasing_by all_goals simp_wf; omega

end BetaWhnfSource

/-- A successful structural call constructs its provenance at the actual
method depth, including zero-depth hits and let-only misses. -/
theorem BetaHeadReduction.exists_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (origins : BetaWhnfSource.HeadOrigins (β := β) flags before source)
    (cold : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = none →
      BetaWhnfSource.Resources resolve locals fuel flags maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfCoreWithFlags source flags).run (methodsN fuel) before = .ok result after) :
    ∃ target, Nonempty (BetaHeadReduction resolve locals fuel flags before source term after result target) := by
  cases observed : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 with
  | some cached =>
      let call := origins.replay (fuel := fuel) reading observed
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (call.2.run.symm.trans accepted)
      exact ⟨call.1, ⟨call.2⟩⟩
  | none =>
      obtain ⟨reduced, rawRun, afterEq⟩ :=
        BetaCoreCache.miss_success flags (BetaWhnfSource.selected_entry chosen) observed accepted
      let path := BetaWhnfSource.construct (cold observed) reading ((betaWhnfKey_environment _ _).symm ▸ coherent) rawRun
      let call := BetaHeadReduction.reduce path.trace (path.moving chosen) path.enough observed
      exact ⟨path.target, afterEq.symm ▸ Nonempty.intro call⟩

/-- Provenance for a newly published entry follows from its successful
production call, without a current-annotation equality premise. -/
theorem BetaWhnfSource.HeadOrigins.of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (origins : BetaWhnfSource.HeadOrigins (β := β) flags before source)
    (cold : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = none →
      BetaWhnfSource.Resources resolve locals fuel flags maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfCoreWithFlags source flags).run (methodsN fuel) before = .ok result after) :
    BetaWhnfSource.HeadOrigins (β := β) flags after source := by
  obtain ⟨target, ⟨call⟩⟩ := BetaHeadReduction.exists_of_success chosen origins cold reading coherent accepted
  exact .ofCall call coherent

/-- Successful structural WHNF on a miss supplies the uncached execution,
then source reconstruction supplies the full reduction and cache witness. -/
theorem BetaCoreExecution.exists_of_miss_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (resources : BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (miss : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = none)
    (accepted : (RecM.whnfCore source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaCoreExecution resolve locals fuel before source term result target,
      execution.after = after := by
  let first := BetaWhnfSource.selected_entry chosen
  have entry : RecM.whnfCore source = RecM.whnfCoreWithFlagsNonLeaf source .FULL := first.core .FULL
  rw [entry] at accepted
  obtain ⟨reduced, rawRun, afterEq⟩ := RecM.whnfCoreWithFlagsNonLeaf_fullMiss_success rfl
    (betaWhnfKey_run source before) (first.not_transient _ _) miss accepted
  have initial : (betaWhnfKey source before).2.env.intern.WF := by
    simpa only [betaWhnfKey_environment] using coherent
  let reconstructed := BetaWhnfSource.construct resources reading initial rawRun
  let execution : BetaCoreExecution resolve locals fuel before source term result reconstructed.target :=
    .reduce reconstructed.trace (reconstructed.moving chosen) reconstructed.enough miss reconstructed.terminal
  exact ⟨reconstructed.target, execution, afterEq.symm⟩

end Ix.Kernel.Consistency
