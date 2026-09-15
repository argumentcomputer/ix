/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaStepConstruction
import Ix.Kernel.Verify.Consistency.BetaHeadConstruction

/-! Recover fresh source annotations along an existing raw reduction.
Cache provenance concerns the actual expression and execution; the current
source check supplies annotations independently of the producing check. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

namespace BetaPrefixPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {before : TcState .anon}

theorem sourceResources (plan : BetaPrefixPlan resolve locals before) :
    BetaPrefixSource.Resources plan.rawLambda plan.rawArguments before := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [BetaPrefixSource.peeled, rawLambda, plan.peeling] using plan.walkerBounds
  · simpa only [BetaPrefixSource.peeled, rawLambda, plan.peeling] using plan.walkerFaithful
  · simpa only [BetaPrefixSource.substituted, BetaPrefixSource.peeled, rawLambda, plan.peeling] using plan.suffixFaithful

theorem sourceOutput (plan : BetaPrefixPlan resolve locals before) :
    plan.output = BetaPrefixSource.output plan.rawLambda plan.rawArguments before := by
  simp only [BetaPrefixSource.output, BetaPrefixSource.substituted, BetaPrefixSource.peeled,
    rawLambda, plan.peeling, output]

end BetaPrefixPlan

namespace BetaStepPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {before : TcState .anon} {source : KExpr .anon} {term : AExpr β}

theorem selected (plan : BetaStepPlan resolve locals before source term) : BetaStepSource.selected source = true := by
  simp only [plan.sourceEq, BetaStepSource.selected, plan.spine]

theorem sourceResources (plan : BetaStepPlan resolve locals before source term) :
    BetaStepSource.Resources source before := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [BetaStepSource.peeled, plan.sourceEq, plan.spine, plan.peeling] using plan.walkerBounds
  · simpa only [BetaStepSource.peeled, plan.sourceEq, plan.spine, plan.peeling] using plan.walkerFaithful
  · simpa only [BetaStepSource.substituted, BetaStepSource.peeled, plan.sourceEq, plan.spine, plan.peeling]
      using plan.suffixFaithful

theorem sourceOutput (plan : BetaStepPlan resolve locals before source term) :
    plan.output = BetaStepSource.output source before := by
  simp only [BetaStepSource.output, BetaStepSource.substituted, BetaStepSource.peeled,
    plan.sourceEq, plan.spine, plan.peeling, output]

theorem sourceAfter (plan : BetaStepPlan resolve locals before source term) :
    plan.after = BetaStepSource.after source before := by
  rw [after, BetaStepSource.after, plan.sourceOutput]

end BetaStepPlan

namespace BetaHeadStepPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {before : TcState .anon} {source : KExpr .anon} {term : AExpr β}

theorem sourceSpine (plan : BetaHeadStepPlan resolve locals before source term) :
    source.collectSpine = (plan.rawHead, plan.rawArguments) :=
  (congrArg KExpr.collectSpine plan.sourceEq).trans plan.spine

theorem sourceResources (plan : BetaHeadStepPlan resolve locals before source term) :
    BetaPrefixSource.Resources plan.rawLambda source.collectSpine.2 before := by
  rw [plan.sourceSpine]
  exact plan.toBetaPrefixPlan.sourceResources

theorem sourceOutput (plan : BetaHeadStepPlan resolve locals before source term) :
    plan.toBetaPrefixPlan.output = BetaPrefixSource.output plan.rawLambda source.collectSpine.2 before := by
  rw [plan.sourceSpine]
  exact plan.toBetaPrefixPlan.sourceOutput

theorem sourceAfter (plan : BetaHeadStepPlan resolve locals before source term) :
    plan.after = BetaPrefixSource.after plan.rawLambda source.collectSpine.2 before := by
  change {before with env := {before.env with intern := plan.toBetaPrefixPlan.output.2}} = _
  rw [plan.sourceOutput]
  rfl

end BetaHeadStepPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

mutual

/-- Fresh annotations are recovered from the current reading. The executed
expressions, intermediate states, method depth, and step count stay fixed. -/
def BetaWhnfTrace.reannotate {γ : Type v} {originResolve : Address → Option (ConstRef γ)}
    {originLocals : List FVarId} {fuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr γ}
    (trace : BetaWhnfTrace originResolve originLocals fuel flags steps before source term after result target)
    {current : AExpr β} (reading : readScopedExpr? resolve locals source = some current.erase)
    (coherent : before.env.intern.WF) :
    Σ output, BetaWhnfTrace resolve locals fuel flags steps before source current after result output :=
  match trace with
  | .done finished => ⟨current, .done finished⟩
  | .next plan rest => by
      let built := BetaStepSource.construct plan.selected reading plan.sourceResources
      have resultEq : built.1.result = plan.result :=
        (BetaStepSource.construct_result plan.selected reading plan.sourceResources).trans
          (congrArg Prod.fst plan.sourceOutput).symm
      have afterEq : built.1.after = plan.after :=
        (BetaStepSource.construct_after plan.selected reading plan.sourceResources).trans plan.sourceAfter.symm
      obtain ⟨nextReading, nextCoherent⟩ := built.1.reading coherent
      rw [resultEq] at nextReading
      rw [afterEq] at nextCoherent
      let remaining := BetaWhnfTrace.reannotate rest nextReading nextCoherent
      refine ⟨remaining.1, .next built.1 ?_⟩
      rw [afterEq, resultEq]
      exact remaining.2
  | .zeta plan rest => by
      obtain ⟨nextReading, nextCoherent⟩ := plan.reading reading coherent
      let remaining := BetaWhnfTrace.reannotate rest nextReading nextCoherent
      exact ⟨remaining.1, .zeta plan remaining.2⟩
  | .head (fuel := depth) (middle := middle) plan call rest => by
      have parsed := AppSpineSource.reading reading
      have headReading : readScopedExpr? resolve locals plan.rawHead =
          some (AppSpineSource.parts source current).1.erase := by
        simpa only [plan.sourceSpine] using parsed.2.1
      let head := BetaHeadReduction.reannotate call headReading coherent
      obtain ⟨returnedReading, headCoherent⟩ := head.2.reading headReading coherent
      let built := BetaHeadStepSource.constructOfEntry
        ⟨plan.rawFunction, plan.rawArgument, plan.appInfo, plan.sourceEq⟩
        (by rw [plan.sourceSpine]; exact plan.headEntry) reading
        (show BetaPrefixSource.selected plan.rawLambda = true from rfl)
        returnedReading plan.sourceResources
      have aligned : BetaHeadReduction resolve locals depth flags before built.plan.rawHead built.plan.headTerm
          middle built.plan.rawLambda built.plan.modelLambda := by
        rw [built.sourceHead, built.sourceTerm, built.resultHead, built.resultTerm, plan.sourceSpine]
        exact head.2
      have resultEq : built.plan.result = plan.result :=
        built.result.trans (congrArg Prod.fst plan.sourceOutput).symm
      have afterEq : built.plan.after = plan.after := built.after.trans plan.sourceAfter.symm
      obtain ⟨nextReading, nextCoherent⟩ := built.plan.reading headCoherent
      rw [resultEq] at nextReading
      rw [afterEq] at nextCoherent
      let remaining := BetaWhnfTrace.reannotate rest nextReading nextCoherent
      refine ⟨remaining.1, .head built.plan aligned ?_⟩
      rw [afterEq, resultEq]
      exact remaining.2
termination_by structural trace

/-- A retained producing call can be reused with the annotations recovered
from any current reading of its exact source expression. -/
def BetaHeadReduction.reannotate {γ : Type v} {originResolve : Address → Option (ConstRef γ)}
    {originLocals : List FVarId} {fuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr γ}
    (call : BetaHeadReduction originResolve originLocals fuel flags before source term after result target)
    {current : AExpr β} (reading : readScopedExpr? resolve locals source = some current.erase)
    (coherent : before.env.intern.WF) :
    Σ output, BetaHeadReduction resolve locals fuel flags before source current after result output :=
  match call with
  | .reduce path moving enough miss =>
      let rebuilt := BetaWhnfTrace.reannotate path reading ((betaWhnfKey_environment _ _).symm ▸ coherent)
      ⟨rebuilt.1, .reduce rebuilt.2 moving enough miss⟩
  | .cached origin initial hit =>
      let rebuilt := BetaHeadReduction.reannotate origin reading initial
      ⟨rebuilt.1, .cached rebuilt.2 initial hit⟩
termination_by structural call

end

end Ix.Kernel.Consistency
