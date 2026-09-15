/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaPrefixPlan
import Ix.Kernel.Verify.Consistency.StructuralWhnfEntry

/-! An application whose recursive head callback returns a lambda.
The prefix starts in the callback's resulting state, including cache writes. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

structure BetaHeadStepPlan {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term : AExpr β)
    extends BetaPrefixPlan resolve locals before where
  rawFunction : KExpr .anon
  rawArgument : KExpr .anon
  appInfo : ExprInfo .anon
  sourceEq : source = .app rawFunction rawArgument appInfo
  rawHead : KExpr .anon
  headTerm : AExpr β
  modelSource : term = headTerm.appN arguments
  spine : (KExpr.app rawFunction rawArgument appInfo).collectSpine = (rawHead, rawArguments)
  headEntry : StructuralWhnfEntry rawHead
  sourceHeadReads : readScopedExpr? resolve locals rawHead = some headTerm.erase

namespace BetaHeadStepPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {locals : List FVarId} {before : TcState .anon} {source : KExpr .anon} {term : AExpr β}

def rawLambda (plan : BetaHeadStepPlan resolve locals before source term) := plan.toBetaPrefixPlan.rawLambda
def modelLambda (plan : BetaHeadStepPlan resolve locals before source term) := plan.toBetaPrefixPlan.modelLambda
def result (plan : BetaHeadStepPlan resolve locals before source term) := plan.toBetaPrefixPlan.result
def after (plan : BetaHeadStepPlan resolve locals before source term) := plan.toBetaPrefixPlan.after
def modelResult (plan : BetaHeadStepPlan resolve locals before source term) := plan.toBetaPrefixPlan.modelResult

theorem entry (plan : BetaHeadStepPlan resolve locals before source term) : StructuralWhnfEntry source := by
  rw [plan.sourceEq]
  exact .application plan.spine plan.headEntry

theorem sourceReading (plan : BetaHeadStepPlan resolve locals before source term) :
    readScopedExpr? resolve locals source = some term.erase := by
  simp only [plan.sourceEq, plan.modelSource]
  exact readScopedExpr?_collectSpine plan.spine plan.sourceHeadReads plan.argumentReads

theorem reading (plan : BetaHeadStepPlan resolve locals before source term) (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals plan.result = some plan.modelResult.erase ∧ plan.after.env.intern.WF :=
  plan.toBetaPrefixPlan.reading coherent

theorem run (plan : BetaHeadStepPlan resolve locals before source term) {methods : Methods .anon}
    {initial : TcState .anon} {flags : WhnfFlags}
    (headRun : methods.whnfCoreFlags plan.rawHead flags initial = .ok plan.rawLambda before) :
    (RecM.whnfCoreWithFlagsStep source flags).run methods initial = .ok (.next plan.result) plan.after := by
  simp only [plan.sourceEq]
  exact plan.toBetaPrefixPlan.run plan.spine headRun

end BetaHeadStepPlan

end Ix.Kernel.Consistency
