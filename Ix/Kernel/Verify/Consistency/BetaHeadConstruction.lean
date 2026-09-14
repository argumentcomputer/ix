/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaHeadStepPlan
import Ix.Kernel.Verify.Consistency.BetaPrefixSource
import Ix.Kernel.Verify.Consistency.AppSpineSource
import Ix.Kernel.Verify.Consistency.LetWhnfPlan

/-! Reconstruct a beta continuation after an explicit-let application head.
The returned lambda and state come from the actual recursive WHNF call. -/

namespace Ix.Kernel.Consistency.BetaHeadStepSource

open Theory Theory.Model

universe u

def selected (source : KExpr .anon) : Bool :=
  match source with
  | .app .. => LetStepSource.selected source.collectSpine.1
  | _ => false

theorem selected_app {source : KExpr .anon} (chosen : selected source = true) :
    ∃ fn arg info, source = .app fn arg info := by
  cases source with
  | app fn arg info => exact ⟨fn, arg, info, rfl⟩
  | _ => cases chosen

theorem selected_head {source : KExpr .anon} (chosen : selected source = true) :
    LetStepSource.selected source.collectSpine.1 = true := by
  obtain ⟨_, _, _, rfl⟩ := selected_app chosen
  exact chosen

theorem selected_entry {source : KExpr .anon} (chosen : selected source = true) : StructuralWhnfEntry source := by
  obtain ⟨_, _, _, rfl⟩ := selected_app chosen
  exact .application (Prod.ext rfl rfl) (LetStepSource.selected_entry chosen)

structure Witness {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (before : TcState .anon) (source : KExpr .anon) (term : AExpr β)
    (head : KExpr .anon) (target : AExpr β) where
  plan : BetaHeadStepPlan resolve locals before source term
  sourceHead : plan.rawHead = source.collectSpine.1
  sourceTerm : plan.headTerm = (AppSpineSource.parts source term).1
  resultHead : plan.rawLambda = head
  resultTerm : plan.modelLambda = target
  result : plan.result = (BetaPrefixSource.output head source.collectSpine.2 before).1
  after : plan.after = BetaPrefixSource.after head source.collectSpine.2 before

def construct {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {before : TcState .anon} {source head : KExpr .anon} {term target : AExpr β}
    (chosen : selected source = true) (reading : readScopedExpr? resolve locals source = some term.erase)
    (returned : BetaPrefixSource.selected head = true)
    (headReads : readScopedExpr? resolve locals head = some target.erase)
    (resources : BetaPrefixSource.Resources head source.collectSpine.2 before) :
    Witness resolve locals before source term head target := by
  cases source with
  | app fn arg info =>
      let parsed := AppSpineSource.reading reading
      let built := BetaPrefixSource.construct returned headReads parsed.2.2
        (AppSpineSource.nonempty fn arg info) resources
      exact ⟨{
        toBetaPrefixPlan := built.plan,
        rawFunction := fn, rawArgument := arg, appInfo := info, sourceEq := rfl,
        rawHead := (KExpr.app fn arg info).collectSpine.1,
        headTerm := (AppSpineSource.parts (.app fn arg info) term).1,
        modelSource := by rw [built.modelArgs]; exact parsed.1,
        spine := Prod.ext rfl built.rawArgs.symm,
        headEntry := LetStepSource.selected_entry chosen, sourceHeadReads := parsed.2.1
      }, rfl, rfl, built.raw, built.model, built.result, built.after⟩
  | _ => cases chosen

/-- Successful application evaluation includes a successful head callback.
This also rules out method depth zero without an extra resource premise. -/
theorem head_of_success {methods : Methods .anon} {flags : WhnfFlags} {before after : TcState .anon}
    {fn arg result : KExpr .anon} {info : ExprInfo .anon} {loopFuel : Nat}
    (accepted : (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags)
      loopFuel (.app fn arg info)).run methods before = .ok result after) :
    ∃ head middle, methods.whnfCoreFlags (KExpr.app fn arg info).collectSpine.1 flags before = .ok head middle := by
  cases loopFuel with
  | zero => cases accepted
  | succ loopFuel =>
      rw [RecM.runBounded, ReaderT.run_bind] at accepted
      change EStateM.bind ((RecM.whnfCoreWithFlagsStep (.app fn arg info) flags).run methods) _ before = _ at accepted
      cases step : (RecM.whnfCoreWithFlagsStep (.app fn arg info) flags).run methods before with
      | error error failed => rw [EStateM.bind, step] at accepted; cases accepted
      | ok action middle =>
          unfold RecM.whnfCoreWithFlagsStep at step
          rw [ReaderT.run_bind] at step
          change EStateM.bind (methods.whnfCoreFlags (KExpr.app fn arg info).collectSpine.1 flags) _ before = _ at step
          cases called : methods.whnfCoreFlags (KExpr.app fn arg info).collectSpine.1 flags before with
          | error error failed => rw [EStateM.bind, called] at step; cases step
          | ok head headAfter => exact ⟨head, headAfter, rfl⟩

end Ix.Kernel.Consistency.BetaHeadStepSource
