/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaHistoryState

/-! The existing inference execution tree preserves complete WHNF histories.
Only actual Pi/sort exposure inputs need supplementary readings; the original
synthesis tree can derive them from its returned-type readings. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

def InferenceCacheTrace.WhnfData (β : Type u) {fuel : Nat} {state : TcState .anon} {source : KExpr .anon} :
    InferenceCacheTrace.{u} fuel state source → Type (u + 1)
  | .hit .. | .sort .. | .fvar .. | .const .. | .lazyConst .. => PUnit
  | .app _ _ _ _ first second | .forallE _ _ first second |
    .lam _ _ _ first second | .lamBody _ _ _ first second => first.WhnfData β × second.WhnfData β
  | .appBeta _ _ trace _ _ first second =>
      first.WhnfData β × BetaHistoryReading β trace.functionState trace.functionType × second.WhnfData β
  | .letE _ _ _ _ first second third => first.WhnfData β × second.WhnfData β × third.WhnfData β
  | .forallSort _ trace _ _ first second =>
      first.WhnfData β × BetaHistoryReading β trace.domainCheck.inferredState trace.domainCheck.inferred ×
        second.WhnfData β × BetaHistoryReading β trace.bodyCheck.inferredState trace.bodyCheck.inferred
  | .lamSort _ _ trace _ first second =>
      first.WhnfData β × BetaHistoryReading β trace.domainCheck.inferredState trace.domainCheck.inferred × second.WhnfData β
  | .letSort _ _ trace _ _ first second third =>
      first.WhnfData β × BetaHistoryReading β trace.domainCheck.inferredState trace.domainCheck.inferred ×
        second.WhnfData β × third.WhnfData β
termination_by structural tree => tree

/-- Every successful supported inference retains the earlier WHNF producers
and appends its actual exposure publications. Recursive children, lazy loads,
substitution, inference-cache writes, and scope cleanup are composed along
their real intermediate states. -/
noncomputable def InferenceCacheTrace.whnfHistory {β : Type u} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    (tree : InferenceCacheTrace.{u} fuel before source) :
    tree.WhnfData β → BetaCacheHistory β before →
    RecM.infer source (methodsN fuel) before = .ok result after → BetaCacheHistory β after :=
  match tree with
  | .hit cached => fun _ history accepted => by
      rw [cached.run] at accepted
      cases accepted
      exact history.afterInferKey cached.keyRun
  | .sort (level := level) miss => fun _ history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        change EStateM.Result.ok
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
          {miss.keyed with env := {miss.keyed.env with intern :=
            (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} = .ok result middle at run
        cases run
        exact keyed.intern _
  | .fvar miss => fun _ history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        change (RecM.inferUncached RecM.inferCall before.inferOnly _).run (methodsN fuel) miss.keyed = _ at run
        unfold RecM.inferUncached at run
        simp only [ReaderT.run_bind] at run
        change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
        rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed = .ok miss.keyed miss.keyed from rfl] at run
        dsimp only at run
        split at run
        · cases run
          exact keyed
        · contradiction
  | .const miss concrete loaded resources => fun _ history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        apply Classical.choice
        obtain ⟨actual, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
        rw [getConst_loaded loaded] at got
        cases got
        have post := TcM.instantiateUnivParams_wf resources.faithful
          (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
        rw [instantiated] at post
        rw [post.2.2.1]
        exact ⟨keyed.intern _⟩
  | .lazyConst miss loader resources => fun _ history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        apply Classical.choice
        obtain ⟨concrete, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
        have loaded := keyed.getConst loader
        rw [got] at loaded
        have resource := resources concrete foundState got
        have post := TcM.instantiateUnivParams_wf resource.faithful
          (fun _ h => Or.inr h) ⟨resource.coherent, fun _ h => Or.inl h⟩
        rw [instantiated] at post
        rw [post.2.2.1]
        exact ⟨loaded.intern _⟩
  | .app full miss trace hashPath first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let functionHistory := first.whnfHistory data.1 keyed trace.functionRun
        let argumentHistory := second.whnfHistory data.2 functionHistory trace.argumentRun
        let compared := argumentHistory.hashConversion hashPath trace.compareRun
        rw [(trace.output_state run).2]
        exact compared.ofMaps (fun partition => by cases partition <;> rfl)
  | .appBeta full miss trace exposure hashPath first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let functionHistory := first.whnfHistory data.1 keyed trace.functionRun
        have exposed : BetaCacheHistory β trace.exposedState := by
          rw [trace.exposure_state exposure]
          exact data.2.1.afterPi exposure functionHistory
        let argumentHistory := second.whnfHistory data.2.2 exposed trace.argumentRun
        let compared := argumentHistory.hashConversion hashPath trace.compareRun
        rw [(trace.output_state run).2]
        exact compared.ofMaps (fun partition => by cases partition <;> rfl)
  | .forallE miss trace first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        let domainHistory := first.whnfHistory data.1 keyed trace.domainRun
        let opened := domainHistory.openBinder trace.openRun
        let bodyHistory := second.whnfHistory data.2 opened trace.bodyRun
        rw [(trace.output_state run).2]
        exact bodyHistory.ofMaps (fun partition => by cases partition <;> rfl)
  | .lam full miss trace first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let domainHistory := first.whnfHistory data.1 keyed trace.domainRun
        let opened := domainHistory.openBinder trace.openRun
        let bodyHistory := second.whnfHistory data.2 opened trace.bodyRun
        rw [(trace.output_state run).2]
        exact bodyHistory.ofMaps (fun partition => by cases partition <;> rfl)
  | .lamBody full miss trace first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let domainHistory := first.whnfHistory data.1 keyed trace.domainRun
        let opened := domainHistory.openBinder trace.openRun
        let bodyHistory := second.whnfHistory data.2 opened trace.bodyRun
        rw [(trace.output_state run).2]
        exact bodyHistory.ofMaps (fun partition => by cases partition <;> rfl)
  | .letE full miss trace hashPath first second third => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let domainHistory := first.whnfHistory data.1 keyed trace.domainRun
        let valueHistory := second.whnfHistory data.2.1 domainHistory trace.valueRun
        let compared := valueHistory.hashConversion hashPath trace.compareRun
        let opened := compared.openLet trace.openRun
        let bodyHistory := third.whnfHistory data.2.2 opened trace.bodyRun
        rw [(trace.output_state run).2]
        exact bodyHistory.ofMaps (fun partition => by cases partition <;> rfl)
  | .forallSort miss trace domainExposure bodyExposure first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        let domainHistory := first.whnfHistory data.1 keyed trace.domainCheck.inferRun
        have domainExposed : BetaCacheHistory β trace.domainCheck.after := by
          rw [trace.domainCheck.exposure_state domainExposure]
          exact data.2.1.afterSort domainExposure domainHistory
        let opened := domainExposed.openBinder trace.openRun
        let bodyHistory := second.whnfHistory data.2.2.1 opened trace.bodyCheck.inferRun
        have bodyExposed : BetaCacheHistory β trace.bodyCheck.after := by
          rw [trace.bodyCheck.exposure_state bodyExposure]
          exact data.2.2.2.afterSort bodyExposure bodyHistory
        rw [(trace.output_state run).2]
        exact bodyExposed.ofMaps (fun partition => by cases partition <;> rfl)
  | .lamSort full miss trace domainExposure first second => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let domainHistory := first.whnfHistory data.1 keyed trace.domainCheck.inferRun
        have domainExposed : BetaCacheHistory β trace.domainCheck.after := by
          rw [trace.domainCheck.exposure_state domainExposure]
          exact data.2.1.afterSort domainExposure domainHistory
        let opened := domainExposed.openBinder trace.openRun
        let bodyHistory := second.whnfHistory data.2.2 opened trace.bodyRun
        rw [(trace.output_state run).2]
        exact bodyHistory.ofMaps (fun partition => by cases partition <;> rfl)
  | .letSort full miss trace domainExposure hashPath first second third => fun data history accepted =>
      history.afterMiss miss accepted fun middle run keyed => by
        rw [full] at run
        let domainHistory := first.whnfHistory data.1 keyed trace.domainCheck.inferRun
        have domainExposed : BetaCacheHistory β trace.domainCheck.after := by
          rw [trace.domainCheck.exposure_state domainExposure]
          exact data.2.1.afterSort domainExposure domainHistory
        let valueHistory := second.whnfHistory data.2.2.1 domainExposed trace.valueRun
        let compared := valueHistory.hashConversion hashPath trace.compareRun
        let opened := compared.openLet trace.openRun
        let bodyHistory := third.whnfHistory data.2.2.2 opened trace.bodyRun
        rw [(trace.output_state run).2]
        exact bodyHistory.ofMaps (fun partition => by cases partition <;> rfl)
termination_by structural tree

end Ix.Kernel.Consistency
