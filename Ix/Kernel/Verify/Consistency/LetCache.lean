/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LetSynthesis
import Ix.Kernel.Verify.Consistency.SynthesisCacheExecution

/-! Derive a let's whole-cache execution from the same three child checks
that establish its typing. Wrapper annotations remain the existing child
resources; no additional operational tree is assumed for the let branch. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

namespace LetInferenceCheck

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
  {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name} {domain value body : KExpr .anon}
  {nonDep : Bool} {info : ExprInfo .anon} {A val b B resultType : AExpr β} {level : VLevel}

structure CacheData
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level) (anchor : Model.Environment β) where
  domain : check.domainTree.CacheData anchor
  value : check.valueTree.CacheData anchor
  body : check.bodyTree.CacheData anchor

/-- Original synthesis trees supply all three operational children. The
root miss and comparison are taken directly from the checked let execution. -/
def cacheTrace
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (data : check.CacheData anchor)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    InferenceCacheTrace.{u} (fuel + 1) before (.letE name domain value body nonDep info) := by
  have keyedAgreement := check.miss.localContext.symm ▸ agreement
  let domainRun := check.domainTree.cacheExecution data.domain contextOrigin keyedAgreement
    check.domainReading check.execution.domainRun
  let valueRun := check.valueTree.cacheExecution data.value contextOrigin
    (keyedAgreement.congr (check.execution.domainContext check.keyedValid).symm) check.valueReading check.execution.valueRun
  have opened := openLet_sound check.opening (keyedAgreement.congr (check.execution.openingContext check.keyedValid).symm)
    (check.absent agreement) check.domainReading check.bodyReading check.execution.openRun
  let bodyRun := check.bodyTree.cacheExecution data.body
    (.push contextOrigin check.domainTree keyedAgreement check.domainReading check.execution.domainRun)
    opened.2.2.1 opened.2.1 check.execution.bodyRun
  exact .letE check.full check.miss check.execution check.hashPath domainRun.trace valueRun.trace bodyRun.trace

/-- The complete maps include every child write followed by the let's own
publication. Scope exit does not discard the recorded local entries. -/
theorem cache_maps {result : KExpr .anon} {after : TcState .anon}
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (data : check.CacheData anchor)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (accepted : RecM.infer (.letE name domain value body nonDep info) (methodsN (fuel + 1)) before =
      .ok result after) :
    after.env.inferCache = InferenceCacheEvent.applyFull
        ((check.cacheTrace data contextOrigin agreement).events accepted) before.env.inferCache ∧
      after.env.inferOnlyCache = InferenceCacheEvent.applyOnly
        ((check.cacheTrace data contextOrigin agreement).events accepted) before.env.inferOnlyCache :=
  (check.cacheTrace data contextOrigin agreement).cache_maps accepted

def cacheHistory {result : KExpr .anon} {after : TcState .anon}
    (check : LetInferenceCheck resolve entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level)
    (data : check.CacheData anchor)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (history : InferenceCacheHistory before)
    (accepted : RecM.infer (.letE name domain value body nonDep info) (methodsN (fuel + 1)) before =
      .ok result after) : InferenceCacheHistory after :=
  history.afterInference (check.cacheTrace data contextOrigin agreement) accepted

end LetInferenceCheck

end Ix.Kernel.Consistency
