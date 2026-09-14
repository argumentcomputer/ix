/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaWhnfPlan
import Ix.Kernel.Verify.Whnf.Driver.CacheExecution

/-! Raw beta/let paths through the public WHNF drivers and their exact cold-cache
state updates. Cached execution composes these primitives in BetaCacheExecution. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

theorem BetaStepPlan.not_transient {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {before : TcState .anon} {source : KExpr .anon} {term : AExpr β}
    (plan : BetaStepPlan resolve locals before source term) (methods : Methods .anon) (state : TcState .anon) :
    (RecM.isTransientNatLiteralWork source).run methods state = .ok false state := by
  simp only [plan.sourceEq, RecM.isTransientNatLiteralWork, RecM.isNatLiteralRecursorApp,
    plan.spine, pure_bind]
  rfl

namespace BetaPublicWhnf

def outerKey (source : KExpr .anon) (before : TcState .anon) :=
  betaWhnfKey source (betaWhnfPrefix before)

def noDeltaKey (source : KExpr .anon) (before : TcState .anon) :=
  betaWhnfKey source (betaWhnfCharge (outerKey source before).2)

def coreKey (source : KExpr .anon) (before : TcState .anon) :=
  betaWhnfKey source (noDeltaKey source before).2

def coreAfter (source result : KExpr .anon) (before reduced : TcState .anon) : TcState .anon :=
  { reduced with env := { reduced.env with
    whnfCoreCache := reduced.env.whnfCoreCache.insert (coreKey source before).1 result } }

def noDeltaAfter (source result : KExpr .anon) (before reduced : TcState .anon) : TcState .anon :=
  let state := coreAfter source result before reduced
  { state with env := { state.env with
    whnfNoDeltaCache := state.env.whnfNoDeltaCache.insert (noDeltaKey source before).1 result } }

def after (source result : KExpr .anon) (before reduced : TcState .anon) : TcState .anon :=
  let state := noDeltaAfter source result before reduced
  { state with env := { state.env with
    whnfCache := state.env.whnfCache.insert (outerKey source before).1 result } }

theorem coreKey_fields (source : KExpr .anon) (before : TcState .anon) :
    (coreKey source before).2.env = before.env ∧
      (coreKey source before).2.lctx = before.lctx ∧
      (coreKey source before).2.inNativeReduce = before.inNativeReduce := by
  simp only [coreKey, noDeltaKey, outerKey, betaWhnfKey_environment, betaWhnfKey_context,
    betaWhnfKey_native, betaWhnfCharge_fields, betaWhnfPrefix_fields, and_self]

end BetaPublicWhnf

/-- A public beta reduction through the three cache-miss layers. The key
states, instrumentation, fuel charge, and final cache insertions are computed;
the only reduction resource is the raw beta/let path. -/
structure BetaPublicWhnfPlan {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (fuel : Nat) (before : TcState .anon)
    (source : KExpr .anon) (term : AExpr β) (result : KExpr .anon) (target : AExpr β) where
  steps : Nat
  reduced : TcState .anon
  path : BetaWhnfTrace resolve locals (fuel + 1) .FULL steps
    (BetaPublicWhnf.coreKey source before).2 source term reduced result target
  moving : 0 < steps
  enough : steps < maxWhnfCoreFuel.toNat
  fuelAvailable : (before.recFuel == 0) = false
  native : before.inNativeReduce = false
  outerMiss : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
    (BetaPublicWhnf.outerKey source before).1]? = none
  noDeltaMiss : (BetaPublicWhnf.noDeltaKey source before).2.env.whnfNoDeltaCache[
    (BetaPublicWhnf.noDeltaKey source before).1]? = none
  coreMiss : (BetaPublicWhnf.coreKey source before).2.env.whnfCoreCache[
    (BetaPublicWhnf.coreKey source before).1]? = none
  terminal : BetaWhnfTerminal result

namespace BetaPublicWhnfPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}

def after (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) : TcState .anon :=
  BetaPublicWhnf.after source result before plan.reduced

theorem run (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    (RecM.whnf source).run (methodsN (fuel + 1)) before = .ok result plan.after := by
  let first := plan.path.first plan.moving
  have coreEntry : RecM.whnfCoreWithFlags source .FULL = RecM.whnfCoreWithFlagsNonLeaf source .FULL :=
    first.core .FULL
  have coreRun : (RecM.whnfCoreWithFlags source .FULL).run (methodsN (fuel + 1))
      (BetaPublicWhnf.noDeltaKey source before).2 =
        .ok result (BetaPublicWhnf.coreAfter source result before plan.reduced) := by
    rw [coreEntry]
    exact RecM.whnfCoreWithFlagsNonLeaf_fullMiss rfl
      (betaWhnfKey_run source _) (first.not_transient _ _) plan.coreMiss (plan.path.run plan.enough)
  have reducedNative : plan.reduced.inNativeReduce = false := by
    exact plan.path.frame.native.trans
      ((BetaPublicWhnf.coreKey_fields source before).2.2.trans plan.native)
  have noDeltaEntry : RecM.whnfNoDeltaImpl source .FULL .collapse =
      RecM.whnfNoDeltaImplNonLeaf source .FULL .collapse := first.noDelta .FULL .collapse
  have noDeltaRun : (RecM.whnfNoDeltaImpl source .FULL .collapse).run (methodsN (fuel + 1))
      (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2) =
        .ok result (BetaPublicWhnf.noDeltaAfter source result before plan.reduced) := by
    rw [noDeltaEntry]
    exact RecM.whnfNoDeltaImplNonLeaf_fullMiss rfl (betaWhnfKey_run source _)
      (first.not_transient _ _) plan.noDeltaMiss
      (plan.terminal.noDelta_uncached .FULL .collapse coreRun) reducedNative
  have fullEntry : RecM.whnf source = RecM.whnfWithNatSuccModeNonLeaf source .collapse := first.full .collapse
  rw [fullEntry]
  exact RecM.whnfWithNatSuccModeNonLeaf_miss (betaWhnfPrefix_run source before _)
    (betaWhnfKey_run source _) (first.not_transient _ _) plan.outerMiss
    (betaWhnfCharge_run _ _ (by
      simpa only [BetaPublicWhnf.outerKey, betaWhnfKey_fuel, (betaWhnfPrefix_fields before).2.2.2] using plan.fuelAvailable))
    (plan.terminal.full_uncached .collapse noDeltaRun) reducedNative

theorem reading (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ plan.after.env.intern.WF := by
  exact plan.path.reading sourceReading ((BetaPublicWhnf.coreKey_fields source before).1.symm ▸ coherent)

theorem context (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    plan.after.lctx = before.lctx := by
  exact plan.path.frame.context.trans (BetaPublicWhnf.coreKey_fields source before).2.1

theorem cache_hit (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target)
    (methods : Methods .anon) (current : TcState .anon)
    (hit : (BetaPublicWhnf.outerKey source current).2.env.whnfCache[
      (BetaPublicWhnf.outerKey source current).1]? = some result) :
    (RecM.whnf source).run methods current = .ok result (BetaPublicWhnf.outerKey source current).2 := by
  let first := plan.path.first plan.moving
  have entry : RecM.whnf source = RecM.whnfWithNatSuccModeNonLeaf source .collapse := first.full .collapse
  rw [entry]
  exact RecM.whnfWithNatSuccModeNonLeaf_hit (betaWhnfPrefix_run source current _)
    (betaWhnfKey_run source _) (first.not_transient _ _) hit

end BetaPublicWhnfPlan


end Ix.Kernel.Consistency
