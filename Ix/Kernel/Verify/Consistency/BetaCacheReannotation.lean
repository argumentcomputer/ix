/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheExecution
import Ix.Kernel.Verify.Consistency.BetaReannotation

/-! Rebuild the annotations of a retained WHNF execution at every cache
layer. Its original returned expression and complete final state are preserved. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

def BetaCoreExecution.reannotate {γ : Type v} {originResolve : Address → Option (ConstRef γ)}
    {originLocals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr γ}
    (execution : BetaCoreExecution originResolve originLocals fuel before source term result target)
    {current : AExpr β} (reading : readScopedExpr? resolve locals source = some current.erase)
    (coherent : before.env.intern.WF) :
    Σ output, { rebuilt : BetaCoreExecution resolve locals fuel before source current result output //
      rebuilt.after = execution.after } :=
  match execution with
  | .reduce path moving enough miss terminal =>
      let rebuilt := path.reannotate reading ((betaWhnfKey_environment _ _).symm ▸ coherent)
      ⟨rebuilt.1, ⟨.reduce rebuilt.2 moving enough miss terminal, rfl⟩⟩
  | .cached origin initial hit =>
      let rebuilt := BetaCoreExecution.reannotate origin reading initial
      ⟨rebuilt.1, ⟨.cached rebuilt.2.1 initial hit, rfl⟩⟩
  | .cachedHead origin initial terminal hit =>
      let rebuilt := origin.reannotate reading initial
      ⟨rebuilt.1, ⟨.cachedHead rebuilt.2 initial terminal hit, rfl⟩⟩
termination_by structural execution

def BetaNoDeltaExecution.reannotate {γ : Type v} {originResolve : Address → Option (ConstRef γ)}
    {originLocals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr γ}
    (execution : BetaNoDeltaExecution originResolve originLocals fuel before source term result target)
    {current : AExpr β} (reading : readScopedExpr? resolve locals source = some current.erase)
    (coherent : before.env.intern.WF) :
    Σ output, { rebuilt : BetaNoDeltaExecution resolve locals fuel before source current result output //
      rebuilt.after = execution.after } :=
  match execution with
  | .reduce core miss =>
      let rebuilt := core.reannotate reading ((betaWhnfKey_environment _ _).symm ▸ coherent)
      ⟨rebuilt.1, ⟨.reduce rebuilt.2.1 miss,
        congrArg (BetaCacheExecution.writeNoDelta (betaWhnfKey source before).1 result) rebuilt.2.2⟩⟩
  | .cached origin initial hit =>
      let rebuilt := BetaNoDeltaExecution.reannotate origin reading initial
      ⟨rebuilt.1, ⟨.cached rebuilt.2.1 initial hit, rfl⟩⟩
termination_by structural execution

def BetaPublicExecution.reannotate {γ : Type v} {originResolve : Address → Option (ConstRef γ)}
    {originLocals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr γ}
    (execution : BetaPublicExecution originResolve originLocals fuel before source term result target)
    {current : AExpr β} (reading : readScopedExpr? resolve locals source = some current.erase)
    (coherent : before.env.intern.WF) :
    Σ output, { rebuilt : BetaPublicExecution resolve locals fuel before source current result output //
      rebuilt.after = execution.after } :=
  match execution with
  | .reduce inner miss fuelAvailable => by
      have initial : (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2).env.intern.WF := by
        simpa only [BetaPublicWhnf.outerKey, betaWhnfCharge_fields, betaWhnfKey_environment,
          betaWhnfPrefix_fields] using coherent
      let rebuilt := inner.reannotate reading initial
      exact ⟨rebuilt.1, ⟨.reduce rebuilt.2.1 miss fuelAvailable,
        congrArg (BetaCacheExecution.writeFull (BetaPublicWhnf.outerKey source before).1 result) rebuilt.2.2⟩⟩
  | .cached origin initial hit =>
      let rebuilt := BetaPublicExecution.reannotate origin reading initial
      ⟨rebuilt.1, ⟨.cached rebuilt.2.1 initial hit, rfl⟩⟩
termination_by structural execution

end Ix.Kernel.Consistency
