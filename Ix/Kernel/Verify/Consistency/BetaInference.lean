/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaChecking

/-! Recover the complete head-beta typing derivation from the source
inference tree. No checks of intermediate reduction results are supplied. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

theorem SynthesisInference.beta_steps_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) (count : Nat) :
    ConversionClaim.{u,v} entries context term (BetaSyntax.steps count term) ∧
      TypingClaim.{u,v} entries context (BetaSyntax.steps count term) type :=
  ((support.betaTyping .current agreement reading accepted).betaSteps count).2.sound formed

end Ix.Kernel.Consistency
