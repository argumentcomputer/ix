/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTyping

/-! Recover syntactic checking evidence from complete retained derivations.
These operations also apply after dependent substitution and head reduction,
when the resulting constructor can come from a substituted value. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

namespace SynthesisBetaTyping

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext : Model.Context β} {incomingBounds : List VLevel}

theorem ForallView.sound {context : Model.Context β} {condition : Certified.PropWhen} {domain body : AExpr β}
    (view : ForallView (resolve := resolve) (incoming := incoming) (incomingContext := incomingContext)
      (incomingBounds := incomingBounds) (entries := entries) context condition domain body)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context domain (.sort view.domainLevel) ∧
      TypingClaim.{u,v} entries (context.push domain) body (.sort view.bodyLevel) :=
  ⟨view.domainCheck.origin.sound formed, view.bodyCheck.origin.sound formed⟩


end SynthesisBetaTyping

end Ix.Kernel.Consistency
