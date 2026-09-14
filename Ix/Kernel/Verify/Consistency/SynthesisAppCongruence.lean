/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTyping

/-! Reapply the original checked argument spine after a function reduction.
Dependent result types and existing type conversions remain in the derivation. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

namespace SynthesisBetaTyping

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
  {incomingBounds : List VLevel}

def mapFunction {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type)
    (head target argument : AExpr β) (same : term = .app head argument)
    (reduce : {headType : AExpr β} →
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context head headType →
        SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context target headType ×
          SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context head target headType) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (.app target argument) type ×
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term (.app target argument) type :=
  match typing with
  | .atom _ shape => False.elim (by cases shape <;> cases same)
  | .bvar .. | .forallE .. | .lam .. => by cases same
  | .app function checked => by
      cases same
      let next := reduce function
      exact ⟨.app next.1 checked, .application next.2 checked.origin⟩
  | .convert prior trace =>
      let next := prior.mapFunction head target argument same reduce
      ⟨.convert next.1 trace, .convertType next.2 trace⟩
termination_by structural typing

/-- The original dependent spine is retained while the recursive callback
reduces its head at whichever type the source derivation assigned it. -/
def mapHead (arguments : List (AExpr β)) {head target type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context
      (head.appN arguments) type)
    (reduce : {headType : AExpr β} →
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context head headType →
        SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context target headType ×
          SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context head target headType) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (target.appN arguments) type ×
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (head.appN arguments) (target.appN arguments) type :=
  match arguments with
  | [] => reduce typing
  | argument :: arguments =>
      mapHead arguments (head := .app head argument) (target := .app target argument) typing
        (fun checked => checked.mapFunction head target argument rfl reduce)

end SynthesisBetaTyping

end Ix.Kernel.Consistency
