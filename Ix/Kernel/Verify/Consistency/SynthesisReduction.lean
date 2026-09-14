/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisDerivation

/-! Retain the checked lambda bodies and application arguments needed for
hereditary beta substitution. Generated results carry the same derivation,
so the next reduction does not require another inference call or origin. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

namespace BetaSyntax

/-- One leftmost beta contraction, retaining the application suffix.
A term without a beta redex at its head is unchanged. -/
def step : AExpr β → AExpr β
  | .app (.lam _ _ body) argument => body.inst argument
  | .app fn arg => .app (step fn) arg
  | term => term

def steps : Nat → AExpr β → AExpr β
  | 0, term => term
  | count + 1, term => steps count (step term)

private theorem step_appN {β : Type u} (head : AExpr β) (arguments : List (AExpr β))
    (notLam : ∀ condition domain body, head ≠ .lam condition domain body) :
    step (head.appN arguments) = (step head).appN arguments := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments ih =>
      rw [AExpr.appN_cons, ih (head.app argument) (by intro condition domain body same; cases same)]
      cases head <;> simp_all [step, AExpr.appN_cons]

theorem step_beta_appN {β : Type u} (condition : Certified.PropWhen)
    (domain body argument : AExpr β) (arguments : List (AExpr β)) :
    step ((AExpr.lam condition domain body).appN (argument :: arguments)) =
      (body.inst argument).appN arguments := by
  rw [AExpr.appN_cons, step_appN _ _ (by intro condition domain body same; cases same)]
  rfl

theorem steps_betaPrefix {β : Type u} (count : Nat) (head : AExpr β) (arguments : List (AExpr β))
    (leading : count ≤ head.lambdaDepth) (supplied : count ≤ arguments.length) :
    steps count (head.appN arguments) = AExpr.betaPrefix count head arguments := by
  induction count generalizing head arguments with
  | zero => rfl
  | succ count ih =>
      cases head with
      | lam condition domain body =>
          cases arguments with
          | nil => simp at supplied
          | cons argument arguments =>
              simp only [steps, step_beta_appN, AExpr.betaPrefix]
              apply ih
              · exact Nat.le_trans (by simpa only [AExpr.lambdaDepth, Nat.add_le_add_iff_right] using leading)
                  (AExpr.lambdaDepth_le_inst body argument 0)
              · simpa only [List.length_cons, Nat.add_le_add_iff_right] using supplied
      | _ => simp [AExpr.lambdaDepth] at leading

end BetaSyntax


/-- One beta step may use a lambda produced by an earlier trace. Its
retained product has the lambda's exact syntactic domain. -/
def SynthesisBetaTrace.beta {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {condition : Certified.PropWhen} {domain body codomain argument : AExpr β}
    (functionOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context
      (.lam condition domain body) (.forallE condition domain codomain))
    (argumentOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context argument domain) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      (.app (.lam condition domain body) argument) (body.inst argument) (codomain.inst argument) := by
  simpa only [List.nil_append, AExpr.appN_cons, AExpr.appN_nil, AExpr.betaPrefix] using
    SynthesisBetaTrace.prefix functionOrigin (.lam (.zero _ _))
      ((SynthesisArgumentSpineOrigin.nil _).snoc argumentOrigin)

theorem BetaAtom.step {β : Type u} {term : AExpr β} (atom : BetaAtom term) : BetaSyntax.step term = term := by
  cases atom <;> rfl

/-- Every head beta contraction computes its next typing derivation and
conversion from the retained source tree, including newly exposed lambdas. -/
def SynthesisBetaTyping.betaStep {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (BetaSyntax.step term) type ×
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term (BetaSyntax.step term) type :=
  match typing with
  | .atom origin shape => by rw [shape.step]; exact ⟨.atom origin shape, .refl origin⟩
  | .bvar origin found => ⟨.bvar origin found, .refl origin⟩
  | .forallE origin domainCheck bodyCheck agrees =>
      ⟨.forallE origin domainCheck bodyCheck agrees, .refl origin⟩
  | .lam origin inner => ⟨.lam origin inner, .refl origin⟩
  | .app (fn := fn) function argument => by
      have nextFunction := function.betaStep
      cases fn with
      | lam condition' domain' inner =>
          have view := function.lambdaView rfl
          obtain ⟨rfl, rfl, codomainEq⟩ := AExpr.forallE.inj view.typeEq
          refine ⟨?_, SynthesisBetaTrace.beta function.origin argument.origin⟩
          simpa only [codomainEq, BetaSyntax.step] using view.inner.substituteAt argument .root
      | bvar | sort | const | app | forallE | proj | natLit =>
          obtain ⟨next, converted⟩ := nextFunction
          exact ⟨.app next argument, .application converted argument.origin⟩
  | .convert prior trace =>
      let next := prior.betaStep
      ⟨.convert next.1 trace, .atType (.convert prior.origin trace) next.2⟩
termination_by structural typing

def SynthesisBetaTyping.betaSteps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} (count : Nat) {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (BetaSyntax.steps count term) type ×
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term (BetaSyntax.steps count term) type :=
  match count with
  | 0 => ⟨typing, .refl typing.origin⟩
  | count + 1 =>
      let first := typing.betaStep
      let rest := first.1.betaSteps count
      ⟨rest.1, first.2.trans rest.2⟩

def SynthesisBetaTyping.betaPrefix {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head type : AExpr β} {arguments : List (AExpr β)}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (head.appN arguments) type)
    (count : Nat) (leading : count ≤ head.lambdaDepth) (supplied : count ≤ arguments.length) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context
        (AExpr.betaPrefix count head arguments) type ×
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (head.appN arguments) (AExpr.betaPrefix count head arguments) type := by
  simpa only [BetaSyntax.steps_betaPrefix count head arguments leading supplied] using typing.betaSteps count

end Ix.Kernel.Consistency
