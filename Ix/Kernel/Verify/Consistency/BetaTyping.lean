/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTrace

/-! Retain the checked lambda bodies and application arguments needed for
hereditary beta substitution. Generated results carry the same derivation,
so the next reduction does not require another inference call or origin. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Constructors that remain outside head beta reduction after substitution. -/
inductive BetaAtom {β : Type u} : AExpr β → Prop
  | sort (level : VLevel) : BetaAtom (.sort level)
  | const (ref : ConstRef β) (levels : List VLevel) : BetaAtom (.const ref levels)
  | forallE (condition : Certified.PropWhen) (domain body : AExpr β) : BetaAtom (.forallE condition domain body)
  | proj (ref : ConstRef β) (field : Nat) (major : AExpr β) : BetaAtom (.proj ref field major)
  | natLit (value : Nat) : BetaAtom (.natLit value)

theorem BetaAtom.liftN {β : Type u} {term : AExpr β} (atom : BetaAtom term) (count cutoff : Nat) :
    BetaAtom (term.liftN count cutoff) := by
  cases atom <;> constructor

theorem BetaAtom.inst {β : Type u} {term : AExpr β} (atom : BetaAtom term) (argument : AExpr β) (cutoff : Nat) :
    BetaAtom (term.inst argument cutoff) := by
  cases atom <;> constructor

theorem BetaAtom.not_lam {β : Type u} {term : AExpr β} (atom : BetaAtom term)
    (condition : Certified.PropWhen) (domain body : AExpr β) : term ≠ .lam condition domain body := by
  cases atom <;> intro same <;> cases same

theorem BetaAtom.step {β : Type u} {term : AExpr β} (atom : BetaAtom term) : BetaSyntax.step term = term := by
  cases atom <;> rfl

/-- A typing derivation whose leaves retain actual checks. Lambda bodies
and both application children remain available after substitution. Forward
beta conversion changes the retained type without discarding this structure. -/
inductive SynthesisBetaTyping {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) : Model.Context β → AExpr β → AExpr β → Type u
  | atom {context term type}
      (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (shape : BetaAtom term) : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type
  | bvar {context index type}
      (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context (.bvar index) type)
      (atIndex : context[index]? = some type) :
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (.bvar index) type
  | lam {context condition domain body codomain}
      (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context
        (.lam condition domain body) (.forallE condition domain codomain))
      (inner : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries (context.push domain) body codomain) :
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context
        (.lam condition domain body) (.forallE condition domain codomain)
  | app {context fn arg condition domain body}
      (function : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context fn
        (.forallE condition domain body))
      (argument : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context arg domain) :
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context (.app fn arg) (body.inst arg)
  | convert {context term sourceType resultType level}
      (prior : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term sourceType)
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        sourceType resultType (.sort level)) :
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term resultType

namespace SynthesisBetaTyping

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {incoming entries : Model.Environment β} {incomingContext : Model.Context β} {incomingBounds : List VLevel}

def origin {context : Model.Context β} {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type :=
  match typing with
  | .atom origin _ | .bvar origin _ | .lam origin _ => origin
  | .app function argument => .application function.origin argument.origin
  | .convert prior trace => .convert prior.origin trace
termination_by structural typing

structure LambdaView (context : Model.Context β) (condition : Certified.PropWhen) (domain body type : AExpr β) where
  codomain : AExpr β
  typeEq : type = .forallE condition domain codomain
  inner : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries (context.push domain) body codomain

def lambdaView {context : Model.Context β} {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    {condition : Certified.PropWhen} → {domain body : AExpr β} → term = .lam condition domain body →
    LambdaView (resolve := resolve) (incoming := incoming) (incomingContext := incomingContext)
      (incomingBounds := incomingBounds) (entries := entries) context condition domain body type :=
  match typing with
  | .atom _ shape => fun same => False.elim (shape.not_lam _ _ _ same)
  | .bvar .. | .app .. => fun same => by cases same
  | .lam _ inner => fun same => by cases same; exact ⟨_, rfl, inner⟩
  | .convert prior trace => fun same =>
      let view := prior.lambdaView same
      ⟨view.codomain, (trace.rigid (by simp only [view.typeEq]; intro fn arg same; cases same)).trans view.typeEq,
        view.inner⟩
termination_by structural typing

def weakenAt {source target : Model.Context β} {cutoff : Nat} {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries source term type)
    (insertion : ContextInsertion source target cutoff) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries target
      (term.liftN 1 cutoff) (type.liftN 1 cutoff) :=
  match typing with
  | .atom origin shape => .atom (.weakenAt origin insertion) (shape.liftN 1 cutoff)
  | .bvar (index := index) origin found => by
      have lifted := SynthesisTypingOrigin.weakenAt origin insertion
      have selected := insertion.lookup found
      by_cases below : index < cutoff
      · simp only [AExpr.liftN, liftVar, below, if_true] at lifted selected ⊢
        exact .bvar lifted selected
      · simp only [AExpr.liftN, liftVar, below, if_false, Nat.add_comm 1] at lifted selected ⊢
        exact .bvar lifted selected
  | .lam origin inner => .lam (.weakenAt origin insertion) (inner.weakenAt (insertion.push _))
  | .app function argument => by
      simpa only [AExpr.liftN, AExpr.liftN_inst_zero] using
        SynthesisBetaTyping.app (function.weakenAt insertion) (argument.weakenAt insertion)
  | .convert prior trace => .convert (prior.weakenAt insertion) (.weakenAt trace insertion)
termination_by structural typing

end SynthesisBetaTyping

/-- The internal substitution walker builds this data itself as it passes
binders. Erasure gives the existing model context-substitution relation. -/
inductive BetaSubstitutionContext {β : Type u} (base : Model.Context β) (domain argument : AExpr β) :
    Model.Context β → Model.Context β → Nat → Type u
  | root : BetaSubstitutionContext base domain argument (base.push domain) base 0
  | push {source target cutoff} (prior : BetaSubstitutionContext base domain argument source target cutoff)
      (binder : AExpr β) :
      BetaSubstitutionContext base domain argument (source.push binder)
        (target.push (binder.inst argument cutoff)) (cutoff + 1)

theorem BetaSubstitutionContext.relation {β : Type u} {base source target : Model.Context β}
    {domain argument : AExpr β} {cutoff : Nat}
    (substitution : BetaSubstitutionContext base domain argument source target cutoff) :
    ContextSubstitution base domain argument source target cutoff :=
  match substitution with
  | .root => .root
  | .push prior binder => .push prior.relation binder

def BetaSubstitutionContext.liftValue {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β} {incomingBounds : List VLevel}
    {base source target : Model.Context β} {domain argument term type : AExpr β} {cutoff : Nat}
    (substitution : BetaSubstitutionContext base domain argument source target cutoff)
    (value : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries base term type) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries target
      (term.liftN cutoff) (type.liftN cutoff) :=
  match substitution with
  | .root => by simpa only [AExpr.liftN_zero] using value
  | .push (target := target) (cutoff := cutoff) prior binder => by
      have lifted := (prior.liftValue value).weakenAt (ContextInsertion.root target (binder.inst argument cutoff))
      simpa only [AExpr.liftN_liftN_merge term cutoff 1 0 0 (Nat.le_refl _) (Nat.zero_le _),
        AExpr.liftN_liftN_merge type cutoff 1 0 0 (Nat.le_refl _) (Nat.zero_le _)] using lifted
termination_by structural substitution

def SynthesisBetaTyping.substituteAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β} {incomingBounds : List VLevel}
    {base source target : Model.Context β} {domain argument term type : AExpr β} {cutoff : Nat}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries source term type)
    (value : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries base argument domain)
    (substitution : BetaSubstitutionContext base domain argument source target cutoff) :
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries target
      (term.inst argument cutoff) (type.inst argument cutoff) :=
  match typing with
  | .atom origin shape => .atom (.substituteAt origin value.origin substitution.relation) (shape.inst argument cutoff)
  | .bvar (index := index) origin found => by
      by_cases equal : index = cutoff
      · subst index
        have sameType := substitution.relation.instantiate_removed_type found
        simpa only [AExpr.inst, AExpr.instVar, Nat.lt_irrefl, if_false, if_true, sameType] using
          substitution.liftValue value
      · have retained := substitution.relation.lookup_other found equal
        have typed := SynthesisTypingOrigin.substituteAt origin value.origin substitution.relation
        by_cases below : index < cutoff
        · simp only [AExpr.inst, AExpr.instVar, below, if_true] at typed retained ⊢
          exact .bvar typed retained
        · simp only [AExpr.inst, AExpr.instVar, below, equal, if_false] at typed retained ⊢
          exact .bvar typed retained
  | .lam origin inner =>
      .lam (.substituteAt origin value.origin substitution.relation)
        (inner.substituteAt value (substitution.push _))
  | .app function applied => by
      simpa only [AExpr.inst, AExpr.inst_inst_zero] using
        SynthesisBetaTyping.app (function.substituteAt value substitution) (applied.substituteAt value substitution)
  | .convert prior trace =>
      .convert (prior.substituteAt value substitution) (.substituteAt trace value.origin substitution.relation)
termination_by structural typing

theorem SynthesisBetaTyping.lambdaPrefix {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (typing : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type) :
    LambdaPrefix term type term.lambdaDepth :=
  match typing with
  | .atom _ shape => by cases shape <;> exact .zero _ _
  | .bvar .. | .app .. => .zero _ _
  | .lam _ inner => .lam inner.lambdaPrefix
  | .convert (term := term) prior trace => by
      have leading := prior.lambdaPrefix
      cases term with
      | lam condition domain body =>
          have view := prior.lambdaView rfl
          have fixed := trace.rigid (by simp only [view.typeEq]; intro fn arg same; cases same)
          simpa only [fixed] using leading
      | _ => exact .zero _ _
termination_by structural typing

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
