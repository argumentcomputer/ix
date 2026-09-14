/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaSpine

/-! Beta traces built from actual inference calls and previously derived
typing origins. Each step retains its lambda domains and argument checks;
the next step can use the preceding result without another inference call. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Apply retained argument checks to a generated function origin. -/
def SynthesisTypingOrigin.applySpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head headType type : AExpr β} {arguments : List (AExpr β)}
    (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context head headType)
    (spine : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context headType arguments type) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context (head.appN arguments) type :=
  match spine with
  | .nil _ => origin
  | .snoc prior checked => by
      simpa only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using
        (origin.applySpine prior).application checked
  | .convert prior trace => .convert (origin.applySpine prior) trace
termination_by structural spine

/-- A function reduction carries its original dependent argument checks
through the complete application suffix. -/
def SynthesisBetaTrace.applySpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {source result headType type : AExpr β} {arguments : List (AExpr β)}
    (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result headType)
    (spine : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context headType arguments type) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      (source.appN arguments) (result.appN arguments) type :=
  match spine with
  | .nil _ => trace
  | .snoc prior checked => by
      simpa only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using
        (trace.applySpine prior).application checked
  | .convert prior typeTrace => .convertType (trace.applySpine prior) typeTrace
termination_by structural spine

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

/-- Any original lambda prefix selected from the source inference starts
a composable trace whose result can be used as another typing origin. -/
def SynthesisInference.betaSpineTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel count : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {head type : AExpr β}
    {arguments : List (AExpr β)} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source (head.appN arguments) type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (head.appN arguments).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (enough : count ≤ head.lambdaDepth) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      (head.appN arguments) (AExpr.betaPrefix count head arguments) type :=
  (support.spineOrigin contextOrigin agreement reading accepted head arguments rfl).betaTrace enough

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

end Ix.Kernel.Consistency
