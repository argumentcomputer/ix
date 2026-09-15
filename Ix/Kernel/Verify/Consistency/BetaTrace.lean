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

end Ix.Kernel.Consistency
