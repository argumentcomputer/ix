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

/-- The head's check and every argument check of an actual application
spine, retained as data for subsequent reductions and substitutions. -/
structure SynthesisSpineOrigin {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β)
    (head : AExpr β) (arguments : List (AExpr β)) (type : AExpr β) where
  headType : AExpr β
  headOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context head headType
  leading : LambdaPrefix head headType head.lambdaDepth
  argumentsOrigin : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
    entries context headType arguments type

private theorem appN_last {β : Type u} {head : AExpr β} {arguments : List (AExpr β)}
    (nonempty : arguments ≠ []) :
    head.appN arguments = (head.appN arguments.dropLast).app (arguments.getLast nonempty) := by
  calc
    head.appN arguments = head.appN (arguments.dropLast ++ [arguments.getLast nonempty]) :=
      congrArg (AExpr.appN head) (List.dropLast_concat_getLast nonempty).symm
    _ = _ := by simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil]

private theorem nonapp_spine_empty {β : Type u} {term head : AExpr β} {arguments : List (AExpr β)}
    (notApp : ∀ fn arg, term ≠ .app fn arg) (same : term = head.appN arguments) : arguments = [] := by
  by_contra nonempty
  exact notApp _ _ (same.trans (appN_last nonempty))

private theorem app_spine_parts {β : Type u} {fn arg head : AExpr β} {arguments : List (AExpr β)}
    (nonempty : arguments ≠ []) (same : fn.app arg = head.appN arguments) :
    arguments = arguments.dropLast ++ [arg] ∧ fn = head.appN arguments.dropLast := by
  have parts := AExpr.app.inj (same.trans (appN_last nonempty))
  exact ⟨by rw [parts.2]; exact (List.dropLast_concat_getLast nonempty).symm, parts.1⟩

def BinderInference.spineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (checked : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (head : AExpr β) (arguments : List (AExpr β)) (same : term = head.appN arguments) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  if empty : arguments = [] then by
    subst arguments
    simp only [AExpr.appN_nil] at same
    subst head
    exact ⟨type, .source checked, support.lambdaPrefix, .nil _⟩
  else match support with
  | .app _ miss trace functionTree functionHead argumentTree conditions hashPath comparisonFaithful
      _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_spine_parts empty same
      have prior := functionTree.spineOrigin (incoming := incoming) (incomingContext := incomingContext)
        (incomingBounds := incomingBounds)
        (.binderHead functionTree functionHead keyedAgreement functionReading trace.functionRun)
        keyedAgreement functionReading head arguments.dropLast parts.2
      refine ⟨prior.headType, prior.headOrigin, prior.leading, ?_⟩
      simpa only [← parts.1] using prior.argumentsOrigin.snoc
        (.source (.binderArgument trace functionTree functionHead argumentTree keyedAgreement
          functionReading argumentReading conditions hashPath comparisonFaithful))
  | .sort .. | .cachedSort .. | .fvar .. | .const .. | .polymorphic .. | .cachedConst .. | .forallE .. | .lam .. => by
      exact False.elim (empty (nonapp_spine_empty (by intro fn arg same; cases same) same))
termination_by structural support

/-- Recover every application argument and the head's original checked
lambda prefix from the executed source inference, including binder-backed
local and constant spines. -/
def SynthesisInference.spineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (head : AExpr β) (arguments : List (AExpr β)) (same : term = head.appN arguments) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  if empty : arguments = [] then by
    subst arguments
    simp only [AExpr.appN_nil] at same
    subst head
    exact ⟨type, .source (.checked contextOrigin support agreement reading accepted), support.lambdaPrefix, .nil _⟩
  else match support with
  | .cached tree priorAgreement priorReading priorRun _ _ _ =>
      tree.spineOrigin contextOrigin priorAgreement priorReading priorRun head arguments same
  | .known inference formation =>
      inference.spineOrigin (.checked contextOrigin (.known inference formation) agreement reading accepted)
        agreement reading head arguments same
  | .reuseType inference typeTree extension typeReading typeRun equivalent =>
      inference.spineOrigin
        (.checked contextOrigin (.reuseType inference typeTree extension typeReading typeRun equivalent)
          agreement reading accepted) agreement reading head arguments same
  | .app _ miss trace functionTree argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_spine_parts empty same
      have prior := functionTree.spineOrigin contextOrigin keyedAgreement functionReading trace.functionRun
        head arguments.dropLast parts.2
      refine ⟨prior.headType, prior.headOrigin, prior.leading, ?_⟩
      simpa only [← parts.1] using prior.argumentsOrigin.snoc
        (.source (.applicationArgument contextOrigin trace functionTree argumentTree keyedAgreement
          functionReading argumentReading conditions hashPath comparisonFaithful))
  | .appBeta _ miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_spine_parts empty same
      have prior := functionTree.spineOrigin contextOrigin keyedAgreement functionReading trace.functionRun
        head arguments.dropLast parts.2
      refine ⟨prior.headType, prior.headOrigin, prior.leading, ?_⟩
      simpa only [← parts.1] using (prior.argumentsOrigin.convert (.rebase contextOrigin reduction)).snoc
        (.source (.applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree
          keyedAgreement functionReading argumentReading conditions hashPath comparisonFaithful))
  | .fvar .. | .forallE .. | .lam .. | .lamBeta .. => by
      exact False.elim (empty (nonapp_spine_empty (by intro fn arg same; cases same) same))
termination_by structural support

def SynthesisSpineOrigin.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head type : AExpr β} {arguments : List (AExpr β)} {count : Nat}
    (origin : SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type)
    (enough : count ≤ head.lambdaDepth) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      (head.appN arguments) (AExpr.betaPrefix count head arguments) type :=
  .prefix origin.headOrigin (origin.leading.truncate enough) origin.argumentsOrigin

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
