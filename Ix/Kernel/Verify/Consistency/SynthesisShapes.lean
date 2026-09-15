/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisSource

/-! Recover function-type children, lambda bodies, and application spines
from complete retained derivations, including after let substitution. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The domain and codomain retain their checking origins after interface
growth, local insertion, and dependent term substitution. -/
abbrev SynthesisRetainedForall {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β)
    (condition : Certified.PropWhen) (domain body : AExpr β) :=
  SynthesisBetaTyping.ForallView (resolve := resolve) (incoming := incoming)
    (incomingContext := incomingContext) (incomingBounds := incomingBounds)
    (entries := entries) context condition domain body

/-- A function-type check at the caller's current inference context. -/
abbrev SynthesisForallBodyCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (context : Model.Context β) (bounds : List VLevel)
    (condition : Certified.PropWhen) (domain body : AExpr β) :=
  SynthesisRetainedForall resolve entries context bounds entries context condition domain body

private def ForallInferenceTrace.bodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} {A B : AExpr β} {domainBound bodyBound : VLevel}
    (trace : ForallInferenceTrace fuel before name bi domain body)
    (opening : BinderOpeningSupport trace.domainState body)
    (domainTree : SynthesisInference resolve entries locals context bounds fuel before domain
      A (.sort (readLevel trace.domainLevel)) domainBound)
    (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
      (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened
      B (.sort (readLevel trace.bodyLevel)) bodyBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (domainReading : readScopedExpr? resolve locals domain = some A.erase)
    (bodyReading : readScopedExpr? resolve locals body 1 = some B.erase) :
    SynthesisForallBodyCheck resolve entries context bounds
      (Certified.zeroCondition (readLevel trace.bodyLevel)) A B := by
  have opened := openBinder_sound opening (agreement.congr trace.contextPreserved.symm)
    (trace.absent agreement) domainReading bodyReading trace.openRun
  exact {
    domainLevel := readLevel trace.domainLevel
    bodyLevel := readLevel trace.bodyLevel
    domainCheck := domainTree.betaTyping .current agreement domainReading trace.domainRun
    bodyCheck := bodyTree.betaTyping (.push .current domainTree agreement domainReading trace.domainRun)
      opened.2.2.1 opened.2.1 trace.bodyRun
    conditionAgrees := rfl }

def BinderInference.forallBodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source
      (.forallE condition domain body) type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (AExpr.forallE condition domain body).erase) :
    SynthesisForallBodyCheck resolve entries context bounds condition domain body := by
  cases support with
  | forallE miss trace opening domainTree bodyTree =>
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      exact trace.bodyCheck opening (.known domainTree (.sort _)) (.known bodyTree (.sort _))
        (miss.localContext.symm ▸ agreement) domainReads bodyReads

/-- Function-type children come from the complete retained derivation,
including a function type exposed by dependent substitution. -/
def SynthesisInference.forallBodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.forallE condition domain body) type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (AExpr.forallE condition domain body).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    SynthesisForallBodyCheck resolve entries context bounds condition domain body :=
  (support.betaTyping .current agreement reading accepted).forallView rfl

def SynthesisRetainedCheck.forallBody {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    {condition : Certified.PropWhen} {domain body : AExpr β}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (same : term = .forallE condition domain body) :
    SynthesisRetainedForall resolve incoming incomingContext incomingBounds entries context condition domain body :=
  check.betaTyping.forallView same

private theorem list_reverse_induction {α : Type u} {motive : List α → Prop}
    (nil : motive [])
    (append_singleton : ∀ tail last, motive tail → motive (tail ++ [last]))
    (values : List α) : motive values := by
  have reversed : ∀ items : List α, motive items.reverse := by
    intro items
    induction items with
    | nil => exact nil
    | cons item items ih =>
        simpa only [List.reverse_cons] using append_singleton items.reverse item ih
  simpa using reversed values.reverse

private theorem not_variable_spine {β : Type u} {term : AExpr β}
    (notApp : ∀ fn arg, term ≠ .app fn arg) (notVar : ∀ index, term ≠ .bvar index)
    (index : Nat) (arguments : List (AExpr β)) : term ≠ (AExpr.bvar index).appN arguments := by
  intro same
  induction arguments using list_reverse_induction with
  | nil => exact notVar index same
  | append_singleton arguments argument ih =>
      exact notApp _ _ (by simpa only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using same)

private theorem bvar_variable_spine {β : Type u} {left right : Nat} {arguments : List (AExpr β)}
    (same : AExpr.bvar left = (AExpr.bvar right).appN arguments) : arguments = [] ∧ left = right := by
  induction arguments using list_reverse_induction with
  | nil => exact ⟨rfl, AExpr.bvar.inj same⟩
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] at same
      cases same

private theorem app_variable_spine {β : Type u} {fn arg : AExpr β} {index : Nat}
    {arguments : List (AExpr β)} (same : fn.app arg = (AExpr.bvar index).appN arguments) :
    arguments = arguments.dropLast ++ [arg] ∧ fn = (AExpr.bvar index).appN arguments.dropLast := by
  induction arguments using list_reverse_induction with
  | nil => cases same
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil, AExpr.app.injEq] at same
      simp only [List.dropLast_concat]
      exact ⟨by rw [same.2], same.1⟩

/-- Extract the actual argument calls from a checked variable application.
No type check on the generated substitutions is added. -/
def BinderInference.variableSpineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (index : Nat) (arguments : List (AExpr β)) (headEquals : term = (AExpr.bvar index).appN arguments) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  match support with
  | .fvar _ _ atIndex => by
      obtain ⟨rfl, rfl⟩ := bvar_variable_spine headEquals
      exact ⟨_, atIndex, .nil _⟩
  | .app _ miss trace functionTree head argumentTree conditions hashPath comparisonFaithful
      _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_variable_spine headEquals
      have prior := functionTree.variableSpineOrigin (incoming := incoming) (incomingContext := incomingContext)
        (incomingBounds := incomingBounds) keyedAgreement functionReading index arguments.dropLast parts.2
      have spine := prior.spine.snoc (.source (.binderArgument trace functionTree head argumentTree
        keyedAgreement functionReading argumentReading conditions hashPath comparisonFaithful))
      exact ⟨prior.headType, prior.atIndex, by simpa only [← parts.1] using spine⟩
  | .sort .. | .cachedSort .. | .natLit .. | .cachedNatLit .. | .const .. | .polymorphic .. |
    .cachedConst .. | .forallE .. | .lam .. => by
      exact False.elim (not_variable_spine (by intro fn arg same; cases same)
        (by intro index same; cases same) index arguments headEquals)
termination_by structural support


def SynthesisInference.variableSpineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (index : Nat) (arguments : List (AExpr β)) (same : term = (AExpr.bvar index).appN arguments) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  (support.betaTyping contextOrigin agreement reading accepted).variableSpineOrigin index arguments same

def SynthesisRetainedCheck.variableSpineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (index : Nat) (arguments : List (AExpr β)) (same : term = (AExpr.bvar index).appN arguments) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  check.betaTyping.variableSpineOrigin index arguments same

def SynthesisForallBodyCheck.variableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {condition : Certified.PropWhen} {domain : AExpr β}
    {index : Nat} {arguments : List (AExpr β)}
    (check : SynthesisForallBodyCheck resolve entries context bounds condition domain
      ((AExpr.bvar index).appN arguments))
    (parentOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries
      (context.push domain) index arguments (.sort check.bodyLevel) :=
  (check.bodyCheck.variableSpineOrigin index arguments rfl).rebase parentOrigin

/-- Keep the actual variable-application checks inside a lambda body.
The body's inferred type is retained separately from the lambda's eventual
codomain, which synthesis may obtain by reducing that type. -/
def BinderInference.lambdaBodyVariableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel index : Nat}
    {before : TcState .anon} {source : KExpr .anon} {domain type : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)}
    (support : BinderInference resolve entries locals context fuel before source
      (.lam condition domain ((AExpr.bvar index).appN arguments)) type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.lam condition domain ((AExpr.bvar index).appN arguments)).erase) :
    Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.push domain) index arguments resultType := by
  cases support with
  | lam full miss trace opening bodyTree constructed bound coherent closingFaithful faithful =>
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have domainAgreement := (miss.localContext.symm ▸ agreement).congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      exact ⟨_, bodyTree.variableSpineOrigin openedAgreement openedReads index arguments rfl⟩

def SynthesisInference.lambdaBodyVariableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel index : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {domain type : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.lam condition domain ((AExpr.bvar index).appN arguments)) type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.lam condition domain ((AExpr.bvar index).appN arguments)).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.push domain) index arguments resultType :=
  (support.betaTyping contextOrigin agreement reading accepted).lambdaBodyVariableSpine rfl

def SynthesisRetainedCheck.lambdaBodyVariableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type domain : AExpr β} {level : VLevel}
    {condition : Certified.PropWhen} {index : Nat} {arguments : List (AExpr β)}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (same : term = .lam condition domain ((AExpr.bvar index).appN arguments)) :
    Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.push domain) index arguments resultType :=
  check.betaTyping.lambdaBodyVariableSpine same

theorem BinderInference.lambdaPrefix {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type) :
    LambdaPrefix term type term.lambdaDepth := by
  induction support with
  | lam _ _ _ _ _ _ _ _ _ _ ih => exact .lam ih
  | _ => exact .zero _ _

theorem SynthesisInference.lambdaPrefix {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    LambdaPrefix term type term.lambdaDepth :=
  (support.betaTyping .current agreement reading accepted).lambdaPrefix

theorem SynthesisRetainedCheck.lambdaPrefix {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    LambdaPrefix term type term.lambdaDepth :=
  check.betaTyping.lambdaPrefix

def SynthesisRetainedCheck.origin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      .source (.checked contextOrigin tree agreement reading accepted)
  | .extend prior extension => prior.origin.extend extension
  | .weakenAt prior insertion => .weakenAt prior.origin insertion
  | .rebase origin prior => .rebase origin prior.origin
termination_by structural check

def SynthesisRetainedCheck.typeOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context type (.sort level) :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      .inferredType contextOrigin tree agreement reading accepted
  | .extend prior extension => prior.typeOrigin.extend extension
  | .weakenAt prior insertion => .weakenAt prior.typeOrigin insertion
  | .rebase origin prior => .rebase origin prior.typeOrigin
termination_by structural check


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
  | .sort .. | .cachedSort .. | .natLit .. | .cachedNatLit .. | .fvar .. | .const .. | .polymorphic .. |
    .cachedConst .. | .forallE .. | .lam .. => by
      exact False.elim (empty (nonapp_spine_empty (by intro fn arg same; cases same) same))
termination_by structural support


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
  (support.betaTyping contextOrigin agreement reading accepted).spineOrigin head arguments same

def SynthesisRetainedCheck.spineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (head : AExpr β) (arguments : List (AExpr β)) (same : term = head.appN arguments) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  check.betaTyping.spineOrigin head arguments same

def SynthesisSpineOrigin.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head type : AExpr β} {arguments : List (AExpr β)} {count : Nat}
    (origin : SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type)
    (enough : count ≤ head.lambdaDepth) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      (head.appN arguments) (AExpr.betaPrefix count head arguments) type :=
  .prefix origin.headOrigin (origin.leading.truncate enough) origin.argumentsOrigin

theorem SynthesisHead.appN_head {β : Type u} {head : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisHead (head.appN arguments)) : SynthesisHead head := by
  induction arguments generalizing head with
  | nil => exact support
  | cons argument arguments ih =>
      have applied := ih support
      cases applied with
      | app head => exact head

private theorem BinderInference.no_lambda_spine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {arguments : List (AExpr β)}
    (support : BinderInference resolve entries locals context fuel before source
      ((AExpr.lam condition domain body).appN arguments) type)
    (nonempty : arguments ≠ []) : False := by
  induction arguments using list_reverse_induction with
  | nil => exact nonempty rfl
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] at support
      cases support with
      | app _ _ _ _ head => cases head.appN_head

theorem BinderInference.lambdaSpineTyping {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (typed : TypingClaim.{u,v} entries context term type) :
    LambdaSpineTyping.{u,v} entries context term type := by
  intro condition domain body arguments same
  subst term
  by_cases empty : arguments = []
  · subst arguments
    exact ⟨type, typed, support.lambdaPrefix, .nil _⟩
  · exact False.elim (support.no_lambda_spine empty)

end Ix.Kernel.Consistency
