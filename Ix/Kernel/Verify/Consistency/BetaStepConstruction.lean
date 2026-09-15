/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaWhnfPlan
import Ix.Kernel.Verify.Consistency.BetaPrefixSource

/-! Construct beta-step witnesses from the source expression. The caller
supplies only its reading and finite arithmetic and interning resources. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

namespace BetaStepSource

def selected (source : KExpr .anon) : Bool :=
  match source with
  | .app .. => match source.collectSpine.1 with
      | .lam .. => true
      | _ => false
  | _ => false

theorem selected_app {source : KExpr .anon} (chosen : selected source = true) :
    ∃ fn arg info, source = .app fn arg info := by
  cases source with
  | app fn arg info => exact ⟨fn, arg, info, rfl⟩
  | _ => cases chosen

theorem selected_entry {source : KExpr .anon} (chosen : selected source = true) : StructuralWhnfEntry source := by
  obtain ⟨fn, arg, info, rfl⟩ := selected_app chosen
  simp only [selected] at chosen
  generalize headEq : (KExpr.app fn arg info).collectSpine.1 = head at chosen
  cases head with
  | lam name bi domain body lambdaInfo => exact .beta (Prod.ext headEq rfl)
  | _ => cases chosen

theorem selected_not_transient {source : KExpr .anon} (chosen : selected source = true)
    (methods : Methods .anon) (before : TcState .anon) :
    (RecM.isTransientNatLiteralWork source).run methods before = .ok false before := by
  obtain ⟨fn, arg, info, rfl⟩ := selected_app chosen
  simp only [selected] at chosen
  generalize headEq : (KExpr.app fn arg info).collectSpine.1 = head at chosen
  cases head with
  | lam name bi domain body lambdaInfo =>
      generalize argumentsEq : (KExpr.app fn arg info).collectSpine.2 = arguments
      have spine : (KExpr.app fn arg info).collectSpine =
          (.lam name bi domain body lambdaInfo, arguments) :=
        Prod.ext headEq argumentsEq
      simp only [RecM.isTransientNatLiteralWork, RecM.isNatLiteralRecursorApp, spine, pure_bind]
      rfl
  | _ => cases chosen

def peeled (source : KExpr .anon) : KExpr .anon × Array (KExpr .anon) :=
  RecM.consumeBetaLams source.collectSpine.1 source.collectSpine.2

def substituted (source : KExpr .anon) (before : TcState .anon) : KExpr .anon × InternTable .anon :=
  simulSubst (peeled source).1 (peeled source).2.reverse 0 before.env.intern

def output (source : KExpr .anon) (before : TcState .anon) : KExpr .anon × InternTable .anon :=
  let result := substituted source before
  internAppChain result.1
    (source.collectSpine.2.extract (peeled source).2.size source.collectSpine.2.size).toList result.2

def after (source : KExpr .anon) (before : TcState .anon) : TcState .anon :=
  { before with env := { before.env with intern := (output source before).2 } }

/-- All candidates are computed by production's own peeling, substitution,
and suffix-building operations. No parsed spine or execution equation is a field. -/
structure Resources (source : KExpr .anon) (before : TcState .anon) : Prop where
  bounds : SimulSubstBounds (peeled source).1 (peeled source).2.reverse 0
  substitutionFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
    KExpr.SimulSubstReach (peeled source).2.reverse (peeled source).1 0 term
  suffixFaithful : KExpr.CollisionFree fun term => (substituted source before).2.ExprSupport term ∨
    term ∈ cheapBetaChainList (substituted source before).1
      (source.collectSpine.2.extract (peeled source).2.size source.collectSpine.2.size).toList

private def modelSpine {β : Type u} : AExpr β → AExpr β × List (AExpr β)
  | .app fn arg => let (head, arguments) := modelSpine fn; (head, arguments ++ [arg])
  | term => (term, [])

private theorem modelSpine_rebuild {β : Type u} (term : AExpr β) :
    term = (modelSpine term).1.appN (modelSpine term).2 := by
  induction term with
  | app fn arg ihFn ihArg =>
      simp only [modelSpine, AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil]
      exact congrArg (AExpr.app · arg) ihFn
  | _ => rfl

private theorem app_reading_shape {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fn arg : KExpr .anon} {info : ExprInfo .anon} {term : AExpr β}
    (reading : readScopedExpr? resolve locals (.app fn arg info) = some term.erase) :
    ∃ f a, term = .app f a ∧ readScopedExpr? resolve locals fn = some f.erase ∧
      readScopedExpr? resolve locals arg = some a.erase := by
  cases term with
  | app f a => exact ⟨f, a, rfl, readScopedExpr?_app_parts reading⟩
  | _ =>
      cases hf : readScopedExpr? resolve locals fn <;>
        cases ha : readScopedExpr? resolve locals arg <;>
        simp [readScopedExpr?, hf, ha, AExpr.erase] at reading

private theorem modelSpine_lambda {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {source : KExpr .anon} {term : AExpr β}
    (headLambda : ∃ name bi domain body info, (RecM.appSpineView source).1 = .lam name bi domain body info)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    ∃ condition domain body, (modelSpine term).1 = .lam condition domain body := by
  induction source generalizing term with
  | app fn arg info ihFn ihArg =>
      obtain ⟨f, a, rfl, fnReads, _⟩ := app_reading_shape reading
      simpa only [modelSpine] using ihFn (term := f) headLambda fnReads
  | lam name bi rawDomain rawBody info ihDomain ihBody =>
      cases term with
      | lam condition domain body => exact ⟨condition, domain, body, rfl⟩
      | _ =>
          cases hd : readScopedExpr? resolve locals rawDomain <;>
            cases hb : readScopedExpr? resolve locals rawBody 1 <;>
            simp [readScopedExpr?, hd, hb, AExpr.erase] at reading
  | _ => obtain ⟨_, _, _, _, _, impossible⟩ := headLambda; cases impossible

/-- The source reading determines all annotated spine components. Actual
collection and peeling determine every raw component and consumed argument. -/
def construct {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {term : AExpr β} {before : TcState .anon}
    (chosen : selected source = true) (reading : readScopedExpr? resolve locals source = some term.erase)
    (resources : Resources source before) :
    { plan : BetaStepPlan resolve locals before source term // plan.output = output source before } := by
  cases source with
  | app fn arg info =>
      simp only [selected] at chosen
      generalize rawHead : (KExpr.app fn arg info).collectSpine.1 = head at chosen
      cases head with
      | lam name bi rawDomain rawInner lambdaInfo =>
          have rawLambda : ∃ name bi domain body info,
              (RecM.appSpineView (.app fn arg info)).1 = .lam name bi domain body info :=
            ⟨name, bi, rawDomain, rawInner, lambdaInfo,
              (RecM.appSpineView_collectSpine (.app fn arg info)).1.symm.trans rawHead⟩
          have modelLambda := modelSpine_lambda (source := .app fn arg info) (term := term) rawLambda reading
          generalize modelHead : (modelSpine term).1 = head at modelLambda
          cases head with
          | lam condition domain inner =>
              have modelSource : term = (AExpr.lam condition domain inner).appN (modelSpine term).2 := by
                rw [← modelHead]; exact modelSpine_rebuild term
              have rawLambda' : ∃ name bi domain body info,
                  (KExpr.app fn arg info).collectSpine.1 = .lam name bi domain body info :=
                ⟨name, bi, rawDomain, rawInner, lambdaInfo, rawHead⟩
              have reads := readScopedExpr?_lambda_spine rawLambda' (modelSource ▸ reading)
              have nonempty : 0 < (KExpr.app fn arg info).collectSpine.2.size := by
                have size := congrArg List.length (RecM.appSpineView_collectSpine (.app fn arg info)).2
                simp only [Array.length_toList, List.length_append, List.length_singleton] at size
                omega
              refine ⟨{
                rawFunction := fn, rawArgument := arg, appInfo := info, sourceEq := rfl,
                name, bi, rawDomain, rawInner, lambdaInfo,
                rawArguments := (KExpr.app fn arg info).collectSpine.2,
                rawBody := (peeled (.app fn arg info)).1, consumed := (peeled (.app fn arg info)).2,
                condition, domain, inner, arguments := (modelSpine term).2, modelSource,
                spine := Prod.ext rawHead rfl, headReads := rawHead ▸ reads.1, argumentReads := reads.2,
                peeling := by simp only [peeled, rawHead],
                nonempty := by simpa only [peeled, rawHead] using BetaPrefixSource.consumed_nonempty nonempty,
                walkerBounds := resources.bounds, walkerFaithful := resources.substitutionFaithful,
                suffixFaithful := resources.suffixFaithful
              }, ?_⟩
              rfl
          | _ => exfalso; obtain ⟨_, _, _, impossible⟩ := modelLambda; cases impossible
      | _ => cases chosen
  | _ => cases chosen

theorem construct_result {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {term : AExpr β} {before : TcState .anon}
    (chosen : selected source = true) (reading : readScopedExpr? resolve locals source = some term.erase)
    (resources : Resources source before) :
    (construct chosen reading resources).1.result = (output source before).1 :=
  congrArg Prod.fst (construct chosen reading resources).2

theorem construct_after {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {term : AExpr β} {before : TcState .anon}
    (chosen : selected source = true) (reading : readScopedExpr? resolve locals source = some term.erase)
    (resources : Resources source before) :
    (construct chosen reading resources).1.after = after source before :=
  congrArg (fun result : KExpr .anon × InternTable .anon =>
    { before with env := { before.env with intern := result.2 } }) (construct chosen reading resources).2

theorem construct_run {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {term : AExpr β} {before : TcState .anon}
    (chosen : selected source = true) (reading : readScopedExpr? resolve locals source = some term.erase)
    (resources : Resources source before) (fuel : Nat) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run (methodsN (fuel + 1)) before =
      .ok (.next (output source before).1) (after source before) := by
  have executed := (construct chosen reading resources).1.run fuel flags
  simpa only [construct_result, construct_after] using executed

end BetaStepSource

end Ix.Kernel.Consistency
