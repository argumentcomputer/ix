/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.Context
import Ix.Kernel.Verify.Consistency.ScopedInstUniv

/-!
# Polymorphic constant inference inside function bodies

Lookup supplies a closed declaration type and finite resources for its actual
universe-instantiation walker. The resulting type remains closed while the
surrounding function's locals are active. A pure prediction of the substituted
syntax fixes an inference tree's annotated result type without assuming its
semantic validity or typing.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The runtime arity guard and the precise state passed to universe
instantiation follow from successful production constant inference. -/
theorem inferUncached_const_instantiation
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (accepted : RecM.inferUncached inferRec inferOnly (.const id arguments info)
      methods before = .ok result after) :
    ∃ concrete loaded, TcM.getConst id before = .ok concrete loaded ∧
      concrete.lvls.toNat = arguments.size ∧
      TcM.instantiateUnivParams concrete.ty arguments loaded = .ok result after := by
  change (RecM.inferUncached inferRec inferOnly (.const id arguments info)).run
    methods before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.getConst id) _ before = _ at accepted
  cases got : TcM.getConst id before with
  | error err failed => rw [EStateM.bind, got] at accepted; contradiction
  | ok concrete loaded =>
      rw [EStateM.bind, got] at accepted
      by_cases arity : concrete.lvls.toNat = arguments.size
      · simp only [arity, bne_self_eq_false, Bool.false_eq_true, if_false] at accepted
        exact ⟨concrete, loaded, rfl, arity, accepted⟩
      · simp only [bne_iff_ne] at accepted
        rw [if_pos arity] at accepted
        contradiction

/-- The selected admitted type is scoped at its declared universe arity.
Lookup uses the closed binder reader, retaining its exclusion of lets and
loose variables. All mutable resources concern the actual post-lookup state. -/
structure ScopedConstantInferenceSupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    (before : TcState .anon) (id : KId .anon) (arguments : Array (KUniv .anon))
    (ref : ConstRef β) (entry : ConstantEntry β) : Prop where
  resolved : resolve id.addr = some ref
  found : entries ref = some entry
  scope : entry.type.Scope entry.universes 0
  lookup : ∀ concrete loaded, TcM.getConst id before = .ok concrete loaded →
    concrete.lvls.toNat = entry.universes ∧
      readScopedExpr? resolve [] concrete.ty = some entry.type.erase ∧
      UniverseInstantiationSupport loaded concrete.ty arguments

/-- The stronger closed binder reading also supplies the earlier constant
refinement's lookup interface. -/
theorem ScopedConstantInferenceSupport.closed {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {ref : ConstRef β} {entry : ConstantEntry β}
    (support : ScopedConstantInferenceSupport resolve entries before id arguments ref entry) :
    ConstantInferenceSupport resolve entries before id arguments ref entry := by
  refine ⟨support.resolved, support.found, ?_⟩
  intro concrete loaded got
  obtain ⟨count, reading, resources⟩ := support.lookup concrete loaded got
  exact ⟨count, readScopedExpr?_closed reading, resources⟩

/-- Refinement derives the exact returned type's scoped reading, arity,
universe congruence, reference inventory, and scope for scoped arguments. -/
theorem inferUncached_const_scoped_refinement {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (support : ScopedConstantInferenceSupport resolve entries before id arguments ref entry)
    (accepted : RecM.inferUncached inferRec inferOnly (.const id arguments info)
      methods before = .ok result after) :
    ∃ output : AExpr β, readScopedExpr? resolve locals result = some output.erase ∧
      AExpr.LevelEquivalent (entry.type.instL (arguments.toList.map readLevel)) output ∧
      (arguments.toList.map readLevel).length = entry.universes ∧
      output.references = entry.type.references ∧
      (∀ n, (∀ level ∈ arguments, (readLevel level).WF n) → output.Scope n 0) := by
  obtain ⟨concrete, loaded, got, arity, instantiated⟩ := inferUncached_const_instantiation accepted
  obtain ⟨count, reading, resources⟩ := support.lookup concrete loaded got
  have scope : entry.type.Scope arguments.size 0 := by
    rw [← arity, count]
    exact support.scope
  obtain ⟨output, outputReads, same⟩ := instantiateUnivParams_readScopedAnnotated
    (locals := locals) resources scope.erase.1 reading instantiated
  refine ⟨output, outputReads, same, ?_,
    same.references.symm.trans (AExpr.references_instL entry.type _), ?_⟩
  · simpa only [List.length_map, Array.length_toList] using arity.symm.trans count
  · intro n argumentsWF
    obtain ⟨scopedOutput, scopedReads, scopedSame, scopedWF, _⟩ :=
      instantiateUnivParams_readAnnotated_scoped resources scope argumentsWF
        (readScopedExpr?_closed reading) instantiated
    have closedOutputReads :=
      (instantiateUnivParams_scoped_eq locals resources reading instantiated).symm.trans outputReads
    have sameOutput := AExpr.eq_of_erase_annotations
      (Option.some.inj (scopedReads.symm.trans closedOutputReads))
      (scopedSame.annotations.symm.trans same.annotations)
    exact sameOutput ▸ scopedWF

/-- Polymorphic references synthesize full typing in every active model
context. The dependency model supplies the instantiated type's validity. -/
theorem inferUncached_const_scoped_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (support : ScopedConstantInferenceSupport resolve entries before id arguments ref entry)
    (accepted : RecM.inferUncached inferRec inferOnly (.const id arguments info)
      methods before = .ok result after) :
    ScopedModelTyping.{u,v} resolve entries locals context (.const id arguments info) result := by
  obtain ⟨output, outputReads, same, arity, _, _⟩ :=
    inferUncached_const_scoped_refinement support accepted
  refine ⟨.const ref (arguments.toList.map readLevel), output, ?_, outputReads,
    same.typing (TypingClaim.const support.found arity)⟩
  simp [readScopedExpr?, support.resolved, AExpr.erase]

/-- Read a pure prediction of the instantiated declaration type. This is a
computable syntax check, independent of interning and semantic typing. -/
def readInstantiatedType? {β : Type u} (resolve : Address → Option (ConstRef β))
    (type : KExpr .anon) (arguments : Array (KUniv .anon)) : Option (VExpr β) :=
  match KExpr.instantiateUnivParamsSpec type arguments with
  | .ok result => readScopedExpr? resolve [] result
  | .error _ => none

/-- The actual interned result agrees with the pure prediction under the
walker's finite resource assumptions. Its reading is closed under locals. -/
theorem inferUncached_const_predicted_type {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (support : ScopedConstantInferenceSupport resolve entries before id arguments ref entry)
    (prediction : ∀ concrete loaded, TcM.getConst id before = .ok concrete loaded →
      readInstantiatedType? resolve concrete.ty arguments = some type.erase)
    (accepted : RecM.inferUncached inferRec inferOnly (.const id arguments info)
      methods before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase := by
  obtain ⟨concrete, loaded, got, _, instantiated⟩ := inferUncached_const_instantiation accepted
  obtain ⟨_, _, resources⟩ := support.lookup concrete loaded got
  have post := TcM.instantiateUnivParams_wf resources.faithful
    (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
  rw [instantiated] at post
  have predicted := prediction concrete loaded got
  rw [readInstantiatedType?, post.2.1] at predicted
  exact readScopedExpr?_weaken_closed predicted locals

/-- Fix an inference tree's result annotation from the pure substituted tree.
The semantic conclusion follows from the admitted entry and actual execution,
including any universe simplification; it is not a witness premise. -/
theorem infer_const_scoped_annotated {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (miss : UncachedInference before (.const id arguments info))
    (support : ScopedConstantInferenceSupport resolve entries miss.keyed id arguments ref entry)
    (prediction : ∀ concrete loaded, TcM.getConst id miss.keyed = .ok concrete loaded →
      readInstantiatedType? resolve concrete.ty arguments = some type.erase)
    (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations = type.annotations)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context (.const ref (arguments.toList.map readLevel)) type := by
  obtain ⟨state, run⟩ := infer_uncached_success miss accepted
  have predicted := inferUncached_const_predicted_type (locals := locals) support prediction run
  obtain ⟨output, outputReads, same, arity, _, _⟩ :=
    inferUncached_const_scoped_refinement (locals := locals) support run
  have sameOutput := AExpr.eq_of_erase_annotations
    (Option.some.inj (outputReads.symm.trans predicted))
    (same.annotations.symm.trans conditions)
  exact ⟨predicted, sameOutput ▸ same.typing (TypingClaim.const support.found arity)⟩

end Ix.Kernel.Consistency
