/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Atomic
import Ix.Kernel.Verify.Consistency.InstUniv

/-!
# Production inference of polymorphic constants

Successful constant inference supplies its own arity check and runs the actual
memoized universe-instantiation routine. Lookup agreement identifies the
loaded declaration's universe count and type with an existing model entry.
No restriction to monomorphic entries or sort-shaped types is needed.

The remaining operational assumptions are explicit: lookup agreement, the
loaded state's finite interning and level-substitution resources, and (for
the cached entry point) misses at the actual inference key. This does not yet
establish these invariants for arbitrary loader states or cache hits.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Agreement with the concrete declaration returned by lazy lookup, together
with the resources needed by the walker at that exact post-lookup state. -/
structure ConstantInferenceSupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    (before : TcState .anon) (id : KId .anon) (arguments : Array (KUniv .anon))
    (ref : ConstRef β) (entry : ConstantEntry β) : Prop where
  resolved : resolve id.addr = some ref
  found : entries ref = some entry
  lookup : ∀ concrete loaded, TcM.getConst id before = .ok concrete loaded →
    concrete.lvls.toNat = entry.universes ∧
      readExpr? resolve concrete.ty = some entry.type.erase ∧
      UniverseInstantiationSupport loaded concrete.ty arguments

/-- A successful uncached production branch types its exact returned tree in
every model of the preceding interface. The runtime guard establishes arity;
the model environment's well-formedness supplies the declaration type's scope. -/
theorem inferUncached_const_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {context : Model.Context β} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {type : KExpr .anon}
    (support : ConstantInferenceSupport resolve entries before id arguments ref entry)
    (wellFormed : entries.WF)
    (accepted : RecM.inferUncached inferRec inferOnly (.const id arguments info)
      methods before = .ok type after) :
    ModelTyping.{u,v} resolve entries context (.const id arguments info) type := by
  change (RecM.inferUncached inferRec inferOnly (.const id arguments info)).run
    methods before = .ok type after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.getConst id) _ before = _ at accepted
  cases got : TcM.getConst id before with
  | error err failed => rw [EStateM.bind, got] at accepted; contradiction
  | ok concrete loaded =>
      rw [EStateM.bind, got] at accepted
      obtain ⟨count, reading, resources⟩ := support.lookup concrete loaded got
      by_cases arity : concrete.lvls.toNat = arguments.size
      · simp only [arity, bne_self_eq_false, Bool.false_eq_true, if_false] at accepted
        change TcM.instantiateUnivParams concrete.ty arguments loaded = .ok type after at accepted
        have length : (arguments.toList.map readLevel).length = entry.universes := by
          simpa only [List.length_map, Array.length_toList] using arity.symm.trans count
        have scope : entry.type.erase.LevelWF arguments.size := by
          rw [← arity, count]
          exact (wellFormed.typeScope ref entry support.found).erase.1
        obtain ⟨output, outputReads, same⟩ :=
          instantiateUnivParams_readAnnotated resources scope reading accepted
        refine ⟨.const ref (arguments.toList.map readLevel), output, ?_, outputReads,
          same.typing (TypingClaim.const support.found length)⟩
        simp [readExpr?, support.resolved, AExpr.erase]
      · simp only [bne_iff_ne] at accepted
        rw [if_pos arity] at accepted
        contradiction

/-- The ordinary production inference entry point, including its actual key
lookup and final cache write, refines polymorphic constant typing on misses. -/
theorem infer_const_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {context : Model.Context β} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {methods : Methods .anon} {before after : TcState .anon} {type : KExpr .anon}
    (miss : UncachedInference before (.const id arguments info))
    (support : ConstantInferenceSupport resolve entries miss.keyed id arguments ref entry)
    (wellFormed : entries.WF)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok type after) :
    ModelTyping.{u,v} resolve entries context (.const id arguments info) type := by
  obtain ⟨state, run⟩ := infer_uncached_success miss accepted
  exact inferUncached_const_sound support wellFormed run

end Ix.Kernel.Consistency
