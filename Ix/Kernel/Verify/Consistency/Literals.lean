/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InferenceCache

/-!
# Natural-number literal inference

The production dispatcher types a literal by the interned constant at the
primitive `Nat` address installed in the checker state. `PrimitiveNatBinding`
is the static binding of that address to a model entry carrying a `natural`
fact: like `StandaloneModelBinding` it inspects no mutable checker state, and
the final theorem will discharge it from the admission of the primitive `Nat`
block. The uncached branch is refined exactly; the public branch is refined
through both cache partitions, with agreement and frame lemmas at the
literal's key mirroring the sort ones.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The primitive `Nat` address resolves to an admitted entry whose facts
contain the natural-number producer. The entry is monomorphic, and its type is
a closed sort so the literal's returned type has a formation level. The
binding is static data about the resolver, interface, and primitive table,
like `StandaloneModelBinding`: it inspects no checker state or cache. The
final theorem discharges it from the admission of the primitive `Nat` block
and its model-side facts (plan items WP5 and WP6); until then it is a premise
of every literal-inference statement. -/
structure PrimitiveNatBinding {β : Type u} {m : Mode} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (prims : Primitives m) where
  ref : ConstRef β
  entry : ConstantEntry β
  zero : ConstRef β
  succ : ConstRef β
  level : VLevel
  resolved : resolve prims.nat.addr = some ref
  found : entries ref = some entry
  natural : .natural zero succ ∈ entry.facts
  monomorphic : entry.universes = 0
  typeSort : entry.type = .sort level
  closed : level.WF 0

namespace PrimitiveNatBinding

variable {β : Type u} {m : Mode} {resolve : Address → Option (ConstRef β)}
  {entries : Model.Environment β} {prims : Primitives m}

/-- The binding depends on the primitive table only through the `Nat` address. -/
def ofPrims (binding : PrimitiveNatBinding resolve entries prims) {prims' : Primitives m}
    (same : prims.nat = prims'.nat) : PrimitiveNatBinding resolve entries prims' :=
  { binding with resolved := by rw [← same]; exact binding.resolved }

@[simp] theorem ofPrims_ref (binding : PrimitiveNatBinding resolve entries prims)
    {prims' : Primitives m} (same : prims.nat = prims'.nat) :
    (binding.ofPrims same).ref = binding.ref := rfl

@[simp] theorem ofPrims_level (binding : PrimitiveNatBinding resolve entries prims)
    {prims' : Primitives m} (same : prims.nat = prims'.nat) :
    (binding.ofPrims same).level = binding.level := rfl

/-- The model's literal rule at the bound entry. -/
theorem typing (binding : PrimitiveNatBinding resolve entries prims)
    (context : Model.Context β) (value : Nat) :
    TypingClaim.{u,v} entries context (.natLit value) (.const binding.ref []) :=
  TypingClaim.natLit binding.found binding.natural binding.monomorphic value

/-- The literal's type is formed at the entry's closed sort level. -/
theorem formation (binding : PrimitiveNatBinding resolve entries prims) (context : Model.Context β) :
    TypingClaim.{u,v} entries context (.const binding.ref []) (.sort binding.level) := by
  have typed := TypingClaim.const (Γ := context) (ls := []) binding.found
    (by simpa using binding.monomorphic.symm)
  have stable : binding.entry.type.instL [] = .sort binding.level := by
    rw [binding.typeSort]
    change AExpr.sort (binding.level.inst []) = _
    rw [show ([] : List VLevel) = VLevel.params 0 from rfl, VLevel.inst_id binding.closed]
  simpa only [stable] using typed

end PrimitiveNatBinding

/-- The production constant smart constructor reads as the resolved reference
with its universe arguments, in every local context. -/
@[simp] theorem readScopedExpr?_mkConst (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (id : KId m) (levels : Array (KUniv m)) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkConst id levels) depth = do
      return .const (← resolve id.addr) (levels.toList.map readLevel) := rfl

@[simp] theorem readExpr?_mkConst (resolve : Address → Option (ConstRef β))
    (id : KId m) (levels : Array (KUniv m)) :
    readExpr? resolve (KExpr.mkConst id levels) = do
      return .const (← resolve id.addr) (levels.toList.map readLevel) := rfl

/-- The bound `Nat` constant reads as the bound reference. -/
theorem PrimitiveNatBinding.typeReading {β : Type u} {m : Mode}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {prims : Primitives m} (binding : PrimitiveNatBinding resolve entries prims)
    (locals : List FVarId) (depth : Nat := 0) :
    readScopedExpr? resolve locals (KExpr.mkConst prims.nat #[]) depth =
      some (AExpr.const binding.ref []).erase := by
  simp [binding.resolved, AExpr.erase]

/-- Key computation changes only the context-digest memo; the primitive table
installed at construction is retained. -/
theorem inferKey_prims {term : KExpr .anon} {before after : TcState .anon}
    {key : Address × Address}
    (run : TcM.inferKey term before = .ok key after) : after.prims = before.prims := by
  unfold TcM.inferKey at run
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
  unfold TcM.ctxAddrForLbr at run
  change EStateM.bind (fun state => EStateM.bind (get : TcM .anon (TcState .anon))
    _ state) _ before = _ at run
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl] at run
  by_cases fast : (term.lbr == 0 || before.ctx.isEmpty) = true
  · rw [if_pos fast] at run
    cases run; rfl
  · rw [if_neg fast] at run
    cases cached : before.ctxAddrCache[(before.ctxId, term.lbr)]? with
    | none => rw [cached] at run; cases run; rfl
    | some address => rw [cached] at run; cases run; rfl

theorem UncachedInference.prims {term : KExpr .anon} {before : TcState .anon}
    (miss : UncachedInference before term) : miss.keyed.prims = before.prims :=
  inferKey_prims miss.keyRun

/-- The exact operational content of the literal branch: it interns the
constant at the installed primitive `Nat` address and updates only the intern
table. -/
theorem inferUncached_nat_run {m : Mode}
    {inferRec : KExpr m → RecM m (KExpr m)} {inferOnly : Bool}
    {methods : Methods m} {before after : TcState m}
    {value : Nat} {blob : Address} {info : ExprInfo m} {type : KExpr m}
    (accepted : RecM.inferUncached inferRec inferOnly (.nat value blob info) methods before =
      .ok type after) :
    type = (before.env.intern.internExpr (KExpr.mkConst before.prims.nat #[])).1 ∧
      after = { before with env := { before.env with intern :=
        (before.env.intern.internExpr (KExpr.mkConst before.prims.nat #[])).2 } } := by
  change EStateM.Result.ok
      (before.env.intern.internExpr (KExpr.mkConst before.prims.nat #[])).1
      { before with env := { before.env with intern :=
        (before.env.intern.internExpr (KExpr.mkConst before.prims.nat #[])).2 } } =
    .ok type after at accepted
  cases accepted
  exact ⟨rfl, rfl⟩

/-- Every successful execution of the production literal branch returns the
interned primitive `Nat` constant, whose scoped reading is the bound
reference, and the model literal rule types the source at that reference.
The intern-table premises are its concrete key coherence and collision
freedom on the table support plus the newly constructed constant. -/
theorem inferUncached_nat_sound {β : Type u} {m : Mode}
    {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} (locals : List FVarId)
    {inferRec : KExpr m → RecM m (KExpr m)} {inferOnly : Bool}
    {methods : Methods m} {before after : TcState m}
    {value : Nat} {blob : Address} {info : ExprInfo m} {type : KExpr m}
    (binding : PrimitiveNatBinding resolve entries before.prims)
    (coherent : before.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun e =>
      before.env.intern.ExprSupport e ∨ e = KExpr.mkConst before.prims.nat #[])
    (accepted : RecM.inferUncached inferRec inferOnly (.nat value blob info) methods before =
      .ok type after) :
    type = (before.env.intern.internExpr (KExpr.mkConst before.prims.nat #[])).1 ∧
      after = { before with env := { before.env with intern :=
        (before.env.intern.internExpr (KExpr.mkConst before.prims.nat #[])).2 } } ∧
      readScopedExpr? resolve locals type = some (AExpr.const binding.ref []).erase ∧
      TypingClaim.{u,v} entries context (.natLit value) (.const binding.ref []) := by
  obtain ⟨rfl, rfl⟩ := inferUncached_nat_run accepted
  refine ⟨rfl, rfl, ?_, binding.typing context value⟩
  rw [internExpr_readScopedExpr? coherent faithful]
  exact binding.typeReading locals

/-- The same branch in the closed model-typing postcondition used by the
sort branch. -/
theorem inferUncached_nat_modelTyping {β : Type u} {m : Mode}
    {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β}
    {inferRec : KExpr m → RecM m (KExpr m)} {inferOnly : Bool}
    {methods : Methods m} {before after : TcState m}
    {value : Nat} {blob : Address} {info : ExprInfo m} {type : KExpr m}
    (binding : PrimitiveNatBinding resolve entries before.prims)
    (coherent : before.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun e =>
      before.env.intern.ExprSupport e ∨ e = KExpr.mkConst before.prims.nat #[])
    (accepted : RecM.inferUncached inferRec inferOnly (.nat value blob info) methods before =
      .ok type after) :
    ModelTyping.{u,v} resolve entries context (.nat value blob info) type := by
  obtain ⟨rfl, rfl⟩ := inferUncached_nat_run accepted
  refine ⟨.natLit value, .const binding.ref [], rfl, ?_, binding.typing context value⟩
  rw [internExpr_readExpr? coherent faithful]
  simp [binding.resolved, AExpr.erase]

/-- Literal inference through both cache lookups and the final cache write,
under the same explicit miss boundary as constant inference. In anonymous mode
the interned constant is exactly the smart-constructed one. -/
theorem infer_nat_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {value : Nat} {blob : Address} {info : ExprInfo .anon}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (miss : UncachedInference before (.nat value blob info))
    (binding : PrimitiveNatBinding resolve entries before.prims)
    (coherent : miss.keyed.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun term => miss.keyed.env.intern.ExprSupport term ∨
      term = KExpr.mkConst before.prims.nat #[])
    (accepted : RecM.infer (.nat value blob info) methods before = .ok result after) :
    result = KExpr.mkConst before.prims.nat #[] ∧
      readScopedExpr? resolve locals result = some (AExpr.const binding.ref []).erase ∧
      ScopedModelTyping.{u,v} resolve entries locals context (.nat value blob info) result := by
  obtain ⟨state, run⟩ := infer_uncached_success miss accepted
  have prims := miss.prims
  obtain ⟨rfl, rfl⟩ := inferUncached_nat_run run
  rw [prims]
  have canonical := miss.keyed.env.intern.internExpr_eraseMeta coherent faithful
  simp only [KExpr.eraseMeta_anon] at canonical
  refine ⟨canonical, ?_, ?_⟩
  · rw [canonical]
    exact binding.typeReading locals
  · refine ⟨.natLit value, .const binding.ref [], rfl, ?_, binding.typing context value⟩
    rw [canonical]
    exact binding.typeReading locals

/-- A cached literal whose entry is the primitive `Nat` constant synthesizes
that constant under any active locals. No intern-table resources are needed
when the selected result is cached. -/
theorem infer_nat_cached_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {before after : TcState .anon} {value : Nat} {blob : Address} {info : ExprInfo .anon}
    {methods : Methods .anon} {result : KExpr .anon}
    (hit : InferenceCacheHit before (.nat value blob info))
    (binding : PrimitiveNatBinding resolve entries before.prims)
    (canonical : hit.cached = KExpr.mkConst before.prims.nat #[])
    (accepted : RecM.infer (.nat value blob info) methods before = .ok result after) :
    readScopedExpr? resolve locals result = some (AExpr.const binding.ref []).erase ∧
      TypingClaim.{u,v} entries context (.natLit value) (.const binding.ref []) := by
  rw [hit.run methods] at accepted
  cases accepted
  rw [canonical]
  exact ⟨binding.typeReading locals, binding.typing context value⟩

/-- Both policies return the exact primitive `Nat` constant and retain
agreement at the literal's key. The miss branch establishes this through
interning and the real cache write; the hit branch reads it from the
maintained invariant. -/
theorem infer_nat_cache_agreement {before keyed after : TcState .anon}
    {value : Nat} {blob : Address} {info : ExprInfo .anon} {key : Address × Address}
    {methods : Methods .anon} {result : KExpr .anon}
    (keyRun : TcM.inferKey (.nat value blob info) before = .ok key keyed)
    (agreement : InferenceCacheAgreement keyed key (KExpr.mkConst before.prims.nat #[]))
    (coherent : keyed.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun term => keyed.env.intern.ExprSupport term ∨
      term = KExpr.mkConst before.prims.nat #[])
    (accepted : RecM.infer (.nat value blob info) methods before = .ok result after) :
    result = KExpr.mkConst before.prims.nat #[] ∧
      InferenceCacheAgreement after key (KExpr.mkConst before.prims.nat #[]) := by
  have prims := inferKey_prims keyRun
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · rw [hit.run methods] at accepted
    cases accepted
    refine ⟨InferenceCacheAgreement.selected hit ?_, ?_⟩
    · simpa only [keyEq, stateEq] using agreement
    · simpa only [stateEq] using agreement
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    obtain ⟨rfl, rfl⟩ := inferUncached_nat_run run
    have keyedFaithful : KExpr.KeyCollisionFree fun term => keyed.env.intern.ExprSupport term ∨
        term = KExpr.mkConst keyed.prims.nat #[] := by
      rw [prims]; exact faithful
    have canonical := keyed.env.intern.internExpr_eraseMeta coherent keyedFaithful
    simp only [KExpr.eraseMeta_anon] at canonical
    refine ⟨canonical.trans (by rw [prims]), ?_⟩
    have unchanged : InferenceCacheAgreement
        { keyed with env := { keyed.env with intern :=
          (keyed.env.intern.internExpr (KExpr.mkConst keyed.prims.nat #[])).2 } }
        key (KExpr.mkConst before.prims.nat #[]) := ⟨agreement.full, agreement.only⟩
    apply unchanged.write (policy := before.inferOnly) (methods := methods)
    rw [cacheInferResult_eq]
    rw [keyEq, canonical] at written
    rw [written, prims]

/-- A successful literal call preserves every other cache key and all loaded
declarations. This frame is operational and needs no typing or cache
agreement premise, even when the call writes a new result at its own key. -/
theorem infer_nat_cache_frame {before keyed after : TcState .anon}
    {value : Nat} {blob : Address} {info : ExprInfo .anon} {key other : Address × Address}
    {methods : Methods .anon} {result : KExpr .anon}
    (keyRun : TcM.inferKey (.nat value blob info) before = .ok key keyed)
    (different : key ≠ other)
    (accepted : RecM.infer (.nat value blob info) methods before = .ok result after) :
    InferenceCacheFrame other before after := by
  have keyFrame := PreservesInferenceCache.inferKey other (.nat value blob info) before
  rw [keyRun] at keyFrame
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · rw [hit.run methods] at accepted
    cases accepted
    simpa only [stateEq] using keyFrame
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    obtain ⟨rfl, rfl⟩ := inferUncached_nat_run run
    apply keyFrame.trans
    rw [keyEq] at written
    rw [written]
    cases policy : before.inferOnly <;> apply InferenceCacheFrame.of_eq <;>
      simp [Std.HashMap.getElem?_insert, different]

end Ix.Kernel.Consistency
