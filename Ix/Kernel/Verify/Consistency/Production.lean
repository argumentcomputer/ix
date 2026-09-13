/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Driver
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.BinderInference

/-!
# Standalone production declaration checks

These theorems invert the public checker, including its error isolation,
initial lazy lookup, block routing, per-constant reset, validation, type
inference, theorem guard, value inference, and conversion. The supported
conversion path is the initial address-equality branch. Finite address
faithfulness connects that comparison to the exact model syntax.

Operational equations and interface agreement suffice to derive body typing.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

private theorem bind_success {α β : Type} {x : TcM .anon α} {k : α → TcM .anon β}
    {before after : TcState .anon} {value : β}
    (accepted : EStateM.bind x k before = .ok value after) :
    ∃ intermediate state, x before = .ok intermediate state ∧
      k intermediate state = .ok value after := by
  rw [EStateM.bind] at accepted
  cases run : x before with
  | error err state => rw [run] at accepted; contradiction
  | ok intermediate state =>
      rw [run] at accepted
      exact ⟨intermediate, state, rfl, accepted⟩

/-- The lookup, routing, and reset states reached by a standalone public check. -/
structure StandalonePrefix (id : KId .anon) (before : TcState .anon)
    (concrete : KConst .anon) where
  first : KConst .anon
  loaded : TcState .anon
  routed : TcState .anon
  reset : TcState .anon
  ready : TcState .anon
  firstGet : TcM.getConst id before = .ok first loaded
  route : (RecM.coordinatedBlockFor first).run (methodsN before.recFuel.toNat)
    loaded = .ok none routed
  resetRun : TcM.reset routed = .ok () reset
  memberGet : TcM.getConst id reset = .ok concrete ready

/-- Public success entails member success through the error-isolation wrapper. -/
theorem StandalonePrefix.member_success {id : KId .anon}
    {before after : TcState .anon} {concrete : KConst .anon}
    (path : StandalonePrefix id before concrete)
    (accepted : TcM.checkConst id before = .ok () after) :
    (RecM.checkConstMember id concrete).run (methodsN before.recFuel.toNat)
      path.ready = .ok () after := by
  unfold TcM.checkConst TcM.isolateCheckErrors at accepted
  cases run : TcM.runRec (RecM.checkConst id) before with
  | error err failed => rw [run] at accepted; contradiction
  | ok result finished =>
      rw [run] at accepted
      cases accepted
      change (RecM.checkConst id).run (methodsN before.recFuel.toNat) before =
        .ok () after at run
      unfold RecM.checkConst at run
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at run
      change EStateM.bind (TcM.getConst id) _ before = _ at run
      rw [EStateM.bind, path.firstGet] at run
      change EStateM.bind
        ((RecM.coordinatedBlockFor path.first).run (methodsN before.recFuel.toNat))
        _ path.loaded = _ at run
      rw [EStateM.bind, path.route] at run
      change (RecM.checkConstMemberFresh id).run (methodsN before.recFuel.toNat)
        path.routed = .ok () after at run
      unfold RecM.checkConstMemberFresh at run
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at run
      change EStateM.bind TcM.reset _ path.routed = _ at run
      rw [EStateM.bind, path.resetRun] at run
      change EStateM.bind (TcM.getConst id) _ path.reset = _ at run
      rw [EStateM.bind, path.memberGet] at run
      exact run

/-- Monomorphic definition data. Its complete concrete declaration is the
one returned by the production lookup, including kind, safety, and block. -/
structure DefinitionInput where
  id : KId .anon
  kind : Ix.DefKind
  safety : Ix.DefinitionSafety
  hints : Lean.ReducibilityHints
  type : KExpr .anon
  value : KExpr .anon
  block : KId .anon

def DefinitionInput.constant (input : DefinitionInput) : KConst .anon :=
  .defn () () input.kind input.safety input.hints 0 input.type input.value () input.block

/-- Closed sort/alias inference, a specialization of an existing constant,
or a finite binder inference tree with a separately checked declared type.
Specializations supply raw syntax and occurrence annotations; successful
inference derives their typing, scope, and references. Binder definitions
also supply syntactic scope and references to the preceding interface. Every
case derives body typing without a semantic typing premise. -/
inductive DefinitionBodySupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    (methods : Methods .anon)
    (before : TcState .anon) (declared : KExpr .anon) :
    KExpr .anon → AExpr β → AExpr β → Type u
  | atomic {term : KExpr .anon} {body type : AExpr β}
      (inference : AtomicInference resolve entries before term body type) :
      DefinitionBodySupport resolve entries methods before declared term body type
  | specialization {id : KId .anon} {arguments : Array (KUniv .anon)}
      {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
      (misses : UncachedInference before (.const id arguments info))
      (support : ConstantInferenceSupport resolve entries misses.keyed id arguments ref entry)
      (closed : ∀ level ∈ arguments, (readLevel level).WF 0)
      (reading : readExpr? resolve declared = some type.erase)
      (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations =
        type.annotations) :
      DefinitionBodySupport resolve entries methods before declared (.const id arguments info)
        (.const ref (arguments.toList.map readLevel)) type
  | binder {fuel : Nat} {term inferredType : KExpr .anon}
      {body type : AExpr β} {level : VLevel} {typeBefore typeAfter : TcState .anon}
      (tied : methods = methodsN fuel)
      (valueInference : BinderInference resolve entries [] [] fuel before term body type)
      (typeInference : BinderInference resolve entries [] [] fuel typeBefore declared type (.sort level))
      (typeRun : RecM.infer declared methods typeBefore = .ok inferredType typeAfter)
      (valueReading : readScopedExpr? resolve [] term = some body.erase)
      (typeReading : readScopedExpr? resolve [] declared = some type.erase)
      (scope : body.Scope 0 0 ∧ type.Scope 0 0)
      (references : body.ReferencesIn entries ∧ type.ReferencesIn entries) :
      DefinitionBodySupport resolve entries methods before declared term body type

theorem DefinitionBodySupport.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {term declared inferred : KExpr .anon}
    {body type : AExpr β} {methods : Methods .anon}
    (fragment : DefinitionBodySupport resolve entries methods before declared term body type)
    (wellFormed : entries.WF)
    (accepted : RecM.infer term methods before = .ok inferred after)
    (faithful : inferred.AddrFaithful declared) (hashPath : (inferred == declared) = true) :
    readExpr? resolve term = some body.erase ∧
      readExpr? resolve declared = some type.erase ∧
      body.Scope 0 0 ∧ type.Scope 0 0 ∧
      body.ReferencesIn entries ∧ type.ReferencesIn entries ∧
      TypingClaim.{u,v} entries [] body type := by
  have hashReads := beq_readExpr? (resolve := resolve) faithful hashPath
  cases fragment with
  | atomic inference =>
      obtain ⟨valueReads, typeReads, typed⟩ := inference.sound accepted
      obtain ⟨bodyScope, typeScope, bodyRefs, typeRefs⟩ :=
        inference.support.scopeAndReferences wellFormed
      exact ⟨valueReads, hashReads.symm.trans typeReads,
        bodyScope, typeScope, bodyRefs, typeRefs, typed⟩
  | specialization misses support closed reading conditions =>
      obtain ⟨output, reads, same, arity, scope, references⟩ :=
        infer_const_refinement misses support wellFormed accepted
      have equal := AExpr.eq_of_erase_annotations
        (Option.some.inj (reads.symm.trans (hashReads.trans reading)))
        (same.annotations.symm.trans conditions)
      refine ⟨?_, reading, ?_, equal ▸ scope 0 closed, ?_, ?_,
        equal ▸ same.typing (TypingClaim.const support.found arity)⟩
      · simp [readExpr?, support.resolved, AExpr.erase]
      · intro level member
        obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
        exact closed value (by simpa using valueMember)
      · intro ref member
        simp only [AExpr.references, List.mem_singleton] at member
        subst ref
        simp only [support.found, Option.isSome_some]
      · intro ref member
        rw [← equal, references] at member
        exact wellFormed.typeReferences _ _ support.found ref member
  | binder tied valueInference typeInference typeRun valueReading typeReading scope references =>
      subst methods
      obtain ⟨_, typeChecked⟩ := typeInference.sound (LocalContextReading.empty _ _)
        typeReading typeRun
      obtain ⟨_, valueChecked⟩ := valueInference.sound (LocalContextReading.empty _ _)
        valueReading accepted
      exact ⟨readScopedExpr?_closed valueReading, readScopedExpr?_closed typeReading,
        scope.1, scope.2, references.1, references.2, valueChecked.typing typeChecked.typingSort⟩

/-- The execution prefix through value conversion. A successful member check
also passes the subsequent safety checks. -/
structure DefinitionBodyTrace (input : DefinitionInput) (methods : Methods .anon)
    (before : TcState .anon) where
  validated : TcState .anon
  inferredType : KExpr .anon
  typeState : TcState .anon
  level : KUniv .anon
  valueStart : TcState .anon
  inferredValue : KExpr .anon
  conversionStart : TcState .anon
  conversionEnd : TcState .anon
  validationRun : (RecM.validateConstWellScoped input.constant).run methods before =
    .ok () validated
  typeRun : (RecM.infer input.type).run methods validated = .ok inferredType typeState
  sortRun : (RecM.ensureSortDirect inferredType).run methods typeState = .ok level valueStart
  theoremGuard : (input.kind == .thm && !univEq level .mkZero) = false
  valueRun : (RecM.infer input.value).run methods valueStart = .ok inferredValue conversionStart
  conversionRun : (RecM.isDefEq inferredValue input.type).run methods conversionStart =
    .ok true conversionEnd

/-- Extract the execution trace from a successful production member check. -/
theorem definition_body_trace {input : DefinitionInput} {methods : Methods .anon}
    {before after : TcState .anon}
    (accepted : (RecM.checkConstMember input.id input.constant).run methods before =
      .ok () after) : Nonempty (DefinitionBodyTrace input methods before) := by
  unfold RecM.checkConstMember at accepted
  simp only [DefinitionInput.constant, Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind] at accepted
  change EStateM.bind ((RecM.validateConstWellScoped input.constant).run methods)
    _ before = _ at accepted
  obtain ⟨⟨⟩, validated, validationRun, accepted⟩ := bind_success accepted
  change EStateM.bind ((RecM.infer input.type).run methods) _ validated = _ at accepted
  obtain ⟨inferredType, typeState, typeRun, accepted⟩ := bind_success accepted
  change EStateM.bind ((RecM.ensureSortDirect inferredType).run methods)
    _ typeState = _ at accepted
  obtain ⟨level, valueStart, sortRun, accepted⟩ := bind_success accepted
  by_cases guard : input.kind == .thm && !univEq level .mkZero
  · simp only [guard, if_true] at accepted
    contradiction
  · simp only [guard, Bool.false_eq_true, if_false, ReaderT.run_bind] at accepted
    change EStateM.bind ((RecM.infer input.value).run methods) _ valueStart = _ at accepted
    obtain ⟨inferredValue, conversionStart, valueRun, accepted⟩ := bind_success accepted
    change EStateM.bind ((RecM.isDefEq inferredValue input.type).run methods)
      _ conversionStart = _ at accepted
    obtain ⟨answer, conversionEnd, conversionRun, accepted⟩ := bind_success accepted
    cases answer with
    | false =>
        simp only [Bool.not_false, if_true] at accepted
        contradiction
    | true =>
        exact ⟨{
          validated, inferredType, typeState, level, valueStart,
          inferredValue, conversionStart, conversionEnd,
          validationRun, typeRun, sortRun,
          theoremGuard := Bool.eq_false_iff.mpr guard, valueRun, conversionRun }⟩

/-- Operational support for the selected production definition fragment.
Resources are required only at the states exposed by successful body traces.
The conversion guard records the actual initial hash-equality path. -/
structure AtomicDefinitionRun {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (input : DefinitionInput) (before : TcState .anon)
    (body type : AExpr β) where
  path : StandalonePrefix input.id before input.constant
  inference : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
    DefinitionBodySupport resolve entries (methodsN before.recFuel.toNat)
      trace.valueStart input.type input.value body type
  hashPath : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
    (trace.inferredValue == input.type) = true
  faithful : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
    trace.inferredValue.AddrFaithful input.type

/-- Successful production checking yields a model typing judgment for the
actual value and declared type, with syntactic closure and dependency support
needed to extend a model. -/
theorem AtomicDefinitionRun.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {input : DefinitionInput} {before after : TcState .anon} {body type : AExpr β}
    (fragment : AtomicDefinitionRun resolve entries input before body type)
    (wellFormed : entries.WF)
    (accepted : TcM.checkConst input.id before = .ok () after) :
    readExpr? resolve input.value = some body.erase ∧
      readExpr? resolve input.type = some type.erase ∧
      body.Scope 0 0 ∧ type.Scope 0 0 ∧
      body.ReferencesIn entries ∧ type.ReferencesIn entries ∧
      TypingClaim.{u,v} entries [] body type := by
  obtain ⟨trace⟩ := definition_body_trace (fragment.path.member_success accepted)
  exact (fragment.inference trace).sound wellFormed trace.valueRun
    (fragment.faithful trace) (fragment.hashPath trace)

/-- A fresh definition cannot justify its type through a self-reference:
its value, at any universe arguments, must reference the preceding interface. -/
theorem AtomicDefinitionRun.no_self_alias {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {input : DefinitionInput} {before after : TcState .anon} {body type : AExpr β}
    (fragment : AtomicDefinitionRun resolve entries input before body type)
    (wellFormed : entries.WF) {ref : ConstRef β}
    (resolved : resolve input.id.addr = some ref) (fresh : entries ref = none)
    {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    (self : input.value = .const input.id arguments info)
    (accepted : TcM.checkConst input.id before = .ok () after) : False := by
  obtain ⟨reads, _, _, _, references, _, _⟩ :=
    AtomicDefinitionRun.sound.{u,0} fragment wellFormed accepted
  rw [self] at reads
  simp [readExpr?, resolved] at reads
  have bodyEq := AExpr.eq_const_of_erase_eq reads.symm
  rw [bodyEq] at references
  have present := references ref (by simp [AExpr.references])
  simp only [fresh, Option.isSome_none, Bool.false_eq_true] at present

end Ix.Kernel.Consistency
