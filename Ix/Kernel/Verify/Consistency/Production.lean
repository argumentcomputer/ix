/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Driver
import Ix.Kernel.Verify.Consistency.Atomic

/-!
# Standalone production declaration checks

These theorems invert the real public checker, including its error isolation,
initial lazy lookup, block routing, per-constant reset, validation, type
inference, theorem guard, value inference, and conversion. The supported
conversion path is the initial address-equality branch. Finite address
faithfulness connects that comparison to the exact model syntax.

The resource records contain operational equations and structural interface
agreement. They do not contain a typing proof, a method-soundness callback,
or an assumption that an accepted declaration already has a model.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

private theorem runTcBind {α β : Type} (x : TcM .anon α) (k : α → TcM .anon β)
    (state : TcState .anon) :
    EStateM.bind x k state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  unfold EStateM.bind
  cases x state <;> rfl

/-- The concrete path of a standalone public check. This ties the member
declaration to both production lookup and the actual reset, without assuming
that block coordination or lazy ingress preserves an arbitrary predicate. -/
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

/-- Success at the public boundary entails success of the exact member
identified by the standalone path. In particular, an error cannot be
turned into acceptance by the public cache rollback wrapper. -/
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
      rw [runTcBind, path.firstGet] at run
      change EStateM.bind
        ((RecM.coordinatedBlockFor path.first).run (methodsN before.recFuel.toNat))
        _ path.loaded = _ at run
      rw [runTcBind, path.route] at run
      change (RecM.checkConstMemberFresh id).run (methodsN before.recFuel.toNat)
        path.routed = .ok () after at run
      unfold RecM.checkConstMemberFresh at run
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at run
      change EStateM.bind TcM.reset _ path.routed = _ at run
      rw [runTcBind, path.resetRun] at run
      change EStateM.bind (TcM.getConst id) _ path.reset = _ at run
      rw [runTcBind, path.memberGet] at run
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

/-- Exact successful observations through a definition's value-conversion
call. Later safety checks may still reject; the extraction theorem requires
the entire member check to have succeeded. -/
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

/-- Invert the production declaration branch rather than assuming that its
acceptance establishes either type or value typing. -/
theorem definition_body_trace {input : DefinitionInput} {methods : Methods .anon}
    {before after : TcState .anon}
    (accepted : (RecM.checkConstMember input.id input.constant).run methods before =
      .ok () after) : Nonempty (DefinitionBodyTrace input methods before) := by
  unfold RecM.checkConstMember at accepted
  simp only [DefinitionInput.constant, Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind] at accepted
  cases validation : (RecM.validateConstWellScoped input.constant).run methods before with
  | error err failed =>
      change EStateM.bind ((RecM.validateConstWellScoped input.constant).run methods)
        _ before = _ at accepted
      rw [runTcBind, validation] at accepted
      contradiction
  | ok result validated =>
      cases result
      change EStateM.bind ((RecM.validateConstWellScoped input.constant).run methods)
        _ before = _ at accepted
      rw [runTcBind, validation] at accepted
      change EStateM.bind ((RecM.infer input.type).run methods) _ validated = _ at accepted
      cases typeRun : (RecM.infer input.type).run methods validated with
      | error err failed => rw [runTcBind, typeRun] at accepted; contradiction
      | ok inferredType typeState =>
          rw [runTcBind, typeRun] at accepted
          change EStateM.bind ((RecM.ensureSortDirect inferredType).run methods)
            _ typeState = _ at accepted
          cases sortRun : (RecM.ensureSortDirect inferredType).run methods typeState with
          | error err failed => rw [runTcBind, sortRun] at accepted; contradiction
          | ok level valueStart =>
              rw [runTcBind, sortRun] at accepted
              simp only at accepted
              by_cases guard : input.kind == .thm && !univEq level .mkZero
              · simp only [guard, if_true] at accepted
                contradiction
              · simp only [guard, Bool.false_eq_true, if_false, ReaderT.run_bind] at accepted
                cases valueRun : (RecM.infer input.value).run methods valueStart with
                | error err failed =>
                    change EStateM.bind ((RecM.infer input.value).run methods)
                      _ valueStart = _ at accepted
                    rw [runTcBind, valueRun] at accepted
                    contradiction
                | ok inferredValue conversionStart =>
                    change EStateM.bind ((RecM.infer input.value).run methods)
                      _ valueStart = _ at accepted
                    rw [runTcBind, valueRun] at accepted
                    change EStateM.bind ((RecM.isDefEq inferredValue input.type).run methods)
                      _ conversionStart = _ at accepted
                    cases conversionRun : (RecM.isDefEq inferredValue input.type).run methods
                        conversionStart with
                    | error err failed => rw [runTcBind, conversionRun] at accepted; contradiction
                    | ok answer conversionEnd =>
                        rw [runTcBind, conversionRun] at accepted
                        cases answer with
                        | false =>
                            simp only [Bool.not_false, if_true] at accepted
                            contradiction
                        | true =>
                            exact ⟨{
                              validated, inferredType, typeState, level, valueStart,
                              inferredValue, conversionStart, conversionEnd,
                              validationRun := validation, typeRun, sortRun,
                              theoremGuard := Bool.eq_false_iff.mpr guard,
                              valueRun, conversionRun }⟩

/-- Operational support for the selected production definition fragment.
Resources are required only at the states exposed by successful body traces.
The conversion guard records the actual initial hash-equality path. -/
structure AtomicDefinitionRun {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (input : DefinitionInput) (before : TcState .anon)
    (body type : AExpr β) where
  path : StandalonePrefix input.id before input.constant
  inference : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
    AtomicInference resolve entries trace.valueStart input.value body type
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
  have result := (fragment.inference trace).sound trace.valueRun
  have same := beq_readExpr? (resolve := resolve)
    (fragment.faithful trace) (fragment.hashPath trace)
  have scope := (fragment.inference trace).support.scopeAndReferences wellFormed
  exact ⟨result.1, same.symm.trans result.2.1, scope.1, scope.2.1,
    scope.2.2.1, scope.2.2.2, result.2.2⟩

/-- A fresh definition cannot use itself as the atomic value that justifies
its own type. This exclusion follows from the preceding interface, without
any assumption about the consistency of the axioms. -/
theorem AtomicDefinitionRun.no_self_alias {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {input : DefinitionInput} {before after : TcState .anon} {body type : AExpr β}
    (fragment : AtomicDefinitionRun resolve entries input before body type)
    (wellFormed : entries.WF) {ref : ConstRef β}
    (resolved : resolve input.id.addr = some ref) (fresh : entries ref = none)
    {info : ExprInfo .anon} (self : input.value = .const input.id #[] info)
    (accepted : TcM.checkConst input.id before = .ok () after) : False := by
  have result := AtomicDefinitionRun.sound.{u,0} fragment wellFormed accepted
  have reads := result.1
  rw [self] at reads
  simp [readExpr?, resolved] at reads
  have bodyEq := AExpr.eq_const_of_erase_eq reads.symm
  have references := result.2.2.2.2.1
  rw [bodyEq] at references
  have present := references ref (by simp [AExpr.references])
  simp only [fresh, Option.isSome_none, Bool.false_eq_true] at present

end Ix.Kernel.Consistency
