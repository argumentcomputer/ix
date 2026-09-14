/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Driver
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.SynthesisInference
import Ix.Kernel.Verify.Consistency.BetaWhnfInference
import Ix.Kernel.Verify.Consistency.Validation

/-!
# Standalone production declaration checks

These theorems invert the public checker, including its error isolation,
initial lazy lookup, block routing, per-constant reset, validation, type
inference, theorem guard, value inference, and conversion. Supported
comparisons use address equality or beta reduction of the declared type,
justified by that declaration's actual type check. Finite address
faithfulness connects hash comparisons to model syntax.

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

/-- Definition data, including its declared universe arity. Its complete concrete declaration is the
one returned by the production lookup, including kind, safety, and block. -/
structure DefinitionInput where
  id : KId .anon
  kind : Ix.DefKind
  safety : Ix.DefinitionSafety
  hints : Lean.ReducibilityHints
  universes : UInt64 := 0
  type : KExpr .anon
  value : KExpr .anon
  block : KId .anon

def DefinitionInput.constant (input : DefinitionInput) : KConst .anon :=
  .defn () () input.kind input.safety input.hints input.universes
    input.type input.value () input.block

private theorem levelScope_mono {level : VLevel} {before after : Nat}
    (scopeOK : level.WF before) (bound : before ≤ after) : level.WF after := by
  induction level with
  | zero => trivial
  | succ level ih => exact ih scopeOK
  | max left right ihLeft ihRight | imax left right ihLeft ihRight =>
      exact ⟨ihLeft scopeOK.1, ihRight scopeOK.2⟩
  | param index => exact Nat.lt_of_lt_of_le scopeOK bound

private theorem expressionScope_mono {β : Type u} {term : AExpr β}
    {before after depth : Nat} (scopeOK : term.Scope before depth)
    (bound : before ≤ after) : term.Scope after depth := by
  have condition {p : Certified.PropWhen} (valid : p.WF before) : p.WF after := by
    cases p with
    | never => trivial
    | allZero indices sorted =>
        exact fun index member => Nat.lt_of_lt_of_le (valid index member) bound
  induction term generalizing depth with
  | bvar => exact scopeOK
  | sort => exact levelScope_mono scopeOK bound
  | const => exact fun level member => levelScope_mono (scopeOK level member) bound
  | app fn arg ihFn ihArg => exact ⟨ihFn scopeOK.1, ihArg scopeOK.2⟩
  | lam p domain body ihDomain ihBody | forallE p domain body ihDomain ihBody =>
      exact ⟨condition scopeOK.1, ihDomain scopeOK.2.1, ihBody scopeOK.2.2⟩
  | proj ref field major ih => exact ih scopeOK
  | natLit => trivial

/-- Closed sort/alias inference, a specialization of an existing constant,
a finite binder inference tree with a separately checked declared type, or
inference that derives formation of its own returned type.
Specializations supply raw syntax and occurrence annotations; successful
inference derives their typing, scope, and references. Universe arguments and
binder conditions may use the declaration's own parameters. Binder definitions
also supply syntactic scope and references to the preceding interface. Every
case derives body typing without a semantic typing premise. -/
inductive DefinitionBodySupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    (methods : Methods .anon)
    (before : TcState .anon) (declared : KExpr .anon) (universes : Nat) :
    KExpr .anon → AExpr β → AExpr β → Type u
  | atomic {term : KExpr .anon} {body type : AExpr β}
      (inference : AtomicInference resolve entries before term body type) :
      DefinitionBodySupport resolve entries methods before declared universes term body type
  | specialization {id : KId .anon} {arguments : Array (KUniv .anon)}
      {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
      (misses : UncachedInference before (.const id arguments info))
      (support : ConstantInferenceSupport resolve entries misses.keyed id arguments ref entry)
      (scopeOK : ∀ level ∈ arguments, (readLevel level).WF universes)
      (reading : readExpr? resolve declared = some type.erase)
      (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations =
        type.annotations) :
      DefinitionBodySupport resolve entries methods before declared universes (.const id arguments info)
        (.const ref (arguments.toList.map readLevel)) type
  | binder {fuel : Nat} {term inferredType : KExpr .anon}
      {body type : AExpr β} {level : VLevel} {typeBefore typeAfter : TcState .anon}
      (tied : methods = methodsN fuel)
      (valueInference : BinderInference resolve entries [] [] fuel before term body type)
      (typeInference : BinderInference resolve entries [] [] fuel typeBefore declared type (.sort level))
      (typeRun : RecM.infer declared methods typeBefore = .ok inferredType typeAfter)
      (valueReading : readScopedExpr? resolve [] term = some body.erase)
      (typeReading : readScopedExpr? resolve [] declared = some type.erase)
      (scope : body.Scope universes 0 ∧ type.Scope universes 0)
      (references : body.ReferencesIn entries ∧ type.ReferencesIn entries) :
      DefinitionBodySupport resolve entries methods before declared universes term body type
  | synthesis {fuel : Nat} {term : KExpr .anon} {body type : AExpr β} {level : VLevel}
      (tied : methods = methodsN fuel)
      (valueInference : SynthesisInference resolve entries [] [] [] fuel before term body type level)
      (valueReading : readScopedExpr? resolve [] term = some body.erase)
      (typeReading : readScopedExpr? resolve [] declared = some type.erase)
      (scope : body.Scope universes 0 ∧ type.Scope universes 0)
      (references : body.ReferencesIn entries ∧ type.ReferencesIn entries) :
      DefinitionBodySupport resolve entries methods before declared universes term body type

theorem DefinitionBodySupport.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {term declared inferred : KExpr .anon}
    {body type : AExpr β} {methods : Methods .anon} {universes : Nat}
    (fragment : DefinitionBodySupport resolve entries methods before declared universes term body type)
    (wellFormed : entries.WF)
    (accepted : RecM.infer term methods before = .ok inferred after)
    (faithful : inferred.AddrFaithful declared) (hashPath : (inferred == declared) = true) :
    readExpr? resolve term = some body.erase ∧
      readExpr? resolve declared = some type.erase ∧
      body.Scope universes 0 ∧ type.Scope universes 0 ∧
      body.ReferencesIn entries ∧ type.ReferencesIn entries ∧
      TypingClaim.{u,v} entries [] body type := by
  have hashReads := beq_readExpr? (resolve := resolve) faithful hashPath
  cases fragment with
  | atomic inference =>
      obtain ⟨valueReads, typeReads, typed⟩ := inference.sound accepted
      obtain ⟨bodyScope, typeScope, bodyRefs, typeRefs⟩ :=
        inference.support.scopeAndReferences wellFormed
      exact ⟨valueReads, hashReads.symm.trans typeReads,
        expressionScope_mono bodyScope (Nat.zero_le universes),
        expressionScope_mono typeScope (Nat.zero_le universes), bodyRefs, typeRefs, typed⟩
  | specialization misses support scopeOK reading conditions =>
      obtain ⟨output, reads, same, arity, scope, references⟩ :=
        infer_const_refinement misses support wellFormed accepted
      have equal := AExpr.eq_of_erase_annotations
        (Option.some.inj (reads.symm.trans (hashReads.trans reading)))
        (same.annotations.symm.trans conditions)
      refine ⟨?_, reading, ?_, equal ▸ scope universes scopeOK, ?_, ?_,
        equal ▸ same.typing (TypingClaim.const support.found arity)⟩
      · simp [readExpr?, support.resolved, AExpr.erase]
      · intro level member
        obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
        exact scopeOK value (by simpa using valueMember)
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
  | synthesis tied valueInference valueReading typeReading scope references =>
      subst methods
      obtain ⟨_, valueTyped, _⟩ := valueInference.closed_sound valueReading accepted
      exact ⟨readScopedExpr?_closed valueReading, readScopedExpr?_closed typeReading,
        scope.1, scope.2, references.1, references.2, valueTyped⟩

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

/-- Recover source universe and term scope from the validation that this
production member check actually executed. Only bounds on the extra model
binder conditions remain a separate syntactic check. -/
theorem DefinitionBodyTrace.scopes {β : Type u} {input : DefinitionInput}
    {methods : Methods .anon} {before : TcState .anon}
    (trace : DefinitionBodyTrace input methods before)
    {resolve : Address → Option (ConstRef β)} {body type : AExpr β}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (valueReading : readScopedExpr? resolve [] input.value = some body.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat body)
    (typeConditions : ConditionsScoped input.universes.toNat type) :
    body.Scope input.universes.toNat 0 ∧ type.Scope input.universes.toNat 0 := by
  have validated := trace.validationRun
  unfold RecM.validateConstWellScoped at validated
  change EStateM.bind
    ((RecM.validateExprWellScoped input.type 0 input.universes.toNat).run methods)
    _ before = _ at validated
  obtain ⟨⟨⟩, intermediate, typeRun, rest⟩ := bind_success validated
  change EStateM.bind
    ((RecM.validateExprWellScoped input.value 0 input.universes.toNat).run methods)
    _ intermediate = _ at rest
  obtain ⟨⟨⟩, _, valueRun, _⟩ := bind_success rest
  obtain ⟨_, _, _, typeScope⟩ := RecM.validateExprWellScoped_sound typeCoverage collision typeRun
  obtain ⟨_, _, _, valueScope⟩ := RecM.validateExprWellScoped_sound valueCoverage collision valueRun
  exact ⟨readScopedExpr?_annotated_scope valueReading valueScope valueConditions,
    readScopedExpr?_annotated_scope typeReading typeScope typeConditions⟩

/-- Build binder admission from the exact type and value inference calls of
a member trace. Production validation derives their source scope, including
the definition's own universe parameters. No whole-expression model scope
or semantic typing witness is supplied by this constructor. -/
def DefinitionBodyTrace.binderSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {body type : AExpr β} {level : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (valueInference : BinderInference resolve entries [] [] fuel trace.valueStart input.value body type)
    (typeInference : BinderInference resolve entries [] [] fuel trace.validated input.type type (.sort level))
    (valueReading : readScopedExpr? resolve [] input.value = some body.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat body)
    (typeConditions : ConditionsScoped input.universes.toNat type)
    (references : body.ReferencesIn entries ∧ type.ReferencesIn entries) :
    DefinitionBodySupport resolve entries (methodsN fuel) trace.valueStart input.type
      input.universes.toNat input.value body type :=
  .binder rfl valueInference typeInference trace.typeRun valueReading typeReading
    (trace.scopes typeCoverage valueCoverage collision valueReading typeReading
      valueConditions typeConditions)
    references

/-- Reuse the exact type inference performed by this declaration admission.
No extra inference on a generated codomain is postulated. -/
def DefinitionBodyTrace.checkedType {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {input : DefinitionInput} {fuel : Nat}
    {before : TcState .anon} (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {type : AExpr β} {level : VLevel}
    (inference : BinderInference resolve entries [] [] fuel trace.validated input.type type (.sort level))
    (reading : readScopedExpr? resolve [] input.type = some type.erase) :
    CheckedType resolve entries [] type level :=
  { locals := [], fuel, before := trace.validated, after := trace.typeState,
    source := input.type, result := trace.inferredType, inference,
    agreement := .empty _ _, reading, run := trace.typeRun }

/-- Retain a type check that uses the synthesis rules, including direct
lambda applications, for subsequent universe-instantiated constant calls. -/
def DefinitionBodyTrace.synthesisTypeCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {input : DefinitionInput} {fuel : Nat}
    {before : TcState .anon} (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {type : AExpr β} {level bound : VLevel}
    (inference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      type (.sort level) bound)
    (reading : readScopedExpr? resolve [] input.type = some type.erase) :
    SynthesisTypeCheck resolve entries type level :=
  { fuel, before := trace.validated, after := trace.typeState, source := input.type,
    result := trace.inferredType, bound, inference, reading, run := trace.typeRun }

/-- Public declaration-check success supplies the stored type-inference
execution. Only its finite inference tree and source reading remain inputs. -/
theorem StandalonePrefix.definitionTypeCheck {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {input : DefinitionInput} {before after : TcState .anon}
    (path : StandalonePrefix input.id before input.constant) {type : AExpr β} {level bound : VLevel}
    (inference : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
      Nonempty (SynthesisInference resolve entries [] [] [] before.recFuel.toNat trace.validated
        input.type type (.sort level) bound))
    (reading : readScopedExpr? resolve [] input.type = some type.erase)
    (accepted : TcM.checkConst input.id before = .ok () after) :
    Nonempty (SynthesisTypeCheck resolve entries type level) := by
  obtain ⟨trace⟩ := definition_body_trace (path.member_success accepted)
  obtain ⟨tree⟩ := inference trace
  exact ⟨trace.synthesisTypeCheck tree reading⟩

/-- Synthesis supplies the body's full typing and the generated type's
formation. Source validation still supplies the scope of the actual declared
type and value; reference coverage is composed at the admission boundary. -/
def DefinitionBodyTrace.synthesisSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {body type : AExpr β} {level : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value body type level)
    (valueReading : readScopedExpr? resolve [] input.value = some body.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat body)
    (typeConditions : ConditionsScoped input.universes.toNat type)
    (references : body.ReferencesIn entries ∧ type.ReferencesIn entries) :
    DefinitionBodySupport resolve entries (methodsN fuel) trace.valueStart input.type
      input.universes.toNat input.value body type :=
  .synthesis rfl valueInference valueReading typeReading
    (trace.scopes typeCoverage valueCoverage collision valueReading typeReading
      valueConditions typeConditions)
    references

/-- The actual declaration trace determines the type and value checks used
to justify conversion. A beta case reuses the declared type's executed
inference; it does not request another check of a generated type. -/
inductive DefinitionCheckSupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    {input : DefinitionInput} {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before) :
    AExpr β → AExpr β → Type u
  | hash {body type : AExpr β}
      (inference : DefinitionBodySupport resolve entries (methodsN fuel)
        trace.valueStart input.type input.universes.toNat input.value body type)
      (faithful : trace.inferredValue.AddrFaithful input.type)
      (hashPath : (trace.inferredValue == input.type) = true) :
      DefinitionCheckSupport resolve entries trace body type
  | betaDeclared {body domain inner argument : AExpr β} {condition : Certified.PropWhen}
      {level typeBound valueBound : VLevel}
      (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
        (.app (.lam condition domain inner) argument) (.sort level) typeBound)
      (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
        body (inner.inst argument) valueBound)
      (valueReading : readScopedExpr? resolve [] input.value = some body.erase)
      (typeReading : readScopedExpr? resolve [] input.type =
        some (AExpr.app (.lam condition domain inner) argument).erase)
      (scope : body.Scope input.universes.toNat 0 ∧
        (AExpr.app (.lam condition domain inner) argument).Scope input.universes.toNat 0)
      (references : body.ReferencesIn entries ∧
        (AExpr.app (.lam condition domain inner) argument).ReferencesIn entries) :
      DefinitionCheckSupport resolve entries trace body (.app (.lam condition domain inner) argument)
  | betaDeclaredSpine {value domain inner body : AExpr β} {condition : Certified.PropWhen}
      {consumed trailing : List (AExpr β)} {level typeBound valueBound : VLevel}
      (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
        ((AExpr.lam condition domain inner).appN (consumed ++ trailing)) (.sort level) typeBound)
      (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
        value ((body.instRev consumed).appN trailing) valueBound)
      (peeling : LambdaPeel (.lam condition domain inner) consumed.length body)
      (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
      (typeReading : readScopedExpr? resolve [] input.type =
        some ((AExpr.lam condition domain inner).appN (consumed ++ trailing)).erase)
      (scope : value.Scope input.universes.toNat 0 ∧
        ((AExpr.lam condition domain inner).appN (consumed ++ trailing)).Scope input.universes.toNat 0)
      (references : value.ReferencesIn entries ∧
        ((AExpr.lam condition domain inner).appN (consumed ++ trailing)).ReferencesIn entries) :
      DefinitionCheckSupport resolve entries trace value
        ((AExpr.lam condition domain inner).appN (consumed ++ trailing))
  | betaDeclaredTwice {value domain binder inner : AExpr β} {condition headCondition : Certified.PropWhen}
      {initialArguments arguments : List (AExpr β)} {count : Nat} {level typeBound valueBound : VLevel}
      (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
        (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
          ((AExpr.lam headCondition binder inner).appN initialArguments)) (.sort level) typeBound)
      (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
        value (AExpr.betaPrefix count (.lam headCondition binder inner)
          (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments))))
        valueBound)
      (enough : count ≤ inner.lambdaDepth + 1)
      (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
      (typeReading : readScopedExpr? resolve [] input.type =
        some (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
          ((AExpr.lam headCondition binder inner).appN initialArguments)).erase)
      (scope : value.Scope input.universes.toNat 0 ∧
        (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
          ((AExpr.lam headCondition binder inner).appN initialArguments)).Scope input.universes.toNat 0)
      (references : value.ReferencesIn entries ∧
        (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
          ((AExpr.lam headCondition binder inner).appN initialArguments)).ReferencesIn entries) :
      DefinitionCheckSupport resolve entries trace value
        (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
          ((AExpr.lam headCondition binder inner).appN initialArguments))
  | betaDeclaredTrace {value type reduced : AExpr β} {level typeBound valueBound : VLevel}
      (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
        type (.sort level) typeBound)
      (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
        value reduced valueBound)
      (reduction : SynthesisBetaTrace resolve entries [] [] entries [] type reduced (.sort level))
      (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
      (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
      (scope : value.Scope input.universes.toNat 0 ∧ type.Scope input.universes.toNat 0)
      (references : value.ReferencesIn entries ∧ type.ReferencesIn entries) :
      DefinitionCheckSupport resolve entries trace value type

theorem DefinitionCheckSupport.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {input : DefinitionInput} {fuel : Nat} {before : TcState .anon}
    {trace : DefinitionBodyTrace input (methodsN fuel) before} {body type : AExpr β}
    (support : DefinitionCheckSupport resolve entries trace body type)
    (wellFormed : entries.WF) :
    readExpr? resolve input.value = some body.erase ∧
      readExpr? resolve input.type = some type.erase ∧
      body.Scope input.universes.toNat 0 ∧ type.Scope input.universes.toNat 0 ∧
      body.ReferencesIn entries ∧ type.ReferencesIn entries ∧
      TypingClaim.{u,v} entries [] body type := by
  cases support with
  | hash inference faithful hashPath =>
      exact inference.sound wellFormed trace.valueRun faithful hashPath
  | betaDeclared typeInference valueInference valueReading typeReading scope references =>
      obtain ⟨_, typeTyped, _⟩ := typeInference.closed_sound typeReading trace.typeRun
      obtain ⟨conversion, _⟩ := typeInference.beta_sound (.empty entries) (.empty _ _)
        typeReading trace.typeRun
      obtain ⟨_, valueTyped, _⟩ := valueInference.closed_sound valueReading trace.valueRun
      exact ⟨readScopedExpr?_closed valueReading, readScopedExpr?_closed typeReading,
        scope.1, scope.2, references.1, references.2,
        valueTyped.conv typeTyped conversion.symm⟩
  | betaDeclaredSpine typeInference valueInference peeling valueReading typeReading scope references =>
      obtain ⟨_, typeTyped, _⟩ := typeInference.closed_sound typeReading trace.typeRun
      obtain ⟨conversion, _⟩ := typeInference.beta_peel_sound (.empty entries) (.empty _ _)
        typeReading trace.typeRun peeling
      obtain ⟨_, valueTyped, _⟩ := valueInference.closed_sound valueReading trace.valueRun
      exact ⟨readScopedExpr?_closed valueReading, readScopedExpr?_closed typeReading,
        scope.1, scope.2, references.1, references.2,
        valueTyped.conv typeTyped conversion.symm⟩
  | betaDeclaredTwice typeInference valueInference enough valueReading typeReading scope references =>
      obtain ⟨_, typeTyped, _⟩ := typeInference.closed_sound typeReading trace.typeRun
      obtain ⟨conversion, _⟩ := typeInference.beta_twice_sound (.empty entries) (.empty _ _)
        typeReading trace.typeRun enough
      obtain ⟨_, valueTyped, _⟩ := valueInference.closed_sound valueReading trace.valueRun
      exact ⟨readScopedExpr?_closed valueReading, readScopedExpr?_closed typeReading,
        scope.1, scope.2, references.1, references.2,
        valueTyped.conv typeTyped conversion.symm⟩
  | betaDeclaredTrace typeInference valueInference reduction valueReading typeReading scope references =>
      obtain ⟨_, typeTyped, _⟩ := typeInference.closed_sound typeReading trace.typeRun
      obtain ⟨conversion, _⟩ := reduction.sound (.empty entries)
      obtain ⟨_, valueTyped, _⟩ := valueInference.closed_sound valueReading trace.valueRun
      exact ⟨readScopedExpr?_closed valueReading, readScopedExpr?_closed typeReading,
        scope.1, scope.2, references.1, references.2,
        valueTyped.conv typeTyped conversion.symm⟩

/-- Production validation supplies scope for the beta-converted declaration
and its value. Both inference trees refer to the checks in this exact trace. -/
def DefinitionBodyTrace.betaDeclaredSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {body domain inner argument : AExpr β} {condition : Certified.PropWhen}
    {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      (.app (.lam condition domain inner) argument) (.sort level) typeBound)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      body (inner.inst argument) valueBound)
    (valueReading : readScopedExpr? resolve [] input.value = some body.erase)
    (typeReading : readScopedExpr? resolve [] input.type =
      some (AExpr.app (.lam condition domain inner) argument).erase)
    (valueConditions : ConditionsScoped input.universes.toNat body)
    (typeConditions : ConditionsScoped input.universes.toNat (.app (.lam condition domain inner) argument))
    (references : body.ReferencesIn entries ∧
      (AExpr.app (.lam condition domain inner) argument).ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace body (.app (.lam condition domain inner) argument) :=
  .betaDeclared typeInference valueInference valueReading typeReading
    (trace.scopes typeCoverage valueCoverage collision valueReading typeReading
      valueConditions typeConditions) references

/-- Admit a declaration whose checked type reduces through a lambda
prefix and an untouched argument suffix. Validation supplies both source
scopes; no inference of an intermediate beta result is required. -/
def DefinitionBodyTrace.betaDeclaredSpineSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {value domain inner body : AExpr β} {condition : Certified.PropWhen}
    {consumed trailing : List (AExpr β)} {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      ((AExpr.lam condition domain inner).appN (consumed ++ trailing)) (.sort level) typeBound)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      value ((body.instRev consumed).appN trailing) valueBound)
    (peeling : LambdaPeel (.lam condition domain inner) consumed.length body)
    (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
    (typeReading : readScopedExpr? resolve [] input.type =
      some ((AExpr.lam condition domain inner).appN (consumed ++ trailing)).erase)
    (valueConditions : ConditionsScoped input.universes.toNat value)
    (typeConditions : ConditionsScoped input.universes.toNat
      ((AExpr.lam condition domain inner).appN (consumed ++ trailing)))
    (references : value.ReferencesIn entries ∧
      ((AExpr.lam condition domain inner).appN (consumed ++ trailing)).ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace value
      ((AExpr.lam condition domain inner).appN (consumed ++ trailing)) :=
  .betaDeclaredSpine typeInference valueInference peeling valueReading typeReading
    (trace.scopes typeCoverage valueCoverage collision valueReading typeReading
      valueConditions typeConditions) references

/-- The declared type can reduce through its outer lambda and then a
prefix of the supplied lambda. The exact declaration checks retain both
origins, including arguments already applied to the supplied lambda. -/
def DefinitionBodyTrace.betaDeclaredTwiceSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {value domain binder inner : AExpr β} {condition headCondition : Certified.PropWhen}
    {initialArguments arguments : List (AExpr β)} {count : Nat} {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)) (.sort level) typeBound)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      value (AExpr.betaPrefix count (.lam headCondition binder inner)
        (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments))))
      valueBound)
    (enough : count ≤ inner.lambdaDepth + 1)
    (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
    (typeReading : readScopedExpr? resolve [] input.type =
      some (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)).erase)
    (valueConditions : ConditionsScoped input.universes.toNat value)
    (typeConditions : ConditionsScoped input.universes.toNat
      (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)))
    (references : value.ReferencesIn entries ∧
      (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)).ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace value
      (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)) :=
  .betaDeclaredTwice typeInference valueInference enough valueReading typeReading
    (trace.scopes typeCoverage valueCoverage collision valueReading typeReading
      valueConditions typeConditions) references

/-- A finite beta trace can connect the declaration's own type and value
checks through any number of successive prefixes. Source validation still
provides both scopes; each reduction retains its original checking calls. -/
def DefinitionBodyTrace.betaDeclaredTraceSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {value type reduced : AExpr β} {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      type (.sort level) typeBound)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      value reduced valueBound)
    (reduction : SynthesisBetaTrace resolve entries [] [] entries [] type reduced (.sort level))
    (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat value)
    (typeConditions : ConditionsScoped input.universes.toNat type)
    (references : value.ReferencesIn entries ∧ type.ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace value type :=
  .betaDeclaredTrace typeInference valueInference reduction valueReading typeReading
    (trace.scopes typeCoverage valueCoverage collision valueReading typeReading
      valueConditions typeConditions) references

/-- A beta WHNF path supplies the declaration's conversion proof. Its
source typing comes from the declaration's actual type-inference call. -/
def DefinitionBodyTrace.betaDeclaredWhnfSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {value type reduced : AExpr β} {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      type (.sort level) typeBound)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      value reduced valueBound)
    {reductionFuel steps : Nat} {flags : WhnfFlags} {after : TcState .anon} {result : KExpr .anon}
    (reduction : SynthesisBetaWhnfTrace resolve entries [] [] entries [] [] reductionFuel flags
      steps trace.conversionStart input.type type after result reduced)
    (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat value)
    (typeConditions : ConditionsScoped input.universes.toNat type)
    (references : value.ReferencesIn entries ∧ type.ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace value type :=
  trace.betaDeclaredTraceSupport typeCoverage valueCoverage collision typeInference valueInference
    (reduction.toBetaTrace (.source (.checked .current typeInference
      (LocalContextReading.empty _ _) typeReading trace.typeRun)))
    valueReading typeReading valueConditions typeConditions references

/-- The declaration's actual type check constructs every successive beta
origin, including functions exposed by substituting earlier arguments. -/
def DefinitionBodyTrace.betaDeclaredStepsSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {value type : AExpr β} {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      type (.sort level) typeBound)
    (count : Nat)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      value (BetaSyntax.steps count type) valueBound)
    (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat value)
    (typeConditions : ConditionsScoped input.universes.toNat type)
    (references : value.ReferencesIn entries ∧ type.ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace value type :=
  trace.betaDeclaredTraceSupport typeCoverage valueCoverage collision typeInference valueInference
    ((SynthesisInference.betaTyping.{u,u} typeInference .current (.empty _ _) typeReading
      trace.typeRun (.empty entries)).betaSteps count).2
    valueReading typeReading valueConditions typeConditions references

/-- An operational WHNF path needs no semantic origins for its intermediate
terms: the declaration's original inference derives them all. -/
def DefinitionBodyTrace.betaDeclaredWhnfPathSupport {β : Type u} {input : DefinitionInput}
    {fuel : Nat} {before : TcState .anon}
    (trace : DefinitionBodyTrace input (methodsN fuel) before)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {value type reduced : AExpr β} {level typeBound valueBound : VLevel}
    {support : RunSupport} (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support)
    (collision : support.CollisionFree)
    (typeInference : SynthesisInference resolve entries [] [] [] fuel trace.validated input.type
      type (.sort level) typeBound)
    (valueInference : SynthesisInference resolve entries [] [] [] fuel trace.valueStart input.value
      value reduced valueBound)
    {reductionFuel steps : Nat} {flags : WhnfFlags} {after : TcState .anon} {result : KExpr .anon}
    (reduction : BetaWhnfTrace resolve [] reductionFuel flags
      steps trace.conversionStart input.type type after result reduced)
    (valueReading : readScopedExpr? resolve [] input.value = some value.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (valueConditions : ConditionsScoped input.universes.toNat value)
    (typeConditions : ConditionsScoped input.universes.toNat type)
    (references : value.ReferencesIn entries ∧ type.ReferencesIn entries) :
    DefinitionCheckSupport resolve entries trace value type :=
  trace.betaDeclaredWhnfSupport typeCoverage valueCoverage collision typeInference valueInference
    (reduction.annotate (SynthesisInference.betaTyping.{u,u} typeInference .current (.empty _ _)
      typeReading trace.typeRun (.empty entries))).1
    valueReading typeReading valueConditions typeConditions references

/-- Operational support for the selected production definition fragment.
Resources are required only at the states exposed by successful body traces. -/
structure AtomicDefinitionRun {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (input : DefinitionInput) (before : TcState .anon)
    (body type : AExpr β) where
  path : StandalonePrefix input.id before input.constant
  support : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
    DefinitionCheckSupport resolve entries trace body type

/-- The original hash-comparison interface embeds in the extended
declaration boundary with the same execution resources. -/
def AtomicDefinitionRun.ofHash {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {input : DefinitionInput} {before : TcState .anon}
    {body type : AExpr β} (path : StandalonePrefix input.id before input.constant)
    (inference : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
      DefinitionBodySupport resolve entries (methodsN before.recFuel.toNat)
        trace.valueStart input.type input.universes.toNat input.value body type)
    (hashPath : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
      (trace.inferredValue == input.type) = true)
    (faithful : ∀ trace : DefinitionBodyTrace input (methodsN before.recFuel.toNat) path.ready,
      trace.inferredValue.AddrFaithful input.type) :
    AtomicDefinitionRun resolve entries input before body type :=
  ⟨path, fun trace => .hash (inference trace) (faithful trace) (hashPath trace)⟩

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
      body.Scope input.universes.toNat 0 ∧ type.Scope input.universes.toNat 0 ∧
      body.ReferencesIn entries ∧ type.ReferencesIn entries ∧
      TypingClaim.{u,v} entries [] body type := by
  obtain ⟨trace⟩ := definition_body_trace (fragment.path.member_success accepted)
  exact (fragment.support trace).sound wellFormed

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
