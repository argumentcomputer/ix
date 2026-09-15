/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Production
import Ix.Theory.Model.Extension

/-!
# Relative consistency of a production environment fragment

The initial interface contains exactly the supplied axiom declarations.
Successful calls from the serial `checkEnvAnon` run add fresh universe-polymorphic
definitions in dependency order. Each addition extends every model of the
previous interface and preserves its existing interpretations.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model Theory.Model.SetTheory

universe u v

/-- A location in the exact work array, retaining the preceding work so the
checker state is the one actually reached by the production serial loop. -/
structure WorkPosition (work : Array AnonWorkItem) (item : AnonWorkItem) where
  leading : List AnonWorkItem
  trailing : List AnonWorkItem
  split : work.toList = leading ++ item :: trailing

def WorkPosition.state {work : Array AnonWorkItem} {item : AnonWorkItem}
    (position : WorkPosition work item) (env : Ixon.Env) (cfg : CheckCfg) :
    AnonCheckLoopState :=
  runAnonCheckList cfg position.leading (initialAnonCheckLoopState env cfg)

private theorem runList_append (cfg : CheckCfg) (left right : List AnonWorkItem)
    (before : AnonCheckLoopState) :
    runAnonCheckList cfg (left ++ right) before =
      runAnonCheckList cfg right (runAnonCheckList cfg left before) := by
  induction left generalizing before with
  | nil => rfl
  | cons item rest ih => exact ih (runAnonCheckItem cfg before item)

private theorem finish_results (cfg : CheckCfg) (before : AnonCheckLoopState)
    (item : AnonWorkItem) (checker : TcState .anon) (err : Option String) :
    (finishAnonCheckItem cfg before item checker err).results =
      before.results ++ item.targets.map (fun addr => ⟨addr, err⟩) := by
  unfold finishAnonCheckItem
  dsimp only
  split <;> rfl

private theorem item_keeps_result (cfg : CheckCfg) (before : AnonCheckLoopState)
    (item : AnonWorkItem) {result : CheckResult} (found : result ∈ before.results) :
    result ∈ (runAnonCheckItem cfg before item).results := by
  cases run : TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) before.checker <;>
    simp only [runAnonCheckItem, EStateM.run, run, finish_results] <;>
    exact Array.mem_append.mpr (.inl found)

private theorem list_keeps_result (cfg : CheckCfg) (work : List AnonWorkItem)
    (before : AnonCheckLoopState) {result : CheckResult} (found : result ∈ before.results) :
    result ∈ (runAnonCheckList cfg work before).results := by
  induction work generalizing before with
  | nil => exact found
  | cons item rest ih => exact ih _ (item_keeps_result cfg before item found)

/-- All-success result rows expose a successful call at this exact work
position. This rules out the public `.ok` result that contains failed rows. -/
theorem WorkPosition.check_success {env : Ixon.Env} {cfg : CheckCfg}
    {work : Array AnonWorkItem} {addr : Address}
    (position : WorkPosition work (.standalone addr))
    (succeeded : ∀ result ∈ (runAnonCheckList cfg work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    ∃ after, TcM.checkConst (⟨addr, ()⟩ : KId .anon)
      (position.state env cfg).checker = .ok () after := by
  rw [position.split, runList_append] at succeeded
  change ∀ result ∈ (runAnonCheckList cfg position.trailing
    (runAnonCheckItem cfg (position.state env cfg) (.standalone addr))).results,
      result.err? = none at succeeded
  cases run : TcM.checkConst (⟨addr, ()⟩ : KId .anon) (position.state env cfg).checker with
  | ok value after =>
      cases value
      exact ⟨after, rfl⟩
  | error err after =>
      let failed : CheckResult := ⟨addr, some (toString err)⟩
      have appears : failed ∈
          (runAnonCheckItem cfg (position.state env cfg) (.standalone addr)).results := by
        simp only [runAnonCheckItem, EStateM.run, AnonWorkItem.primary, run, finish_results,
          AnonWorkItem.targets]
        apply Array.mem_append.mpr
        exact .inr (by simp [failed])
      have contradiction := succeeded failed
        (list_keeps_result cfg position.trailing _ appears)
      simp [failed] at contradiction

/-- A definition entry with its exact universe arity and body, and no additional laws or facts. -/
def definitionEntry {β : Type u} (universes : Nat) (body type : AExpr β) : ConstantEntry β :=
  { universes, type, body := some body }

/-- Interpret a fresh definition's body to extend the preceding model.
Body typing supplies hereditary validity of the declared type. -/
theorem extend_atomic_definition {β : Type u} [DecidableEq β]
    {entries : Model.Environment β} {ref : ConstRef β} {body type : AExpr β} {universes : Nat}
    (wellFormed : entries.WF) (fresh : entries ref = none)
    (bodyScope : body.Scope universes 0)
    (bodyRefs : body.ReferencesIn entries) (typeRefs : type.ReferencesIn entries)
    (typed : TypingClaim.{u,v} entries [] body type)
    {V : Type v} [SetTheory V] (constants : Assignment β V) (realizes : Realizes constants entries) :
    ∃ next : Assignment β V,
      Realizes next (entries.insert ref (definitionEntry universes body type)) ∧
        Assignment.AgreesOn entries constants next := by
  let next := constants.insert ref (fun levels => interp constants levels (fun _ => empty) body)
  have agrees : Assignment.AgreesOn entries constants next :=
    Assignment.insert_agrees fresh constants _
  have value (levels : List Nat) (env : Nat → V) :
      next ref levels = interp constants levels env body := by
    simp only [next, Assignment.insert, if_true]
    exact interp_closed body constants levels bodyScope _ env
  refine ⟨next, (realizes.of_agrees wellFormed agrees).insert ?_, agrees⟩
  constructor
  · intro levels _ env
    exact (agrees.wellDenoted typeRefs levels env).mpr
      (typed V constants realizes levels env (Context.valid_nil constants levels env)).2.1
  · intro levels _ env
    change next ref levels ∈ˢ interp next levels env type
    rw [value, agrees.interp typeRefs]
    exact (typed V constants realizes levels env (Context.valid_nil constants levels env)).2.2
  · intro candidate present levels _ env
    change some body = some candidate at present
    cases present
    exact (agrees.wellDenoted bodyRefs levels env).mpr
      (typed V constants realizes levels env (Context.valid_nil constants levels env)).1
  · intro candidate present levels _ env
    change some body = some candidate at present
    cases present
    rw [value, agrees.interp bodyRefs]
  · intro law present
    exact (List.not_mem_nil present).elim
  · intro fact present
    exact (List.not_mem_nil present).elim

/-- A declaration's source data and its annotated semantic interface. The
production run must establish both erasure agreements and body typing. -/
structure DefinitionSpec (β : Type u) where
  input : DefinitionInput
  ref : ConstRef β
  body : AExpr β
  type : AExpr β

def DefinitionSpec.entry {β : Type u} (spec : DefinitionSpec β) : ConstantEntry β :=
  definitionEntry spec.input.universes.toNat spec.body spec.type

private theorem insert_definition_wf {β : Type u} [DecidableEq β]
    {entries : Model.Environment β} {ref : ConstRef β} {body type : AExpr β} {universes : Nat}
    (wellFormed : entries.WF) (bodyScope : body.Scope universes 0) (typeScope : type.Scope universes 0)
    (bodyRefs : body.ReferencesIn entries) (typeRefs : type.ReferencesIn entries) :
    (entries.insert ref (definitionEntry universes body type)).WF := by
  apply wellFormed.insert typeScope
  · intro candidate present
    change some body = some candidate at present
    cases present
    exact bodyScope
  · exact typeRefs
  · intro candidate present
    change some body = some candidate at present
    cases present
    exact bodyRefs
  · simp [definitionEntry]
  · simp [definitionEntry]
  · simp [definitionEntry]
  · simp [definitionEntry]

/-- Definitions in dependency order, with fresh references and bodies that
read the preceding interface. Work positions retain the runtime serial order,
which may differ from this dependency order. -/
inductive AtomicDefinitionPlan {β : Type u} [DecidableEq β]
    (env : Ixon.Env) (cfg : CheckCfg) (work : Array AnonWorkItem)
    (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → List (DefinitionSpec β) → Model.Environment β → Prop
  | nil (entries) : AtomicDefinitionPlan env cfg work resolve entries [] entries
  | cons {before after : Model.Environment β} {rest : List (DefinitionSpec β)}
      (spec : DefinitionSpec β)
      (resolved : resolve spec.input.id.addr = some spec.ref)
      (fresh : before spec.ref = none)
      (position : WorkPosition work (.standalone spec.input.id.addr))
      (run : AtomicDefinitionRun resolve before spec.input
        (position.state env cfg).checker spec.body spec.type)
      (tail : AtomicDefinitionPlan env cfg work resolve
        (before.insert spec.ref spec.entry) rest after) :
      AtomicDefinitionPlan env cfg work resolve before (spec :: rest) after

/-- Every old interface entry is retained by a dependency plan. -/
theorem AtomicDefinitionPlan.extends {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {resolve : Address → Option (ConstRef β)}
    {before after : Model.Environment β} {definitions : List (DefinitionSpec β)}
    (plan : AtomicDefinitionPlan env cfg work resolve before definitions after) :
    ∀ ref entry, before ref = some entry → after ref = some entry := by
  induction plan with
  | nil entries => exact fun _ _ h => h
  | cons spec resolved fresh position run tail ih =>
      intro ref entry present
      exact ih ref entry (Model.Environment.insert_old fresh present)

/-- Model preservation keeps every old reference's interpretation fixed. -/
def PreservesModels {β : Type u} (before after : Model.Environment β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
    Realizes constants before → ∃ next : Assignment β V,
      Realizes next after ∧ Assignment.AgreesOn before constants next

private theorem anon_id (id : KId .anon) : (⟨id.addr, ()⟩ : KId .anon) = id := by
  cases id with
  | mk addr name => cases name; rfl

/-- Accepted definitions extend every model of the preceding interface. -/
theorem AtomicDefinitionPlan.sound {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {resolve : Address → Option (ConstRef β)}
    {before after : Model.Environment β} {definitions : List (DefinitionSpec β)}
    (plan : AtomicDefinitionPlan env cfg work resolve before definitions after)
    (wellFormed : before.WF)
    (succeeded : ∀ result ∈ (runAnonCheckList cfg work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    after.WF ∧ PreservesModels.{u,v} before after := by
  induction plan with
  | nil entries =>
      exact ⟨wellFormed, fun _ _ constants realizes =>
        ⟨constants, realizes, fun _ _ _ _ => rfl⟩⟩
  | @cons before after rest spec resolved fresh position run tail ih =>
      obtain ⟨checkedState, accepted⟩ := position.check_success succeeded
      rw [anon_id] at accepted
      obtain ⟨_, _, bodyScope, typeScope, bodyRefs, typeRefs, typed⟩ :=
        run.sound wellFormed accepted
      have formed : (before.insert spec.ref spec.entry).WF :=
        insert_definition_wf wellFormed bodyScope typeScope bodyRefs typeRefs
      obtain ⟨finalFormed, preserve⟩ := ih formed
      refine ⟨finalFormed, ?_⟩
      intro V _ constants realizes
      obtain ⟨next, nextModel, agrees⟩ := extend_atomic_definition wellFormed fresh
        bodyScope bodyRefs typeRefs typed constants realizes
      obtain ⟨final, finalModel, finalAgrees⟩ := preserve V next nextModel
      refine ⟨final, finalModel, ?_⟩
      intro ref entry present levels
      exact (finalAgrees ref entry (Model.Environment.insert_old fresh present) levels).trans
        (agrees ref entry present levels)

/-- Every published definition interface reads the actual checked type and
body. Freshness ensures later definitions cannot overwrite that interface. -/
theorem AtomicDefinitionPlan.represents {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {resolve : Address → Option (ConstRef β)}
    {before after : Model.Environment β} {definitions : List (DefinitionSpec β)}
    (plan : AtomicDefinitionPlan env cfg work resolve before definitions after)
    (wellFormed : before.WF)
    (succeeded : ∀ result ∈ (runAnonCheckList cfg work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    ∀ spec ∈ definitions,
      resolve spec.input.id.addr = some spec.ref ∧ after spec.ref = some spec.entry ∧
      readExpr? resolve spec.input.value = some spec.body.erase ∧
      readExpr? resolve spec.input.type = some spec.type.erase := by
  induction plan with
  | nil entries => simp
  | @cons before after rest spec resolved fresh position run tail ih =>
      obtain ⟨checkedState, accepted⟩ := position.check_success succeeded
      rw [anon_id] at accepted
      obtain ⟨valueReads, typeReads, bodyScope, typeScope, bodyRefs, typeRefs, _⟩ :=
        AtomicDefinitionRun.sound.{u,0} run wellFormed accepted
      have formed : (before.insert spec.ref spec.entry).WF :=
        insert_definition_wf wellFormed bodyScope typeScope bodyRefs typeRefs
      intro candidate present
      rcases List.mem_cons.mp present with same | later
      · subst candidate
        exact ⟨resolved, tail.extends _ _ (Model.Environment.insert_same ..),
          valueReads, typeReads⟩
      · exact ih formed candidate later

private theorem AtomicDefinitionPlan.locations {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {resolve : Address → Option (ConstRef β)}
    {before after : Model.Environment β} {definitions : List (DefinitionSpec β)}
    (plan : AtomicDefinitionPlan env cfg work resolve before definitions after) :
    ∀ spec ∈ definitions, ∃ position : WorkPosition work (.standalone spec.input.id.addr),
      Nonempty (StandalonePrefix spec.input.id (position.state env cfg).checker spec.input.constant) := by
  induction plan with
  | nil => simp
  | cons spec resolved fresh position run tail ih =>
      intro candidate present
      rcases List.mem_cons.mp present with same | later
      · subst candidate
        exact ⟨position, ⟨run.path⟩⟩
      · exact ih candidate later

/-- An axiom retains its declared universe arity and has no value or
computational equations in the initial model. -/
structure AxiomSpec (β : Type u) where
  id : KId .anon
  ref : ConstRef β
  isUnsafe : Bool
  universes : UInt64 := 0
  sourceType : KExpr .anon
  type : AExpr β

def AxiomSpec.constant {β : Type u} (spec : AxiomSpec β) : KConst .anon :=
  .axio () () spec.isUnsafe spec.universes spec.sourceType

def AxiomSpec.entry {β : Type u} (spec : AxiomSpec β) : ConstantEntry β :=
  { universes := spec.universes.toNat, type := spec.type, body := none }

/-- The axiom's type check is an actual prefix of member validation, just
as a definition's type check is. Its eventual interpretation remains the
user-supplied axiom-model premise. -/
structure AxiomTypeTrace {β : Type u} (spec : AxiomSpec β) (methods : Methods .anon)
    (before : TcState .anon) where
  validated : TcState .anon
  inferred : KExpr .anon
  typeState : TcState .anon
  level : KUniv .anon
  afterSort : TcState .anon
  validationRun : (RecM.validateConstWellScoped spec.constant).run methods before = .ok () validated
  typeRun : (RecM.infer spec.sourceType).run methods validated = .ok inferred typeState
  sortRun : (RecM.ensureSortDirect inferred).run methods typeState = .ok level afterSort

private theorem axiom_bind_success {α γ : Type} {action : TcM .anon α} {next : α → TcM .anon γ}
    {before after : TcState .anon} {result : γ}
    (accepted : EStateM.bind action next before = .ok result after) :
    ∃ value state, action before = .ok value state ∧ next value state = .ok result after := by
  cases run : action before with
  | error err failed => rw [EStateM.bind, run] at accepted; contradiction
  | ok value state =>
      rw [EStateM.bind, run] at accepted
      exact ⟨value, state, rfl, accepted⟩

theorem axiom_type_trace {β : Type u} {spec : AxiomSpec β} {methods : Methods .anon}
    {before after : TcState .anon}
    (accepted : (RecM.checkConstMember spec.id spec.constant).run methods before = .ok () after) :
    Nonempty (AxiomTypeTrace spec methods before) := by
  unfold RecM.checkConstMember at accepted
  simp only [AxiomSpec.constant, Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind] at accepted
  change EStateM.bind ((RecM.validateConstWellScoped spec.constant).run methods) _ before = _ at accepted
  obtain ⟨⟨⟩, validated, validationRun, accepted⟩ := axiom_bind_success accepted
  change EStateM.bind ((RecM.infer spec.sourceType).run methods) _ validated = _ at accepted
  obtain ⟨inferred, typeState, typeRun, accepted⟩ := axiom_bind_success accepted
  change EStateM.bind ((RecM.ensureSortDirect inferred).run methods) _ typeState = _ at accepted
  obtain ⟨level, afterSort, sortRun, _⟩ := axiom_bind_success accepted
  exact ⟨⟨validated, inferred, typeState, level, afterSort, validationRun, typeRun, sortRun⟩⟩

/-- Store formation from the exact inference call made while admitting this
axiom. The source reading and finite inference tree establish its meaning. -/
def AxiomTypeTrace.synthesisTypeCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {spec : AxiomSpec β} {fuel : Nat} {before : TcState .anon}
    (trace : AxiomTypeTrace spec (methodsN fuel) before) {level bound : VLevel}
    (inference : SynthesisInference resolve entries [] [] [] fuel trace.validated spec.sourceType
      spec.type (.sort level) bound)
    (reading : readScopedExpr? resolve [] spec.sourceType = some spec.type.erase) :
    SynthesisTypeCheck resolve entries spec.type level :=
  { fuel, before := trace.validated, after := trace.typeState, source := spec.sourceType,
    result := trace.inferred, bound, inference, reading, run := trace.typeRun }

/-- Exactly the declared axiom interface, starting with no other entries. -/
def axiomEnvironment {β : Type u} [DecidableEq β] : List (AxiomSpec β) → Model.Environment β
  | [] => fun _ => none
  | spec :: rest => (axiomEnvironment rest).insert spec.ref spec.entry

/-- Syntactic provenance of one axiom at a real work position. The model
hypothesis supplies its inhabitant; this record only identifies its source
declaration and exact type. -/
structure AxiomObservation {β : Type u} (env : Ixon.Env) (cfg : CheckCfg)
    (work : Array AnonWorkItem) (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (spec : AxiomSpec β) where
  position : WorkPosition work (.standalone spec.id.addr)
  path : StandalonePrefix spec.id (position.state env cfg).checker spec.constant
  resolved : resolve spec.id.addr = some spec.ref
  installed : entries spec.ref = some spec.entry
  reads : readExpr? resolve spec.sourceType = some spec.type.erase

/-- Successful rows from this environment run supply the axiom's executed
type check. The caller supplies only its finite inference support and scoped
source reading, not another successful inference call or a semantic judgment. -/
theorem AxiomObservation.synthesisTypeCheck {β : Type u}
    {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β} {spec : AxiomSpec β}
    (observation : AxiomObservation env cfg work resolve entries spec) {level bound : VLevel}
    (inference : ∀ trace : AxiomTypeTrace spec
        (methodsN (observation.position.state env cfg).checker.recFuel.toNat) observation.path.ready,
      Nonempty (SynthesisInference resolve entries [] [] []
        (observation.position.state env cfg).checker.recFuel.toNat trace.validated spec.sourceType
        spec.type (.sort level) bound))
    (reading : readScopedExpr? resolve [] spec.sourceType = some spec.type.erase)
    (enumerated : buildAnonWork env = .ok work)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    Nonempty (SynthesisTypeCheck resolve entries spec.type level) := by
  have serial : ∀ result ∈ (runAnonCheckList cfg work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none := by
    unfold checkEnvAnon at accepted
    rw [enumerated] at accepted
    cases accepted
    exact succeeded
  obtain ⟨after, run⟩ := observation.position.check_success serial
  have member := observation.path.member_success (by simpa only [anon_id] using run)
  obtain ⟨trace⟩ := axiom_type_trace member
  obtain ⟨tree⟩ := inference trace
  exact ⟨trace.synthesisTypeCheck tree reading⟩

/-- Complete support for the selected production environment fragment.
Every source key is checked, every work item is represented, and the axiom
interface contains exactly the listed source axioms. All definition resources
refer to concrete states of this same production run. -/
structure AtomicEnvironmentFragment {β : Type u} [DecidableEq β]
    (env : Ixon.Env) (cfg : CheckCfg) (resolve : Address → Option (ConstRef β)) where
  work : Array AnonWorkItem
  enumerated : buildAnonWork env = .ok work
  axioms : List (AxiomSpec β)
  definitions : List (DefinitionSpec β)
  entries : Model.Environment β
  axiomRuns : ∀ spec ∈ axioms,
    Nonempty (AxiomObservation env cfg work resolve (axiomEnvironment axioms) spec)
  plan : AtomicDefinitionPlan env cfg work resolve (axiomEnvironment axioms) definitions entries
  sourceCovered : ∀ addr ∈ env.consts.keys, .standalone addr ∈ work
  workCovered : ∀ item ∈ work,
    (∃ spec ∈ axioms, item = .standalone spec.id.addr) ∨
      (∃ spec ∈ definitions, item = .standalone spec.input.id.addr)

private theorem AtomicEnvironmentFragment.serial_success {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {resolve : Address → Option (ConstRef β)}
    (fragment : AtomicEnvironmentFragment env cfg resolve) {results : Array CheckResult}
    (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none := by
  unfold checkEnvAnon at accepted
  rw [fragment.enumerated] at accepted
  cases accepted
  exact succeeded

/-- A successful `checkEnvAnon` run in the fragment extends every model of
its axiom set while preserving all axiom interpretations. -/
theorem checkEnvAnon_atomic_preserves_model {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {resolve : Address → Option (ConstRef β)}
    (fragment : AtomicEnvironmentFragment env cfg resolve)
    (wellFormed : (axiomEnvironment fragment.axioms).WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    fragment.entries.WF ∧ PreservesModels.{u,v}
      (axiomEnvironment fragment.axioms) fragment.entries :=
  fragment.plan.sound wellFormed (fragment.serial_success accepted succeeded)

/-- Exact type, universe arity, and value agreement with the declaration
returned by production lookup. Axiom and quotient entries contain no body. -/
def DeclarationReading {β : Type u} (resolve : Address → Option (ConstRef β))
    (concrete : KConst .anon) (entry : ConstantEntry β) : Prop :=
  readExpr? resolve concrete.ty = some entry.type.erase ∧
    entry.universes = concrete.lvls.toNat ∧
    match concrete with
    | .axio .. | .quot .. => entry.body = none
    | .defn (val := value) .. =>
      ∃ body, entry.body = some body ∧ readExpr? resolve value = some body.erase
    | _ => False

/-- Every source address receives an interface entry whose type reads the
declaration actually reached by production lookup. Definitions additionally
have the exact checked body in their model entry. -/
theorem checkEnvAnon_atomic_represents_source {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {resolve : Address → Option (ConstRef β)}
    (fragment : AtomicEnvironmentFragment env cfg resolve)
    (wellFormed : (axiomEnvironment fragment.axioms).WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    ∀ addr ∈ env.consts.keys, ∃ ref entry,
      resolve addr = some ref ∧ fragment.entries ref = some entry ∧
      ∃ concrete : KConst .anon,
        (∃ before after, TcM.checkConst (⟨addr, ()⟩ : KId .anon) before = .ok () after ∧
          Nonempty (StandalonePrefix (⟨addr, ()⟩ : KId .anon) before concrete)) ∧
        DeclarationReading resolve concrete entry := by
  have serial := fragment.serial_success accepted succeeded
  have represented := fragment.plan.represents wellFormed serial
  intro addr present
  rcases fragment.workCovered (.standalone addr) (fragment.sourceCovered addr present) with
    ⟨spec, listed, same⟩ | ⟨spec, listed, same⟩
  · cases AnonWorkItem.standalone.inj same
    obtain ⟨observation⟩ := fragment.axiomRuns spec listed
    obtain ⟨after, run⟩ := observation.position.check_success serial
    refine ⟨spec.ref, spec.entry, observation.resolved,
      fragment.plan.extends _ _ observation.installed, spec.constant,
      ⟨(observation.position.state env cfg).checker, after, run, ?_⟩,
      observation.reads, rfl, rfl⟩
    simpa only [anon_id] using Nonempty.intro observation.path
  · cases AnonWorkItem.standalone.inj same
    obtain ⟨resolved, installed, valueReads, typeReads⟩ := represented spec listed
    obtain ⟨position, path⟩ := fragment.plan.locations spec listed
    obtain ⟨after, run⟩ := position.check_success serial
    refine ⟨spec.ref, spec.entry, resolved, installed, spec.input.constant,
      ⟨(position.state env cfg).checker, after, run, ?_⟩, typeReads,
      rfl, spec.body, rfl, valueReads⟩
    simpa only [anon_id] using path

/-- No declaration can inhabit an axiom type interpreted as empty, such as
`False`: model extension preserves the initial empty interpretation. -/
theorem checkEnvAnon_atomic_no_false {β : Type u} [DecidableEq β]
    {env : Ixon.Env} {cfg : CheckCfg} {resolve : Address → Option (ConstRef β)}
    (fragment : AtomicEnvironmentFragment env cfg resolve)
    (wellFormed : (axiomEnvironment fragment.axioms).WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none)
    {V : Type v} [SetTheory V] (axiomValues : Assignment β V)
    (axiomModel : Realizes axiomValues (axiomEnvironment fragment.axioms))
    {falseRef : ConstRef β} {falseEntry : ConstantEntry β}
    (hasFalse : axiomEnvironment fragment.axioms falseRef = some falseEntry)
    (falseEmpty : axiomValues falseRef [] = empty)
    {ref : ConstRef β} {entry : ConstantEntry β}
    (present : fragment.entries ref = some entry)
    (isFalse : entry.type.erase = .const falseRef []) : False := by
  obtain ⟨_, preserve⟩ := checkEnvAnon_atomic_preserves_model fragment wellFormed accepted succeeded
  obtain ⟨values, model, agrees⟩ := preserve V axiomValues axiomModel
  have emptyValue : values falseRef [] = empty := (agrees _ _ hasFalse []).trans falseEmpty
  have typeEq := AExpr.eq_const_of_erase_eq isFalse
  have member := model.member ref entry present (List.replicate entry.universes 0)
    (by simp) (fun _ => empty)
  rw [typeEq] at member
  simp only [interp, List.map_nil, emptyValue] at member
  exact not_mem_empty _ member

end Ix.Kernel.Consistency
