/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.DefEqTiers

/-!
# The reducing DefEq tiers under the contracts: seams and shared tools

After the quick structural probe misses, production conversion reduces: the
eager `Bool.true` shortcut, the cheap structural-core and no-delta passes,
proof irrelevance, the lazy-delta loop, and the final WHNF tiers. This module
states what those tiers consume and proves the pieces shared by all of them.

Inside the conversion body the reducers `whnf`, `whnfCore`,
`whnfCoreWithFlags`, and `whnfNoDeltaImpl` are the production bodies run at
the conversion's own table, not entries of the `Methods` record; their
soundness at that table is the reduction package's `StepContracts` obligation
and enters here as fields of `DefEqReducingSeams`, together with the optional
reducers of the lazy-delta loop, the Nat-offset and projection-delta probes,
the structure-eta, unit-like, Nat, let, and eta-expansion tails, one frame
fact no invariant field records (full reduction never writes the primitive
table), and three boundaries of the set model: hereditary typing of
applications, formation of the type of a typed term, and transport of a
recorded proposition classification to the caller's registration. The table
edges `isDefEqCall` and `inferOnlyCall` are covered by the smaller table's
`MethodContracts`.

Proved here: the run equations of the cheap-depth scope, the caught probe,
and the inference-only edge; invariant preservation through lookups, the
is-prop memo write, and the rejection-cache write; soundness of the cheap
reducers from the flagged bodies; the bounded-loop driver; the hash path of
a reduced pair; annotated spine readings with their typing; the proof
irrelevance tier through the memoized proposition classifier; and the upper
chain from the eager `Bool.true` shortcut through the no-delta pass, each
with its continuation abstracted by its contract.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Run equations of the reducing tiers' primitives -/

theorem EStateM.run_bind_ok {ε σ α γ : Type} {action : EStateM ε σ α} {next : α → EStateM ε σ γ}
    {state after : σ} {value : α} (run : action state = .ok value after) :
    (action >>= next) state = next value after := by
  change EStateM.bind action next state = _
  unfold EStateM.bind
  rw [run]

theorem EStateM.run_bind_error {ε σ α γ : Type} {action : EStateM ε σ α} {next : α → EStateM ε σ γ}
    {state after : σ} {err : ε} (run : action state = .error err after) :
    (action >>= next) state = .error err after := by
  change EStateM.bind action next state = _
  unfold EStateM.bind
  rw [run]

/-- The reflexive lift of a checker action into itself. -/
theorem monadLift_self {α : Type} (action : TcM .anon α) :
    (monadLift action : TcM .anon α) = action := rfl

theorem prims_run (methods : Methods .anon) (state : TcState .anon) :
    (RecM.prims (m := .anon)).run methods state = .ok state.prims state := rfl

theorem inferOnlyCall_run (term : KExpr .anon) (methods : Methods .anon) :
    (RecM.inferOnlyCall term).run methods = TcM.withInferOnly (methods.infer term) := rfl

/-- The caught probe never fails: it maps an error to `none` and keeps the
error-side state. -/
theorem try?_run {α : Type} (action : RecM .anon α) (methods : Methods .anon)
    (state : TcState .anon) :
    (RecM.try? action).run methods state =
      match action.run methods state with
      | .ok value after => .ok (some value) after
      | .error _ after => .ok none after := by
  unfold RecM.try?
  change EStateM.tryCatch (EStateM.bind (action.run methods) _) _ state = _
  unfold EStateM.tryCatch EStateM.bind
  cases action.run methods state <;> rfl

theorem tryFinally_run {α γ : Type} (action : RecM .anon α) (cleanup : RecM .anon γ)
    (methods : Methods .anon) (state : TcState .anon) :
    (tryFinally action cleanup).run methods state =
      match action.run methods state with
      | .ok value middle =>
          match cleanup.run methods middle with
          | .ok _ after => .ok value after
          | .error err after => .error err after
      | .error err middle =>
          match cleanup.run methods middle with
          | .ok _ after => .error err after
          | .error err' after => .error err' after := by
  change tryFinally (action.run methods) (cleanup.run methods) state = _
  unfold tryFinally
  change EStateM.map (fun value : α × γ => value.1)
    (tryFinally' (action.run methods) (fun _ => cleanup.run methods)) state = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases run : action.run methods state <;> simp only [run] <;>
    cases finished : cleanup.run methods _ <;> rfl

/-- The cheap recursion scope bumps the depth around its body and restores it
on both outcomes. -/
theorem withCheapRecursionDepth_run {α : Type} (action : RecM .anon α) (methods : Methods .anon)
    (state : TcState .anon) :
    (RecM.withCheapRecursionDepth action).run methods state =
      match action.run methods {state with cheapRecursionDepth := state.cheapRecursionDepth + 1} with
      | .ok value after =>
          .ok value {after with cheapRecursionDepth := after.cheapRecursionDepth - 1}
      | .error err after =>
          .error err {after with cheapRecursionDepth := after.cheapRecursionDepth - 1} := by
  unfold RecM.withCheapRecursionDepth
  simp only [ReaderT.run_bind]
  rw [EStateM.run_bind_ok (modify_run _ methods state), tryFinally_run]
  cases action.run methods _ <;> simp only [modify_run]

/-- The caught inference-only edge: the policy is raised around the callback
and restored on both outcomes. -/
theorem tryInferOnly_run (term : KExpr .anon) (methods : Methods .anon) (before : TcState .anon) :
    (RecM.try? (RecM.inferOnlyCall term)).run methods before =
      match methods.infer term {before with inferOnly := true} with
      | .ok type after => .ok (some type) {after with inferOnly := before.inferOnly}
      | .error _ after => .ok none {after with inferOnly := before.inferOnly} := by
  rw [try?_run, inferOnlyCall_run, withInferOnly_eq]
  cases methods.infer term {before with inferOnly := true} <;> rfl

theorem whnfCoreForDefEq_def (term : KExpr .anon) :
    RecM.whnfCoreForDefEq term =
      RecM.withCheapRecursionDepth (RecM.whnfCoreWithFlags term .DEF_EQ_CORE) := rfl

theorem whnfNoDeltaForDefEq_def (term : KExpr .anon) :
    RecM.whnfNoDeltaForDefEq term =
      RecM.withCheapRecursionDepth (RecM.whnfNoDeltaImpl term .DEF_EQ_CORE .collapse) := rfl

/-- The answer of the `Bool.true` recognizer at a primitive table. -/
def isBoolTrueAnswer (prims : Primitives .anon) : KExpr .anon → Bool
  | .const id us _ => us.isEmpty && id.addr == prims.boolTrue.addr
  | _ => false

theorem isBoolTrue_run (term : KExpr .anon) (methods : Methods .anon) (state : TcState .anon) :
    (RecM.isBoolTrue term).run methods state = .ok (isBoolTrueAnswer state.prims term) state := by
  unfold RecM.isBoolTrue isBoolTrueAnswer
  cases term <;> rfl

/-- The eager-reduction policy answer: closed syntax, or the caller's marker. -/
def boolTrueAllowed (state : TcState .anon) (term : KExpr .anon) : Bool :=
  if !term.hasFVars then true else state.eagerReduce

theorem boolTrueReductionAllowed_run (term : KExpr .anon) (methods : Methods .anon)
    (state : TcState .anon) :
    (RecM.boolTrueReductionAllowed term).run methods state = .ok (boolTrueAllowed state term) state := by
  unfold RecM.boolTrueReductionAllowed boolTrueAllowed
  split <;> rfl

/-! ### Outcomes of optional probes -/

section Posts

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source)) (locals : List FVarId)
  (context : Model.Context β) (bounds : List VLevel)

/-- Both outcomes of a run keep the invariant. -/
def KeepsInvariant {α : Type} : EStateM.Result (TcError .anon) (TcState .anon) α → Prop
  | .ok _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One optional reduction outcome: `none` and errors keep the invariant; a
result has an annotated reading convertible to the source that retains every
type of the source. -/
def OptionalReductionPost (term : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) (Option (KExpr .anon)) → Prop
  | .ok (some result) after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ∃ target : AExpr β, readScopedExpr? resolve locals result = some target.erase ∧
        ConversionClaim.{u,v} entries context term target ∧
        ∀ type, TypingClaim.{u,v} entries context term type →
          TypingClaim.{u,v} entries context target type
  | .ok none after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One optional conversion outcome: only `some true` carries a claim. -/
def OptionalConversionPost (left right : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) (Option Bool) → Prop
  | .ok (some true) after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ConversionClaim.{u,v} entries context left right
  | .ok (some false) after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .ok none after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One proposition-classification outcome: `true` classifies the annotated
reading as a proposition. -/
def PropositionPost (term : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) Bool → Prop
  | .ok true after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      TypingClaim.{u,v} entries context term (.sort .zero)
  | .ok false after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

end Posts

section SoundOptional

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- An optional reduction probe is sound in every scope. -/
def SoundOptionalReduction (input : KExpr .anon) (action : TcM .anon (Option (KExpr .anon))) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (term : AExpr β),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals input = some term.erase →
    (∃ type, TypingClaim.{u,v} entries context term type) →
    OptionalReductionPost.{u,v} resolve anchor entries source catalog locals context bounds term
      (action before)

/-- An optional conversion probe is sound in every scope. -/
def SoundOptionalConversion (left right : KExpr .anon) (action : TcM .anon (Option Bool)) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (a b : AExpr β),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals left = some a.erase →
    (∃ type, TypingClaim.{u,v} entries context a type) →
    readScopedExpr? resolve locals right = some b.erase →
    (∃ type, TypingClaim.{u,v} entries context b type) →
    OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      (action before)

/-- The annotation discipline of the hash path, as the direct tiers state it:
two typed readings of one raw term carry equal binder annotations. -/
def SameRawAnnotations : Prop :=
  ∀ (context : Model.Context β) (a b : AExpr β), a.erase = b.erase →
    (∃ type, TypingClaim.{u,v} entries context a type) →
    (∃ type, TypingClaim.{u,v} entries context b type) → a.annotations = b.annotations

/-- Where a proposition-classification key was computed: an invariant state
at the caller's registration whose actual digest at the type's radius is the
key's context component. -/
def IsPropKeyOrigin (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (type : KExpr .anon) (ctxAddr : Address) : Prop :=
  ∃ (state after : TcState .anon),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state ∧
    TcM.ctxAddrForLbr type.lbr state = .ok ctxAddr after

end SoundOptional

/-! ### The seams of the reducing tiers -/

section Seams

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- What the reducing tiers consume beyond the smaller table's contracts.

The first group is soundness of the reduction bodies the conversion tiers
run at their own table: `whnf`, `whnfCore`, and `whnfCoreWithFlags` are
exactly the `StepContracts` reduction fields at this depth, and
`whnfNoDeltaImpl` is the no-delta body those fields are proved through; the
cheap def-eq variants are derived below. The one frame fact, that full
reduction retains the primitive table, is a state field the invariant does
not record. The second group is the optional
reducers and probes of the lazy-delta loop: each returns `none` with the
invariant preserved or a result convertible to its source, the Nat-offset
probe answers as a conversion, and the projection-delta loop compares two
projections of one field. The third group is the final-tier tails that need
inductive structure or literal facts: Nat bridging, structure eta, unit-like
types, let congruence (reached only when structural WHNF left a `let`), and
the constructed eta-expansion, whose reading and typing need the intern
resources and the typing of the expansion. The last group is boundaries of
the set model: the contracts supply whole-term typing only, so hereditary
typing of an application's function and argument, formation of the type of a
typed term, and the transport of a recorded proposition classification to the
caller's registration (the is-prop instance of the context-digest boundary)
are stated here rather than derived. -/
structure DefEqReducingSeams (depth : Nat) : Prop where
  /-- The full reduction body at this table (`StepContracts.whnf`). -/
  whnf : ∀ term, SoundReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.whnf term).run (methodsN depth))
  /-- Full reduction never writes the primitive table; the invariant records
  no frame for that field, and the eager `Bool.true` tier compares the
  recognitions made before and after one reduction. -/
  whnfPrims : ∀ (term : KExpr .anon) (before : TcState .anon),
    match (RecM.whnf term).run (methodsN depth) before with
    | .ok _ after | .error _ after => after.prims = before.prims
  /-- The structural reduction body at this table (`StepContracts.whnfCore`). -/
  whnfCore : ∀ term, SoundReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.whnfCore term).run (methodsN depth))
  /-- The flagged structural body at this table (`StepContracts.whnfCoreFlags`). -/
  whnfCoreWithFlags : ∀ term flags, SoundReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.whnfCoreWithFlags term flags).run (methodsN depth))
  /-- The no-delta body at this table under any flags and succ mode. -/
  whnfNoDeltaImpl : ∀ term flags mode, SoundReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.whnfNoDeltaImpl term flags mode).run (methodsN depth))
  /-- Nat literal and primitive reduction. -/
  reduceNat : ∀ term, SoundOptionalReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.tryReduceNat term).run (methodsN depth))
  /-- Native reduction; `none` without state change under `noAccel`. -/
  reduceNative : ∀ term, SoundOptionalReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.tryReduceNative term).run (methodsN depth))
  /-- Decidable-instance reduction; `none` without state change under `noAccel`. -/
  reduceDecidable : ∀ term, SoundOptionalReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.tryReduceDecidable term).run (methodsN depth))
  /-- The projection-headed no-delta probe. -/
  unfoldProjApp : ∀ term, SoundOptionalReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.tryUnfoldProjApp term).run (methodsN depth))
  /-- One delta unfolding of a defined head, justified by the reduction
  package's `DefinitionBinding`. -/
  deltaUnfoldOne : ∀ term, SoundOptionalReduction.{u,v} resolve anchor entries source catalog term
    ((RecM.deltaUnfoldOne term).run (methodsN depth))
  /-- Nat-offset comparison by shared-offset injectivity. -/
  offset : ∀ left right, SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
    ((RecM.tryDefEqOffset left right).run (methodsN depth))
  /-- The projection-directed delta loop on two projections of one field. -/
  projectionDelta : ∀ (id : KId .anon) (field : UInt64) (left right : KExpr .anon)
    (leftInfo rightInfo : ExprInfo .anon),
    SoundConversion.{u,v} resolve anchor entries source catalog (.prj id field left leftInfo)
      (.prj id field right rightInfo) ((RecM.lazyDeltaProjReduction id field left right).run (methodsN depth))
  /-- Nat-like bridging in the final tier. -/
  whnfNat : ∀ left right, SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
    ((RecM.tryDefEqWhnfNat left right).run (methodsN depth))
  /-- Structure eta in both directions. -/
  structEta : ∀ left right, SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
    ((RecM.tryDefEqWhnfStructEta left right).run (methodsN depth))
  /-- Unit-like types. -/
  unit : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
    ((RecM.tryDefEqUnit left right).run (methodsN depth))
  /-- Let congruence through the local declaration. -/
  whnfLet : ∀ (name : Mode.anon.F Name) (ty1 v1 body1 ty2 v2 body2 : KExpr .anon)
    (nonDep1 nonDep2 : Bool) (info1 info2 : ExprInfo .anon),
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog
      (.letE name ty1 v1 body1 nonDep1 info1) (.letE name ty2 v2 body2 nonDep2 info2)
      ((RecM.tryDefEqWhnfLet name ty1 v1 body1 ty2 v2 body2).run (methodsN depth))
  /-- The constructed eta-expansion of a function typed by the exposed
  dependent function type, compared against the lambda operand. -/
  compareEta : ∀ (t s : KExpr .anon) (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (ty : KExpr .anon) (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (T S A B : AExpr β) (condition : Certified.PropWhen),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals t = some T.erase →
    (∃ type, TypingClaim.{u,v} entries context T type) →
    readScopedExpr? resolve locals s = some S.erase →
    readScopedExpr? resolve locals ty = some A.erase →
    TypingClaim.{u,v} entries context S (.forallE condition A B) →
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds T S
      ((RecM.compareEtaExpansion t s name bi ty).run (methodsN depth) before)
  /-- Hereditary typing of an application. -/
  appHereditary : ∀ (context : Model.Context β) (fn arg type : AExpr β),
    TypingClaim.{u,v} entries context (.app fn arg) type →
    (∃ type, TypingClaim.{u,v} entries context fn type) ∧
    (∃ type, TypingClaim.{u,v} entries context arg type)
  /-- The type of a typed term is a type. -/
  typeFormation : ∀ (context : Model.Context β) (term type : AExpr β),
    TypingClaim.{u,v} entries context term type →
    ∃ level, TypingClaim.{u,v} entries context type (.sort level)
  /-- A positive is-prop entry at a key computed from the caller's registration
  classifies the caller's reading of the keyed type. -/
  isPropTransport : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (type : KExpr .anon) (ctxAddr : Address) (A : AExpr β),
    IsPropKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds type ctxAddr →
    readScopedExpr? resolve locals type = some A.erase →
    (∃ type, TypingClaim.{u,v} entries context A type) →
    (∃ (locals' : List FVarId) (context' : Model.Context β) (source' : KExpr .anon) (term : AExpr β),
      source'.addr = type.addr ∧ readScopedExpr? resolve locals' source' = some term.erase ∧
      TypingClaim.{u,v} entries context' term (.sort .zero)) →
    TypingClaim.{u,v} entries context A (.sort .zero)

/-- Finite resources of the reducing tiers: the direct tiers' resources for
every operand, and per-lookup conversion data at every invariant state, each
an instance of `RunAssumptions`. -/
structure DefEqReducingResources : Prop where
  tiers : DefEqTierResources.{u,v} resolve anchor entries source catalog fun _ => True
  lookup : ∀ (state : TcState .anon) (locals : List FVarId) (context : Model.Context β)
    (bounds : List VLevel),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    ∀ addr, StandaloneConversionData source addr state.env

end Seams

/-! ### Invariant preservation through the reducing tiers' bookkeeping -/

namespace CheckerInvariant

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- The rejection-only same-head cache carries no claim. -/
theorem ofDefEqFailure {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (key : Address × Address × Address) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with env := {state.env with defEqFailure := state.env.defEqFailure.insert key}} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl

/-- Recording a proposition classification preserves the invariant once a
positive answer records a proposition with the key's address. -/
theorem ofIsPropInsert {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (key : Address × Address) (answer : Bool)
    (justified : answer = true →
      ∃ (locals' : List FVarId) (context' : Model.Context β) (source' : KExpr .anon) (term : AExpr β),
        source'.addr = key.1 ∧ readScopedExpr? resolve locals' source' = some term.erase ∧
        TypingClaim.{u,v} entries context' term (.sort .zero)) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with env := {state.env with isPropCache := state.env.isPropCache.insert key answer}} where
  sourceCache := ⟨valid.sourceState.ofMaps rfl rfl rfl valid.coherent, valid.cache.ofMaps rfl rfl rfl⟩
  synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps rfl rfl⟩
  whnf := valid.whnf.elim fun history => ⟨history.ofMaps fun partition => by cases partition <;> rfl⟩
  structural := ⟨valid.structural.coherent, valid.structural.allocated, valid.structural.loader⟩
  reading := valid.reading
  origin := valid.origin
  semantics := ⟨valid.semantics.whnf.ofMaps (fun partition => by cases partition <;> rfl),
    valid.semantics.defEq.ofMaps (fun partition => by cases partition <;> rfl),
    valid.semantics.equivalence, valid.semantics.unfold.ofMap rfl, by
      intro stored hit
      change (state.env.isPropCache.insert key answer)[stored]? = some true at hit
      rw [Std.HashMap.getElem?_insert] at hit
      split at hit
      · next same =>
          rw [← eq_of_beq same]
          exact justified (Option.some.inj hit)
      · exact valid.semantics.isProp stored hit⟩

/-- Lookup retains the invariant on both outcomes of the optional variant. -/
theorem tryGetConst {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) (data : StandaloneConversionData source id.addr before.env) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      (TcM.tryGetConst id before) := by
  have preserved := valid.getConst id data
  unfold TcM.getConst at preserved
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after)
    at preserved
  unfold EStateM.bind at preserved
  cases run : TcM.tryGetConst id before <;> rw [run] at preserved
  · rename_i optional after
    cases optional <;> exact preserved
  · exact preserved

end CheckerInvariant

/-! ### Reductions and probes -/

section Reductions

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- The type of a typed term is typed. -/
theorem DefEqReducingSeams.formed {depth : Nat}
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    {context : Model.Context β} {term type : AExpr β}
    (typed : TypingClaim.{u,v} entries context term type) :
    ∃ type', TypingClaim.{u,v} entries context type type' :=
  (seams.typeFormation context term type typed).elim fun _ formed => ⟨_, formed⟩

/-- The cheap recursion scope preserves reduction soundness: the depth is a
scalar outside every invariant map. -/
theorem SoundReduction.withCheapRecursionDepth {input : KExpr .anon}
    {action : RecM .anon (KExpr .anon)} {methods : Methods .anon}
    (sound : SoundReduction.{u,v} resolve anchor entries source catalog input (action.run methods)) :
    SoundReduction.{u,v} resolve anchor entries source catalog input
      ((RecM.withCheapRecursionDepth action).run methods) := by
  intro locals context bounds before term valid reads typed
  rw [withCheapRecursionDepth_run]
  have inner := sound locals context bounds {before with cheapRecursionDepth := before.cheapRecursionDepth + 1}
    term (valid.ofDefEqScalars rfl rfl rfl rfl) reads typed
  cases run : action.run methods {before with cheapRecursionDepth := before.cheapRecursionDepth + 1} <;>
    rw [run] at inner
  · exact ⟨inner.1.ofDefEqScalars rfl rfl rfl rfl, inner.2⟩
  · exact inner.ofDefEqScalars rfl rfl rfl rfl

theorem whnfCoreForDefEq_sound {depth : Nat}
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth) (term : KExpr .anon) :
    SoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCoreForDefEq term).run (methodsN depth)) := by
  rw [whnfCoreForDefEq_def]
  exact (seams.whnfCoreWithFlags term .DEF_EQ_CORE).withCheapRecursionDepth

theorem whnfNoDeltaForDefEq_sound {depth : Nat}
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth) (term : KExpr .anon) :
    SoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfNoDeltaForDefEq term).run (methodsN depth)) := by
  rw [whnfNoDeltaForDefEq_def]
  exact (seams.whnfNoDeltaImpl term .DEF_EQ_CORE .collapse).withCheapRecursionDepth

/-- The caught inference-only edge under the smaller table's contract, at an
already typed annotated reading of the source. -/
theorem tryInferOnly_sound {methods : Methods .anon}
    (recursive : InferContract.{u,v} resolve anchor entries source catalog methods)
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {before : TcState .anon}
    {term : KExpr .anon} {a T : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (reads : readScopedExpr? resolve locals term = some a.erase)
    (typed : TypingClaim.{u,v} entries context a T) :
    match (RecM.try? (RecM.inferOnlyCall term)).run methods before with
    | .ok (some type) after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
        ∃ A : AExpr β, readScopedExpr? resolve locals type = some A.erase ∧
          TypingClaim.{u,v} entries context a A
    | .ok none after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
    | .error _ after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [tryInferOnly_run]
  have post := (recursive.infer term).only locals context bounds {before with inferOnly := true} a T
    (valid.policy true) rfl reads typed
  cases run : methods.infer term {before with inferOnly := true} <;> rw [run] at post
  · exact ⟨post.1.policy _, post.2⟩
  · exact post.policy _

/-- A lookup-only classifier keeps the invariant. -/
theorem KeepsInvariant.lookup {α : Type} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {before : TcState .anon} {id : KId .anon}
    {next : Option (KConst .anon) → TcM .anon α}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (data : StandaloneConversionData source id.addr before.env)
    (pureNext : ∀ value state, ∃ result, next value state = .ok result state) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      ((TcM.tryGetConst id >>= next) before) := by
  have kept := valid.tryGetConst id data
  cases run : TcM.tryGetConst id before <;> rw [run] at kept
  · rw [EStateM.run_bind_ok run]
    obtain ⟨result, next⟩ := pureNext _ _
    rw [next]
    exact kept
  · rw [EStateM.run_bind_error run]
    exact kept

/-- The bounded loop driver: an invariant on loop states that every step
respects yields the loop's outcome property, with exhaustion an error at an
invariant state. -/
theorem runBoundedInvariant_sound {σ α : Type} {methods : Methods .anon}
    {step : σ → RecM .anon (RecM.BoundedStep σ α)}
    {Inv : σ → TcState .anon → Prop}
    {Post : EStateM.Result (TcError .anon) (TcState .anon) α → Prop}
    (stepSound : ∀ state before, Inv state before →
      match (step state).run methods before with
      | .ok (.next state') after => Inv state' after
      | .ok (.done result) after => Post (.ok result after)
      | .error err after => Post (.error err after))
    (exhausted : ∀ state before, Inv state before → Post (.error .maxRecDepth before)) :
    ∀ (fuel : Nat) (state : σ) (before : TcState .anon), Inv state before →
      Post ((RecM.runBounded step fuel state).run methods before)
  | 0, state, before, invariant => exhausted state before invariant
  | fuel + 1, state, before, invariant => by
      rw [RecM.runBounded, ReaderT.run_bind]
      have post := stepSound state before invariant
      cases run : (step state).run methods before with
      | error err after =>
          rw [EStateM.run_bind_error run]
          rw [run] at post
          exact post
      | ok next after =>
          rw [EStateM.run_bind_ok run]
          rw [run] at post
          cases next with
          | next state' => exact runBoundedInvariant_sound stepSound exhausted fuel state' after post
          | done result => exact post

end Reductions

/-! ### Readings of the reduced shapes -/

section Readings

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

private theorem bind_some {α γ : Type _} {action : Option α} {next : α → Option γ} {result : γ}
    (run : action.bind next = some result) :
    ∃ value, action = some value ∧ next value = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

theorem readScopedExpr?_app_annotated {fn arg : KExpr .anon} {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.app fn arg info) = some a.erase) :
    ∃ f x : AExpr β, a = .app f x ∧ readScopedExpr? resolve locals fn = some f.erase ∧
      readScopedExpr? resolve locals arg = some x.erase := by
  rw [readScopedExpr?] at reading
  obtain ⟨f', fnReads, reading⟩ := bind_some reading
  obtain ⟨x', argReads, reading⟩ := bind_some reading
  have erased : a.erase = .app f' x' := (Option.some.inj reading).symm
  cases a <;> simp only [AExpr.erase] at erased <;> cases erased
  exact ⟨_, _, rfl, fnReads, argReads⟩

theorem readScopedExpr?_prj_annotated {id : KId .anon} {index : UInt64} {value : KExpr .anon}
    {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.prj id index value info) = some a.erase) :
    ∃ (ref : ConstRef β) (v : AExpr β), resolve id.addr = some ref ∧ a = .proj ref index.toNat v ∧
      readScopedExpr? resolve locals value = some v.erase := by
  rw [readScopedExpr?] at reading
  obtain ⟨ref, resolved, reading⟩ := bind_some reading
  obtain ⟨v', valueReads, reading⟩ := bind_some reading
  have erased : a.erase = .proj ref index.toNat v' := (Option.some.inj reading).symm
  cases a <;> simp only [AExpr.erase] at erased <;> cases erased
  exact ⟨_, _, resolved, rfl, valueReads⟩

theorem readScopedExpr?_nat_annotated {value : Nat} {blob : Address}
    {info : ExprInfo .anon} {a : AExpr β}
    (reading : readScopedExpr? resolve locals (.nat value blob info) = some a.erase) :
    a = .natLit value := by
  have erased : a.erase = .natLit value := (Option.some.inj reading).symm
  cases a <;> simp only [AExpr.erase] at erased <;> cases erased
  rfl

theorem readScopedExpr?_var_none (index : UInt64) (name : Mode.anon.F Name) (info : ExprInfo .anon) :
    readScopedExpr? resolve locals (.var index name info) = none := by
  simp [readScopedExpr?]

theorem readScopedExpr?_str_none (value : String) (blob : Address)
    (info : ExprInfo .anon) :
    readScopedExpr? resolve locals (.str value blob info) = none := rfl

/-- Neither operand of a readable pair is a compact string literal. -/
theorem hasStringLiteralPair_eq_false {left right : KExpr .anon} {a b : VExpr β}
    (leftReads : readScopedExpr? resolve locals left = some a)
    (rightReads : readScopedExpr? resolve locals right = some b) :
    RecM.hasStringLiteralPair left right = false := by
  unfold RecM.hasStringLiteralPair
  cases left <;> first
    | (simp [readScopedExpr?] at leftReads; done)
    | (cases right <;> first | rfl | (simp [readScopedExpr?] at rightReads; done))

end Readings

/-! ### The hash path of a reduced pair -/

section HashPath

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
  {locals : List FVarId} {context : Model.Context β}

/-- Address equality of two readable, typed operands is conversion under
address faithfulness and the annotation discipline. -/
theorem ConversionClaim.ofAddrEq {left right : KExpr .anon} {a b : AExpr β}
    (faithful : left.AddrFaithful right) (annotations : SameRawAnnotations.{u,v} entries)
    (equal : (left.addr == right.addr) = true)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type) :
    ConversionClaim.{u,v} entries context a b := by
  have same := beq_readScopedExpr? (resolve := resolve) (locals := locals) (depth := 0) faithful
    (by rw [KExpr.beq_def]; exact equal)
  have erased : a.erase = b.erase := Option.some.inj (leftReads.symm.trans (same.trans rightReads))
  cases AExpr.eq_of_erase_annotations erased (annotations context a b erased leftTyped rightTyped)
  exact ConversionClaim.refl a

end HashPath

/-! ### Annotated spines -/

section Spines

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
  {locals : List FVarId} {context : Model.Context β}

/-- Application congruence along a spine of pairwise convertible arguments. -/
theorem ConversionClaim.appN {f f' : AExpr β} :
    ∀ {args args' : List (AExpr β)}, ConversionClaim.{u,v} entries context f f' →
      args.length = args'.length →
      (∀ pair ∈ args.zip args', ConversionClaim.{u,v} entries context pair.1 pair.2) →
      ConversionClaim.{u,v} entries context (f.appN args) (f'.appN args')
  | [], [], head, _, _ => head
  | [], _ :: _, _, lengths, _ => absurd lengths (by simp)
  | _ :: _, [], _, lengths, _ => absurd lengths (by simp)
  | a :: as, a' :: as', head, lengths, pairs =>
      ConversionClaim.appN (f := .app f a) (f' := .app f' a')
        (ConversionClaim.app head (pairs (a, a') (List.mem_cons_self ..)))
        (by simpa using lengths) (fun pair member => pairs pair (List.mem_cons_of_mem _ member))

/-- Hereditary typing of a typed spine: the head and every argument are typed. -/
theorem AExpr.appN_typed
    (appHereditary : ∀ (context : Model.Context β) (fn arg type : AExpr β),
      TypingClaim.{u,v} entries context (.app fn arg) type →
      (∃ type, TypingClaim.{u,v} entries context fn type) ∧
      (∃ type, TypingClaim.{u,v} entries context arg type)) :
    ∀ {f : AExpr β} {args : List (AExpr β)}, (∃ type, TypingClaim.{u,v} entries context (f.appN args) type) →
      (∃ type, TypingClaim.{u,v} entries context f type) ∧
      ∀ a ∈ args, ∃ type, TypingClaim.{u,v} entries context a type
  | _, [], typed => ⟨typed, fun _ member => nomatch member⟩
  | f, a :: as, typed => by
      obtain ⟨⟨type, headTyped⟩, argsTyped⟩ := AExpr.appN_typed appHereditary (f := .app f a) (args := as) typed
      obtain ⟨fTyped, aTyped⟩ := appHereditary context f a type headTyped
      refine ⟨fTyped, fun x member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact aTyped
      · exact argsTyped x member

/-- Typed spine readings of two argument lists of equal length. -/
theorem SpineReadings.ofLists :
    ∀ {rawLeft rawRight : List (KExpr .anon)} {left right : List (AExpr β)},
      rawLeft.map (readScopedExpr? resolve locals ·) = left.map (some ·.erase) →
      rawRight.map (readScopedExpr? resolve locals ·) = right.map (some ·.erase) →
      (∀ a ∈ left, ∃ type, TypingClaim.{u,v} entries context a type) →
      (∀ b ∈ right, ∃ type, TypingClaim.{u,v} entries context b type) →
      rawLeft.length = rawRight.length →
      SpineReadings.{u,v} resolve entries locals context (rawLeft.zip rawRight) (left.zip right)
  | [], [], left, right, leftReads, rightReads, _, _, _ => by
      cases left <;> cases right <;> simp at leftReads rightReads
      exact .nil
  | [], _ :: _, _, _, _, _, _, _, lengths => absurd lengths (by simp)
  | _ :: _, [], _, _, _, _, _, _, lengths => absurd lengths (by simp)
  | l :: ls, r :: rs, left, right, leftReads, rightReads, leftTyped, rightTyped, lengths => by
      cases left with
      | nil => simp at leftReads
      | cons a as =>
      cases right with
      | nil => simp at rightReads
      | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at leftReads rightReads
      exact .cons leftReads.1 (leftTyped a (List.mem_cons_self ..)) rightReads.1
        (rightTyped b (List.mem_cons_self ..))
        (SpineReadings.ofLists leftReads.2 rightReads.2
          (fun x member => leftTyped x (List.mem_cons_of_mem _ member))
          (fun x member => rightTyped x (List.mem_cons_of_mem _ member)) (by simpa using lengths))

/-- The typed annotated spine parts of two readable operands whose raw spines
have equal size: both decompose as heads applied to argument lists, the raw
heads read the annotated heads, the heads are typed, and the zipped arguments
are typed spine readings. -/
theorem spine_parts
    (appHereditary : ∀ (context : Model.Context β) (fn arg type : AExpr β),
      TypingClaim.{u,v} entries context (.app fn arg) type →
      (∃ type, TypingClaim.{u,v} entries context fn type) ∧
      (∃ type, TypingClaim.{u,v} entries context arg type))
    {left right : KExpr .anon} {a b : AExpr β}
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type)
    (sizes : left.collectSpine.2.size = right.collectSpine.2.size) :
    a = (AppSpineSource.parts left a).1.appN (AppSpineSource.parts left a).2 ∧
    b = (AppSpineSource.parts right b).1.appN (AppSpineSource.parts right b).2 ∧
    readScopedExpr? resolve locals left.collectSpine.1 = some (AppSpineSource.parts left a).1.erase ∧
    readScopedExpr? resolve locals right.collectSpine.1 = some (AppSpineSource.parts right b).1.erase ∧
    (∃ type, TypingClaim.{u,v} entries context (AppSpineSource.parts left a).1 type) ∧
    (∃ type, TypingClaim.{u,v} entries context (AppSpineSource.parts right b).1 type) ∧
    (AppSpineSource.parts left a).2.length = (AppSpineSource.parts right b).2.length ∧
    SpineReadings.{u,v} resolve entries locals context
      (left.collectSpine.2.toList.zip right.collectSpine.2.toList)
      ((AppSpineSource.parts left a).2.zip (AppSpineSource.parts right b).2) := by
  obtain ⟨aEq, aHeadReads, aArgsRead⟩ := AppSpineSource.reading leftReads
  obtain ⟨bEq, bHeadReads, bArgsRead⟩ := AppSpineSource.reading rightReads
  have aParts := AExpr.appN_typed appHereditary (aEq ▸ leftTyped)
  have bParts := AExpr.appN_typed appHereditary (bEq ▸ rightTyped)
  have aLength : left.collectSpine.2.toList.length = (AppSpineSource.parts left a).2.length := by
    simpa using congrArg List.length aArgsRead
  have bLength : right.collectSpine.2.toList.length = (AppSpineSource.parts right b).2.length := by
    simpa using congrArg List.length bArgsRead
  refine ⟨aEq, bEq, aHeadReads, bHeadReads, aParts.1, bParts.1, ?_, ?_⟩
  · rw [← aLength, ← bLength]
    simpa using sizes
  · exact SpineReadings.ofLists aArgsRead bArgsRead aParts.2 bParts.2 (by simpa using sizes)

end Spines

/-! ### Proof irrelevance -/

section ProofIrrelevance

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- The uncached classifier: infer the type of the type, normalize it, and
accept a semantically zero sort. -/
theorem classifyPropTypeUncached_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {type : KExpr .anon} {A T : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (typeReads : readScopedExpr? resolve locals type = some A.erase)
    (typed : TypingClaim.{u,v} entries context A T) :
    PropositionPost.{u,v} resolve anchor entries source catalog locals context bounds A
      ((RecM.classifyPropTypeUncached type).run (methodsN depth) before) := by
  unfold RecM.classifyPropTypeUncached
  simp only [ReaderT.run_bind]
  have probe := tryInferOnly_sound (methods := methodsN depth) recursive.toInferContract valid typeReads typed
  cases runI : (RecM.try? (RecM.inferOnlyCall type)).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runI]
      rw [runI] at probe
      exact probe
  | ok sort? s₁ =>
      rw [EStateM.run_bind_ok runI]
      rw [runI] at probe
      cases sort? with
      | none =>
          try dsimp only
          rw [pure_run]
          exact probe
      | some sort =>
          obtain ⟨valid₁, S, sortReads, typedS⟩ := probe
          obtain ⟨level, formedS⟩ := seams.typeFormation context A S typedS
          try dsimp only
          simp only [ReaderT.run_bind]
          have reduced := seams.whnf sort locals context bounds s₁ S valid₁ sortReads ⟨_, formedS⟩
          cases runW : (RecM.whnf sort).run (methodsN depth) s₁ with
          | error err s₂ =>
              have caught : (RecM.try? (RecM.whnf sort)).run (methodsN depth) s₁ = .ok none s₂ := by
                rw [try?_run, runW]
              rw [EStateM.run_bind_ok caught]
              rw [runW] at reduced
              try dsimp only
              rw [pure_run]
              exact reduced
          | ok w s₂ =>
              have caught : (RecM.try? (RecM.whnf sort)).run (methodsN depth) s₁ = .ok (some w) s₂ := by
                rw [try?_run, runW]
              rw [EStateM.run_bind_ok caught]
              rw [runW] at reduced
              obtain ⟨valid₂, W, wReads, claimSW, _⟩ := reduced
              cases w
              case sort u info =>
                  try dsimp only
                  rw [pure_run]
                  cases zero : u.isSemanticZero with
                  | false => exact valid₂
                  | true =>
                      have wEq := readScopedExpr?_sort_annotated wReads
                      subst wEq
                      obtain ⟨_, bound, _⟩ := resources.tiers.sorts u u info info trivial trivial
                      have zeroEq : ∀ values, (readLevel u).eval values = VLevel.zero.eval values :=
                        fun values => by
                          rw [readLevel_eval]
                          exact Theory.VLevel.equiv_def.mp
                            (KUniv.toVLevel_equiv_zero_of_isSemanticZero bound zero) values
                      exact ⟨valid₂, TypingClaim.conv typedS (TypingClaim.sort .zero)
                        (claimSW.trans (ConversionClaim.sort zeroEq))⟩
              all_goals
                try dsimp only
                rw [pure_run]
                exact valid₂

/-- The memoized classifier: a positive memo hit is transported to the
caller's registration, a miss classifies and records its answer. -/
theorem isPropType_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {type : KExpr .anon} {A T : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (typeReads : readScopedExpr? resolve locals type = some A.erase)
    (typed : TypingClaim.{u,v} entries context A T) :
    PropositionPost.{u,v} resolve anchor entries source catalog locals context bounds A
      ((RecM.isPropType type).run (methodsN depth) before) := by
  unfold RecM.isPropType
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  obtain ⟨ctxAddr, s₁, keyRun⟩ := ctxAddrForLbr_ok type.lbr before
  rw [EStateM.run_bind_ok keyRun]
  have valid₁ : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds s₁ := by
    rw [ctxAddrForLbr_state keyRun]
    exact valid.ofCtxAddrCache _
  have origin : IsPropKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds
      type ctxAddr := ⟨before, s₁, valid, keyRun⟩
  rw [EStateM.run_bind_ok (get_run (methodsN depth) s₁)]
  try dsimp only
  cases hit : s₁.env.isPropCache[(type.addr, ctxAddr)]? with
  | some cached =>
      try dsimp only
      rw [pure_run]
      cases cached with
      | false => exact valid₁
      | true =>
          exact ⟨valid₁, seams.isPropTransport locals context bounds type ctxAddr A origin typeReads
            ⟨_, typed⟩ (valid₁.semantics.isProp _ hit)⟩
  | none =>
      try dsimp only
      simp only [ReaderT.run_bind]
      have classified := classifyPropTypeUncached_sound recursive seams resources valid₁ typeReads typed
      cases runC : (RecM.classifyPropTypeUncached type).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runC]
          rw [runC] at classified
          exact classified
      | ok answer s₂ =>
          rw [EStateM.run_bind_ok runC]
          rw [runC] at classified
          try dsimp only
          rw [EStateM.run_bind_ok (modify_run _ (methodsN depth) s₂)]
          try dsimp only
          rw [pure_run]
          cases answer with
          | false => exact classified.ofIsPropInsert (type.addr, ctxAddr) false (fun h => nomatch h)
          | true =>
              exact ⟨classified.1.ofIsPropInsert (type.addr, ctxAddr) true
                (fun _ => ⟨locals, context, type, A, rfl, typeReads, classified.2⟩), classified.2⟩

/-- Proof irrelevance: both operands typed by one proposition are convertible. -/
theorem tryProofIrrel_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryProofIrrel left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  obtain ⟨Ta, aTyped⟩ := leftTyped
  obtain ⟨Tb, bTyped⟩ := rightTyped
  unfold RecM.tryProofIrrel
  simp only [ReaderT.run_bind]
  have probeA := tryInferOnly_sound (methods := methodsN depth) recursive.toInferContract valid leftReads aTyped
  cases runA : (RecM.try? (RecM.inferOnlyCall left)).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at probeA
      exact probeA
  | ok aType? s₁ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at probeA
      cases aType? with
      | none =>
          try dsimp only
          rw [pure_run]
          exact probeA
      | some aType =>
          obtain ⟨valid₁, A, aTypeReads, typedA⟩ := probeA
          obtain ⟨levelA, formedA⟩ := seams.typeFormation context a A typedA
          try dsimp only
          simp only [ReaderT.run_bind]
          have prop := isPropType_sound recursive seams resources valid₁ aTypeReads formedA
          cases runP : (RecM.isPropType aType).run (methodsN depth) s₁ with
          | error err s₂ =>
              rw [EStateM.run_bind_error runP]
              rw [runP] at prop
              exact prop
          | ok isProp s₂ =>
              rw [EStateM.run_bind_ok runP]
              rw [runP] at prop
              cases isProp with
              | false =>
                  simp only [Bool.not_false, ↓reduceIte]
                  rw [pure_run]
                  exact prop
              | true =>
                  obtain ⟨valid₂, propA⟩ := prop
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  simp only [ReaderT.run_bind]
                  have probeB := tryInferOnly_sound (methods := methodsN depth) recursive.toInferContract
                    valid₂ rightReads bTyped
                  cases runB : (RecM.try? (RecM.inferOnlyCall right)).run (methodsN depth) s₂ with
                  | error err s₃ =>
                      rw [EStateM.run_bind_error runB]
                      rw [runB] at probeB
                      exact probeB
                  | ok bType? s₃ =>
                      rw [EStateM.run_bind_ok runB]
                      rw [runB] at probeB
                      cases bType? with
                      | none =>
                          try dsimp only
                          rw [pure_run]
                          exact probeB
                      | some bType =>
                          obtain ⟨valid₃, B, bTypeReads, typedB⟩ := probeB
                          try dsimp only
                          rw [isDefEqCall_run]
                          have conv := recursive.isDefEq aType bType locals context bounds s₃ A B valid₃
                            aTypeReads ⟨_, propA⟩ bTypeReads (seams.formed typedB)
                          cases runD : (methodsN depth).isDefEq aType bType s₃ with
                          | error err s₄ =>
                              rw [runD] at conv
                              exact conv
                          | ok answer s₄ =>
                              rw [runD] at conv
                              cases answer with
                              | false => exact conv
                              | true =>
                                  obtain ⟨valid₄, claimAB⟩ := conv
                                  exact ⟨valid₄, ConversionClaim.proofIrrel propA typedA
                                    (TypingClaim.conv typedB propA claimAB.symm)⟩

end ProofIrrelevance

/-! ### The upper chain: eager `Bool.true`, string expansion, and the cheap passes -/

section UpperChain

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- A recognized `Bool.true` operand reads as the bound `Bool.true` reference
at no universes. -/
theorem isBoolTrue_reading {locals : List FVarId} {prims : Primitives .anon} {term : KExpr .anon}
    {a : AExpr β}
    (recognized : isBoolTrueAnswer prims term = true)
    (reads : readScopedExpr? resolve locals term = some a.erase) :
    ∃ ref, resolve prims.boolTrue.addr = some ref ∧ a = .const ref [] := by
  unfold isBoolTrueAnswer at recognized
  cases term
  case const id us info =>
    simp only [Bool.and_eq_true, beq_iff_eq] at recognized
    obtain ⟨empty, addr⟩ := recognized
    obtain ⟨ref, resolved, aEq⟩ := readScopedExpr?_const_annotated reads
    have usNil : us = #[] := by simpa using empty
    subst usNil
    rw [← addr]
    exact ⟨ref, resolved, aEq⟩
  all_goals exact absurd recognized Bool.false_ne_true

/-- The eager `Bool.true` shortcut with the right operand recognized: the
left operand reduces to the same constant, or the remaining tiers decide. -/
theorem isDefEqInnerAfterQuick_sound_of_tail {depth : Nat}
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (tail : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterBoolTrue left right).run (methodsN depth)))
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterQuick left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  have symmetric : SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterFirstBoolGuardMiss left right).run (methodsN depth)) := by
    intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
    unfold RecM.isDefEqInnerAfterFirstBoolGuardMiss
    simp only [ReaderT.run_bind]
    rw [EStateM.run_bind_ok (isBoolTrue_run left (methodsN depth) before)]
    try dsimp only
    rw [EStateM.run_bind_ok (boolTrueReductionAllowed_run right (methodsN depth) before)]
    try dsimp only
    by_cases guard : (isBoolTrueAnswer before.prims left && boolTrueAllowed before right) = true
    · rw [if_pos guard]
      simp only [Bool.and_eq_true] at guard
      obtain ⟨leftTrue, _⟩ := guard
      obtain ⟨ref, resolved, aEq⟩ := isBoolTrue_reading leftTrue leftReads
      unfold RecM.whnfIsBoolTrue
      simp only [ReaderT.run_bind, bind_assoc]
      have reduced := seams.whnf right locals context bounds before b valid rightReads rightTyped
      have prims := seams.whnfPrims right before
      cases runW : (RecM.whnf right).run (methodsN depth) before with
      | error err s₁ =>
          rw [EStateM.run_bind_error runW]
          rw [runW] at reduced
          exact reduced
      | ok w s₁ =>
          rw [EStateM.run_bind_ok runW]
          rw [runW] at reduced prims
          obtain ⟨valid₁, W, wReads, claimBW, _⟩ := reduced
          rw [EStateM.run_bind_ok (isBoolTrue_run w (methodsN depth) s₁)]
          try dsimp only
          by_cases wTrue : isBoolTrueAnswer s₁.prims w = true
          · rw [if_pos wTrue, pure_run]
            rw [prims] at wTrue
            obtain ⟨ref', resolved', wEq⟩ := isBoolTrue_reading wTrue wReads
            cases Option.some.inj (resolved.symm.trans resolved')
            subst aEq wEq
            exact ⟨valid₁, claimBW.symm⟩
          · rw [if_neg wTrue]
            try simp only [ReaderT.run_bind]
            try rw [EStateM.run_bind_ok (pure_run _ (methodsN depth) s₁)]
            try dsimp only
            exact tail left right locals context bounds s₁ a b valid₁ leftReads leftTyped rightReads
              rightTyped
    · rw [if_neg guard]
      try simp only [ReaderT.run_bind]
      try rw [EStateM.run_bind_ok (pure_run _ (methodsN depth) before)]
      try dsimp only
      exact tail left right locals context bounds before a b valid leftReads leftTyped rightReads
        rightTyped
  unfold RecM.isDefEqInnerAfterQuick
  simp only [ReaderT.run_bind]
  rw [EStateM.run_bind_ok (isBoolTrue_run right (methodsN depth) before)]
  try dsimp only
  rw [EStateM.run_bind_ok (boolTrueReductionAllowed_run left (methodsN depth) before)]
  try dsimp only
  by_cases guard : (isBoolTrueAnswer before.prims right && boolTrueAllowed before left) = true
  · rw [if_pos guard]
    simp only [Bool.and_eq_true] at guard
    obtain ⟨rightTrue, _⟩ := guard
    obtain ⟨ref, resolved, bEq⟩ := isBoolTrue_reading rightTrue rightReads
    unfold RecM.whnfIsBoolTrue
    simp only [ReaderT.run_bind, bind_assoc]
    have reduced := seams.whnf left locals context bounds before a valid leftReads leftTyped
    have prims := seams.whnfPrims left before
    cases runW : (RecM.whnf left).run (methodsN depth) before with
    | error err s₁ =>
        rw [EStateM.run_bind_error runW]
        rw [runW] at reduced
        exact reduced
    | ok w s₁ =>
        rw [EStateM.run_bind_ok runW]
        rw [runW] at reduced prims
        obtain ⟨valid₁, W, wReads, claimAW, _⟩ := reduced
        rw [EStateM.run_bind_ok (isBoolTrue_run w (methodsN depth) s₁)]
        try dsimp only
        by_cases wTrue : isBoolTrueAnswer s₁.prims w = true
        · rw [if_pos wTrue, pure_run]
          rw [prims] at wTrue
          obtain ⟨ref', resolved', wEq⟩ := isBoolTrue_reading wTrue wReads
          cases Option.some.inj (resolved.symm.trans resolved')
          subst bEq wEq
          exact ⟨valid₁, claimAW⟩
        · rw [if_neg wTrue]
          try simp only [ReaderT.run_bind]
          try rw [EStateM.run_bind_ok (pure_run _ (methodsN depth) s₁)]
          try dsimp only
          exact tail left right locals context bounds s₁ a b valid₁ leftReads leftTyped rightReads
            rightTyped
  · rw [if_neg guard]
    exact symmetric locals context bounds before a b valid leftReads leftTyped rightReads rightTyped

/-- String-literal expansion is never reached on readable operands. -/
theorem isDefEqInnerAfterBoolTrue_sound_of_tail {depth : Nat}
    (tail : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterStringExpansion left right).run (methodsN depth)))
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterBoolTrue left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqInnerAfterBoolTrue
  rw [hasStringLiteralPair_eq_false leftReads rightReads]
  simp only [Bool.false_eq_true, ↓reduceIte]
  try simp only [ReaderT.run_bind, pure_run]
  try rw [EStateM.run_bind_ok (pure_run _ (methodsN depth) before)]
  exact tail left right locals context bounds before a b valid leftReads leftTyped rightReads rightTyped

/-- The cheap structural-core pass: both operands are reduced, an address
match or the quick tier decides, otherwise the no-delta pass runs on the
original operands. -/
theorem isDefEqInnerAfterStringExpansion_sound_of_tail {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (tail : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterCorePass left right).run (methodsN depth)))
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterStringExpansion left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqInnerAfterStringExpansion
  simp only [ReaderT.run_bind]
  have reducedA := whnfCoreForDefEq_sound seams left locals context bounds before a valid leftReads leftTyped
  cases runA : (RecM.whnfCoreForDefEq left).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at reducedA
      exact reducedA
  | ok ca s₁ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at reducedA
      obtain ⟨valid₁, Ca, caReads, claimA, typesA⟩ := reducedA
      have caTyped : ∃ type, TypingClaim.{u,v} entries context Ca type := leftTyped.imp fun _ => typesA _
      have reducedB := whnfCoreForDefEq_sound seams right locals context bounds s₁ b valid₁ rightReads
        rightTyped
      cases runB : (RecM.whnfCoreForDefEq right).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runB]
          rw [runB] at reducedB
          exact reducedB
      | ok cb s₂ =>
          rw [EStateM.run_bind_ok runB]
          rw [runB] at reducedB
          obtain ⟨valid₂, Cb, cbReads, claimB, typesB⟩ := reducedB
          have cbTyped : ∃ type, TypingClaim.{u,v} entries context Cb type :=
            rightTyped.imp fun _ => typesB _
          try dsimp only
          split
          · rename_i same
            rw [pure_run]
            exact ⟨valid₂, claimA.trans ((ConversionClaim.ofAddrEq (resources.tiers.faithful ca cb trivial
              trivial) annotations same caReads caTyped cbReads cbTyped).trans claimB.symm)⟩
          · simp only [ReaderT.run_bind]
            have quick := quickDefEq_sound recursive.toDefEqContract (MethodsLocalState.methodsN depth)
              binders resources.tiers valid₂ trivial trivial caReads caTyped cbReads cbTyped
            cases runQ : (RecM.quickDefEq ca cb).run (methodsN depth) s₂ with
            | error err s₃ =>
                rw [EStateM.run_bind_error runQ]
                rw [runQ] at quick
                exact quick
            | ok answer s₃ =>
                rw [EStateM.run_bind_ok runQ]
                rw [runQ] at quick
                cases answer with
                | true =>
                    simp only [↓reduceIte]
                    rw [pure_run]
                    exact ⟨quick.1, claimA.trans (quick.2.trans claimB.symm)⟩
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact tail left right locals context bounds s₃ a b quick leftReads leftTyped
                      rightReads rightTyped

/-- The cheap no-delta pass: both operands are reduced, an address match or
the quick tier decides, otherwise the remaining tiers run on the reduced
pair, whose readings are convertible to the originals. -/
theorem isDefEqInnerAfterCorePass_sound_of_tail {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (tail : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterNoDeltaPass left right).run (methodsN depth)))
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterCorePass left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqInnerAfterCorePass
  simp only [ReaderT.run_bind]
  have reducedA := whnfNoDeltaForDefEq_sound seams left locals context bounds before a valid leftReads
    leftTyped
  cases runA : (RecM.whnfNoDeltaForDefEq left).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at reducedA
      exact reducedA
  | ok wa s₁ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at reducedA
      obtain ⟨valid₁, Wa, waReads, claimA, typesA⟩ := reducedA
      have waTyped : ∃ type, TypingClaim.{u,v} entries context Wa type := leftTyped.imp fun _ => typesA _
      have reducedB := whnfNoDeltaForDefEq_sound seams right locals context bounds s₁ b valid₁ rightReads
        rightTyped
      cases runB : (RecM.whnfNoDeltaForDefEq right).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runB]
          rw [runB] at reducedB
          exact reducedB
      | ok wb s₂ =>
          rw [EStateM.run_bind_ok runB]
          rw [runB] at reducedB
          obtain ⟨valid₂, Wb, wbReads, claimB, typesB⟩ := reducedB
          have wbTyped : ∃ type, TypingClaim.{u,v} entries context Wb type :=
            rightTyped.imp fun _ => typesB _
          try dsimp only
          split
          · rename_i same
            rw [pure_run]
            exact ⟨valid₂, claimA.trans ((ConversionClaim.ofAddrEq (resources.tiers.faithful wa wb trivial
              trivial) annotations same waReads waTyped wbReads wbTyped).trans claimB.symm)⟩
          · simp only [ReaderT.run_bind]
            have quick := quickDefEq_sound recursive.toDefEqContract (MethodsLocalState.methodsN depth)
              binders resources.tiers valid₂ trivial trivial waReads waTyped wbReads wbTyped
            cases runQ : (RecM.quickDefEq wa wb).run (methodsN depth) s₂ with
            | error err s₃ =>
                rw [EStateM.run_bind_error runQ]
                rw [runQ] at quick
                exact quick
            | ok answer s₃ =>
                rw [EStateM.run_bind_ok runQ]
                rw [runQ] at quick
                cases answer with
                | true =>
                    simp only [↓reduceIte]
                    rw [pure_run]
                    exact ⟨quick.1, claimA.trans (quick.2.trans claimB.symm)⟩
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have rest := tail wa wb locals context bounds s₃ Wa Wb quick waReads waTyped wbReads
                      wbTyped
                    cases runT : (RecM.isDefEqInnerAfterNoDeltaPass wa wb).run (methodsN depth) s₃ with
                    | error err s₄ =>
                        rw [runT] at rest
                        exact rest
                    | ok answer s₄ =>
                        rw [runT] at rest
                        cases answer with
                        | false => exact rest
                        | true => exact ⟨rest.1, claimA.trans (rest.2.trans claimB.symm)⟩

/-- Proof irrelevance before delta, then the lazy-delta tail. -/
theorem isDefEqInnerAfterNoDeltaPass_sound_of_tail {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (tail : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterProofIrrelevance left right).run (methodsN depth)))
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterNoDeltaPass left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqInnerAfterNoDeltaPass
  simp only [ReaderT.run_bind]
  have irrel := tryProofIrrel_sound recursive seams resources left right locals context bounds before a b
    valid leftReads leftTyped rightReads rightTyped
  cases runI : (RecM.tryProofIrrel left right).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runI]
      rw [runI] at irrel
      exact irrel
  | ok answer s₁ =>
      rw [EStateM.run_bind_ok runI]
      rw [runI] at irrel
      cases answer with
      | true =>
          simp only [↓reduceIte]
          rw [pure_run]
          exact irrel
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact tail left right locals context bounds s₁ a b irrel leftReads leftTyped rightReads rightTyped

end UpperChain

end Ix.Kernel.Consistency
