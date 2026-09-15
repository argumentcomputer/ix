/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ConversionRecipe
import Ix.Kernel.Verify.Consistency.RecursiveState

/-!
# Standalone source agreement through actual lazy loading

Source-only conversion predicts a complete standalone declaration. A loaded
declaration agrees with this prediction, initially by emptiness and afterward
by actual conversion and publication. Source ownership prevents block loads
from overwriting these standalone entries. Model bindings inspect only the
source prediction, rather than assuming a reading after each mutable lookup.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

theorem predictStandalone?_verified {source : Ixon.Env} {addr : Address} {constant : Ixon.Constant}
    (verified : getConstVerified source addr true = .ok (some constant))
    (standalone : ingressBlockAddr? addr constant.info = none) :
    predictStandalone? source addr =
      (ConversionRecipe.standalone source addr constant).predict.map some := by
  unfold predictStandalone?
  change Except.bind (getConstVerified source addr true) _ = _
  rw [verified, Except.bind]
  dsimp only
  rw [standalone]
  cases (ConversionRecipe.standalone source addr constant).predict <;> rfl

theorem predictStandalone?_some {source : Ixon.Env} {addr : Address} {expected : KConst .anon}
    (predicted : predictStandalone? source addr = .ok (some expected)) :
    ∃ constant, getConstVerified source addr true = .ok (some constant) ∧
      ingressBlockAddr? addr constant.info = none ∧
      (ConversionRecipe.standalone source addr constant).predict = .ok expected := by
  unfold predictStandalone? at predicted
  change Except.bind (getConstVerified source addr true) _ = _ at predicted
  cases verified : getConstVerified source addr true with
  | error err => rw [verified, Except.bind] at predicted; contradiction
  | ok optional =>
      cases optional with
      | none =>
          rw [verified, Except.bind] at predicted
          change Except.ok none = Except.ok (some expected) at predicted
          cases predicted
      | some constant =>
          simp only [verified, Except.bind] at predicted
          cases standalone : ingressBlockAddr? addr constant.info with
          | some block =>
              rw [standalone] at predicted
              change Except.ok none = Except.ok (some expected) at predicted
              cases predicted
          | none =>
              rw [standalone] at predicted
              cases result : (ConversionRecipe.standalone source addr constant).predict with
              | error err => simp [result, Bind.bind, Except.bind] at predicted
              | ok concrete =>
                  simp only [result, Bind.bind, Except.bind, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at predicted
                  cases predicted
                  exact ⟨constant, rfl, standalone, result⟩

/-- Agreement is required at the standalone catalog's selected keys. The
catalog does not claim to interpret mutual members or admit declarations. -/
def StandaloneSourceAgreement (source : Ixon.Env) (env : AnonEnv) : Prop :=
  ∀ id concrete, env.get? id = some concrete → ∀ expected,
    predictStandalone? source id.addr = .ok (some expected) → concrete = expected

theorem StandaloneSourceAgreement.empty (source : Ixon.Env) : StandaloneSourceAgreement source {} := by
  intro id concrete loaded
  simp [KEnv.get?] at loaded

theorem StandaloneSourceAgreement.ofMap {source : Ixon.Env} {before after : AnonEnv}
    (valid : StandaloneSourceAgreement source before) (constants : after.consts = before.consts) :
    StandaloneSourceAgreement source after := by
  intro id concrete loaded
  exact valid id concrete (by simpa only [KEnv.get?, constants] using loaded)

private theorem agreement_insert {source : Ixon.Env} {env : AnonEnv} {id : KId .anon}
    {concrete : KConst .anon} (valid : StandaloneSourceAgreement source env)
    (corresponds : ∀ expected, predictStandalone? source id.addr = .ok (some expected) → concrete = expected) :
    StandaloneSourceAgreement source (env.insert id concrete) := by
  intro other actual loaded expected predicted
  by_cases same : id = other
  · subst other
    simp only [KEnv.get?, KEnv.insert, Std.HashMap.getElem?_insert_self, Option.some.injEq] at loaded
    subst actual
    exact corresponds expected predicted
  · exact valid other actual
      (by simpa [KEnv.get?, KEnv.insert, Std.HashMap.getElem?_insert, same] using loaded) expected predicted

/-- A projected member cannot be a selected standalone catalog key. -/
theorem SourceOwnership.projection_unpredicted {source : Ixon.Env} (ownership : SourceOwnership source)
    {block : Address} {id : KId .anon} (projection : SourceProjection source block id)
    {expected : KConst .anon} (predicted : predictStandalone? source id.addr = .ok (some expected)) : False := by
  obtain ⟨constant, verified, standalone, _⟩ := predictStandalone?_some predicted
  have eta : (⟨id.addr, ()⟩ : KId .anon) = id := by
    cases id with | mk addr name => cases name; rfl
  exact ownership.standalone id.addr constant verified standalone block (by rwa [eta])

private theorem agreement_fold {source : Ixon.Env} (entries : List Entry)
    (corresponds : ∀ entry ∈ entries, ∀ expected,
      predictStandalone? source entry.1.addr = .ok (some expected) → entry.2 = expected)
    (before : AnonEnv) (valid : StandaloneSourceAgreement source before) :
    StandaloneSourceAgreement source
      (entries.foldl (fun env entry => env.insert entry.1 entry.2) before) := by
  induction entries generalizing before with
  | nil => exact valid
  | cons entry rest ih =>
      apply ih (fun member found => corresponds member (List.mem_cons_of_mem _ found))
      exact agreement_insert valid (corresponds entry List.mem_cons_self)

private theorem agreement_publish {source : Ixon.Env} {before : AnonEnv} {entries : Array Entry}
    (valid : StandaloneSourceAgreement source before)
    (corresponds : ∀ entry ∈ entries, ∀ expected,
      predictStandalone? source entry.1.addr = .ok (some expected) → entry.2 = expected) :
    StandaloneSourceAgreement source (insertMutsEntriesState before entries) := by
  unfold insertMutsEntriesState insertEntriesState
  apply agreement_fold entries.toList (by simpa using corresponds)
  split <;> exact valid.ofMap rfl

private theorem agreement_insertMuts {source : Ixon.Env} {before : AnonEnv} {entries : Array Entry}
    (valid : StandaloneSourceAgreement source before)
    (corresponds : ∀ entry ∈ entries, ∀ expected,
      predictStandalone? source entry.1.addr = .ok (some expected) → entry.2 = expected) :
    match insertMutsEntries entries before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after := by
  unfold insertMutsEntries
  change (match (EStateM.bind (guardReserved entries) _ : IngressM Unit) before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
  rw [EStateM.bind, guardReserved_state]
  cases checkReserved entries with
  | error err => exact valid
  | ok value => exact agreement_publish valid corresponds

/-- Block conversion may add arbitrary member types while preserving all
standalone source bindings: its emitted keys belong only to the owning block. -/
theorem ingressAnonBlock_sourceAgreement {source : Ixon.Env} (ownership : SourceOwnership source)
    {addr : Address} {constant : Ixon.Constant}
    (verified : getConstVerified source addr true = .ok (some constant))
    (before : AnonEnv) (valid : StandaloneSourceAgreement source before) :
    match ingressAnonBlock source constant addr before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after := by
  have inner : match ingressAnonBlockWithTrace source constant addr before with
      | .ok _ after | .error _ after => StandaloneSourceAgreement source after := by
    unfold ingressAnonBlockWithTrace
    change (match (EStateM.bind (prepareAnonBlock source constant addr) _ :
      IngressM AnonBlockIngressTrace) before with
      | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
    unfold prepareAnonBlock IngressM.runIntern EStateM.bind
    dsimp only
    cases converted : convertAnonBlock source constant addr before.intern with
    | error err it => exact valid.ofMap rfl
    | ok trace it =>
        have keys := convertAnonBlock_projection_keys converted
        have published := agreement_insertMuts (valid.ofMap (after := {before with intern := it}) rfl)
          (entries := trace.allEntries) (fun entry member _ predicted => False.elim
            (ownership.projection_unpredicted ⟨constant, verified, keys entry member⟩ predicted))
        change (match EStateM.bind (insertMutsEntries trace.allEntries)
          (fun _ => EStateM.pure trace) {before with intern := it} with
          | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
        rw [EStateM.bind]
        cases run : insertMutsEntries trace.allEntries {before with intern := it} <;>
          rw [run] at published <;> exact published
  unfold ingressAnonBlock
  change (match (EStateM.bind (ingressAnonBlockWithTrace source constant addr) _ :
    IngressM (Array (KId .anon))) before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
  rw [EStateM.bind]
  cases run : ingressAnonBlockWithTrace source constant addr before <;> rw [run] at inner <;> exact inner

/-- Actual standalone publication establishes the catalog agreement using
finite collision data before conversion, with no post-load reading premise. -/
theorem ingressAnonStandalone_sourceAgreement {source : Ixon.Env} {addr : Address}
    {constant : Ixon.Constant}
    (verified : getConstVerified source addr true = .ok (some constant))
    (standalone : ingressBlockAddr? addr constant.info = none)
    (before : AnonEnv) (valid : StandaloneSourceAgreement source before) (coherent : before.intern.WF)
    (data : ConversionData (ConversionRecipe.standalone source addr constant) before.intern) :
    match ingressAnonStandalone source addr constant before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after := by
  unfold ingressAnonStandalone
  change (match (EStateM.bind (IngressM.runIntern (convertAnonStandalone source addr constant))
    _ : IngressM (KId .anon)) before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
  unfold EStateM.bind IngressM.runIntern
  cases converted : convertAnonStandalone source addr constant before.intern with
  | error err it => exact valid.ofMap rfl
  | ok concrete it =>
      have predicted := (convertAnonStandalone_prediction coherent data converted).1
      have catalog : predictStandalone? source addr = .ok (some concrete) := by
        rw [predictStandalone?_verified verified standalone, predicted]
        rfl
      change (match (EStateM.bind (insertStandaloneEntries #[(⟨addr, ()⟩, concrete)])
        _ : IngressM (KId .anon)) {before with intern := it} with
        | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
      rw [EStateM.bind, insertStandaloneEntries_singleton]
      cases reservedMarkerName addr with
      | some marker => exact valid.ofMap rfl
      | none =>
          apply (agreement_insert (valid.ofMap (after := {before with intern := it}) rfl) ?_).ofMap rfl
          intro expected expectedPrediction
          exact Option.some.inj (Except.ok.inj (catalog.symm.trans expectedPrediction))

/-- Only a verified standalone's source conversion needs collision data.
Blocks need key ownership to preserve this catalog, not a reading of their types. -/
def StandaloneConversionData (source : Ixon.Env) (addr : Address) (before : AnonEnv) : Prop :=
  ∀ constant, getConstVerified source addr true = .ok (some constant) →
    ingressBlockAddr? addr constant.info = none →
    ConversionData (ConversionRecipe.standalone source addr constant) before.intern

theorem ingressAnonAddrShallow_sourceAgreement {source : Ixon.Env} (ownership : SourceOwnership source)
    (addr : Address) (before : AnonEnv) (valid : StandaloneSourceAgreement source before)
    (coherent : before.intern.WF) (data : StandaloneConversionData source addr before) :
    match ingressAnonAddrShallow source addr true before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after := by
  unfold ingressAnonAddrShallow
  change (match (EStateM.bind (IngressM.liftExcept (getConstVerified source addr true))
    _ : IngressM Bool) before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after)
  cases verified : getConstVerified source addr true with
  | error err => exact valid
  | ok optional =>
      cases optional with
      | none => exact valid
      | some constant =>
          dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
          cases block : ingressBlockAddr? addr constant.info with
          | none =>
              dsimp only [Bind.bind, EStateM.bind]
              have preserved := ingressAnonStandalone_sourceAgreement verified block before valid coherent
                (data constant verified block)
              cases run : ingressAnonStandalone source addr constant before <;>
                rw [run] at preserved <;> exact preserved
          | some blockAddr =>
              dsimp only [Bind.bind, EStateM.bind]
              rw [show (get : IngressM AnonEnv) before = .ok before before from rfl]
              dsimp only
              by_cases recorded : before.blocks.contains ⟨blockAddr, ()⟩ = true
              · simp only [recorded, ↓reduceIte]
                exact valid
              · simp only [recorded, Bool.false_eq_true, ↓reduceIte]
                cases parent : getConstVerified source blockAddr true with
                | error err => exact valid
                | ok optional =>
                    cases optional with
                    | none => exact valid
                    | some blockConstant =>
                        have preserved := ingressAnonBlock_sourceAgreement ownership parent before valid
                        dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
                        cases run : ingressAnonBlock source blockConstant blockAddr before <;>
                          rw [run] at preserved <;> exact preserved

/-- Reusable source agreement accompanies the previously established ownership
and coherence resource. It makes no claim about the typing of newly loaded code. -/
structure SourceStateInvariant (source : Ixon.Env) (before : TcState .anon) : Prop where
  state : InferenceStateInvariant source before
  agreement : StandaloneSourceAgreement source before.env

theorem SourceStateInvariant.ofCheckedSource (source : Ixon.Env)
    (checked : sourceOwnershipCheck source = true) :
    SourceStateInvariant source (TcState.newLazyAnon source) :=
  ⟨.ofCheckedSource source checked, .empty source⟩

theorem SourceStateInvariant.ofMaps {source : Ixon.Env} {before after : TcState .anon}
    (valid : SourceStateInvariant source before) (installed : after.lazyFault = before.lazyFault)
    (constants : after.env.consts = before.env.consts) (blocks : after.env.blocks = before.env.blocks)
    (coherent : after.env.intern.WF) : SourceStateInvariant source after :=
  ⟨valid.state.ofMaps installed constants blocks coherent, valid.agreement.ofMap constants⟩

theorem SourceStateInvariant.afterInferKey {source : Ixon.Env} {before after : TcState .anon}
    {term : KExpr .anon} {key : Address × Address} (valid : SourceStateInvariant source before)
    (run : TcM.inferKey term before = .ok key after) : SourceStateInvariant source after :=
  ⟨valid.state.afterInferKey run, valid.agreement.ofMap (congrArg KEnv.consts (inferKey_environment run))⟩

theorem lazyIngressAddr_sourceAgreement {source : Ixon.Env} {before : TcState .anon} {addr : Address}
    (valid : SourceStateInvariant source before) (data : StandaloneConversionData source addr before.env) :
    match TcM.lazyIngressAddr addr before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after.env := by
  unfold TcM.lazyIngressAddr
  rw [valid.state.installed]
  dsimp only
  by_cases faulted : before.faultedAddrs.contains addr = true
  · rw [if_pos faulted]
    exact valid.agreement
  · rw [if_neg faulted]
    have preserved := ingressAnonAddrShallow_sourceAgreement valid.state.ownership addr before.env
      valid.agreement valid.state.coherent data
    cases run : ingressAnonAddrShallow source addr true before.env <;>
      rw [run] at preserved <;> exact preserved

theorem tryGetConst_sourceAgreement {source : Ixon.Env} {before : TcState .anon} {id : KId .anon}
    (valid : SourceStateInvariant source before) (data : StandaloneConversionData source id.addr before.env) :
    match TcM.tryGetConst id before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after.env := by
  unfold TcM.tryGetConst
  change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
    TcM .anon (Option (KConst .anon))) before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after.env)
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  dsimp only
  cases before.env.get? id with
  | some concrete => exact valid.agreement
  | none =>
      change (match (EStateM.bind (TcM.lazyIngressAddr id.addr) _ :
        TcM .anon (Option (KConst .anon))) before with
        | .ok _ after | .error _ after => StandaloneSourceAgreement source after.env)
      have preserved := lazyIngressAddr_sourceAgreement valid data
      cases fault : TcM.lazyIngressAddr id.addr before with
      | error err after =>
          rw [EStateM.bind, fault]
          simpa only [fault] using preserved
      | ok value after =>
          rw [fault] at preserved
          rw [EStateM.bind, fault]
          change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
            TcM .anon (Option (KConst .anon))) after with
            | .ok _ state | .error _ state => StandaloneSourceAgreement source state.env)
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
          dsimp only
          cases after.env.get? id with
          | some concrete => exact preserved
          | none => cases before.lazyFault.isSome <;> exact preserved

theorem getConst_sourceAgreement {source : Ixon.Env} {before : TcState .anon} {id : KId .anon}
    (valid : SourceStateInvariant source before) (data : StandaloneConversionData source id.addr before.env) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after.env := by
  unfold TcM.getConst
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after => StandaloneSourceAgreement source after.env)
  have preserved := tryGetConst_sourceAgreement valid data
  cases tried : TcM.tryGetConst id before with
  | error err after =>
      rw [EStateM.bind, tried]
      simpa only [tried] using preserved
  | ok optional after =>
      rw [tried] at preserved
      rw [EStateM.bind, tried]
      cases optional <;> exact preserved

/-- Both lookup outcomes return ownership, coherence, and exact agreement
with the standalone source prediction for use by subsequent calls. -/
theorem SourceStateInvariant.getConst {source : Ixon.Env} {before : TcState .anon} {id : KId .anon}
    (valid : SourceStateInvariant source before) (data : StandaloneConversionData source id.addr before.env) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => SourceStateInvariant source after := by
  have state := valid.state.getConst id
  have agreement := getConst_sourceAgreement valid data
  cases run : TcM.getConst id before <;> rw [run] at state agreement <;> exact ⟨state, agreement⟩

private theorem tryGetConst_result_loaded {id : KId .anon} {concrete : KConst .anon}
    {before after : TcState .anon} (run : TcM.tryGetConst id before = .ok (some concrete) after) :
    after.env.get? id = some concrete := by
  unfold TcM.tryGetConst at run
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _ at run
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl] at run
  dsimp only at run
  cases loaded : before.env.get? id with
  | some value => rw [loaded] at run; cases run; exact loaded
  | none =>
      rw [loaded] at run
      change EStateM.bind (TcM.lazyIngressAddr id.addr) _ before = _ at run
      rw [EStateM.bind] at run
      cases fault : TcM.lazyIngressAddr id.addr before with
      | error err failed => rw [fault] at run; contradiction
      | ok value foundState =>
          rw [fault] at run
          change EStateM.bind (get : TcM .anon (TcState .anon)) _ foundState = _ at run
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) foundState =
            .ok foundState foundState from rfl] at run
          dsimp only at run
          cases found : foundState.env.get? id with
          | some value => rw [found] at run; cases run; exact found
          | none =>
              rw [found] at run
              cases enabled : before.lazyFault.isSome with
              | false =>
                  simp only [enabled, Bool.false_eq_true, ↓reduceIte] at run
                  change EStateM.Result.ok none foundState = .ok (some concrete) after at run
                  cases run
              | true =>
                  simp only [enabled, ↓reduceIte] at run
                  change EStateM.Result.error (TcError.unknownConst id.addr) foundState = _ at run
                  cases run

/-- A successful lookup returns a declaration present in its actual final
environment, regardless of which lazy callback was installed. -/
theorem getConst_result_loaded {id : KId .anon} {concrete : KConst .anon}
    {before after : TcState .anon} (run : TcM.getConst id before = .ok concrete after) :
    after.env.get? id = some concrete := by
  unfold TcM.getConst at run
  change EStateM.bind (TcM.tryGetConst id) _ before = _ at run
  rw [EStateM.bind] at run
  cases tried : TcM.tryGetConst id before with
  | error err failed => rw [tried] at run; contradiction
  | ok optional foundState =>
      rw [tried] at run
      cases optional with
      | none => cases run
      | some value => cases run; exact tryGetConst_result_loaded tried

/-- A model binding inspects the immutable source prediction once. Its
universe count and closed type reading do not mention a mutable lookup run. -/
structure StandaloneModelBinding {β : Type u} (source : Ixon.Env)
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    (id : KId .anon) (ref : ConstRef β) (entry : ConstantEntry β) where
  constant : KConst .anon
  predicted : predictStandalone? source id.addr = .ok (some constant)
  resolved : resolve id.addr = some ref
  found : entries ref = some entry
  universes : constant.lvls.toNat = entry.universes
  reading : readScopedExpr? resolve [] constant.ty = some entry.type.erase

/-- Actual lookup derives the admitted entry's arity and type reading from
the static source binding, and returns the invariant for the next call. -/
theorem StandaloneModelBinding.getConst {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {id : KId .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {before after : TcState .anon} {concrete : KConst .anon}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (valid : SourceStateInvariant source before)
    (data : StandaloneConversionData source id.addr before.env)
    (run : TcM.getConst id before = .ok concrete after) :
    concrete.lvls.toNat = entry.universes ∧
      readScopedExpr? resolve [] concrete.ty = some entry.type.erase ∧ SourceStateInvariant source after := by
  have post := valid.getConst data
  rw [run] at post
  have equal := post.agreement id concrete (getConst_result_loaded run) binding.constant binding.predicted
  exact ⟨equal ▸ binding.universes, equal ▸ binding.reading, post⟩

/-- Build the existing scoped inference interface without its post-lookup
arity, type-reading, or coherence premises. Only finite conversion and
universe-instantiation collision/level data remain at the executed operations. -/
theorem ScopedConstantInferenceSupport.ofSource {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {ref : ConstRef β} {entry : ConstantEntry β}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (valid : SourceStateInvariant source before) (wellFormed : entries.WF)
    (conversion : StandaloneConversionData source id.addr before.env)
    (instantiation : ConstantInstantiationData before id arguments) :
    ScopedConstantInferenceSupport resolve entries before id arguments ref entry := by
  refine ⟨binding.resolved, binding.found, wellFormed.typeScope ref entry binding.found, ?_⟩
  intro concrete loaded got
  obtain ⟨arity, reading, post⟩ := binding.getConst valid conversion got
  exact ⟨arity, reading, post.state.coherent,
    instantiation.faithful concrete loaded got, instantiation.levels concrete loaded got⟩

theorem ConstantInferenceSupport.ofSource {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {ref : ConstRef β} {entry : ConstantEntry β}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (valid : SourceStateInvariant source before) (wellFormed : entries.WF)
    (conversion : StandaloneConversionData source id.addr before.env)
    (instantiation : ConstantInstantiationData before id arguments) :
    ConstantInferenceSupport resolve entries before id arguments ref entry :=
  (ScopedConstantInferenceSupport.ofSource binding valid wellFormed conversion instantiation).closed

/-- The actual constant call refines model typing from a source-only binding,
with key computation included and no assumed type reading after lookup. -/
theorem infer_const_source_sound {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {context : Model.Context β} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (valid : SourceStateInvariant source before) (wellFormed : entries.WF)
    (miss : UncachedInference before (.const id arguments info))
    (conversion : StandaloneConversionData source id.addr before.env)
    (instantiation : ConstantInstantiationData miss.keyed id arguments)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok result after) :
    ModelTyping.{u,v} resolve entries context (.const id arguments info) result :=
  infer_const_sound miss (.ofSource binding (valid.afterInferKey miss.keyRun) wellFormed
    (by rwa [inferKey_environment miss.keyRun]) instantiation) wellFormed accepted

/-- Binder opening changes only local state and intern tables, retaining the
standalone source catalog while deriving the new table's coherence. -/
theorem SourceStateInvariant.openBinder {source : Ixon.Env}
    {before after : TcState .anon} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {domain body opened : KExpr .anon} {fresh : FVarId}
    (valid : SourceStateInvariant source before) (data : BinderOpeningData before body)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    SourceStateInvariant source after := by
  refine ⟨valid.state.openBinder data run, ?_⟩
  rw [openBinder_eq] at run
  split at run
  · cases run; exact valid.agreement.ofMap rfl
  · contradiction

/-- The existing operational tree needs only finite standalone-conversion
collision data at constant misses. It carries no post-load reading or source
agreement assumption at any recursive boundary. -/
def OwnedInferenceTrace.SourceData {fuel : Nat} {before : TcState .anon} {term : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (source : Ixon.Env) : Prop :=
  match tree with
  | .hit _ | .sort _ | .fvar _ | .nat _ => True
  | @OwnedInferenceTrace.const _ _ id _ _ miss _ =>
      StandaloneConversionData source id.addr miss.keyed.env
  | .app _ _ _ _ _ first second | .forallE _ _ _ first second |
      .lam _ _ _ _ _ first second => first.SourceData source ∧ second.SourceData source

private theorem source_invariant_hash {source : Ixon.Env} {before after : TcState .anon}
    {left right : KExpr .anon} {methods : Methods .anon}
    (valid : SourceStateInvariant source before) (equal : (left.addr == right.addr) = true)
    (run : RecM.isDefEq left right methods before = .ok true after) :
    SourceStateInvariant source after := by
  rw [isDefEq_hash_state equal] at run
  split at run <;> cases run <;> exact valid.ofMaps rfl rfl rfl valid.state.coherent

private theorem source_invariant_miss {source : Ixon.Env} {term result : KExpr .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    (valid : SourceStateInvariant source before) (miss : UncachedInference before term)
    (accepted : RecM.infer term methods before = .ok result after)
    (uncached : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly term methods miss.keyed = .ok result middle →
      SourceStateInvariant source miss.keyed → SourceStateInvariant source middle) :
    SourceStateInvariant source after := by
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  have post := uncached middle run (valid.afterInferKey miss.keyRun)
  rw [written]
  cases before.inferOnly <;> exact post.ofMaps rfl rfl rfl post.state.coherent

/-- Actual recursive inference preserves the source catalog from its initial state. -/
theorem OwnedInferenceTrace.preservesSource {source : Ixon.Env} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (valid : SourceStateInvariant source before)
    (sourceData : tree.SourceData source)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    SourceStateInvariant source after := by
  induction tree generalizing result after with
  | hit hit =>
      rw [hit.run] at accepted
      cases accepted
      exact valid.afterInferKey hit.keyRun
  | @sort fuel before level info miss =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      change EStateM.Result.ok
        (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
        {miss.keyed with env := {miss.keyed.env with intern :=
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
        .ok result middle at run
      cases run
      exact keyed.ofMaps rfl rfl rfl (keyed.state.coherent.internExpr _)
  | @fvar fuel before id name info miss =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      change (RecM.inferUncached RecM.inferCall before.inferOnly (.fvar id name info)).run
        (methodsN fuel) miss.keyed = _ at run
      unfold RecM.inferUncached at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed =
        .ok miss.keyed miss.keyed from rfl] at run
      dsimp only at run
      split at run
      · cases run; exact keyed
      · contradiction
  | @nat fuel before value blob info miss =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      obtain ⟨_, rfl⟩ := inferUncached_nat_run run
      exact keyed.ofMaps rfl rfl rfl (keyed.state.coherent.internExpr _)
  | @const fuel before id arguments info miss data =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      obtain ⟨concrete, loaded, got, _, instantiated⟩ := inferUncached_const_instantiation run
      have lookup := keyed.getConst sourceData
      rw [got] at lookup
      have post := TcM.instantiateUnivParams_wf (data.faithful concrete loaded got)
        (fun _ h => Or.inr h) ⟨lookup.state.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      rw [post.2.2.1]
      exact lookup.ofMaps rfl rfl rfl post.1.1
  | app full miss trace hashPath data functionTree argumentTree functionIH argumentIH =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      rw [full] at run
      have function := functionIH keyed sourceData.1 trace.functionRun
      have argument := argumentIH function sourceData.2 trace.argumentRun
      have compared := source_invariant_hash argument hashPath trace.compareRun
      rw [(trace.output_state run).2]
      exact compared.ofMaps rfl rfl rfl (data.coherent compared.state.coherent)
  | forallE miss trace opening domainTree bodyTree domainIH bodyIH =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      have domain := domainIH keyed sourceData.1 trace.domainRun
      have opened := domain.openBinder opening trace.openRun
      have body := bodyIH opened sourceData.2 trace.bodyRun
      rw [(trace.output_state run).2]
      exact body.ofMaps rfl rfl rfl (body.state.coherent.internExpr _)
  | lam full miss trace opening closing domainTree bodyTree domainIH bodyIH =>
      apply source_invariant_miss valid miss accepted
      intro middle run keyed
      rw [full] at run
      have domain := domainIH keyed sourceData.1 trace.domainRun
      have opened := domain.openBinder opening trace.openRun
      have body := bodyIH opened sourceData.2 trace.bodyRun
      rw [(trace.output_state run).2]
      exact body.ofMaps rfl rfl rfl ((closing.coherent body.state.coherent).internExpr _)

/-- A recursive call retains the existing cache frame and returns source
agreement, ownership, and coherence for subsequent dependent lookups. -/
theorem OwnedInferenceTrace.frameSource {source : Ixon.Env} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (valid : SourceStateInvariant source before)
    (sourceData : tree.SourceData source)
    {key : Address × Address} (outside : key ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    InferenceCacheFrame key before after ∧ after.inferOnly = before.inferOnly ∧
      SourceStateInvariant source after :=
  let frame := tree.frame valid.state outside accepted
  ⟨frame.1, frame.2.1, tree.preservesSource valid sourceData accepted⟩

end Ix.Kernel.Consistency
