/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.IngressCoherence
import Ix.Kernel.SourceOwnership

/-!
# Source ownership and complete lazy blocks

Projection ownership depends only on source headers and deterministic addresses.
Once any projection is loaded, its block is recorded. This invariant makes the
entries of an unrecorded block fresh, independently of expression conversion.
-/

namespace Ix.Kernel.Consistency

private def publicationBlock? : KConst .anon → Option (KId .anon)
  | .defn (block := block) .. | .recr (block := block) .. | .indc (block := block) .. => some block
  | _ => none

private def HeadOwned (block : Address) (entries : Array Entry) : Prop :=
  ∀ entry, entries[0]? = some entry → publicationBlock? entry.2 = some ⟨block, ()⟩

private def BlockShape (block : Address) (keys : Array (KId .anon)) (entries : Array Entry) : Prop :=
  (∀ entry ∈ entries, entry.1 ∈ keys) ∧ HeadOwned block entries

private def InternEnsures (action : InternIngressM α) (P : α → Prop) : Prop :=
  ∀ before value after, action before = .ok value after → P value

private theorem ensures_pure (value : α) (P : α → Prop) (holds : P value) :
    InternEnsures (pure value) P := by
  intro before result after run
  cases run
  exact holds

private theorem ensures_throw (err : IngressErr) (P : α → Prop) :
    InternEnsures (throw err) P := by
  intro before result after run
  cases run

private theorem ensures_throw_bind (err : IngressErr) (next : α → InternIngressM β) (P : β → Prop) :
    InternEnsures ((throw err : InternIngressM α) >>= next) P := by
  intro before result after run
  cases run

private theorem ensures_bind {action : InternIngressM α} {next : α → InternIngressM β}
    {P : α → Prop} {Q : β → Prop}
    (first : InternEnsures action P) (rest : ∀ value, P value → InternEnsures (next value) Q) :
    InternEnsures (action >>= next) Q := by
  intro before result after run
  change EStateM.bind action next before = _ at run
  rw [EStateM.bind] at run
  cases step : action before with
  | error err failed => rw [step] at run; contradiction
  | ok value middle =>
      rw [step] at run
      exact rest value (first before value middle step) middle result after run

private theorem ensures_then {action : InternIngressM α} {next : α → InternIngressM β}
    {Q : β → Prop} (rest : ∀ value, InternEnsures (next value) Q) :
    InternEnsures (action >>= next) Q :=
  ensures_bind (P := fun _ => True) (fun _ _ _ _ => True.intro) (fun value _ => rest value)

private theorem ensures_forIn' (items : List α) (initial : β) (P : β → Prop)
    (body : (item : α) → item ∈ items → β → InternIngressM (ForInStep β))
    (holds : P initial)
    (step : ∀ item member state, P state → InternEnsures (body item member state)
      (fun result => match result with | .done next | .yield next => P next)) :
    InternEnsures (forIn' items initial body) P := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn'_nil] using ensures_pure initial P holds
  | cons item rest ih =>
      rw [List.forIn'_cons]
      refine ensures_bind (Q := P) (step item (List.mem_cons_self) initial holds) ?_
      intro result preserved
      cases result with
      | done state => exact ensures_pure state P preserved
      | yield state =>
          exact ih state _ preserved
            (fun item member state valid => step item (List.mem_cons_of_mem _ member) state valid)

private theorem ensures_range (range : Std.Legacy.Range) (initial : β) (P : β → Prop)
    (body : (item : Nat) → item ∈ range → β → InternIngressM (ForInStep β))
    (holds : P initial)
    (step : ∀ item member state, P state → InternEnsures (body item member state)
      (fun result => match result with | .done next | .yield next => P next)) :
    InternEnsures (forIn' range initial body) P := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact ensures_forIn' _ initial P _ holds (fun item _ state valid => step item _ state valid)

attribute [local irreducible] InternEnsures

private theorem headOwned_empty (block : Address) : HeadOwned block #[] := by
  intro entry found
  simp at found

private theorem headOwned_append {block : Address} {left right : Array Entry}
    (hl : HeadOwned block left) (hr : HeadOwned block right) : HeadOwned block (left ++ right) := by
  intro entry found
  by_cases empty : left.size = 0
  · have equal : left = #[] := Array.eq_empty_of_size_eq_zero empty
    exact hr entry (by simpa only [equal, Array.empty_append] using found)
  · rw [Array.getElem?_append_left (by omega)] at found
    exact hl entry found

private theorem shape_empty (block : Address) (keys : Array (KId .anon)) : BlockShape block keys #[] :=
  ⟨by simp, headOwned_empty block⟩

private theorem shape_append {block : Address} {keys : Array (KId .anon)} {left right : Array Entry}
    (hl : BlockShape block keys left) (hr : BlockShape block keys right) :
    BlockShape block keys (left ++ right) := by
  refine ⟨?_, headOwned_append hl.2 hr.2⟩
  intro entry member
  rcases Array.mem_append.mp member with member | member
  · exact hl.1 entry member
  · exact hr.1 entry member

private theorem shape_singleton {block : Address} {keys : Array (KId .anon)} {entry : Entry}
    (key : entry.1 ∈ keys) (owned : publicationBlock? entry.2 = some ⟨block, ()⟩) :
    BlockShape block keys #[entry] := by
  refine ⟨?_, ?_⟩
  · intro value member
    simpa using (Array.mem_singleton.mp member ▸ key)
  · intro value found
    simp only [Array.getElem?_singleton, ↓reduceIte] at found
    cases found
    exact owned

private theorem shape_push {block : Address} {keys : Array (KId .anon)}
    {entries : Array Entry} {entry : Entry} (shape : BlockShape block keys entries)
    (nonempty : 0 < entries.size) (key : entry.1 ∈ keys) :
    BlockShape block keys (entries.push entry) := by
  refine ⟨?_, ?_⟩
  · intro value member
    rcases Array.mem_push.mp member with member | equal
    · exact shape.1 value member
    · exact equal ▸ key
  · intro value found
    rw [Array.getElem?_push_lt nonempty] at found
    exact shape.2 value (by simpa only [Array.getElem?_eq_getElem nonempty] using found)

private theorem convertDefnAnon_block (source : Ixon.Env) (defn : Ixon.Definition)
    (constant : Ixon.Constant) (block : KId .anon) (mutCtx : Array (KId .anon))
    (hints : Option Lean.ReducibilityHints) :
    InternEnsures (convertDefnAnon source defn constant block mutCtx hints)
      (fun concrete => publicationBlock? concrete = some block) := by
  unfold convertDefnAnon
  apply ensures_then
  intro result
  apply ensures_then
  intro value
  exact ensures_pure _ _ rfl

private theorem convertRecursorAnon_block (source : Ixon.Env) (rec : Ixon.Recursor)
    (constant : Ixon.Constant) (block : KId .anon) (mutCtx : Array (KId .anon)) :
    InternEnsures (convertRecursorAnon source rec constant block mutCtx)
      (fun concrete => publicationBlock? concrete = some block) := by
  unfold convertRecursorAnon
  apply ensures_then
  intro result
  apply ensures_then
  intro value
  exact ensures_pure _ _ rfl

private theorem convertAnonInductive_shape (source : Ixon.Env) (ind : Ixon.Inductive)
    (self : KId .anon) (constant : Ixon.Constant) (block : Address) (idx : UInt64)
    (ctorAddrs : Array Address) (mutCtx : Array (KId .anon)) (keys : Array (KId .anon))
    (selfKey : self ∈ keys)
    (ctorKeys : ∀ id ∈ ctorAddrs.map (⟨·, ()⟩ : Address → KId .anon), id ∈ keys) :
    InternEnsures (convertAnonInductive source ind self constant ⟨block, ()⟩ idx ctorAddrs mutCtx)
      (BlockShape block keys) := by
  unfold convertAnonInductive
  split
  · exact ensures_throw_bind _ _ _
  · rename_i lengths
    have sameSize : ctorAddrs.size = ind.ctors.size := by simpa using lengths
    apply ensures_then
    intro result
    refine ensures_bind (P := fun state => BlockShape block keys state.1 ∧ 0 < state.1.size)
      (Q := BlockShape block keys) ?_ ?_
    · apply ensures_range
      · exact ⟨shape_singleton selfKey rfl, by simp⟩
      · intro cidx member state valid
        apply ensures_then
        intro converted
        apply ensures_pure
        refine ⟨shape_push valid.1 valid.2 ?_, by simp⟩
        apply ctorKeys
        have bound : cidx < (ctorAddrs.map (⟨·, ()⟩ : Address → KId .anon)).size := by
          simp only [Array.size_map, sameSize]
          exact member.2.1
        dsimp only
        rw [getElem!_pos (ctorAddrs.map (⟨·, ()⟩ : Address → KId .anon)) cidx bound]
        exact Array.getElem_mem _
    · intro state valid
      exact ensures_pure _ _ valid.1

private theorem memberProjectionIds_mem {block : Address} {constant : Ixon.Constant}
    {members : Array Ixon.MutConst} (info : constant.info = .muts members)
    {idx : Nat} (bound : idx < members.size) {id : KId .anon}
    (member : id ∈ memberProjectionIds block idx.toUInt64 members[idx]) :
    id ∈ blockProjectionIds block constant := by
  simp only [blockProjectionIds, info]
  apply Array.mem_flatMap.mpr
  refine ⟨idx, Array.mem_range.mpr bound, ?_⟩
  simpa only [getElem!_pos members idx bound] using member

private theorem convertAnonBlock_shape (source : Ixon.Env) (constant : Ixon.Constant)
    (block : Address) : InternEnsures (convertAnonBlock source constant block)
      (fun trace => BlockShape block (blockProjectionIds block constant) trace.allEntries) := by
  unfold convertAnonBlock
  cases info : constant.info with
  | defn | recr | axio | quot | dPrj | iPrj | rPrj | cPrj => exact ensures_throw _ _
  | muts members =>
      refine ensures_bind (P := fun state : Array Entry × Array (KId .anon) =>
          BlockShape block (blockProjectionIds block constant) state.1)
        (Q := fun trace : AnonBlockIngressTrace =>
          BlockShape block (blockProjectionIds block constant) trace.allEntries) ?_ ?_
      · apply ensures_range
        · exact shape_empty _ _
        · intro idx member state valid
          dsimp only
          cases entry : members[idx] with
          | defn defn =>
              apply ensures_then
              intro _
              refine ensures_bind
                (convertDefnAnon_block source defn constant ⟨block, ()⟩ _ _) ?_
              intro converted header
              apply ensures_pure
              apply shape_append valid
              apply shape_singleton _ header
              apply memberProjectionIds_mem info member.2.1
              simp only [entry, memberProjectionIds, Array.mem_singleton]
          | recr rec =>
              apply ensures_then
              intro _
              refine ensures_bind
                (convertRecursorAnon_block source rec constant ⟨block, ()⟩ _) ?_
              intro converted header
              apply ensures_pure
              apply shape_append valid
              apply shape_singleton _ header
              apply memberProjectionIds_mem info member.2.1
              simp only [entry, memberProjectionIds, Array.mem_singleton]
          | indc ind =>
              apply ensures_then
              intro _
              apply ensures_then
              intro _
              refine ensures_bind
                (convertAnonInductive_shape source ind ⟨indcProjAddr block idx.toUInt64, ()⟩
                  constant block idx.toUInt64 (anonCtorAddrs block idx.toUInt64 ind) _
                  (blockProjectionIds block constant)
                  (by
                    apply memberProjectionIds_mem info member.2.1
                    simp [entry, memberProjectionIds])
                  (by
                    intro id ctor
                    apply memberProjectionIds_mem info member.2.1
                    simp only [entry, memberProjectionIds]
                    exact Array.mem_append.mpr (Or.inr ctor))) ?_
              intro converted shape
              exact ensures_pure _ _ (shape_append valid shape)
      · intro state valid
        exact ensures_pure _ _ valid

attribute [local semireducible] InternEnsures

/-- Successful production conversion emits only the finite projection keys
computed from this source block's headers. Interning needs no extra premise. -/
theorem convertAnonBlock_projection_keys {source : Ixon.Env} {constant : Ixon.Constant}
    {block : Address} {before after : InternTable .anon} {trace : AnonBlockIngressTrace}
    (run : convertAnonBlock source constant block before = .ok trace after) :
    ∀ entry ∈ trace.allEntries, entry.1 ∈ blockProjectionIds block constant :=
  (convertAnonBlock_shape source constant block before trace after run).1

/-- A projection belongs to a block verified in this fixed source. The key
inventory uses only declaration headers, member indices, and constructor counts. -/
def SourceProjection (source : Ixon.Env) (block : Address) (id : KId .anon) : Prop :=
  ∃ constant, getConstVerified source block true = .ok (some constant) ∧
    id ∈ blockProjectionIds block constant

/-- Finite source address separation. Different verified blocks have disjoint
projection inventories, and verified standalones have no projection key.
This says nothing about converted expressions, caches, or final checker states. -/
structure SourceOwnership (source : Ixon.Env) : Prop where
  blocks : ∀ block other id, SourceProjection source block id →
    SourceProjection source other id → block = other
  standalone : ∀ addr constant, getConstVerified source addr true = .ok (some constant) →
    ingressBlockAddr? addr constant.info = none →
    ∀ block, ¬ SourceProjection source block ⟨addr, ()⟩

/-- A source-only ownership table can discharge separation by finite lookups. -/
theorem SourceOwnership.ofOwner {source : Ixon.Env} (owner : KId .anon → Option Address)
    (projections : ∀ block id, SourceProjection source block id → owner id = some block)
    (standalones : ∀ addr constant, getConstVerified source addr true = .ok (some constant) →
      ingressBlockAddr? addr constant.info = none → owner ⟨addr, ()⟩ = none) :
    SourceOwnership source := by
  refine ⟨?_, ?_⟩
  · intro block other id left right
    exact Option.some.inj ((projections block id left).symm.trans (projections other id right))
  · intro addr constant verified standalone block projection
    have owned := projections block ⟨addr, ()⟩ projection
    rw [standalones addr constant verified standalone] at owned
    contradiction

/-- Every loaded source projection has an already-recorded owning block.
An unrecorded block therefore cannot overlap the current declaration map. -/
def LoadedBlockInvariant (source : Ixon.Env) (env : AnonEnv) : Prop :=
  ∀ block id, SourceProjection source block id → ∀ concrete,
    env.get? id = some concrete → env.blocks.contains ⟨block, ()⟩ = true

theorem LoadedBlockInvariant.empty (source : Ixon.Env) : LoadedBlockInvariant source {} := by
  intro block id projection concrete loaded
  simp [KEnv.get?] at loaded

theorem LoadedBlockInvariant.ofMaps {source : Ixon.Env} {before after : AnonEnv}
    (valid : LoadedBlockInvariant source before)
    (constants : after.consts = before.consts) (blocks : after.blocks = before.blocks) :
    LoadedBlockInvariant source after := by
  intro block id projection concrete loaded
  rw [blocks]
  exact valid block id projection concrete (by simpa only [KEnv.get?, constants] using loaded)

theorem LoadedBlockInvariant.intern {source : Ixon.Env} {env : AnonEnv}
    (valid : LoadedBlockInvariant source env) (table : InternTable .anon) :
    LoadedBlockInvariant source {env with intern := table} := valid

private theorem invariant_insertBlock {source : Ixon.Env} {env : AnonEnv}
    (valid : LoadedBlockInvariant source env) (id : KId .anon) (members : Array (KId .anon)) :
    LoadedBlockInvariant source (env.insertBlock id members) := by
  intro block key projection concrete loaded
  have recorded := valid block key projection concrete loaded
  simp only [KEnv.insertBlock, Std.HashMap.contains_insert, recorded, Bool.or_true]

private theorem invariant_insert {source : Ixon.Env} {env : AnonEnv}
    (valid : LoadedBlockInvariant source env) (entry : Entry)
    (recorded : ∀ block, SourceProjection source block entry.1 →
      env.blocks.contains ⟨block, ()⟩ = true) :
    LoadedBlockInvariant source (env.insert entry.1 entry.2) := by
  intro block id projection concrete loaded
  by_cases equal : entry.1 = id
  · subst id
    exact recorded block projection
  · apply valid block id projection concrete
    simpa only [KEnv.get?, KEnv.insert, Std.HashMap.getElem?_insert, beq_iff_eq,
      equal, ↓reduceIte] using loaded

private theorem invariant_insert_list {source : Ixon.Env} {env : AnonEnv}
    (valid : LoadedBlockInvariant source env) (entries : List Entry)
    (recorded : ∀ entry ∈ entries, ∀ block, SourceProjection source block entry.1 →
      env.blocks.contains ⟨block, ()⟩ = true) :
    LoadedBlockInvariant source
      (entries.foldl (fun current entry => current.insert entry.1 entry.2) env) := by
  induction entries generalizing env with
  | nil => exact valid
  | cons entry rest ih =>
      exact ih (invariant_insert valid entry (recorded entry (List.mem_cons_self)))
        (fun item member => recorded item (List.mem_cons_of_mem _ member))

private theorem publish_shape_invariant {source : Ixon.Env} {constant : Ixon.Constant}
    {block : Address} {env : AnonEnv} {entries : Array Entry}
    (sourceOwned : SourceOwnership source)
    (verified : getConstVerified source block true = .ok (some constant))
    (valid : LoadedBlockInvariant source env)
    (shape : BlockShape block (blockProjectionIds block constant) entries) :
    LoadedBlockInvariant source (insertMutsEntriesState env entries) := by
  unfold insertMutsEntriesState insertEntriesState
  change LoadedBlockInvariant source (entries.toList.foldl
    (fun current entry => current.insert entry.1 entry.2)
    (match entries[0]?.bind (fun entry => publicationBlock? entry.2) with
      | some id => env.insertBlock id (entries.map (·.1))
      | none => env))
  cases first : entries[0]? with
  | none =>
      have empty : entries = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        have := Array.getElem?_eq_none_iff.mp first
        omega
      simpa only [empty, Array.toList_empty, List.foldl_nil, Option.bind_none] using valid
  | some entry =>
      rw [Option.bind_some, shape.2 entry first]
      apply invariant_insert_list (invariant_insertBlock valid _ _)
      intro item member other projection
      have own : SourceProjection source block item.1 :=
        ⟨constant, verified, shape.1 item (by simpa using member)⟩
      have equal := sourceOwned.blocks block other item.1 own projection
      subst other
      simp [KEnv.insertBlock]

/-- Any actual preparation of an unrecorded block has entirely fresh keys.
No per-entry comparison with old converted declarations is required. -/
theorem LoadedBlockInvariant.compatible {source : Ixon.Env} {constant : Ixon.Constant}
    {block : Address} {before : AnonEnv}
    (valid : LoadedBlockInvariant source before)
    (verified : getConstVerified source block true = .ok (some constant))
    (unrecorded : before.blocks.contains ⟨block, ()⟩ ≠ true) :
    BlockEntriesCompatible source constant block before := by
  apply BlockEntriesCompatible.ofFresh
  intro trace converted run entry member
  unfold prepareAnonBlock IngressM.runIntern at run
  cases conversion : convertAnonBlock source constant block before.intern with
  | error err failed => rw [conversion] at run; contradiction
  | ok result table =>
      rw [conversion] at run
      cases run
      have projection : SourceProjection source block entry.1 :=
        ⟨constant, verified, convertAnonBlock_projection_keys conversion entry member⟩
      cases loaded : before.get? entry.1 with
      | none => rfl
      | some concrete => exact False.elim (unrecorded (valid block entry.1 projection concrete loaded))

theorem LoadedBlockInvariant.materialization {source : Ixon.Env} {before : AnonEnv}
    (valid : LoadedBlockInvariant source before) (addr : Address) :
    LazyMaterializationSupport source addr before := by
  unfold LazyMaterializationSupport
  cases getConstVerified source addr true with
  | error => trivial
  | ok optional =>
      cases optional with
      | none => trivial
      | some constant =>
          dsimp only
          cases ingressBlockAddr? addr constant.info with
          | none => trivial
          | some block =>
              dsimp only
              split
              · trivial
              · rename_i unrecorded
                cases verified : getConstVerified source block true with
                | error => trivial
                | ok optional =>
                    cases optional with
                    | none => trivial
                    | some constant => exact valid.compatible verified unrecorded

private theorem ingressAnonStandalone_blocks {source : Ixon.Env} {addr : Address}
    {constant : Ixon.Constant} (sourceOwned : SourceOwnership source)
    (verified : getConstVerified source addr true = .ok (some constant))
    (standalone : ingressBlockAddr? addr constant.info = none)
    (before : AnonEnv) (valid : LoadedBlockInvariant source before) :
    match ingressAnonStandalone source addr constant before with
    | .ok _ after | .error _ after => LoadedBlockInvariant source after := by
  unfold ingressAnonStandalone
  change (match (EStateM.bind (IngressM.runIntern (convertAnonStandalone source addr constant))
    _ : IngressM (KId .anon)) before with
    | .ok _ after | .error _ after => LoadedBlockInvariant source after)
  unfold EStateM.bind IngressM.runIntern
  cases converted : convertAnonStandalone source addr constant before.intern with
  | error err table => exact valid.intern table
  | ok concrete table =>
      change (match (EStateM.bind (insertStandaloneEntries #[(⟨addr, ()⟩, concrete)])
        _ : IngressM (KId .anon)) {before with intern := table} with
        | .ok _ after | .error _ after => LoadedBlockInvariant source after)
      rw [EStateM.bind, insertStandaloneEntries_singleton]
      cases reservedMarkerName addr with
      | some marker => exact valid.intern table
      | none =>
          apply invariant_insertBlock
          apply invariant_insert (valid.intern table) (⟨addr, ()⟩, concrete)
          intro block projection
          exact False.elim (sourceOwned.standalone addr constant verified standalone block projection)

/-- Whole-block loading preserves the ownership invariant on both outcomes,
including failure after partial conversion and successful flat publication. -/
theorem ingressAnonBlock_blocks {source : Ixon.Env} {constant : Ixon.Constant}
    {block : Address} (sourceOwned : SourceOwnership source)
    (verified : getConstVerified source block true = .ok (some constant))
    (before : AnonEnv) (valid : LoadedBlockInvariant source before) :
    match ingressAnonBlock source constant block before with
    | .ok _ after | .error _ after => LoadedBlockInvariant source after := by
  unfold ingressAnonBlock ingressAnonBlockWithTrace
  change (match (EStateM.bind (EStateM.bind (prepareAnonBlock source constant block)
    _) _ : IngressM (Array (KId .anon))) before with
    | .ok _ after | .error _ after => LoadedBlockInvariant source after)
  unfold prepareAnonBlock IngressM.runIntern EStateM.bind
  dsimp only
  cases converted : convertAnonBlock source constant block before.intern with
  | error err table => exact valid.intern table
  | ok trace table =>
      have shape := convertAnonBlock_shape source constant block before.intern trace table converted
      change (match (EStateM.bind (EStateM.bind (insertMutsEntries trace.allEntries)
        _) _ : IngressM (Array (KId .anon))) {before with intern := table} with
        | .ok _ after | .error _ after => LoadedBlockInvariant source after)
      simp only [insertMutsEntries, Bind.bind, EStateM.bind]
      rw [guardReserved_state]
      cases checkReserved trace.allEntries with
      | error err => exact valid.intern table
      | ok value => exact publish_shape_invariant sourceOwned verified (valid.intern table) shape

/-- The source ownership condition and the current invariant suffice for
every shallow load. Source misses and all failure paths preserve the invariant. -/
theorem ingressAnonAddrShallow_blocks {source : Ixon.Env} (sourceOwned : SourceOwnership source)
    (addr : Address) (before : AnonEnv) (valid : LoadedBlockInvariant source before) :
    match ingressAnonAddrShallow source addr true before with
    | .ok _ after | .error _ after => LoadedBlockInvariant source after := by
  unfold ingressAnonAddrShallow
  change (match (EStateM.bind (IngressM.liftExcept (getConstVerified source addr true))
    _ : IngressM Bool) before with
    | .ok _ after | .error _ after => LoadedBlockInvariant source after)
  cases verified : getConstVerified source addr true with
  | error err => exact valid
  | ok optional =>
      cases optional with
      | none => exact valid
      | some constant =>
          dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
          cases block : ingressBlockAddr? addr constant.info with
          | none =>
              have preserved := ingressAnonStandalone_blocks sourceOwned verified block before valid
              dsimp only [Bind.bind, EStateM.bind]
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
                        have preserved := ingressAnonBlock_blocks sourceOwned parent before valid
                        dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
                        cases run : ingressAnonBlock source blockConstant blockAddr before <;>
                          rw [run] at preserved <;> exact preserved

/-- One reusable loader resource for every address in a fixed source. Its
state field is initialized empty and preserved by actual production lookup. -/
structure OwnedLazySupport (before : TcState .anon) where
  source : Ixon.Env
  ownership : SourceOwnership source
  installed : before.lazyFault = some (fun addr => ingressAnonAddrShallow source addr true)
  blocks : LoadedBlockInvariant source before.env

def OwnedLazySupport.toVerified {before : TcState .anon} (support : OwnedLazySupport before)
    (addr : Address) : VerifiedLazySupport before addr :=
  ⟨support.source, support.installed, fun _ => support.blocks.materialization addr⟩

/-- No block-overlap assumptions on a checker state are needed at startup. -/
def OwnedLazySupport.newLazyAnon (source : Ixon.Env) (ownership : SourceOwnership source) :
    OwnedLazySupport (TcState.newLazyAnon source) :=
  ⟨source, ownership, rfl, LoadedBlockInvariant.empty source⟩

theorem lazyIngressAddr_blocks {before : TcState .anon} {addr : Address}
    (support : OwnedLazySupport before) :
    match TcM.lazyIngressAddr addr before with
    | .ok _ after | .error _ after => LoadedBlockInvariant support.source after.env := by
  unfold TcM.lazyIngressAddr
  rw [support.installed]
  dsimp only
  by_cases faulted : before.faultedAddrs.contains addr = true
  · rw [if_pos faulted]
    exact support.blocks
  · rw [if_neg faulted]
    have preserved := ingressAnonAddrShallow_blocks support.ownership addr before.env support.blocks
    cases run : ingressAnonAddrShallow support.source addr true before.env <;>
      rw [run] at preserved <;> exact preserved

theorem tryGetConst_blocks {before : TcState .anon} {id : KId .anon}
    (support : OwnedLazySupport before) :
    match TcM.tryGetConst id before with
    | .ok _ after | .error _ after => LoadedBlockInvariant support.source after.env := by
  unfold TcM.tryGetConst
  change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
    TcM .anon (Option (KConst .anon))) before with
    | .ok _ after | .error _ after => LoadedBlockInvariant support.source after.env)
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  dsimp only
  cases before.env.get? id with
  | some concrete => exact support.blocks
  | none =>
      change (match (EStateM.bind (TcM.lazyIngressAddr id.addr) _ :
        TcM .anon (Option (KConst .anon))) before with
        | .ok _ after | .error _ after => LoadedBlockInvariant support.source after.env)
      have preserved := lazyIngressAddr_blocks (addr := id.addr) support
      cases fault : TcM.lazyIngressAddr id.addr before with
      | error err after =>
          rw [EStateM.bind, fault]
          simpa only [fault] using preserved
      | ok value after =>
          rw [fault] at preserved
          rw [EStateM.bind, fault]
          change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
            TcM .anon (Option (KConst .anon))) after with
            | .ok _ state | .error _ state => LoadedBlockInvariant support.source state.env)
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
          dsimp only
          cases after.env.get? id with
          | some concrete => exact preserved
          | none => cases before.lazyFault.isSome <;> exact preserved

/-- Actual lookup derives cache preservation and retains the block invariant
for the next call, without per-block freshness or declaration comparisons. -/
theorem getConst_owned {before : TcState .anon} {id : KId .anon}
    (support : OwnedLazySupport before) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after =>
        LazyLookupFrame before after ∧ LoadedBlockInvariant support.source after.env := by
  have frame := getConst_verified_cache (id := id) (support.toVerified id.addr)
  have blocks : match TcM.getConst id before with
      | .ok _ after | .error _ after => LoadedBlockInvariant support.source after.env := by
    unfold TcM.getConst
    change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
      | .ok _ after | .error _ after => LoadedBlockInvariant support.source after.env)
    have preserved := tryGetConst_blocks (id := id) support
    cases tried : TcM.tryGetConst id before with
    | error err after =>
        rw [EStateM.bind, tried]
        simpa only [tried] using preserved
    | ok optional after =>
        rw [tried] at preserved
        rw [EStateM.bind, tried]
        cases optional <;> exact preserved
  cases run : TcM.getConst id before <;>
    rw [run] at frame blocks <;> exact ⟨frame, blocks⟩

def OwnedLazySupport.afterGetConst {before after : TcState .anon} {id : KId .anon}
    {concrete : KConst .anon} (support : OwnedLazySupport before)
    (run : TcM.getConst id before = .ok concrete after) : OwnedLazySupport after := by
  have preserved := getConst_owned (id := id) support
  rw [run] at preserved
  refine ⟨support.source, support.ownership, ?_, preserved.2⟩
  rw [preserved.1.checker]
  exact support.installed

def OwnedLazySupport.afterFailedGetConst {before after : TcState .anon} {id : KId .anon}
    {err : TcError .anon} (support : OwnedLazySupport before)
    (run : TcM.getConst id before = .error err after) : OwnedLazySupport after := by
  have preserved := getConst_owned (id := id) support
  rw [run] at preserved
  refine ⟨support.source, support.ownership, ?_, preserved.2⟩
  rw [preserved.1.checker]
  exact support.installed

end Ix.Kernel.Consistency
