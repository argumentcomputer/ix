import Ix.CompileCert.CanonUnivEmit
import Ix.CompileCert.CanonUnivScope
import Ix.CompileCert.UniverseMeaning
import Ix.CompileCert.Interning
import Std.Data.HashMap.Lemmas

/-! Correctness of actual source-universe compilation, canonical memoization,
table interning and certified reading. Both ordinary and metadata table modes
preserve scope and evaluation. Successful runs preserve cache and index
invariants; scope, wire capacity and preseed coverage imply success. Empty
initialization discharges the cache, table and preseed premises. Production
preseed coverage remains a separate caller obligation. -/

namespace Ix.CompileCert.UniversePipeline

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

/-- A canonical-cache hit is the exact producer output, not merely a value
equivalent universe. Empty initialization establishes this invariant. -/
def CanonCacheExact (state : BlockState) : Prop :=
  ∀ source value, state.canonUnivCache.get? source = some value → value = Ixon.canonUniv source

theorem canonCache_empty (state : BlockState) : CanonCacheExact { state with canonUnivCache := {} } := by
  intro source value impossible
  simp at impossible

theorem canonCache_insert {state : BlockState} (prior : CanonCacheExact state) (source : Ixon.Univ) :
    CanonCacheExact { state with canonUnivCache := state.canonUnivCache.insert source (Ixon.canonUniv source) } := by
  intro query value found
  change (state.canonUnivCache.insert source (Ixon.canonUniv source))[query]? = some value at found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have same : source = query := beq_iff_eq.mp same
    subst query
    exact (Option.some.inj found).symm
  · exact prior query value found

def withoutCanonCache (state : BlockState) : BlockState := { state with canonUnivCache := {} }

theorem canonUnivCached_run (source : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (canonUnivCached source) context state =
      match state.canonUnivCache.get? source with
      | some value => (.ok value, state)
      | none => (.ok (Ixon.canonUniv source),
          { state with canonUnivCache := state.canonUnivCache.insert source (Ixon.canonUniv source) }) := by
  unfold canonUnivCached
  simp only [rawRun_bind, rawRun_get]
  cases state.canonUnivCache.get? source <;> simp only [rawRun_bind, rawRun_modify, rawRun_pure]

theorem canonUnivCached_correct (source : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : CanonCacheExact before) :
    ∃ after, rawRun (canonUnivCached source) context before = (.ok (Ixon.canonUniv source), after) ∧
      CanonCacheExact after ∧ withoutCanonCache after = withoutCanonCache before := by
  rw [canonUnivCached_run]
  cases found : before.canonUnivCache.get? source with
  | none => exact ⟨_, rfl, canonCache_insert valid source, rfl⟩
  | some value =>
    rw [valid source value found]
    exact ⟨before, rfl, valid, rfl⟩

theorem canonUnivCached_eval (source : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : CanonCacheExact before) (ρ : UInt64 → Nat) :
    ∃ value after, rawRun (canonUnivCached source) context before = (.ok value, after) ∧
      CanonCacheExact after ∧ univEval ρ value = univEval ρ source := by
  obtain ⟨after, ran, sound, _⟩ := canonUnivCached_correct source context before valid
  exact ⟨Ixon.canonUniv source, after, ran, sound, CanonUnivEmit.canonUniv_eval ρ source⟩

def Preserves (projection : BlockState → α) (action : CompileM β) : Prop :=
  ∀ context before, projection (rawRun action context before).2 = projection before

theorem Preserves.pure (projection : BlockState → α) (value : β) : Preserves projection (pure value) := by
  intro context before; rfl

theorem Preserves.throw (projection : BlockState → α) (error : CompileError) :
    Preserves projection (throw error : CompileM β) := by intro context before; rfl

theorem Preserves.get (projection : BlockState → α) : Preserves projection getBlockState := by
  intro context before; rfl

theorem Preserves.read (projection : BlockState → α) : Preserves projection getBlockEnv := by
  intro context before; rfl

theorem Preserves.modify (projection : BlockState → α) (update : BlockState → BlockState)
    (unchanged : ∀ before, projection (update before) = projection before) :
    Preserves projection (modifyBlockState update) := by intro context before; exact unchanged before

theorem Preserves.bind {projection : BlockState → α} {action : CompileM β} {next : β → CompileM γ}
    (first : Preserves projection action) (later : ∀ value, Preserves projection (next value)) :
    Preserves projection (action >>= next) := by
  intro context before
  rw [rawRun_bind]
  have prior := first context before
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at prior
    cases outcome with
    | error error => exact prior
    | ok value => exact (later value context after).trans prior

theorem Preserves.checkedIndex (projection : BlockState → α) (table : String) (index : Nat) :
    Preserves projection (checkedTableIndex table index) := by
  unfold checkedTableIndex
  split
  · exact Preserves.pure projection _
  · exact Preserves.throw projection _

def withoutUnivCache (state : BlockState) : BlockState := { state with univCache := {} }

/-- Raw universe compilation can change only its memo, including on errors.
In particular it preserves the canonical memo and every reader table. -/
theorem compileUniv_frame (source : Ix.Level) : Preserves withoutUnivCache (compileUniv source) := by
  induction source <;> rw [compileUniv]
  all_goals
    with_reducible repeat' first
      | assumption
      | exact Preserves.pure withoutUnivCache _
      | exact Preserves.throw withoutUnivCache _
      | exact Preserves.get withoutUnivCache
      | exact Preserves.read withoutUnivCache
      | exact Preserves.checkedIndex withoutUnivCache _ _
      | refine Preserves.bind ?_ (fun _ => ?_)
      | apply Preserves.modify; intro before; simp only [withoutUnivCache, BlockState.cacheUniv]
      | dsimp only
      | split

/-- The actual initial two actions of canonical universe interning, with
success derived from source scope and representation bounds. -/
theorem compileCanonical_total_eval (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (rawValid : UniverseMeaning.CacheSound before) (canonValid : CanonCacheExact before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : UniverseMeaning.Scoped context.2.univCtx source) :
    ∃ value after,
      rawRun (do let raw ← compileUniv source; canonUnivCached raw) context before = (.ok value, after) ∧
      UniverseMeaning.CacheSound after ∧ CanonCacheExact after ∧
      ∀ (φ : Lean.Name → Nat) (ρ : UInt64 → Nat),
        (∀ index name, context.2.univCtx[index]? = some name → index < UInt64.size →
          φ (ixName name) = ρ index.toUInt64) → ixLevelEval φ source = some (univEval ρ value) := by
  obtain ⟨raw, middle, rawRunEq, rawSound, represented⟩ :=
    UniverseMeaning.compileUniv_total_correct source context bounded scope before rawValid
  have framed := compileUniv_frame source context before
  rw [rawRunEq] at framed
  have sameCanon := congrArg BlockState.canonUnivCache framed
  change middle.canonUnivCache = before.canonUnivCache at sameCanon
  have middleCanon : CanonCacheExact middle := by
    intro key value found
    rw [sameCanon] at found
    exact canonValid key value found
  obtain ⟨after, canonRunEq, canonSound, canonFrame⟩ := canonUnivCached_correct raw context middle middleCanon
  have sameRaw := congrArg BlockState.univCache canonFrame
  change after.univCache = middle.univCache at sameRaw
  have afterRaw : UniverseMeaning.CacheSound after := by
    intro key value found
    rw [sameRaw] at found
    exact rawSound key value found
  refine ⟨Ixon.canonUniv raw, after, ?_, afterRaw, canonSound, ?_⟩
  · rw [rawRun_bind, rawRunEq]
    exact canonRunEq
  · intro φ ρ aligned
    rw [CanonUnivEmit.canonUniv_eval]
    exact represented.eval φ ρ aligned

theorem compileCanonical_empty_eval (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : UniverseMeaning.Scoped context.2.univCtx source) :
    ∃ value after,
      rawRun (do let raw ← compileUniv source; canonUnivCached raw) context
        { before with univCache := {}, canonUnivCache := {} } = (.ok value, after) ∧
      UniverseMeaning.CacheSound after ∧ CanonCacheExact after ∧
      ∀ (φ : Lean.Name → Nat) (ρ : UInt64 → Nat),
        (∀ index name, context.2.univCtx[index]? = some name → index < UInt64.size →
          φ (ixName name) = ρ index.toUInt64) → ixLevelEval φ source = some (univEval ρ value) :=
  compileCanonical_total_eval source context { before with univCache := {}, canonUnivCache := {} }
    (UniverseMeaning.cache_empty { before with canonUnivCache := {} })
    (canonCache_empty { before with univCache := {} }) bounded scope

open Interning

/-- Projection that forgets precisely the tables changed by universe interning. -/
def withoutUnivTables (state : BlockState) : BlockState :=
  { state with univs := #[], univsIndex := {}, metaUnivs := #[], metaUnivsIndex := {} }

theorem internUniv_frame (univ : Ixon.Univ) : Preserves withoutUnivTables (internUniv univ) := by
  intro context state
  cases found : state.univsIndex.get? univ with
  | some index => rw [internUniv_hit univ context state found]
  | none =>
    rw [internUniv_miss univ context state found]
    split
    · rfl
    · rw [checkedTableCount_state]

theorem internMetaUniv_frame (univ : Ixon.Univ) : Preserves withoutUnivTables (internMetaUniv univ) := by
  intro context state
  cases found : state.metaUnivsIndex.get? univ with
  | some index => rw [internMetaUniv_hit univ context state found, checkedTableIndex_state]
  | none => rw [internMetaUniv_miss univ context state found]; split <;> rfl

theorem internMetaUniv_primary (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (internMetaUniv univ) context state).2.univs = state.univs := by
  cases found : state.metaUnivsIndex.get? univ with
  | some index => rw [internMetaUniv_hit univ context state found, checkedTableIndex_state]
  | none => rw [internMetaUniv_miss univ context state found]; split <;> rfl

theorem internMetaUniv_retains (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState)
    (primary : UnivIndexSound state) (metadata : MetaUnivIndexSound state) :
    Retains (univTable state) (univTable (rawRun (internMetaUniv univ) context state).2) := by
  have mode := congrArg BlockState.p3MetaMode (internMetaUniv_frame univ context state)
  change (rawRun (internMetaUniv univ) context state).2.p3MetaMode = state.p3MetaMode at mode
  unfold univTable
  rw [mode]
  split
  · exact (internMetaUniv_correct univ context state primary metadata).2.2.1
  · rw [internMetaUniv_primary]
    exact .refl _

/-- The final spelling-patch action of the production caller. -/
def finishSpelling (raw canon : Ixon.Univ) (index : UInt64) : CompileM (UInt64 × Option UInt64) := do
  if canon == raw then return (index, none)
  return (index, some (← internMetaUniv raw))

/-- Primary-table branch, including the production preseeding tripwire. -/
def internPrimaryCanonical (raw canon : Ixon.Univ) : CompileM (UInt64 × Option UInt64) := do
  let sizeBefore := (← getBlockState).univs.size
  let index ← internUniv canon
  if (← getBlockState).univsFinal && (← getBlockState).univs.size != sizeBefore then
    throw (.invalidMutualBlock
      s!"preseed missed canonical form {repr canon} — primary univ table \
        grew after preseeding, shifting univPatches virtual indices \
        (canonicity 10.6 V3)")
  finishSpelling raw canon index

/-- The table-writing suffix of `compileAndInternUnivCanon`. -/
def internCanonical (raw canon : Ixon.Univ) : CompileM (UInt64 × Option UInt64) := do
  if (← getBlockState).p3MetaMode then
    if !(← getBlockState).univsIndex.contains canon then
      let index ← internMetaUniv canon
      finishSpelling raw canon index
    else internPrimaryCanonical raw canon
  else internPrimaryCanonical raw canon

theorem compileAndInternUnivCanon_eq (source : Ix.Level) :
    compileAndInternUnivCanon source = (do
      let raw ← compileUniv source
      let canon ← canonUnivCached raw
      internCanonical raw canon) := rfl

def TablesSound (state : BlockState) : Prop := UnivIndexSound state ∧ MetaUnivIndexSound state

theorem TablesSound.primary {state : BlockState} (sound : TablesSound state) : UnivIndexSound state := sound.1
theorem TablesSound.metadata {state : BlockState} (sound : TablesSound state) : MetaUnivIndexSound state := sound.2

structure Interned (raw canon : Ixon.Univ) (state : BlockState) (result : UInt64 × Option UInt64) : Prop where
  canonical : (univTable state)[result.1.toNat]? = some canon
  spelling : ∀ index, result.2 = some index → (state.univs ++ state.metaUnivs)[index.toNat]? = some raw
  unchanged : result.2 = none → canon = raw

theorem finishSpelling_correct (raw canon : Ixon.Univ) (index : UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) (sound : TablesSound before)
    (located : (univTable before)[index.toNat]? = some canon) :
    let result := rawRun (finishSpelling raw canon index) context before
    TablesSound result.2 ∧ withoutUnivTables result.2 = withoutUnivTables before ∧
      Retains (univTable before) (univTable result.2) ∧
      ∀ value, result.1 = .ok value → Interned raw canon result.2 value := by
  unfold finishSpelling
  by_cases same : canon == raw
  · simp only [same, ↓reduceIte, rawRun_pure]
    refine ⟨sound, by trivial, .refl _, ?_⟩
    intro value success
    cases Except.ok.inj success
    exact ⟨located, by intros; contradiction, fun _ => beq_iff_eq.mp same⟩
  · simp only [same, Bool.false_eq_true, ↓reduceIte, rawRun_bind]
    have correct := internMetaUniv_correct raw context before sound.primary sound.metadata
    have framed := internMetaUniv_frame raw context before
    have retained := internMetaUniv_retains raw context before sound.primary sound.metadata
    cases ran : rawRun (internMetaUniv raw) context before with
    | mk outcome after =>
      rw [ran] at correct framed retained
      cases outcome with
      | error error => exact ⟨⟨correct.1, correct.2.1⟩, framed, retained, by intro value bad; cases bad⟩
      | ok patch =>
        simp only [rawRun_pure]
        refine ⟨⟨correct.1, correct.2.1⟩, framed, retained, ?_⟩
        intro value success
        cases Except.ok.inj success
        refine ⟨retained _ _ located, ?_, by intro bad; cases bad⟩
        intro value same
        cases Option.some.inj same
        exact correct.2.2.2 _ rfl

theorem Retains.trans {first middle last : Array α} (head : Retains first middle)
    (tail : Retains middle last) : Retains first last := fun index value found => tail index value (head index value found)

/-- Success and failure states retain table integrity and existing readable
levels. The output obligation applies only to successful returned indices. -/
def TablesCorrect (raw canon : Ixon.Univ) (before : BlockState)
    (result : Except CompileError (UInt64 × Option UInt64) × BlockState) : Prop :=
  TablesSound result.2 ∧ withoutUnivTables result.2 = withoutUnivTables before ∧
    Retains (univTable before) (univTable result.2) ∧
    ∀ value, result.1 = .ok value → Interned raw canon result.2 value

theorem internUniv_metadata (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (internUniv univ) context state).2.metaUnivs = state.metaUnivs ∧
    (rawRun (internUniv univ) context state).2.metaUnivsIndex = state.metaUnivsIndex := by
  cases found : state.univsIndex.get? univ with
  | some index => rw [internUniv_hit univ context state found]; exact ⟨rfl, rfl⟩
  | none =>
    rw [internUniv_miss univ context state found]
    split
    · exact ⟨rfl, rfl⟩
    · rw [checkedTableCount_state]; exact ⟨rfl, rfl⟩

theorem primary_in_view {state : BlockState} {index : UInt64} {univ : Ixon.Univ}
    (found : state.univs[index.toNat]? = some univ) : (univTable state)[index.toNat]? = some univ := by
  unfold univTable
  split
  · rwa [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp found).1]
  · exact found

theorem internPrimaryCanonical_correct (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : TablesSound before)
    (route : before.p3MetaMode = false ∨ before.univsIndex.contains canon = true) :
    TablesCorrect raw canon before (rawRun (internPrimaryCanonical raw canon) context before) := by
  have primary := internUniv_correct canon context before sound.primary
  have frame := internUniv_frame canon context before
  have metadata := internUniv_metadata canon context before
  have keeps : Retains (univTable before) (univTable (rawRun (internUniv canon) context before).2) := by
    rcases route with mode | hit
    · have modeAfter := congrArg BlockState.p3MetaMode frame
      change (rawRun (internUniv canon) context before).2.p3MetaMode = before.p3MetaMode at modeAfter
      simpa only [univTable, modeAfter, mode, Bool.false_eq_true, ↓reduceIte] using primary.2.1
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at hit
      change (before.univsIndex.get? canon).isSome = true at hit
      cases found : before.univsIndex.get? canon with
      | none => rw [found] at hit; cases hit
      | some index => rw [internUniv_hit canon context before found]; exact .refl _
  unfold internPrimaryCanonical
  simp only [rawRun_bind, rawRun_get]
  cases ran : rawRun (internUniv canon) context before with
  | mk outcome middle =>
    rw [ran] at primary frame metadata keeps
    have middleSound : TablesSound middle := ⟨primary.1, by
      intro univ index found
      rw [metadata.2] at found
      rw [metadata.1]
      exact sound.metadata univ index found⟩
    cases outcome with
    | error error => exact ⟨middleSound, frame, keeps, by intro value bad; cases bad⟩
    | ok index =>
      dsimp only
      split
      · exact ⟨middleSound, frame, keeps, by intro value bad; cases bad⟩
      · have finished := finishSpelling_correct raw canon index context middle middleSound
          (primary_in_view (primary.2.2 index rfl))
        exact ⟨finished.1, finished.2.1.trans frame, Retains.trans keeps finished.2.2.1, finished.2.2.2⟩

theorem internCanonical_correct (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : TablesSound before) :
    TablesCorrect raw canon before (rawRun (internCanonical raw canon) context before) := by
  unfold internCanonical
  simp only [rawRun_bind, rawRun_get]
  by_cases mode : before.p3MetaMode = true
  · simp only [mode, ↓reduceIte, rawRun_bind, rawRun_get]
    by_cases hit : before.univsIndex.contains canon = true
    · simp only [hit, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact internPrimaryCanonical_correct raw canon context before sound (.inr hit)
    · have miss : before.univsIndex.contains canon = false := Bool.eq_false_iff.mpr hit
      simp only [miss, Bool.not_false, ↓reduceIte, rawRun_bind]
      have correct := internMetaUniv_correct canon context before sound.primary sound.metadata
      have frame := internMetaUniv_frame canon context before
      have keeps := internMetaUniv_retains canon context before sound.primary sound.metadata
      cases ran : rawRun (internMetaUniv canon) context before with
      | mk outcome middle =>
        rw [ran] at correct frame keeps
        have middleSound : TablesSound middle := ⟨correct.1, correct.2.1⟩
        cases outcome with
        | error error => exact ⟨middleSound, frame, keeps, by intro value bad; cases bad⟩
        | ok index =>
          have modeAfter := congrArg BlockState.p3MetaMode frame
          change middle.p3MetaMode = before.p3MetaMode at modeAfter
          have located : (univTable middle)[index.toNat]? = some canon := by
            simpa only [univTable, modeAfter, mode, ↓reduceIte] using correct.2.2.2 index rfl
          have finished := finishSpelling_correct raw canon index context middle middleSound located
          exact ⟨finished.1, finished.2.1.trans frame, Retains.trans keeps finished.2.2.1, finished.2.2.2⟩
  · simp only [mode]
    exact internPrimaryCanonical_correct raw canon context before sound (.inl (Bool.eq_false_iff.mpr mode))

structure Sound (state : BlockState) : Prop where
  rawCache : UniverseMeaning.CacheSound state
  canonCache : CanonCacheExact state
  tables : TablesSound state

/-- The source relation carried through the entire production universe
operation, including optional original-spelling metadata. -/
def SourceInterned (params : List Ix.Name) (source : Ix.Level) (state : BlockState)
    (result : UInt64 × Option UInt64) : Prop :=
  ∃ raw, UniverseMeaning.Represents params source raw ∧ Interned raw (Ixon.canonUniv raw) state result

theorem compileAndInternUnivCanon_correct (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) :
    let result := rawRun (compileAndInternUnivCanon source) context before
    Sound result.2 ∧ Retains (univTable before) (univTable result.2) ∧
      ∀ value, result.1 = .ok value → SourceInterned context.2.univCtx source result.2 value := by
  rw [compileAndInternUnivCanon_eq, rawRun_bind]
  have compiled := UniverseMeaning.compileUniv_correct source context before valid.rawCache
  have rawFrame := compileUniv_frame source context before
  cases rawRan : rawRun (compileUniv source) context before with
  | mk outcome middle =>
    rw [rawRan] at compiled rawFrame
    have sameCanon := congrArg CanonCacheExact rawFrame
    have sameTables := congrArg TablesSound rawFrame
    have sameView : univTable middle = univTable before := by
      have same := congrArg univTable rawFrame
      exact same
    have middleSound : Sound middle := ⟨compiled.1, sameCanon.mpr valid.canonCache, sameTables.mpr valid.tables⟩
    cases outcome with
    | error error =>
      refine ⟨middleSound, ?_, by intro value bad; cases bad⟩
      rw [sameView]
      exact .refl _
    | ok raw =>
      obtain ⟨canonicalState, canonRan, canonSound, canonFrame⟩ :=
        canonUnivCached_correct raw context middle middleSound.canonCache
      have canonicalRaw : UniverseMeaning.CacheSound canonicalState := by
        have same := congrArg UniverseMeaning.CacheSound canonFrame
        exact same.mpr middleSound.rawCache
      have canonicalTables : TablesSound canonicalState := by
        have same := congrArg TablesSound canonFrame
        exact same.mpr middleSound.tables
      have canonicalView : univTable canonicalState = univTable before := by
        have same := congrArg univTable canonFrame
        exact same.trans sameView
      dsimp only
      rw [rawRun_bind, canonRan]
      have tail := internCanonical_correct raw (Ixon.canonUniv raw) context canonicalState canonicalTables
      refine ⟨⟨?_, ?_, tail.1⟩, ?_, ?_⟩
      · have same := congrArg UniverseMeaning.CacheSound tail.2.1
        exact same.mpr canonicalRaw
      · have same := congrArg CanonCacheExact tail.2.1
        exact same.mpr canonSound
      · rw [← canonicalView]
        exact tail.2.2.1
      · intro value success
        exact ⟨raw, compiled.2 raw rfl, tail.2.2.2 value success⟩

theorem blockReader_level (context : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name) (state : BlockState)
    {index : UInt64} {univ : Ixon.Univ} (found : (univTable state)[index.toNat]? = some univ) :
    (ExpressionRead.blockReader context base param self state).ecx.level index =
      .ok (Kernel.Reader.convUniv param univ) := by
  change (match ((univTable state).map (Kernel.Reader.convUniv param))[index.toNat]? with
    | some level => pure level
    | none => Kernel.Reader.malformed "universe table index is out of bounds") = _
  rw [Array.getElem?_map, found]
  rfl

/-- The actual certified reader returns a scoped level whose value agrees
with the source. Both ordinary and metadata mode use the same conclusion. -/
theorem compileAndInternUnivCanon_read (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) {value : UInt64 × Option UInt64} {after : BlockState}
    (ran : rawRun (compileAndInternUnivCanon source) context before = (.ok value, after))
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length) :
    ∃ level,
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx.level value.1 = .ok level ∧
      Kernel.Level.allParamsDefined params level = true ∧
      ∀ (φ : Lean.Name → Nat) (ψ : Kernel.Name → Nat),
        (∀ index name, context.2.univCtx[index]? = some name → index < UInt64.size →
          φ (ixName name) = ψ (Kernel.Reader.paramOf params index)) →
        ixLevelEval φ source = some (Kernel.Level.Geran.levelEval ψ level) := by
  have correct := compileAndInternUnivCanon_correct source context before valid
  rw [ran] at correct
  obtain ⟨raw, represented, interned⟩ := correct.2.2 value rfl
  refine ⟨Kernel.Reader.convUniv (Kernel.Reader.paramOf params) (Ixon.canonUniv raw),
    blockReader_level reader base _ self after interned.canonical, ?_, ?_⟩
  · exact CanonUnivScope.convCanon_defined raw params (by
      rw [arity]
      exact CanonUnivScope.represents_bounded represented)
  · intro φ ψ aligned
    rw [CanonUnivScope.convUniv_eval, CanonUnivEmit.canonUniv_eval]
    apply represented.eval
    intro index name found bound
    rw [UInt64.toNat_ofNat_of_lt' bound]
    exact aligned index name found bound

/-- A metadata insertion needs a representable combined slot. Sound cached
slots lie below the existing extension size, so hits need no stronger bound. -/
theorem internMetaUniv_returns (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (sound : MetaUnivIndexSound before) (room : before.univs.size + before.metaUnivs.size < UInt64.size) :
    ∃ index after, rawRun (internMetaUniv univ) context before = (.ok index, after) ∧
      after.univs.size + after.metaUnivs.size ≤ before.univs.size + before.metaUnivs.size + 1 := by
  cases found : before.metaUnivsIndex.get? univ with
  | some slot =>
    have inside := (Array.getElem?_eq_some_iff.mp (sound univ slot found)).1
    have fits : before.univs.size + slot.toNat < UInt64.size := by omega
    rw [internMetaUniv_hit univ context before found]
    simp only [checkedTableIndex, fits, ↓reduceIte, rawRun_pure]
    exact ⟨_, before, rfl, by omega⟩
  | none =>
    rw [internMetaUniv_miss univ context before found]
    simp only [checkedTableIndex, room, ↓reduceIte, rawRun_pure]
    exact ⟨_, _, rfl, by simp only [Array.size_push]; omega⟩

theorem internUniv_returns (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (room : before.univs.size + 1 < UInt64.size) :
    ∃ index after, rawRun (internUniv univ) context before = (.ok index, after) ∧
      after.univs.size + after.metaUnivs.size ≤ before.univs.size + before.metaUnivs.size + 1 := by
  cases found : before.univsIndex.get? univ with
  | some index =>
    rw [internUniv_hit univ context before found]
    exact ⟨index, before, rfl, by omega⟩
  | none =>
    rw [internUniv_miss univ context before found, ite_eq_left room]
    exact ⟨_, _, rfl, by simp only [Array.size_push]; omega⟩

theorem finishSpelling_returns (raw canon : Ixon.Univ) (index : UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) (sound : MetaUnivIndexSound before)
    (room : before.univs.size + before.metaUnivs.size < UInt64.size) :
    ∃ value after, rawRun (finishSpelling raw canon index) context before = (.ok value, after) := by
  unfold finishSpelling
  split
  · exact ⟨_, before, rfl⟩
  · obtain ⟨patch, after, ran, _⟩ := internMetaUniv_returns raw context before sound room
    rw [rawRun_bind, ran]
    exact ⟨_, after, rfl⟩

theorem internPrimaryCanonical_returns (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : TablesSound before)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : before.univsFinal = false ∨ before.univsIndex.contains canon = true) :
    ∃ value after, rawRun (internPrimaryCanonical raw canon) context before = (.ok value, after) := by
  obtain ⟨index, middle, ran, sizeBound⟩ := internUniv_returns canon context before (by omega)
  have metadata := internUniv_metadata canon context before
  rw [ran] at metadata
  have middleSound : MetaUnivIndexSound middle := by
    intro univ index found
    rw [metadata.2] at found
    rw [metadata.1]
    exact sound.metadata univ index found
  have frame := internUniv_frame canon context before
  rw [ran] at frame
  have tripwire : (middle.univsFinal && middle.univs.size != before.univs.size) = false := by
    rcases seeded with unfinished | hit
    · have finalFlag := congrArg BlockState.univsFinal frame
      change middle.univsFinal = before.univsFinal at finalFlag
      simp only [finalFlag, unfinished, Bool.false_and]
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at hit
      change (before.univsIndex.get? canon).isSome = true at hit
      cases found : before.univsIndex.get? canon with
      | none => rw [found] at hit; cases hit
      | some slot =>
        rw [internUniv_hit canon context before found] at ran
        have same : before = middle := (Prod.mk.inj ran).2
        subst middle
        simp only [bne_self_eq_false, Bool.and_false]
  unfold internPrimaryCanonical
  simp only [rawRun_bind, rawRun_get, ran, tripwire, Bool.false_eq_true, ↓reduceIte]
  exact finishSpelling_returns raw canon index context middle middleSound (by omega)

theorem internCanonical_returns (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : TablesSound before)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : before.univsFinal = true → before.p3MetaMode = false → before.univsIndex.contains canon = true) :
    ∃ value after, rawRun (internCanonical raw canon) context before = (.ok value, after) := by
  unfold internCanonical
  simp only [rawRun_bind, rawRun_get]
  by_cases mode : before.p3MetaMode = true
  · simp only [mode, ↓reduceIte, rawRun_bind, rawRun_get]
    by_cases hit : before.univsIndex.contains canon = true
    · simp only [hit, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact internPrimaryCanonical_returns raw canon context before sound room (.inr hit)
    · have miss : before.univsIndex.contains canon = false := Bool.eq_false_iff.mpr hit
      simp only [miss, Bool.not_false, ↓reduceIte, rawRun_bind]
      obtain ⟨index, middle, ran, sizeBound⟩ := internMetaUniv_returns canon context before sound.metadata (by omega)
      rw [ran]
      have correct := internMetaUniv_correct canon context before sound.primary sound.metadata
      rw [ran] at correct
      exact finishSpelling_returns raw canon index context middle correct.2.1 (by omega)
  · simp only [mode]
    apply internPrimaryCanonical_returns raw canon context before sound room
    cases finalFlag : before.univsFinal with
    | false => exact .inl rfl
    | true => exact .inr (seeded finalFlag (Bool.eq_false_iff.mpr mode))

/-- The primary preseed obligation is a table property over the independent
source representation relation. It is not defined by compiler success. -/
def Preseeded (params : List Ix.Name) (source : Ix.Level) (state : BlockState) : Prop :=
  state.univsFinal = true → state.p3MetaMode = false →
    ∀ raw, UniverseMeaning.Represents params source raw → state.univsIndex.contains (Ixon.canonUniv raw) = true

theorem compileAndInternUnivCanon_returns (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : UniverseMeaning.Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : Preseeded context.2.univCtx source before) :
    ∃ value after, rawRun (compileAndInternUnivCanon source) context before = (.ok value, after) := by
  obtain ⟨raw, middle, compiled, _, represented⟩ :=
    UniverseMeaning.compileUniv_total_correct source context bounded scope before valid.rawCache
  have rawFrame := compileUniv_frame source context before
  rw [compiled] at rawFrame
  have middleCanon := congrArg CanonCacheExact rawFrame
  obtain ⟨canonicalState, canonical, _, canonFrame⟩ :=
    canonUnivCached_correct raw context middle (middleCanon.mpr valid.canonCache)
  have sameTablesRaw := congrArg TablesSound rawFrame
  have sameTablesCanon := congrArg TablesSound canonFrame
  have tables : TablesSound canonicalState := sameTablesCanon.mpr (sameTablesRaw.mpr valid.tables)
  have sameSizesRaw := congrArg (fun state => state.univs.size + state.metaUnivs.size) rawFrame
  have sameSizesCanon := congrArg (fun state => state.univs.size + state.metaUnivs.size) canonFrame
  have sameSizes : canonicalState.univs.size + canonicalState.metaUnivs.size =
      before.univs.size + before.metaUnivs.size := sameSizesCanon.trans sameSizesRaw
  have sameSeededRaw := congrArg (Preseeded context.2.univCtx source) rawFrame
  have sameSeededCanon := congrArg (Preseeded context.2.univCtx source) canonFrame
  have prepared : Preseeded context.2.univCtx source canonicalState := sameSeededCanon.mpr (sameSeededRaw.mpr seeded)
  obtain ⟨value, after, interned⟩ := internCanonical_returns raw (Ixon.canonUniv raw) context canonicalState tables
    (by omega) (fun finalFlag mode => prepared finalFlag mode raw represented)
  refine ⟨value, after, ?_⟩
  rw [compileAndInternUnivCanon_eq, rawRun_bind, compiled]
  dsimp only
  rw [rawRun_bind, canonical]
  exact interned

theorem sound_empty (state : BlockState) : Sound
    { state with
      univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
      metaUnivs := #[], metaUnivsIndex := {} } := by
  constructor
  · intro key value found; simp at found
  · intro key value found; simp at found
  · exact ⟨IndexSound.empty, IndexSound.empty⟩

/-- Scope, capacity and source preseed coverage suffice for the full
production operation to succeed and for its actual reader result to preserve
the source value. No successful-compilation premise occurs in this theorem. -/
theorem compileAndInternUnivCanon_total_read (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : UniverseMeaning.Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : Preseeded context.2.univCtx source before)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length) :
    ∃ value after level,
      rawRun (compileAndInternUnivCanon source) context before = (.ok value, after) ∧ Sound after ∧
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx.level value.1 = .ok level ∧
      Kernel.Level.allParamsDefined params level = true ∧
      ∀ (φ : Lean.Name → Nat) (ψ : Kernel.Name → Nat),
        (∀ index name, context.2.univCtx[index]? = some name → index < UInt64.size →
          φ (ixName name) = ψ (Kernel.Reader.paramOf params index)) →
        ixLevelEval φ source = some (Kernel.Level.Geran.levelEval ψ level) := by
  obtain ⟨value, after, ran⟩ := compileAndInternUnivCanon_returns source context before valid bounded scope room seeded
  obtain ⟨level, read, defined, eval⟩ := compileAndInternUnivCanon_read source context before valid ran
    reader base self params arity
  have correct := compileAndInternUnivCanon_correct source context before valid
  rw [ran] at correct
  exact ⟨value, after, level, ran, correct.1, read, defined, eval⟩

/-- Empty initialization discharges both memo invariants, both table-index
invariants, preseed coverage and table capacity. The remaining hypotheses
refer only to the source's parameter scope and its logical reader bindings. -/
theorem compileAndInternUnivCanon_empty_read (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : UniverseMeaning.Scoped context.2.univCtx source)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length) :
    ∃ value after level,
      rawRun (compileAndInternUnivCanon source) context
        { before with
          univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
          metaUnivs := #[], metaUnivsIndex := {}, univsFinal := false } = (.ok value, after) ∧ Sound after ∧
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx.level value.1 = .ok level ∧
      Kernel.Level.allParamsDefined params level = true ∧
      ∀ (φ : Lean.Name → Nat) (ψ : Kernel.Name → Nat),
        (∀ index name, context.2.univCtx[index]? = some name → index < UInt64.size →
          φ (ixName name) = ψ (Kernel.Reader.paramOf params index)) →
        ixLevelEval φ source = some (Kernel.Level.Geran.levelEval ψ level) :=
  compileAndInternUnivCanon_total_read source context
    { before with
      univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
      metaUnivs := #[], metaUnivsIndex := {}, univsFinal := false }
    (sound_empty { before with univsFinal := false }) bounded scope (by change 1 < UInt64.size; decide)
    (by intro bad; cases bad) reader base self params arity

end Ix.CompileCert.UniversePipeline

