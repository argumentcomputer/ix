import Ix.CompileCert.Interning
import Ix.CompileCert.CanonUnivCache
import Ix.CompileCert.CanonUnivScope
import Ix.CompileCert.UniverseMeaning

/-! # The universe pipeline: interning the canonical form, and reading it back

`Ix.CompileM.compileAndInternUnivCanon` compiles a level (`compileUniv`),
canonicalizes the result through the block memo (`canonUnivCached`), and
interns the canonical form into the primary universe table, together with
the original spelling, when it differs, in the current constant's extension
(`internCanonical`). This file proves the table half, everything after the
raw compile (`canonicalTail`), and then the whole operation:

* the interners keep both index invariants and every old primary slot, and a
  successful run returns the slot of the canonical form and, where the
  spelling differs, the extension slot of the raw form
  (`internCanonical_correct`);
* capacity and preseed coverage make the run succeed
  (`internCanonical_returns`, `canonicalTail_returns`);
* the certified reader reads the returned slot as the canonical universe,
  whose value under every valuation is the raw universe's
  (`canonicalTail_read`, through CT-12's `convCanon_eval`), and every earlier
  successful reading survives (`canonicalTail_reading`).

The raw compile computes the exact lowering of the source level
(`UniverseMeaning.compileUniv_exact`, which needs CQ2.8's exact memo keys),
and `compileAndInternUnivCanon_eq` composes it with the tail:

* every run keeps the universe invariants (`Sound`) and every old primary
  slot, and a successful one returns the canonical slot of the source
  level's lowering (`compileAndInternUnivCanon_correct`);
* the certified reader reads that slot as a level that means the source
  level as Source mode reads it (`LevelMeaning`, through
  `Ix.LeanIngress.ingressLevel`; `compileAndInternUnivCanon_read`);
* scope, capacity and preseed coverage make it succeed, with no success
  premise (`compileAndInternUnivCanon_total_read`), and an empty
  initialization discharges all but scope (`_empty_read`);
* it writes only the universe memos and tables
  (`compileAndInternUnivCanon_frame`), so earlier readings and the
  expression cache's meanings survive it (`_reading`, `_cache_sound`). -/

namespace Ix.CompileCert.UniversePipeline

open Ix.CompileM Ix.CompileCert Ix.CompileCert.Interning Ix.CompileCert.CanonUnivCache
open Ix.Kernel (Mode LevelParam)

/-- Forget precisely the tables universe interning changes. -/
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

/-- The spelling step of the production operation. -/
def finishSpelling (raw canon : Ixon.Univ) (index : UInt64) : CompileM (UInt64 × Option UInt64) := do
  if canon == raw then return (index, none)
  return (index, some (← internMetaUniv raw))

/-- The table-writing suffix of `compileAndInternUnivCanon`, with the
production preseeding tripwire. -/
def internCanonical (raw canon : Ixon.Univ) : CompileM (UInt64 × Option UInt64) := do
  let sizeBefore := (← getBlockState).univs.size
  let index ← internUniv canon
  if (← getBlockState).univsFinal && (← getBlockState).univs.size != sizeBefore then
    throw (.invalidMutualBlock
      s!"preseed missed canonical form {repr canon} — primary univ table \
        grew after preseeding, shifting univPatches virtual indices \
        (canonicity 10.6 V3)")
  finishSpelling raw canon index

/-- Everything after the raw compile. -/
def canonicalTail (raw : Ixon.Univ) : CompileM (UInt64 × Option UInt64) := do
  let canon ← canonUnivCached raw
  internCanonical raw canon

theorem compileAndInternUnivCanon_eq (source : Ix.Level) :
    compileAndInternUnivCanon source = (compileUniv source >>= canonicalTail) := rfl

/-- Both universe index invariants. -/
def TablesSound (state : BlockState) : Prop := UnivIndexSound state ∧ MetaUnivIndexSound state

theorem TablesSound.primary {state : BlockState} (sound : TablesSound state) : UnivIndexSound state := sound.1
theorem TablesSound.metadata {state : BlockState} (sound : TablesSound state) : MetaUnivIndexSound state :=
  sound.2

theorem tablesSound_empty (state : BlockState) :
    TablesSound { state with univs := #[], univsIndex := {}, metaUnivs := #[], metaUnivsIndex := {} } :=
  ⟨IndexSound.empty, IndexSound.empty⟩

/-- A successful result: the canonical slot, and the spelling slot where the
spelling differs. -/
structure Interned (raw canon : Ixon.Univ) (state : BlockState) (result : UInt64 × Option UInt64) : Prop where
  canonical : state.univs[result.1.toNat]? = some canon
  spelling : ∀ index, result.2 = some index → (state.univs ++ state.metaUnivs)[index.toNat]? = some raw
  unchanged : result.2 = none → canon = raw

/-- Every run keeps the index invariants, the untouched state and every old
primary slot; a successful one returns its slots. -/
def TablesCorrect (raw canon : Ixon.Univ) (before : BlockState)
    (result : Except CompileError (UInt64 × Option UInt64) × BlockState) : Prop :=
  TablesSound result.2 ∧ withoutUnivTables result.2 = withoutUnivTables before ∧
    Retains before.univs result.2.univs ∧
    ∀ value, result.1 = .ok value → Interned raw canon result.2 value

theorem finishSpelling_correct (raw canon : Ixon.Univ) (index : UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) (sound : TablesSound before)
    (located : before.univs[index.toNat]? = some canon) :
    TablesCorrect raw canon before (rawRun (finishSpelling raw canon index) context before) := by
  unfold finishSpelling
  by_cases same : canon == raw
  · simp only [same, ↓reduceIte, rawRun_pure]
    refine ⟨sound, rfl, .refl _, ?_⟩
    intro value success
    cases Except.ok.inj success
    exact ⟨located, by intros; contradiction, fun _ => beq_iff_eq.mp same⟩
  · simp only [same, Bool.false_eq_true, ↓reduceIte, rawRun_bind]
    have correct := internMetaUniv_correct raw context before sound.primary sound.metadata
    have framed := internMetaUniv_frame raw context before
    have primary := (internMetaUniv_tables raw context before).2.1
    cases ran : rawRun (internMetaUniv raw) context before with
    | mk outcome after =>
      rw [ran] at correct framed primary
      have retained : Retains before.univs after.univs := by rw [primary]; exact .refl _
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

/-- **The table suffix** keeps the index invariants and every old primary
slot, and a successful run returns the canonical form's slot and the raw
spelling's extension slot. -/
theorem internCanonical_correct (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : TablesSound before) :
    TablesCorrect raw canon before (rawRun (internCanonical raw canon) context before) := by
  have primary := internUniv_correct canon context before sound.primary
  have frame := internUniv_frame canon context before
  have tables := internUniv_tables canon context before
  unfold internCanonical
  simp only [rawRun_bind, rawRun_get]
  cases ran : rawRun (internUniv canon) context before with
  | mk outcome middle =>
    rw [ran] at primary frame tables
    have middleSound : TablesSound middle := ⟨primary.1, by
      intro univ index found
      rw [tables.2.2.2.2] at found
      rw [tables.2.2.2.1]
      exact sound.metadata univ index found⟩
    cases outcome with
    | error error => exact ⟨middleSound, frame, primary.2.1, by intro value bad; cases bad⟩
    | ok index =>
      dsimp only
      split
      · exact ⟨middleSound, frame, primary.2.1, by intro value bad; cases bad⟩
      · have finished := finishSpelling_correct raw canon index context middle middleSound
          (primary.2.2 index rfl)
        exact ⟨finished.1, finished.2.1.trans frame, Retains.trans primary.2.1 finished.2.2.1,
          finished.2.2.2⟩

/-! ## Success -/

/-- A spelling insertion needs a representable combined slot. Sound cached
slots lie below the extension's size, so hits need no stronger bound. -/
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

/-- Capacity and preseed coverage (the primary table is not yet final, or
already holds the canonical form) make the table suffix succeed. -/
theorem internCanonical_returns (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : TablesSound before)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : before.univsFinal = false ∨ before.univsIndex.contains canon = true) :
    ∃ value after, rawRun (internCanonical raw canon) context before = (.ok value, after) := by
  obtain ⟨index, middle, ran, sizeBound⟩ := internUniv_returns canon context before (by omega)
  have tables := internUniv_tables canon context before
  rw [ran] at tables
  have middleSound : MetaUnivIndexSound middle := by
    intro univ index found
    rw [tables.2.2.2.2] at found
    rw [tables.2.2.2.1]
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
  unfold internCanonical
  simp only [rawRun_bind, rawRun_get, ran, tripwire, Bool.false_eq_true, ↓reduceIte]
  exact finishSpelling_returns raw canon index context middle middleSound (by omega)

/-! ## The tail after the raw compile -/

theorem finishSpelling_frame (raw canon : Ixon.Univ) (index : UInt64) :
    Preserves withoutUnivTables (finishSpelling raw canon index) := by
  unfold finishSpelling
  split
  · exact Preserves.pure _ _
  · exact Preserves.bind (internMetaUniv_frame raw) (fun _ => Preserves.pure _ _)

/-- The table suffix writes only the universe tables, on every run. -/
theorem internCanonical_frame (raw canon : Ixon.Univ) :
    Preserves withoutUnivTables (internCanonical raw canon) := by
  unfold internCanonical
  with_reducible repeat' first
    | exact Preserves.pure _ _
    | exact Preserves.throw _ _
    | exact Preserves.get _
    | exact internUniv_frame _
    | exact finishSpelling_frame _ _ _
    | refine Preserves.bind ?_ (fun _ => ?_)
    | dsimp only
    | split

theorem canonUnivCached_frame (raw : Ixon.Univ) : Preserves withoutCanonCache (canonUnivCached raw) := by
  intro context before
  rw [canonUnivCached_run]
  cases before.canonUnivCache.get? raw <;> rfl

/-- The block state without the canonical memo and the universe tables, the
only fields the tail writes. -/
def withoutTail (state : BlockState) : BlockState := withoutUnivTables (withoutCanonCache state)

theorem canonicalTail_frame (raw : Ixon.Univ) : Preserves withoutTail (canonicalTail raw) := by
  unfold canonicalTail
  refine Preserves.bind ?_ (fun canon => ?_)
  · intro context before
    have same := congrArg withoutUnivTables (canonUnivCached_frame raw context before)
    exact same
  · intro context before
    have same := congrArg withoutCanonCache (internCanonical_frame raw canon context before)
    exact same

/-- **The tail's tables**: from an exact canonical memo and sound universe
tables, every run keeps both and every old primary slot, and a successful
run returns the slot of `canonUniv raw` and, where it differs from `raw`,
the extension slot of `raw`. -/
theorem canonicalTail_correct (raw : Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (exact : CanonCacheExact before) (sound : TablesSound before) :
    let result := rawRun (canonicalTail raw) context before
    CanonCacheExact result.2 ∧ TablesSound result.2 ∧ Retains before.univs result.2.univs ∧
      ∀ value, result.1 = .ok value → Interned raw (Ixon.canonUniv raw) result.2 value := by
  obtain ⟨middle, canonRan, canonExact, canonFrame⟩ := canonUnivCached_correct raw context before exact
  have middleSound : TablesSound middle := by
    have same := congrArg TablesSound canonFrame
    exact same.mpr sound
  have middleUnivs : middle.univs = before.univs := by
    have same := congrArg BlockState.univs canonFrame
    exact same
  have tail := internCanonical_correct raw (Ixon.canonUniv raw) context middle middleSound
  have kept := internCanonical_frame raw (Ixon.canonUniv raw) context middle
  have exactAfter : CanonCacheExact (rawRun (internCanonical raw (Ixon.canonUniv raw)) context middle).2 := by
    have same := congrArg BlockState.canonUnivCache kept
    change (rawRun (internCanonical raw (Ixon.canonUniv raw)) context middle).2.canonUnivCache =
      middle.canonUnivCache at same
    intro source value found
    rw [same] at found
    exact canonExact source value found
  have run : rawRun (canonicalTail raw) context before =
      rawRun (internCanonical raw (Ixon.canonUniv raw)) context middle := by
    unfold canonicalTail
    rw [rawRun_bind, canonRan]
  simp only [run]
  refine ⟨exactAfter, tail.1, ?_, tail.2.2.2⟩
  rw [← middleUnivs]
  exact tail.2.2.1

/-- Capacity and preseed coverage make the tail succeed. -/
theorem canonicalTail_returns (raw : Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (exact : CanonCacheExact before) (sound : TablesSound before)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : before.univsFinal = false ∨ before.univsIndex.contains (Ixon.canonUniv raw) = true) :
    ∃ value after, rawRun (canonicalTail raw) context before = (.ok value, after) := by
  obtain ⟨middle, canonRan, _, canonFrame⟩ := canonUnivCached_correct raw context before exact
  have middleSound : TablesSound middle := by
    have same := congrArg TablesSound canonFrame
    exact same.mpr sound
  have sizes : middle.univs.size + middle.metaUnivs.size = before.univs.size + before.metaUnivs.size := by
    have same := congrArg (fun state => state.univs.size + state.metaUnivs.size) canonFrame
    exact same
  have middleSeeded : middle.univsFinal = false ∨ middle.univsIndex.contains (Ixon.canonUniv raw) = true := by
    have finalFlag : middle.univsFinal = before.univsFinal := by
      have same := congrArg BlockState.univsFinal canonFrame
      exact same
    have index : middle.univsIndex = before.univsIndex := by
      have same := congrArg BlockState.univsIndex canonFrame
      exact same
    rw [finalFlag, index]
    exact seeded
  obtain ⟨value, after, ran⟩ := internCanonical_returns raw (Ixon.canonUniv raw) context middle middleSound
    (by omega) middleSeeded
  refine ⟨value, after, ?_⟩
  unfold canonicalTail
  rw [rawRun_bind, canonRan]
  exact ran

/-- **The tail reads back at the raw universe's value.** After a successful
run, the certified reader reads the returned slot as the canonical form of
`raw`, whose value under every valuation of its level parameters is the
value of `raw` itself (CT-12's `convCanon_eval`). -/
theorem canonicalTail_read {md : Mode} (raw : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (exact : CanonCacheExact before) (sound : TablesSound before)
    {value : UInt64 × Option UInt64} {after : BlockState}
    (ran : rawRun (canonicalTail raw) context before = (.ok value, after))
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) :
    CanonCacheExact after ∧ TablesSound after ∧
      (ExpressionRead.blockReader reader param self after).ecx.level value.1 =
        .ok (Kernel.Reader.convUniv param (Ixon.canonUniv raw)) ∧
      ∀ φ : LevelParam → Nat, Kernel.Level.eval φ (Kernel.Reader.convUniv param (Ixon.canonUniv raw)) =
        univEval (fun index => φ (param index.toNat)) raw := by
  have correct := canonicalTail_correct raw context before exact sound
  rw [ran] at correct
  exact ⟨correct.1, correct.2.1,
    ExpressionRead.blockReader_level reader param self after (correct.2.2.2 value rfl).canonical,
    fun φ => CanonUnivScope.convCanon_eval param φ raw⟩

/-- Every earlier successful reading of the in-flight reader survives the
tail, failing runs included. -/
theorem canonicalTail_reading {md : Mode} (raw : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (before : BlockState) (exact : CanonCacheExact before) (sound : TablesSound before)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader param self before).ecx
      (ExpressionRead.blockReader reader param self (rawRun (canonicalTail raw) compileContext before).2).ecx := by
  have correct := canonicalTail_correct raw compileContext before exact sound
  have frame := canonicalTail_frame raw compileContext before
  apply ExpressionRead.blockReader_growth_tables reader param self
  · have same := congrArg BlockState.refs frame
    change (rawRun (canonicalTail raw) compileContext before).2.refs = before.refs at same
    rw [same]
    exact Retains.refl _
  · exact correct.2.2.1
  · have same := congrArg BlockState.blockBlobs frame
    exact same

/-- The expression cache's meanings survive the tail. -/
theorem canonicalTail_cache_sound {md : Mode} (raw : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (before : BlockState) (exact : CanonCacheExact before) (sound : TablesSound before)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (source : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (valid : CacheSound
      (ExpressionRead.KeyReading source (ExpressionRead.blockReader reader param self) before)
      before.exprCache) :
    let after := (rawRun (canonicalTail raw) compileContext before).2
    CacheSound
      (ExpressionRead.KeyReading source (ExpressionRead.blockReader reader param self) after)
      after.exprCache :=
  ExpressionRead.blockReader_cache_sound
    (canonicalTail_reading raw compileContext before exact sound reader param self)
    (by have same := congrArg BlockState.exprCache (canonicalTail_frame raw compileContext before); exact same)
    valid

/-! ## The whole operation (R4: after CQ2.8's exact universe memo)

`compileAndInternUnivCanon = compileUniv >>= canonicalTail` (by `rfl`), so the
whole operation composes the raw compiler's exactness
(`UniverseMeaning.compileUniv_exact`) with the tail's tables. -/

open Ix.CompileCert.UniverseMeaning (lower UnivCacheExact Scoped)

/-- The universe invariants of a block state: the raw memo is exact, the
canonical memo is exact, both universe tables are index-sound. -/
structure Sound (state : BlockState) : Prop where
  rawCache : UnivCacheExact state
  canonCache : CanonCacheExact state
  tables : TablesSound state

/-- The fields `Sound` reads. -/
def univView (state : BlockState) :=
  (state.univCache, state.canonUnivCache, state.univs, state.univsIndex, state.metaUnivs,
    state.metaUnivsIndex)

/-- A step that leaves the universe fields alone keeps `Sound`. -/
theorem Sound.of_view {before after : BlockState} (same : univView after = univView before)
    (sound : Sound before) : Sound after := by
  simp only [univView, Prod.mk.injEq] at same
  obtain ⟨rawSame, canonSame, univsSame, indexSame, metaSame, metaIndexSame⟩ := same
  refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
  · unfold UnivCacheExact; rw [rawSame]; exact sound.rawCache
  · intro key value found; rw [canonSame] at found; exact sound.canonCache key value found
  · intro univ index found; rw [indexSame] at found; rw [univsSame]
    exact sound.tables.primary univ index found
  · intro univ index found; rw [metaIndexSame] at found; rw [metaSame]
    exact sound.tables.metadata univ index found

theorem sound_empty (state : BlockState) : Sound
    { state with
      univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
      metaUnivs := #[], metaUnivsIndex := {} } :=
  ⟨CacheSound.empty _, fun _ _ found => by simp at found, ⟨IndexSound.empty, IndexSound.empty⟩⟩

/-- **The whole operation keeps every universe invariant and every old
primary slot**, failing runs included, and a successful run returns the
slot of the canonical form of the exact lowering `raw` of the source level,
and the extension slot of `raw` where it differs. -/
theorem compileAndInternUnivCanon_correct (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) :
    let result := rawRun (compileAndInternUnivCanon source) context before
    Sound result.2 ∧ Retains before.univs result.2.univs ∧
      ∀ value, result.1 = .ok value →
        ∃ raw, lower context.2.univCtx source = some raw ∧
          Interned raw (Ixon.canonUniv raw) result.2 value := by
  rw [compileAndInternUnivCanon_eq, rawRun_bind]
  have compiled := UniverseMeaning.compileUniv_exact source context before valid.rawCache
  have rawFrame := compileUniv_frame source context before
  cases rawRan : rawRun (compileUniv source) context before with
  | mk outcome middle =>
    rw [rawRan] at compiled rawFrame
    have sameUnivs : middle.univs = before.univs := by
      have same := congrArg BlockState.univs rawFrame; exact same
    have middleSound : Sound middle := by
      refine ⟨compiled.1, ?_, ?_⟩
      · have same := congrArg CanonCacheExact rawFrame
        exact same.mpr valid.canonCache
      · have same := congrArg TablesSound rawFrame
        exact same.mpr valid.tables
    cases outcome with
    | error error =>
      refine ⟨middleSound, ?_, by intro value bad; cases bad⟩
      rw [sameUnivs]
      exact .refl _
    | ok raw =>
      dsimp only
      have tail := canonicalTail_correct raw context middle middleSound.canonCache middleSound.tables
      have tailFrame := canonicalTail_frame raw context middle
      have sameRaw : (rawRun (canonicalTail raw) context middle).2.univCache = middle.univCache :=
        by have same := congrArg BlockState.univCache tailFrame; exact same
      refine ⟨⟨?_, tail.1, tail.2.1⟩, ?_, ?_⟩
      · unfold UnivCacheExact
        rw [sameRaw]
        exact middleSound.rawCache
      · rw [← sameUnivs]
        exact tail.2.2.1
      · intro value success
        exact ⟨raw, compiled.2 raw rfl, tail.2.2.2 value success⟩

/-- What the certified reader reads at a compiled universe slot, against the
source level. Source mode reads `source` under the numbering `σ` as a level
`target`; the reader's `level` has `target`'s value under every pair of
valuations aligned at the slots `nameIndex` gives (`φ` of Source's
positions, `ψ` of the reader's level parameters `param i`). And the
reader's level mentions only parameters `param i` of the context's slots. -/
structure LevelMeaning (params : List Ix.Name) (σ : Ix.Name → LevelParam)
    (param : Nat → LevelParam) (source : Ix.Level) (level : Kernel.Level) : Prop where
  value : ∃ target, Ix.LeanIngress.ingressLevel σ source = .ok target ∧
    ∀ φ ψ : LevelParam → Nat,
      (∀ name index, Ix.Compile.ExactKey.nameIndex name params = some index →
        φ (σ name) = ψ (param index)) →
      Kernel.Level.eval φ target = Kernel.Level.eval ψ level
  defined : ∀ allowed : List LevelParam, (∀ index, index < params.length → param index ∈ allowed) →
    Kernel.Level.allParamsDefined allowed level = true

/-- The reading of the canonical form of an exact lowering means the source
level. -/
theorem levelMeaning_of_lower {params : List Ix.Name} {source : Ix.Level} {raw : Ixon.Univ}
    (lowered : lower params source = some raw) (σ : Ix.Name → LevelParam) (param : Nat → LevelParam) :
    LevelMeaning params σ param source (Kernel.Reader.convUniv param (Ixon.canonUniv raw)) := by
  obtain ⟨target, ingress, meaning⟩ := UniverseMeaning.lower_eval params σ lowered
  refine ⟨⟨target, ingress, fun φ ψ aligned => ?_⟩, fun allowed inside => ?_⟩
  · rw [CanonUnivScope.convCanon_eval]
    apply meaning φ (fun index => ψ (param index.toNat))
    intro name index found bounded
    rw [aligned name index found, UInt64.toNat_ofNat_of_lt' bounded]
  · exact CanonUnivScope.convUniv_defined (Ixon.canonUniv raw) param allowed (fun parameter occurs =>
      inside _ (UniverseMeaning.lower_occurs lowered parameter
        (CanonUnivScope.canonUniv_occurs raw parameter occurs)))

/-- **The certified reader reads the returned slot as the source level.**
After a successful run, the in-flight reader reads the canonical slot as a
level that means the source level (`LevelMeaning`), under every numbering
`σ` and every reader parameter map `param`. -/
theorem compileAndInternUnivCanon_read {md : Mode} (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) {value : UInt64 × Option UInt64} {after : BlockState}
    (ran : rawRun (compileAndInternUnivCanon source) context before = (.ok value, after))
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) (σ : Ix.Name → LevelParam) :
    Sound after ∧ ∃ level,
      (ExpressionRead.blockReader reader param self after).ecx.level value.1 = .ok level ∧
      LevelMeaning context.2.univCtx σ param source level := by
  have correct := compileAndInternUnivCanon_correct source context before valid
  rw [ran] at correct
  obtain ⟨raw, lowered, interned⟩ := correct.2.2 value rfl
  exact ⟨correct.1, _, ExpressionRead.blockReader_level reader param self after interned.canonical,
    levelMeaning_of_lower lowered σ param⟩

/-- The primary preseed obligation: once the primary table is final, it
holds the canonical form of the source level's exact lowering. A table
property over the specification, not defined by compiler success. -/
def Preseeded (params : List Ix.Name) (source : Ix.Level) (state : BlockState) : Prop :=
  state.univsFinal = true →
    ∀ raw, lower params source = some raw → state.univsIndex.contains (Ixon.canonUniv raw) = true

/-- **Scope, capacity and preseed coverage make the whole operation
succeed.** -/
theorem compileAndInternUnivCanon_returns (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : Preseeded context.2.univCtx source before) :
    ∃ value after, rawRun (compileAndInternUnivCanon source) context before = (.ok value, after) := by
  obtain ⟨raw, middle, compiled, _, lowered⟩ :=
    UniverseMeaning.compileUniv_total source context bounded scope before valid.rawCache
  have rawFrame := compileUniv_frame source context before
  rw [compiled] at rawFrame
  have middleCanon : CanonCacheExact middle := (congrArg CanonCacheExact rawFrame).mpr valid.canonCache
  have middleTables : TablesSound middle := (congrArg TablesSound rawFrame).mpr valid.tables
  have sizes : middle.univs.size + middle.metaUnivs.size = before.univs.size + before.metaUnivs.size :=
    by have same := congrArg (fun state => state.univs.size + state.metaUnivs.size) rawFrame; exact same
  have finalFlag : middle.univsFinal = before.univsFinal := by
    have same := congrArg BlockState.univsFinal rawFrame; exact same
  have sameIndex : middle.univsIndex = before.univsIndex := by
    have same := congrArg BlockState.univsIndex rawFrame; exact same
  have middleSeeded : middle.univsFinal = false ∨ middle.univsIndex.contains (Ixon.canonUniv raw) = true := by
    rw [finalFlag, sameIndex]
    cases flag : before.univsFinal with
    | false => exact .inl rfl
    | true => exact .inr (seeded flag raw lowered)
  obtain ⟨value, after, tail⟩ :=
    canonicalTail_returns raw context middle middleCanon middleTables (by omega) middleSeeded
  refine ⟨value, after, ?_⟩
  rw [compileAndInternUnivCanon_eq, rawRun_bind, compiled]
  exact tail

/-- **No success premise**: scope, capacity and preseed coverage make the
whole operation succeed, and the certified reader reads its slot as a level
that means the source level. -/
theorem compileAndInternUnivCanon_total_read {md : Mode} (source : Ix.Level)
    (context : CompileEnv × BlockEnv) (before : BlockState) (valid : Sound before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : Preseeded context.2.univCtx source before)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) (σ : Ix.Name → LevelParam) :
    ∃ value after level,
      rawRun (compileAndInternUnivCanon source) context before = (.ok value, after) ∧ Sound after ∧
      (ExpressionRead.blockReader reader param self after).ecx.level value.1 = .ok level ∧
      LevelMeaning context.2.univCtx σ param source level := by
  obtain ⟨value, after, ran⟩ :=
    compileAndInternUnivCanon_returns source context before valid bounded scope room seeded
  obtain ⟨sound, level, read, meaning⟩ :=
    compileAndInternUnivCanon_read source context before valid ran reader param self σ
  exact ⟨value, after, level, ran, sound, read, meaning⟩

/-- Empty initialization discharges both memo invariants, both index
invariants, preseed coverage and capacity: what remains is the source
level's scope under a wire-sized context. -/
theorem compileAndInternUnivCanon_empty_read {md : Mode} (source : Ix.Level)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : Scoped context.2.univCtx source)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) (σ : Ix.Name → LevelParam) :
    ∃ value after level,
      rawRun (compileAndInternUnivCanon source) context
        { before with
          univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
          metaUnivs := #[], metaUnivsIndex := {}, univsFinal := false } = (.ok value, after) ∧
      Sound after ∧
      (ExpressionRead.blockReader reader param self after).ecx.level value.1 = .ok level ∧
      LevelMeaning context.2.univCtx σ param source level :=
  compileAndInternUnivCanon_total_read source context _ (sound_empty { before with univsFinal := false })
    bounded scope (by change 1 < UInt64.size; decide) (by intro bad; cases bad) reader param self σ

/-! ## The whole operation's footprint -/

/-- Forget precisely the memos and tables the whole operation writes. -/
def withoutUniverseWrites (state : BlockState) : BlockState :=
  { state with
    univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
    metaUnivs := #[], metaUnivsIndex := {} }

/-- The whole operation writes only the universe memos and tables, on every
run. -/
theorem compileAndInternUnivCanon_frame (source : Ix.Level) :
    Preserves withoutUniverseWrites (compileAndInternUnivCanon source) := by
  rw [compileAndInternUnivCanon_eq]
  refine Preserves.bind ?_ (fun raw => ?_)
  · intro context before
    have same := congrArg withoutUniverseWrites (compileUniv_frame source context before)
    exact same
  · intro context before
    have same := congrArg withoutUniverseWrites (canonicalTail_frame raw context before)
    exact same

/-- Every earlier successful reading of the in-flight reader survives the
whole operation, failing runs included. -/
theorem compileAndInternUnivCanon_reading {md : Mode} (source : Ix.Level)
    (compileContext : CompileEnv × BlockEnv) (before : BlockState) (valid : Sound before)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader param self before).ecx
      (ExpressionRead.blockReader reader param self
        (rawRun (compileAndInternUnivCanon source) compileContext before).2).ecx := by
  have frame := compileAndInternUnivCanon_frame source compileContext before
  apply ExpressionRead.blockReader_growth_tables reader param self
  · have same : (rawRun (compileAndInternUnivCanon source) compileContext before).2.refs = before.refs :=
      by have same := congrArg BlockState.refs frame; exact same
    rw [same]
    exact Retains.refl _
  · exact (compileAndInternUnivCanon_correct source compileContext before valid).2.1
  · have same := congrArg BlockState.blockBlobs frame; exact same

/-- The expression cache's meanings survive the whole operation. -/
theorem compileAndInternUnivCanon_cache_sound {md : Mode} (source : Ix.Level)
    (compileContext : CompileEnv × BlockEnv) (before : BlockState) (valid : Sound before)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (related : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (cache : CacheSound
      (ExpressionRead.KeyReading related (ExpressionRead.blockReader reader param self) before)
      before.exprCache) :
    let after := (rawRun (compileAndInternUnivCanon source) compileContext before).2
    CacheSound
      (ExpressionRead.KeyReading related (ExpressionRead.blockReader reader param self) after)
      after.exprCache :=
  ExpressionRead.blockReader_cache_sound
    (compileAndInternUnivCanon_reading source compileContext before valid reader param self)
    (by
      have same := congrArg BlockState.exprCache
        (compileAndInternUnivCanon_frame source compileContext before)
      exact same)
    cache

end Ix.CompileCert.UniversePipeline
