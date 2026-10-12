import Ix.CompileCert.UniversePipeline
import Ix.CompileCert.ExpressionCacheRun

/-! Production expression leaves interpreted by the certified reader.
Fresh sort and bound-variable occurrences compile and preserve source meaning
under explicit scope, capacity and preseed conditions. Universe operations
preserve earlier expression readings and cache validity, including error
states. The cached sort rule composes with a caller's full source relation;
the remaining constructors and whole-expression induction are separate. -/

namespace Ix.CompileCert.ExpressionLeaves

open Ix.CompileM Ix.CompileCert.HeadWriterFrame Ix.CompileCert.UniversePipeline

/-- Metadata allocation and spelling patches are not certified reader inputs. -/
def withoutExprMetadata (state : BlockState) : BlockState :=
  { state with arena := {}, univPatches := #[] }

def finishSort (index : UInt64) (patch : Option UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode .leaf
  if let some original := patch then pushUnivPatch root #[original]
  pure (.sort index, root)

theorem sort_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (level : Ix.Level) (hash : Address) :
    compileExprTotalStep compile (.sort level hash) = (do
      let (index, patch) ← compileAndInternUnivCanon level
      finishSort index patch) := rfl

theorem finishSort_returns (index : UInt64) (patch : Option UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ root after, rawRun (finishSort index patch) context before = (.ok (.sort index, root), after) ∧
      withoutExprMetadata after = withoutExprMetadata before := by
  unfold finishSort allocArenaNode
  simp only [rawRun_bind, Interning.rawRun_modifyGet]
  cases patch with
  | none => exact ⟨_, _, rfl, rfl⟩
  | some original =>
    simp only [pushUnivPatch, rawRun_bind, rawRun_modify, rawRun_pure]
    exact ⟨_, _, rfl, rfl⟩

theorem withoutExprMetadata_reader (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
    {before after : BlockState} (frame : withoutExprMetadata after = withoutExprMetadata before) :
    ExpressionRead.blockReader reader base param self after =
      ExpressionRead.blockReader reader base param self before := by
  have same := congrArg (ExpressionRead.blockReader reader base param self) frame
  exact same

theorem withoutExprMetadata_sound {before after : BlockState}
    (frame : withoutExprMetadata after = withoutExprMetadata before) (sound : Sound before) : Sound after := by
  constructor
  · have same := congrArg UniverseMeaning.CacheSound frame
    exact same.mpr sound.rawCache
  · have same := congrArg CanonCacheExact frame
    exact same.mpr sound.canonCache
  · have same := congrArg TablesSound frame
    exact same.mpr sound.tables

/-- Meaning of a source level under its positional logical parameter map.
The relation excludes external name metadata and preserves every aligned
valuation, not one chosen test assignment. -/
def LevelMeaning (sourceParams : List Ix.Name) (params : List Kernel.Name)
    (source : Ix.Level) (level : Kernel.Level) : Prop :=
  Kernel.Level.allParamsDefined params level = true ∧
    ∀ (φ : Lean.Name → Nat) (ψ : Kernel.Name → Nat),
      (∀ index name, sourceParams[index]? = some name → index < UInt64.size →
        φ (ixName name) = ψ (Kernel.Reader.paramOf params index)) →
      ixLevelEval φ source = some (Kernel.Level.Geran.levelEval ψ level)

theorem sort_step_total_read (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (source : Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : UniverseMeaning.Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : Preseeded context.2.univCtx source before)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length) :
    ∃ value after level,
      rawRun (compileExprTotalStep compile (.sort source hash)) context before = (.ok value, after) ∧
      Sound after ∧
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).read value.1 = .ok (.sort level) ∧
      LevelMeaning context.2.univCtx params source level := by
  obtain ⟨⟨index, patch⟩, middle, level, compiled, middleSound, read, meaning⟩ :=
    compileAndInternUnivCanon_total_read source context before valid bounded scope room seeded reader base self params arity
  obtain ⟨root, after, finished, frame⟩ := finishSort_returns index patch context middle
  refine ⟨(.sort index, root), after, level, ?_, withoutExprMetadata_sound frame middleSound, ?_, meaning⟩
  · rw [sort_step_eq, rawRun_bind, compiled]
    exact finished
  · rw [withoutExprMetadata_reader reader base _ self frame]
    change (do pure (Kernel.Expr.sort (← (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self middle).ecx.level index))) = _
    rw [read]
    rfl

/-- Anonymous bound-variable emission is exact whenever its source index is
representable. The arena allocation is irrelevant to the certified reading. -/
theorem bvar_step_total_read (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (index : Nat) (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (bounded : index < UInt64.size) (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name) :
    ∃ value after,
      rawRun (compileExprTotalStep compile (.bvar index hash)) context before = (.ok value, after) ∧
      (ExpressionRead.blockReader reader base param self after).read value.1 = .ok (.bvar index) ∧
      withoutExprMetadata after = withoutExprMetadata before := by
  refine ⟨(.var index.toUInt64, before.arena.nodes.size.toUInt64),
    { before with arena := { nodes := before.arena.nodes.push .leaf } }, rfl, ?_, rfl⟩
  change (.ok (Kernel.Expr.mkBvar index.toUInt64.toNat) : Kernel.Reader.ReadM Kernel.Expr) = _
  rw [UInt64.toNat_ofNat_of_lt' bounded, Kernel.Expr.mkBvar_eq]

/-- The actual universe operation changes only these memos and tables. -/
def withoutUniverseWrites (state : BlockState) : BlockState :=
  { state with
    univCache := {}, canonUnivCache := {}, univs := #[], univsIndex := {},
    metaUnivs := #[], metaUnivsIndex := {} }

theorem compileUniv_frame (source : Ix.Level) : Preserves withoutUniverseWrites (compileUniv source) := by
  intro context before
  have frame := congrArg withoutUniverseWrites (UniversePipeline.compileUniv_frame source context before)
  exact frame

theorem canonUnivCached_frame (source : Ixon.Univ) : Preserves withoutUniverseWrites (canonUnivCached source) := by
  intro context before
  rw [canonUnivCached_run]
  cases before.canonUnivCache.get? source <;> rfl

theorem internUniv_frame (source : Ixon.Univ) : Preserves withoutUniverseWrites (internUniv source) := by
  intro context before
  have frame := congrArg withoutUniverseWrites (UniversePipeline.internUniv_frame source context before)
  exact frame

theorem internMetaUniv_frame (source : Ixon.Univ) : Preserves withoutUniverseWrites (internMetaUniv source) := by
  intro context before
  have frame := congrArg withoutUniverseWrites (UniversePipeline.internMetaUniv_frame source context before)
  exact frame

theorem compileAndInternUnivCanon_frame (source : Ix.Level) :
    Preserves withoutUniverseWrites (compileAndInternUnivCanon source) := by
  unfold compileAndInternUnivCanon
  with_reducible repeat' first
    | exact Preserves.pure withoutUniverseWrites _
    | exact Preserves.throw withoutUniverseWrites _
    | exact Preserves.get withoutUniverseWrites
    | exact compileUniv_frame _
    | exact canonUnivCached_frame _
    | exact internUniv_frame _
    | exact internMetaUniv_frame _
    | refine Preserves.bind ?_ (fun _ => ?_)
    | dsimp only
    | split

theorem compileAndInternUnivCanon_reading (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader base param self before).ecx
      (ExpressionRead.blockReader reader base param self (rawRun (compileAndInternUnivCanon source) context before).2).ecx := by
  have frame := compileAndInternUnivCanon_frame source context before
  have sameRefs := congrArg Interning.refTable frame
  have sameBlobs := congrArg BlockState.blockBlobs frame
  apply Interning.blockReader_growth reader base param self
  · change Interning.refTable (rawRun (compileAndInternUnivCanon source) context before).2 =
      Interning.refTable before at sameRefs
    rw [sameRefs]
    exact .refl _
  · exact (compileAndInternUnivCanon_correct source context before valid).2.1
  · exact sameBlobs

theorem compileAndInternUnivCanon_cache (source : Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
    (related : Ix.Expr → Kernel.Expr → Prop)
    (cache : ExpressionCacheRun.Valid
      (ExpressionRead.Reading related (ExpressionRead.blockReader reader base param self)) before) :
    ExpressionCacheRun.Valid (ExpressionRead.Reading related (ExpressionRead.blockReader reader base param self))
      (rawRun (compileAndInternUnivCanon source) context before).2 := by
  apply ExpressionRead.cache_sound_of_growth
    (compileAndInternUnivCanon_reading source context before valid reader base param self)
  · intro index value found
    change (#[] : Array (Kernel.Reader.ReadM Kernel.Expr))[index]? = some (.ok value) at found
    simp at found
  · have frame := congrArg BlockState.exprCache (compileAndInternUnivCanon_frame source context before)
    exact frame
  · exact cache

theorem sort_step_correct (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (source : Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length)
    (related : Ix.Expr → Kernel.Expr → Prop)
    (sortRelated : ∀ level, LevelMeaning context.2.univCtx params source level → related (.sort source hash) (.sort level))
    (cache : ExpressionCacheRun.Valid
      (ExpressionRead.Reading related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self)) before) :
    let result := rawRun (compileExprTotalStep compile (.sort source hash)) context before
    Sound result.2 ∧ ExpressionCacheRun.CorrectResult
      (ExpressionRead.Reading related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self))
      (.sort source hash) result := by
  have univCorrect := compileAndInternUnivCanon_correct source context before valid
  have cacheAfter := compileAndInternUnivCanon_cache source context before valid reader base
    (Kernel.Reader.paramOf params) self related cache
  rw [sort_step_eq, rawRun_bind]
  cases ran : rawRun (compileAndInternUnivCanon source) context before with
  | mk outcome middle =>
    rw [ran] at univCorrect cacheAfter
    cases outcome with
    | error error => exact ⟨univCorrect.1, cacheAfter, by intro value bad; cases bad⟩
    | ok value =>
      obtain ⟨level, read, meaning⟩ := compileAndInternUnivCanon_read source context before valid ran reader base self params arity
      obtain ⟨root, after, finished, frame⟩ := finishSort_returns value.1 value.2 context middle
      dsimp only
      rw [finished]
      have sameReader := withoutExprMetadata_reader reader base (Kernel.Reader.paramOf params) self frame
      have sameCache := congrArg BlockState.exprCache frame
      change after.exprCache = middle.exprCache at sameCache
      refine ⟨withoutExprMetadata_sound frame univCorrect.1, ?_, ?_⟩
      · intro expr result found
        rw [sameCache] at found
        obtain ⟨target, relatedTarget, reading⟩ := cacheAfter expr result found
        exact ⟨target, relatedTarget, by rw [sameReader]; exact reading⟩
      · intro result success
        cases Except.ok.inj success
        refine ⟨.sort level, sortRelated level meaning, ?_⟩
        rw [sameReader]
        change (do pure (Kernel.Expr.sort (← (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self middle).ecx.level value.1))) = _
        rw [read]
        rfl

theorem sort_cached_correct (source : Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length)
    (related : Ix.Expr → Kernel.Expr → Prop)
    (sortRelated : ∀ level, LevelMeaning context.2.univCtx params source level → related (.sort source hash) (.sort level))
    (cache : ExpressionCacheRun.Valid
      (ExpressionRead.Reading related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self)) before) :
    ExpressionCacheRun.CorrectResult
      (ExpressionRead.Reading related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self))
      (.sort source hash) (rawRun (compileExprPartial (.sort source hash)) context before) :=
  ExpressionCacheRun.partial_run_correct _
    (ExpressionRead.reading_cache_blind related reader base (Kernel.Reader.paramOf params) self)
    (.sort source hash) context before cache (fun _ =>
      (sort_step_correct compileExprPartial source hash context before valid reader base self params arity related sortRelated cache).2)

/-- Exact cache-miss completion for the actual direct compiler. -/
theorem partial_miss_run (source : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (missing : before.exprCache.get? source = none) {value : Ixon.Expr × UInt64} {after : BlockState}
    (step : rawRun (compileExprTotalStep compileExprPartial source) context before = (.ok value, after)) :
    rawRun (compileExprPartial source) context before =
      (.ok value, { after with exprCache := after.exprCache.insert source value }) := by
  rw [ExpressionRuntime.partial_unfold]
  simp only [ExpressionRuntime.cached, rawRun_bind, rawRun_get, missing, step]
  cases value
  rfl

theorem sound_exprCache (state : BlockState) (cache) (valid : Sound state) :
    Sound { state with exprCache := cache } := ⟨valid.rawCache, valid.canonCache, valid.tables⟩

/-- A fresh sort occurrence is compiled by the actual cached expression
entry point and read by the certified reader. There is no compiler-success
premise or assumed whole-expression semantic relation. -/
theorem sort_miss_total_read (source : Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : Sound before) (missing : before.exprCache.get? (Ix.Expr.sort source hash) = none)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : UniverseMeaning.Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : Preseeded context.2.univCtx source before)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (params : List Kernel.Name) (arity : params.length = context.2.univCtx.length) :
    ∃ value after level,
      rawRun (compileExprPartial (.sort source hash)) context before = (.ok value, after) ∧ Sound after ∧
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).read value.1 = .ok (.sort level) ∧
      LevelMeaning context.2.univCtx params source level := by
  obtain ⟨value, middle, level, step, middleSound, read, meaning⟩ :=
    sort_step_total_read compileExprPartial source hash context before valid bounded scope room seeded reader base self params arity
  exact ⟨value, { middle with exprCache := middle.exprCache.insert (Ix.Expr.sort source hash) value }, level,
    partial_miss_run _ context before missing step, sound_exprCache middle _ middleSound, read, meaning⟩

theorem bvar_miss_total_read (index : Nat) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (missing : before.exprCache.get? (Ix.Expr.bvar index hash) = none) (bounded : index < UInt64.size)
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name) :
    ∃ value after,
      rawRun (compileExprPartial (.bvar index hash)) context before = (.ok value, after) ∧
      (ExpressionRead.blockReader reader base param self after).read value.1 = .ok (.bvar index) := by
  obtain ⟨value, middle, step, read, _⟩ :=
    bvar_step_total_read compileExprPartial index hash context before bounded reader base param self
  exact ⟨value, { middle with exprCache := middle.exprCache.insert (Ix.Expr.bvar index hash) value },
    partial_miss_run _ context before missing step, read⟩

end Ix.CompileCert.ExpressionLeaves

