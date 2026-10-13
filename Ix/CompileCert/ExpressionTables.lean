import Ix.CompileCert.ExpressionState

/-! Actual reference and universe table operations preserve reader meaning,
cache validity and fixed declaration-prefix bindings, including error states. -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.CompileCert.ExpressionCacheRun (Meaning Valid)

section Constructors

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
  (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
  (related : Ix.Expr → Kernel.Expr → Prop) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx base param self
local notation "meaning" => ExpressionRead.Reading related reader

def Good (state : BlockState) : Prop := StateSound bindings state ∧ Valid meaning state

def Checked (source : Ix.Expr) (before : BlockState)
    (result : Except CompileError (Ixon.Expr × UInt64) × BlockState) : Prop :=
  Good cx base param self related bindings result.2 ∧
    ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
    ∀ value, result.1 = .ok value → meaning result.2 source value

theorem good_metadata {before after : BlockState}
    (frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before)
    (good : Good cx base param self related bindings before) : Good cx base param self related bindings after := by
  refine ⟨⟨ExpressionLeaves.withoutExprMetadata_sound frame good.1.1, ?_, ?_, ?_⟩, ?_⟩
  · have same := congrArg Interning.RefIndexSound frame
    exact same.mpr good.1.2.1
  · have same := congrArg Interning.MetaRefIndexSound frame
    exact same.mpr good.1.2.2.1
  · have same := congrArg bindingView frame
    exact same.trans good.1.2.2.2
  · have sameReader := ExpressionLeaves.withoutExprMetadata_reader cx base param self frame
    have sameCache := congrArg BlockState.exprCache frame
    change after.exprCache = before.exprCache at sameCache
    intro expr value found
    rw [sameCache] at found
    obtain ⟨target, rel, read⟩ := good.2 expr value found
    exact ⟨target, rel, by rw [sameReader]; exact read⟩

theorem internRef_good (address : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) :
    let result := rawRun (internRef address) context before
    Good cx base param self related bindings result.2 ∧
      ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ index, result.1 = .ok index → (Interning.refTable result.2)[index.toNat]? = some address := by
  have frame := internRef_frame address context before
  have indices := internRef_indices address context before good.1.2.1 good.1.2.2.1
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, indices.1, indices.2.1, ?_⟩,
    Interning.internRef_cache_sound address context before cx base param self related good.2⟩,
    Interning.internRef_reading address context before cx base param self, indices.2.2⟩
  · have same := congrArg UniverseMeaning.CacheSound frame
    exact same.mpr good.1.1.rawCache
  · have same := congrArg UniversePipeline.CanonCacheExact frame
    exact same.mpr good.1.1.canonCache
  · have same := congrArg UniversePipeline.TablesSound frame
    exact same.mpr good.1.1.tables
  · have same := congrArg bindingView frame
    exact same.trans good.1.2.2.2

theorem storeBlob_good (bytes : ByteArray) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    let result := rawRun (storeBlob bytes) context before
    Good cx base param self related bindings result.2 ∧
      ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ address, result.1 = .ok address → result.2.blockBlobs.get? address = some bytes := by
  have preserved := BlobWrites.storeBlob_preserves bytes context before
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    BlobWrites.cache_preserved context.1.blobs before _ preserved.1 preserved.2.1 cx base param self aligned related good.2⟩,
    BlobWrites.storeBlob_reading bytes context before cx base param self aligned, preserved.2.2⟩
  · have same := congrArg UniverseMeaning.CacheSound preserved.1
    exact same.mpr good.1.1.rawCache
  · have same := congrArg UniversePipeline.CanonCacheExact preserved.1
    exact same.mpr good.1.1.canonCache
  · have same := congrArg UniversePipeline.TablesSound preserved.1
    exact same.mpr good.1.1.tables
  · have same := congrArg Interning.RefIndexSound preserved.1
    exact same.mpr good.1.2.1
  · have same := congrArg Interning.MetaRefIndexSound preserved.1
    exact same.mpr good.1.2.2.1
  · have same := congrArg bindingView preserved.1
    exact same.trans good.1.2.2.2

theorem blockReader_blob (state : BlockState) {index : UInt64} {address : Address} {bytes : ByteArray}
    (found : (Interning.refTable state)[index.toNat]? = some address)
    (stored : state.blockBlobs.get? address = some bytes) :
    (reader state).ecx.blobAt index = .ok bytes := by
  unfold Kernel.Reader.ECx.blobAt
  change (do
    let some key := (Interning.refTable state)[index.toNat]? | Kernel.Reader.malformed "literal reference index is out of bounds"
    let some value := (state.blockBlobs.get? key).orElse (fun _ => cx.blob key)
      | Kernel.Reader.malformed s!"literal blob {key} is missing"
    pure value) = _
  rw [found]
  dsimp only
  rw [stored]
  rfl

theorem blockReader_ref (state : BlockState) {index : UInt64} {address : Address} {ref : Kernel.ConstRef Address}
    (found : (Interning.refTable state)[index.toNat]? = some address)
    (resolved : Kernel.Reader.resolve cx.store address = some ref) :
    (reader state).ecx.refAt index = .ok ref := by
  unfold Kernel.Reader.ECx.refAt
  change (do
    let some key := (Interning.refTable state)[index.toNat]? | Kernel.Reader.malformed "reference index is out of bounds"
    let some value := Kernel.Reader.resolve cx.store key | Kernel.Reader.malformed s!"reference {key} is missing or has invalid ownership"
    pure value) = _
  rw [found]
  dsimp only
  rw [resolved]
  rfl

theorem compileLevel_good (source : Ix.Level) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (params : List Kernel.Name)
    (parameterMap : param = Kernel.Reader.paramOf params) (arity : params.length = context.2.univCtx.length) :
    let result := rawRun (compileAndInternUnivCanon source) context before
    Good cx base param self related bindings result.2 ∧ ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ value, result.1 = .ok value → ∃ level,
        (reader result.2).ecx.level value.1 = .ok level ∧
        ExpressionLeaves.LevelMeaning context.2.univCtx params source level := by
  have correct := UniversePipeline.compileAndInternUnivCanon_correct source context before good.1.1
  have frame := ExpressionLeaves.compileAndInternUnivCanon_frame source context before
  refine ⟨⟨⟨correct.1, ?_, ?_, ?_⟩,
    ExpressionLeaves.compileAndInternUnivCanon_cache source context before good.1.1 cx base param self related good.2⟩,
    ExpressionLeaves.compileAndInternUnivCanon_reading source context before good.1.1 cx base param self, ?_⟩
  · have same := congrArg Interning.RefIndexSound frame
    exact same.mpr good.1.2.1
  · have same := congrArg Interning.MetaRefIndexSound frame
    exact same.mpr good.1.2.2.1
  · have same := congrArg bindingView frame
    exact same.trans good.1.2.2.2
  · intro value success
    have ran : rawRun (compileAndInternUnivCanon source) context before =
        (.ok value, (rawRun (compileAndInternUnivCanon source) context before).2) := by
      exact Prod.ext success rfl
    subst param
    exact UniversePipeline.compileAndInternUnivCanon_read source context before good.1.1 ran cx base self params arity

/-- Compiled universe arguments retain their source order and meaning. -/
def LevelsRead (sourceParams : List Ix.Name) (params : List Kernel.Name)
    (source : List Ix.Level) (values : List (UInt64 × Option UInt64)) (state : BlockState) : Prop :=
  ∃ target, List.Forall₂ (ExpressionLeaves.LevelMeaning sourceParams params) source target ∧
    ((values.map Prod.fst).mapM (reader state).ecx.level) = .ok target

theorem levels_grow {sourceParams : List Ix.Name} {params : List Kernel.Name}
    {source : List Ix.Level} {values : List (UInt64 × Option UInt64)} {before after : BlockState}
    (growth : ExpressionRead.Extends (reader before).ecx (reader after).ecx)
    (prior : LevelsRead cx base param self sourceParams params source values before) :
    LevelsRead cx base param self sourceParams params source values after := by
  obtain ⟨target, rel, read⟩ := prior
  refine ⟨target, rel, ?_⟩
  have preserved := growth.levels (values.map Prod.fst).toArray target
  simpa only [Kernel.Reader.ECx.levels, List.toList_toArray] using preserved read

theorem compileLevels_list_good (sources : List Ix.Level) (context : CompileEnv × BlockEnv)
    (params : List Kernel.Name) (parameterMap : param = Kernel.Reader.paramOf params)
    (arity : params.length = context.2.univCtx.length) :
    ∀ before, Good cx base param self related bindings before →
      let result := rawRun (sources.mapM compileAndInternUnivCanon) context before
      Good cx base param self related bindings result.2 ∧ ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
        ∀ values, result.1 = .ok values → LevelsRead cx base param self context.2.univCtx params sources values result.2 := by
  induction sources with
  | nil =>
    intro before good
    refine ⟨good, extends_refl _, ?_⟩
    intro values success
    cases Except.ok.inj success
    exact ⟨[], .nil, rfl⟩
  | cons source rest ih =>
    intro before good
    rw [List.mapM_cons, rawRun_bind]
    have head := compileLevel_good cx base param self related bindings source context before good params parameterMap arity
    cases ran : rawRun (compileAndInternUnivCanon source) context before with
    | mk outcome middle =>
      rw [ran] at head
      cases outcome with
      | error error => exact ⟨head.1, head.2.1, by intro values bad; cases bad⟩
      | ok value =>
        dsimp only
        rw [rawRun_bind]
        have tail := ih middle head.1
        cases tailRun : rawRun (rest.mapM compileAndInternUnivCanon) context middle with
        | mk outcome after =>
          rw [tailRun] at tail
          cases outcome with
          | error error => exact ⟨tail.1, extends_trans head.2.1 tail.2.1, by intro values bad; cases bad⟩
          | ok values =>
            refine ⟨tail.1, extends_trans head.2.1 tail.2.1, ?_⟩
            intro output success
            cases Except.ok.inj success
            obtain ⟨level, readLevel, levelMeaning⟩ := head.2.2 value rfl
            obtain ⟨levels, relatedLevels, readLevels⟩ := tail.2.2 values rfl
            refine ⟨level :: levels, .cons levelMeaning relatedLevels, ?_⟩
            have retained := tail.2.1.level value.1 level readLevel
            change ((value.1 :: values.map Prod.fst).mapM (reader after).ecx.level) = .ok (level :: levels)
            simp only [List.mapM_cons, retained, readLevels]
            rfl

theorem compileLevels_good (sources : Array Ix.Level) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (params : List Kernel.Name)
    (parameterMap : param = Kernel.Reader.paramOf params) (arity : params.length = context.2.univCtx.length) :
    let result := rawRun (sources.mapM compileAndInternUnivCanon) context before
    Good cx base param self related bindings result.2 ∧ ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ values, result.1 = .ok values → ∃ levels,
        List.Forall₂ (ExpressionLeaves.LevelMeaning context.2.univCtx params) sources.toList levels ∧
        (reader result.2).ecx.levels (values.map Prod.fst) = .ok levels := by
  rw [Array.mapM_eq_mapM_toList]
  have correct := compileLevels_list_good cx base param self related bindings sources.toList context params parameterMap arity before good
  simp only [map_eq_pure_bind, rawRun_bind]
  cases ran : rawRun (sources.toList.mapM compileAndInternUnivCanon) context before with
  | mk outcome after =>
    rw [ran] at correct
    cases outcome with
    | error error => exact ⟨correct.1, correct.2.1, by intro values bad; cases bad⟩
    | ok values =>
      simp only [rawRun_pure]
      refine ⟨correct.1, correct.2.1, ?_⟩
      intro output success
      cases Except.ok.inj success
      obtain ⟨levels, rel, read⟩ := correct.2.2 values rfl
      exact ⟨levels, rel, by simpa only [Kernel.Reader.ECx.levels, Array.toList_map, List.toList_toArray] using read⟩

def finishReference (name : Ix.Name) (levels : Array (UInt64 × Option UInt64)) (value : Ixon.Expr) :
    CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.ref name.getHash)
  if levels.any (·.2.isSome) then
    pushUnivPatch root (levels.map fun (canonical, original) => original.getD canonical)
  pure (value, root)

theorem finishReference_returns (name : Ix.Name) (levels : Array (UInt64 × Option UInt64)) (value : Ixon.Expr)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ root after, rawRun (finishReference name levels value) context before = (.ok (value, root), after) ∧
      ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := by
  unfold finishReference allocArenaNode
  simp only [rawRun_bind, Interning.rawRun_modifyGet]
  split
  · exact ⟨_, _, rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl⟩

theorem finishReference_checked (source : Ix.Expr) (name : Ix.Name) (levels : Array (UInt64 × Option UInt64))
    (value : Ixon.Expr) (target : Kernel.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (rel : related source target)
    (read : (reader before).read value = .ok target) :
    Checked cx base param self related bindings source before (rawRun (finishReference name levels value) context before) := by
  obtain ⟨root, after, ran, frame⟩ := finishReference_returns name levels value context before
  rw [ran]
  have same := ExpressionLeaves.withoutExprMetadata_reader cx base param self frame
  refine ⟨good_metadata cx base param self related bindings frame good, ?_, ?_⟩
  · rw [same]
    exact extends_refl _
  · intro result success
    cases Except.ok.inj success
    exact ⟨target, rel, by rw [same]; exact read⟩

def constBody (name : Ix.Name) (compiled : Array (UInt64 × Option UInt64)) (mutCtx : Ix.MutCtx) :
    CompileM (Ixon.Expr × UInt64) := do
  match mutCtx.get? name with
  | some slot =>
    let index ← checkedTableIndex "mutual reference" slot
    finishReference name compiled (.recur index (compiled.map Prod.fst))
  | none =>
    let address ← lookupConstAddr name
    let index ← internRef address
    finishReference name compiled (.ref index (compiled.map Prod.fst))

theorem compileConstExprRaw_eq (name : Ix.Name) (levels : Array Ix.Level) :
    compileConstExprRaw name levels = (do
      let mutCtx := (← getBlockEnv).mutCtx
      let compiled ← levels.mapM compileAndInternUnivCanon
      compileName name
      constBody name compiled mutCtx) := by
  unfold compileConstExprRaw
  apply congrArg (fun next : BlockEnv → CompileM (Ixon.Expr × UInt64) => getBlockEnv >>= next)
  funext block
  apply congrArg (fun next : Array (UInt64 × Option UInt64) → CompileM (Ixon.Expr × UInt64) =>
    levels.mapM compileAndInternUnivCanon >>= next)
  funext compiled
  apply congrArg (fun next : Unit → CompileM (Ixon.Expr × UInt64) => compileName name >>= next)
  funext _done
  unfold constBody
  cases block.mutCtx.get? name <;> dsimp only
  all_goals
    by_cases patches : compiled.any (·.2.isSome) = true
    · simp only [finishReference, patches, ↓reduceIte]
    · simp only [finishReference, patches, Bool.false_eq_true, ↓reduceIte, pure_bind]

theorem constBody_checked_at (name : Ix.Name) (sources : Array Ix.Level) (hash : Address)
    (compiled : Array (UInt64 × Option UInt64)) (levels : List Kernel.Level)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (names : Ix.Name → Kernel.Name → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (selfSound : ∀ index, context.2.mutCtx.get? name = some index →
      ∃ target, self index = some target ∧ names name target)
    (readLevels : (reader before).ecx.levels (compiled.map Prod.fst) = .ok levels)
    (constantRelated : ∀ target, names name target → related (.const name sources hash) (.const target levels)) :
    Checked cx base param self related bindings (.const name sources hash) before
      (rawRun (constBody name compiled context.2.mutCtx) context before) := by
  unfold constBody
  cases found : context.2.mutCtx.get? name with
  | some slot =>
    rw [rawRun_bind]
    have unchanged := Interning.checkedTableIndex_state "mutual reference" slot context before
    cases checked : rawRun (checkedTableIndex "mutual reference" slot) context before with
    | mk outcome after =>
      rw [checked] at unchanged
      dsimp only at unchanged
      subst after
      cases outcome with
      | error error => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩
      | ok index =>
        have exactIndex := (Interning.checkedTableIndex_value "mutual reference" slot context before (congrArg Prod.fst checked)).1
        obtain ⟨target, selfFound, nameRel⟩ := selfSound slot found
        apply finishReference_checked cx base param self related bindings _ name compiled _ (.const target levels) context before good
          (constantRelated target nameRel)
        change (do
          let some target := self index.toNat | Kernel.Reader.malformed "recursive reference is outside its block"
          pure (Kernel.Expr.const target (← (reader before).ecx.levels (compiled.map Prod.fst)))) = _
        rw [exactIndex, selfFound]
        dsimp only
        rw [readLevels]
        rfl
  | none =>
    rw [rawRun_bind]
    have unchanged := lookupConstAddr_state name context before
    cases looked : rawRun (lookupConstAddr name) context before with
    | mk outcome after =>
      rw [looked] at unchanged
      dsimp only at unchanged
      subst after
      cases outcome with
      | error error => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩
      | ok address =>
        obtain ⟨ref, resolved, nameRel⟩ := lookupConstAddr_correct name context before bindings good.1.2.2.2
          cx names external (congrArg Prod.fst looked)
        dsimp only
        rw [rawRun_bind]
        have interned := internRef_good cx base param self related bindings address context before good
        cases internRun : rawRun (internRef address) context before with
        | mk outcome after =>
          rw [internRun] at interned
          cases outcome with
          | error error => exact ⟨interned.1, interned.2.1, by intro value bad; cases bad⟩
          | ok index =>
            have reads := blockReader_ref cx base param self after (interned.2.2 index rfl) resolved
            have retainedLevels := interned.2.1.levels (compiled.map Prod.fst) levels readLevels
            have finished := finishReference_checked cx base param self related bindings _ name compiled
              (.ref index (compiled.map Prod.fst)) (.const (cx.nameOf ref) levels) context after interned.1
              (constantRelated _ nameRel) (by
                change (do
                  let resolvedRef ← (reader after).ecx.refAt index
                  pure (Kernel.Expr.const (cx.nameOf resolvedRef) (← (reader after).ecx.levels (compiled.map Prod.fst)))) = _
                rw [reads, retainedLevels]
                rfl)
            exact ⟨finished.1, extends_trans interned.2.1 finished.2.1, finished.2.2⟩


/-- Preserve the original whole-context API; a particular transition uses
only its queried source name's self-binding correspondence. -/
theorem constBody_checked (name : Ix.Name) (sources : Array Ix.Level) (hash : Address)
    (compiled : Array (UInt64 × Option UInt64)) (levels : List Kernel.Level)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (names : Ix.Name → Kernel.Name → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (selfSound : SelfCorrect context.2 self names)
    (readLevels : (reader before).ecx.levels (compiled.map Prod.fst) = .ok levels)
    (constantRelated : ∀ target, names name target → related (.const name sources hash) (.const target levels)) :
    Checked cx base param self related bindings (.const name sources hash) before
      (rawRun (constBody name compiled context.2.mutCtx) context before) :=
  constBody_checked_at cx base param self related bindings name sources hash compiled levels context before good
    names external (selfSound name) readLevels constantRelated

end Constructors

end Ix.CompileCert.ExpressionState
