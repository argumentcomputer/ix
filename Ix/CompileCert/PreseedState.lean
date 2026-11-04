import Ix.CompileCert.ExpressionCorrectness
import Ix.CompileCert.PreseedValidation

/-! # Preseeding keeps the expression invariant

`Ix.CompileM.preseedExprTables` collects the references and universes of a
block's root expressions (`collectPreseedExprs`, through the structural
collector `collectExprTablesStructural`, which compiled code runs as the
proved-equal worklist), interns them into the primary tables in canonical
sorted order, and marks the primary universe table final.

Every run of it keeps the expression compiler's invariant
`ExpressionState.Good` and extends the in-flight reader, failing runs
included (`preseed_good`): the raw universe memo stays exact, the canonical
memo exact, both index maps sound, the binding view fixed, and every
earlier reading and expression-memo meaning survives. So the expression
compiler's correctness (`ExpressionState.compileExpr_scoped`)
applies after preseeding. A successful run leaves the primary universe
table final (`preseed_final`).

`GoodStep` covers the traversal: each collector and table insertion keeps
the invariant, including the binding and expression-cache frames. -/

namespace Ix.CompileCert.PreseedState

open Ix.CompileM Ix.CompileCert Ix.CompileCert.UniversePipeline Ix.CompileCert.ExpressionState
open Ix.CompileCert.CanonUnivCache (CanonCacheExact canonUnivCached_correct)
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

section Good

variable {md : Mode} {cx : Ctx md} {param : Nat → LevelParam}
  {self : Nat → Option (ReadM (CName md))} {related : Ix.Expr → CExpr md → Prop}
  {bindings : Bindings} {compileEnv : CompileEnv}

local notation "reader" => ExpressionRead.blockReader cx param self

variable (cx param self related bindings compileEnv) in
/-- Under the compile environment `compileEnv` and any block environment,
every run of the action keeps the expression invariant and extends the
in-flight reader, failing runs included. -/
def GoodStep (action : CompileM α) : Prop :=
  ∀ (block : BlockEnv) (before : BlockState), Good cx param self related bindings before →
    Good cx param self related bindings (rawRun action (compileEnv, block) before).2 ∧
      ExpressionRead.Extends (reader before).ecx (reader (rawRun action (compileEnv, block) before).2).ecx

/-- A step that keeps the universe invariants and the reference index, keeps
the binding view, the memo and the blobs, and retains every primary slot,
keeps `Good` and extends the reader. -/
theorem good_of_growth {before after : BlockState} (sound : Sound after)
    (refIndex : Interning.RefIndexSound after) (refs : Interning.Retains before.refs after.refs)
    (univs : Interning.Retains before.univs after.univs) (binding : bindingView after = bindingView before)
    (cache : after.exprCache = before.exprCache) (blobs : after.blockBlobs = before.blockBlobs)
    (good : Good cx param self related bindings before) :
    Good cx param self related bindings after ∧
      ExpressionRead.Extends (reader before).ecx (reader after).ecx := by
  have growth := ExpressionRead.blockReader_growth_tables cx param self before after refs univs blobs
  exact ⟨⟨⟨sound, refIndex, binding.trans good.1.2.2⟩, ExpressionRead.blockReader_cache_sound growth cache good.2⟩,
    growth⟩

/-- A step that changes none of the fields `Good` and the reader read. -/
theorem good_of_same {before after : BlockState} (univs : univView after = univView before)
    (refs : after.refs = before.refs) (refsIndex : after.refsIndex = before.refsIndex)
    (binding : bindingView after = bindingView before) (cache : after.exprCache = before.exprCache)
    (blobs : after.blockBlobs = before.blockBlobs) (good : Good cx param self related bindings before) :
    Good cx param self related bindings after ∧
      ExpressionRead.Extends (reader before).ecx (reader after).ecx := by
  have univsSame : after.univs = before.univs := by
    have same := congrArg (fun view => view.2.2.1) univs
    exact same
  refine good_of_growth (Sound.of_view univs good.1.1) ?_ (by rw [refs]; exact Interning.Retains.refl _)
    (by rw [univsSame]; exact Interning.Retains.refl _) binding cache blobs good
  show Interning.IndexSound after.refs after.refsIndex
  rw [refs, refsIndex]
  exact good.1.2.1

theorem GoodStep.pure (value : α) :
    GoodStep cx param self related bindings compileEnv (pure value) :=
  fun _ _ good => ⟨good, ExpressionRead.Extends.refl _⟩

theorem GoodStep.throw (error : CompileError) :
    GoodStep cx param self related bindings compileEnv (throw error : CompileM α) :=
  fun _ _ good => ⟨good, ExpressionRead.Extends.refl _⟩

theorem GoodStep.get : GoodStep cx param self related bindings compileEnv getBlockState :=
  fun _ _ good => ⟨good, ExpressionRead.Extends.refl _⟩

theorem GoodStep.readBlock : GoodStep cx param self related bindings compileEnv getBlockEnv :=
  fun _ _ good => ⟨good, ExpressionRead.Extends.refl _⟩

theorem GoodStep.bind {action : CompileM α} {next : α → CompileM β}
    (head : GoodStep cx param self related bindings compileEnv action)
    (tail : ∀ value, GoodStep cx param self related bindings compileEnv (next value)) :
    GoodStep cx param self related bindings compileEnv (action >>= next) := by
  intro block before good
  have first := head block before good
  rw [rawRun_bind]
  cases ran : rawRun action (compileEnv, block) before with
  | mk outcome middle =>
    rw [ran] at first
    cases outcome with
    | error error => exact first
    | ok value =>
      have second := tail value block middle first.1
      exact ⟨second.1, extends_trans first.2 second.2⟩

theorem GoodStep.discard {action : CompileM α}
    (inner : GoodStep cx param self related bindings compileEnv action) :
    GoodStep cx param self related bindings compileEnv (Functor.discard action) := by
  unfold Functor.discard
  exact GoodStep.bind inner (fun _ => GoodStep.pure ())

theorem GoodStep.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α}
    (inner : GoodStep cx param self related bindings compileEnv action) :
    GoodStep cx param self related bindings compileEnv (withBlockEnv update action) := by
  intro block before good
  rw [rawRun_withBlockEnv]
  exact inner (update block) before good

theorem GoodStep.lookup (name : Ix.Name) :
    GoodStep cx param self related bindings compileEnv (lookupConstAddr name) := by
  intro block before good
  rw [lookupConstAddr_state]
  exact ⟨good, ExpressionRead.Extends.refl _⟩

theorem GoodStep.check (values : Array Ixon.Univ) :
    GoodStep cx param self related bindings compileEnv (checkPreseedUnivs values) := by
  intro block before good
  rw [PreseedValidation.state]
  exact ⟨good, ExpressionRead.Extends.refl _⟩

theorem GoodStep.blob (bytes : ByteArray) (aligned : ∀ address, cx.blob address = compileEnv.blobs.get? address) :
    GoodStep cx param self related bindings compileEnv (storeBlob bytes) := by
  intro block before good
  have kept := storeBlob_good cx param self related bindings bytes (compileEnv, block) before good aligned
  exact ⟨kept.1, kept.2.1⟩

theorem GoodStep.ref (address : Address) :
    GoodStep cx param self related bindings compileEnv (internRef address) := by
  intro block before good
  have kept := internRef_good cx param self related bindings address (compileEnv, block) before good
  exact ⟨kept.1, kept.2.1⟩

theorem GoodStep.compileUniv (source : Ix.Level) :
    GoodStep cx param self related bindings compileEnv (compileUniv source) := by
  intro block before good
  have exact := (UniverseMeaning.compileUniv_exact source (compileEnv, block) before good.1.1.rawCache).1
  have frame := CanonUnivCache.compileUniv_frame source (compileEnv, block) before
  generalize (rawRun (Ix.CompileM.compileUniv source) (compileEnv, block) before).2 = after at exact frame ⊢
  have sound : Sound after :=
    ⟨exact, (congrArg CanonCacheExact frame).mpr good.1.1.canonCache, (congrArg TablesSound frame).mpr good.1.1.tables⟩
  have refs : after.refs = before.refs := by have same := congrArg BlockState.refs frame; exact same
  have univs : after.univs = before.univs := by have same := congrArg BlockState.univs frame; exact same
  exact good_of_growth sound ((congrArg Interning.RefIndexSound frame).mpr good.1.2.1)
    (by rw [refs]; exact Interning.Retains.refl _) (by rw [univs]; exact Interning.Retains.refl _)
    (by have same := congrArg bindingView frame; exact same)
    (by have same := congrArg BlockState.exprCache frame; exact same)
    (by have same := congrArg BlockState.blockBlobs frame; exact same) good

theorem GoodStep.canon (value : Ixon.Univ) :
    GoodStep cx param self related bindings compileEnv (canonUnivCached value) := by
  intro block before good
  obtain ⟨after, ran, exact, frame⟩ := canonUnivCached_correct value (compileEnv, block) before good.1.1.canonCache
  rw [ran]
  have refs : after.refs = before.refs := by have same := congrArg BlockState.refs frame; exact same
  have univs : after.univs = before.univs := by have same := congrArg BlockState.univs frame; exact same
  exact good_of_growth ⟨(congrArg UniverseMeaning.UnivCacheExact frame).mpr good.1.1.rawCache, exact,
      (congrArg TablesSound frame).mpr good.1.1.tables⟩
    ((congrArg Interning.RefIndexSound frame).mpr good.1.2.1)
    (by rw [refs]; exact Interning.Retains.refl _) (by rw [univs]; exact Interning.Retains.refl _)
    (by have same := congrArg bindingView frame; exact same)
    (by have same := congrArg BlockState.exprCache frame; exact same)
    (by have same := congrArg BlockState.blockBlobs frame; exact same) good

theorem GoodStep.univ (value : Ixon.Univ) :
    GoodStep cx param self related bindings compileEnv (internUniv value) := by
  intro block before good
  have correct := Interning.internUniv_correct value (compileEnv, block) before good.1.1.tables.primary
  have tables := Interning.internUniv_tables value (compileEnv, block) before
  have frame := internUniv_frame value (compileEnv, block) before
  generalize (rawRun (internUniv value) (compileEnv, block) before) = result at correct tables frame ⊢
  obtain ⟨outcome, after⟩ := result
  dsimp only at correct tables frame
  have sound : Sound after := by
    refine ⟨(congrArg UniverseMeaning.UnivCacheExact frame).mpr good.1.1.rawCache,
      (congrArg CanonCacheExact frame).mpr good.1.1.canonCache, correct.1, ?_⟩
    intro univ index found
    rw [tables.2.2.2.2] at found
    rw [tables.2.2.2.1]
    exact good.1.1.tables.metadata univ index found
  exact good_of_growth sound ((congrArg Interning.RefIndexSound frame).mpr good.1.2.1)
    (by rw [tables.1]; exact Interning.Retains.refl _) correct.2.1
    (by have same := congrArg bindingView frame; exact same) tables.2.2.1 tables.2.1 good

theorem GoodStep.final :
    GoodStep cx param self related bindings compileEnv
      (modifyBlockState fun state => { state with univsFinal := true }) := by
  intro block before good
  exact good_of_same rfl rfl rfl rfl rfl rfl good

theorem GoodStep.resetUnivCache :
    GoodStep cx param self related bindings compileEnv
      (modifyBlockState fun state => { state with univCache := {} }) := by
  intro block before good
  exact good_of_growth ⟨CacheSound.empty _, good.1.1.canonCache, good.1.1.tables⟩ good.1.2.1
    (Interning.Retains.refl _) (Interning.Retains.refl _) rfl rfl rfl good

theorem GoodStep.withUnivCtx (params : List Ix.Name) {action : CompileM α}
    (inner : GoodStep cx param self related bindings compileEnv action) :
    GoodStep cx param self related bindings compileEnv (withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  exact GoodStep.bind GoodStep.resetUnivCache (fun _ => GoodStep.withBlockEnv _ inner)

/-! ## The collector -/

theorem GoodStep.collectUnivs (levels : List Ix.Level) (initial : Array Ixon.Univ) :
    GoodStep cx param self related bindings compileEnv (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact GoodStep.pure initial
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact GoodStep.bind (GoodStep.compileUniv level) (fun value => ih (initial.push value))

theorem GoodStep.collectStructural (aligned : ∀ address, cx.blob address = compileEnv.blobs.get? address)
    (context : Address) (mutualContext : MutCtx) (params : List Ix.Name) (expr : Ix.Expr)
    (acc : ExprTableCollection) :
    GoodStep cx param self related bindings compileEnv
      (collectExprTablesStructural context mutualContext params expr acc) := by
  induction expr generalizing acc
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases acc with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact GoodStep.pure _
    · with_reducible repeat' first
        | exact GoodStep.pure _
        | exact GoodStep.throw _
        | exact GoodStep.compileUniv _
        | exact GoodStep.lookup _
        | exact GoodStep.blob _ aligned
        | exact GoodStep.collectUnivs _ _
        | refine GoodStep.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem GoodStep.collect (aligned : ∀ address, cx.blob address = compileEnv.blobs.get? address)
    (expr : Ix.Expr) (context : Address) (acc : ExprTableCollection) :
    GoodStep cx param self related bindings compileEnv (collectExprTables expr context acc) :=
  GoodStep.bind GoodStep.readBlock (fun block =>
    GoodStep.collectStructural aligned context block.mutCtx block.univCtx expr acc)

theorem GoodStep.collectRoots (aligned : ∀ address, cx.blob address = compileEnv.blobs.get? address)
    (roots : List (Ix.Expr × List Ix.Name)) (initial : ExprTableCollection) :
    GoodStep cx param self related bindings compileEnv (collectPreseedExprs roots initial) := by
  induction roots generalizing initial with
  | nil => exact GoodStep.pure initial
  | cons root rest ih =>
    rcases root with ⟨expr, params⟩
    rw [collectPreseedExprs]
    exact GoodStep.bind (GoodStep.withUnivCtx params (GoodStep.collect aligned expr (univParamsKey params) initial))
      (fun next => ih next)

/-! ## The inserters and the whole preseed -/

theorem GoodStep.internRefs (refs : List Address) (previous : Option Address) :
    GoodStep cx param self related bindings compileEnv (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact GoodStep.pure ()
  | cons address rest ih =>
    unfold internPreseedRefs
    split
    · exact GoodStep.bind (GoodStep.discard (GoodStep.ref address)) (fun _ => ih (some address))
    · exact ih (some address)

theorem GoodStep.canonUnivs (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    GoodStep cx param self related bindings compileEnv (canonPreseedUnivs values initial) := by
  induction values generalizing initial with
  | nil => exact GoodStep.pure initial
  | cons value rest ih =>
    unfold canonPreseedUnivs
    exact GoodStep.bind (GoodStep.canon value) (fun canonical => ih (initial.push canonical))

theorem GoodStep.internUnivs (entries : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    GoodStep cx param self related bindings compileEnv (internPreseedUnivs entries previous) := by
  induction entries generalizing previous with
  | nil => exact GoodStep.pure ()
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    unfold internPreseedUnivs
    split
    · exact GoodStep.bind (GoodStep.discard (GoodStep.univ value)) (fun _ => ih (some key))
    · exact ih (some key)

/-- **Preseeding keeps the expression invariant**: every run of
`preseedExprTables`, failing runs included, keeps `Good` and extends the
in-flight reader, given blobs aligned with the published store. -/
theorem preseed_good (aligned : ∀ address, cx.blob address = compileEnv.blobs.get? address)
    (roots : Array (Ix.Expr × List Ix.Name)) :
    GoodStep cx param self related bindings compileEnv (preseedExprTables roots) := by
  rw [preseedExprTables]
  apply GoodStep.bind (GoodStep.collectRoots aligned roots.toList (#[], #[], {}))
  rintro ⟨refs, univs, _⟩
  apply GoodStep.bind (GoodStep.internRefs _ none)
  intro _
  apply GoodStep.bind (GoodStep.canonUnivs _ _)
  intro canonical
  apply GoodStep.bind (GoodStep.check _)
  intro _
  apply GoodStep.bind (GoodStep.internUnivs _ none)
  intro _
  exact GoodStep.final

end Good

/-- A successful preseed leaves the primary universe table final. -/
theorem preseed_final (roots : Array (Ix.Expr × List Ix.Name)) (context : CompileEnv × BlockEnv)
    {before after : BlockState} (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    after.univsFinal = true := by
  rw [preseedExprTables] at ran
  obtain ⟨collection, collected, _, tail⟩ := bind_ok ran
  rcases collection with ⟨refs, univs, seen⟩
  dsimp only at tail
  obtain ⟨_, interned, _, tail⟩ := bind_ok tail
  obtain ⟨_, canonicalized, _, tail⟩ := bind_ok tail
  obtain ⟨_, checked, _, tail⟩ := bind_ok tail
  obtain ⟨_, univsDone, _, tail⟩ := bind_ok tail
  rw [rawRun_modify] at tail
  cases tail
  rfl

/-- **Preseed, then compile**: from a state satisfying `Good`, after a
successful preseed of the block's roots, a successful compile of an
expression reads back as its source. -/
theorem preseed_compileExpr_read {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (roots : Array (Ix.Expr × List Ix.Name)) (source : Ix.Expr) {before middle after : BlockState}
    {value : Ixon.Expr × UInt64}
    (good : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before)
    (preseeded : rawRun (preseedExprTables roots) context before = (.ok (), middle))
    (ran : rawRun (compileExpr source) context middle = (.ok value, after)) :
    ∃ target, Related names (LevelMeaning context.2.univCtx σ param) source target ∧
      (ExpressionRead.blockReader cx param self after).read value.1 = .ok target := by
  have kept : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings
      (rawRun (preseedExprTables roots) context before).2 :=
    (preseed_good aligned roots context.2 before good).1
  rw [preseeded] at kept
  exact compileExpr_read cx param self names σ bindings context aligned external selfSound source middle
    kept ran

end Ix.CompileCert.PreseedState
