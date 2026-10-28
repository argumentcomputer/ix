import Ix.CompileCert.ExpressionSteps

/-! # The ordinary expression compiler reads back as its source

`Ix.CompileM.compileExprNoSurgery` is one well-founded function: the memo,
then one step (`compileExprNoSurgeryStep`) whose recursive calls are on
strict subterms. Its correctness is proved by strong induction on `sizeOf`
(CT-13's top induction, re-derived for this tree):

* `cached_checked`: a memo hit returns an entry whose meaning the invariant
  carries (exact keys, CQ2.8); a miss runs the step, and inserting its
  result keeps the memo's meaning;
* `compileExprNoSurgery_checked`: from every state satisfying `Good`, every
  run keeps `Good` and every earlier reading, and a successful run returns
  a value the certified reader reads as a term `Related` to the source,
  under the declaration prefix's bindings (`BindingsCorrect`), the block's
  own members (`SelfCorrect`) and blobs aligned with the published store;
* `compileExpr_surgeryFree`: the production entry `compileExpr` is
  `compileExprNoSurgery`, so `compileExpr_read` holds for it. -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

section Cache

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
  (self : Nat → Option (ReadM (CName md))) (related : Ix.Expr → CExpr md → Prop)
  (bindings : Bindings)

/-- **The memo**: a hit returns an entry whose meaning `Good` carries; a
miss runs the step, and its result's insertion keeps the memo's meaning. -/
theorem cached_checked (source : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (stepCorrect : before.exprCache.get? ⟨source⟩ = none →
      Checked cx param self related bindings source before
        (rawRun (step compileExprNoSurgery source) context before)) :
    Checked cx param self related bindings source before
      (rawRun (compileExprNoSurgery source) context before) := by
  rw [compileExprNoSurgery]
  simp only [rawRun_bind, rawRun_get]
  cases found : before.exprCache.get? ⟨source⟩ with
  | some value =>
    refine ⟨good, ExpressionRead.Extends.refl _, ?_⟩
    intro result same
    cases Except.ok.inj same
    exact good.2 ⟨source⟩ value found
  | none =>
    dsimp only
    rw [show (compileExprNoSurgeryStep source fun x _h => compileExprNoSurgery x) =
      step compileExprNoSurgery source from rfl]
    rw [rawRun_bind]
    have stepResult := stepCorrect found
    cases ran : rawRun (step compileExprNoSurgery source) context before with
    | mk outcome middle =>
      rw [ran] at stepResult
      cases outcome with
      | error error => exact stepResult
      | ok value =>
        obtain ⟨result, root⟩ := value
        dsimp only
        simp only [rawRun_bind, rawRun_modify, rawRun_pure]
        have entry := stepResult.2.2 (result, root) rfl
        refine ⟨⟨⟨Sound.of_view (before := middle) rfl stepResult.1.1.1, stepResult.1.1.2.1, stepResult.1.1.2.2⟩, ?_⟩,
          stepResult.2.1, ?_⟩
        · exact CacheSound.insert stepResult.1.2 ⟨source⟩ (result, root) entry
        · intro output same
          cases Except.ok.inj same
          exact entry

end Cache

/-- **The ordinary expression compiler reads back as its source** (scoped).
From every state satisfying `Good`, under the declaration prefix's
bindings, and where every constant occurrence of the source that is a
member of the block reads as a related key, every run keeps `Good` and every
earlier reading, and a successful run returns a value the certified reader
reads as a term `Related` to the source, with levels meaning the source
levels. -/
theorem compileExprNoSurgery_scoped {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) :
    ∀ source, ConstsSatisfy (SelfName context.2 self names) source → ∀ before,
      Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before →
      Checked cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings source before
        (rawRun (compileExprNoSurgery source) context before) := by
  intro source
  induction source using (measure (fun e : Ix.Expr => sizeOf e)).wf.induction with
  | h source ih =>
    intro scope before good
    have children : ∀ child, sizeOf child < sizeOf source →
        ConstsSatisfy (SelfName context.2 self names) child → ∀ state,
        Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings state →
        Checked cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings child state
          (rawRun (compileExprNoSurgery child) context state) :=
      fun child smaller childScope => ih child smaller childScope
    apply cached_checked cx param self _ bindings source context before good
    intro _
    cases source with
    | bvar index hash =>
      exact bvar_step_checked cx param self _ bindings _ index hash context before good (.bvar index hash)
    | sort level hash =>
      exact sort_step_checked cx param self _ bindings _ level hash context before good σ
        (fun level meaning => .sort hash meaning)
    | const name levels hash =>
      exact const_step_checked cx param self _ bindings _ name levels hash context before good σ aligned names
        external scope (fun key targets nameRel levelRel => .const hash levels targets nameRel levelRel)
    | app fn arg hash =>
      obtain ⟨headScope, argsScope⟩ := constsSatisfy_spine _ scope
      exact app_step_checked cx param self _ bindings _ fn arg hash context before good
        (children _ (Ix.CompileM.decomposeApps_app_head_lt fn arg hash) headScope)
        (fun x member => children x (Ix.CompileM.decomposeApps_app_mem_lt fn arg hash member)
          (argsScope x member))
        (fun _ _ h _ _ fnRel argRel => .app h fnRel argRel)
    | lam name type body info hash =>
      obtain ⟨typeScope, bodyScope⟩ := scope
      exact binder_step_checked cx param self _ bindings false _ name type body info hash context before good
        aligned (children type (by simp; omega) typeScope) (children body (by simp; omega) bodyScope)
        (fun _ _ typeRel bodyRel => .lam name info hash typeRel bodyRel)
    | forallE name type body info hash =>
      obtain ⟨typeScope, bodyScope⟩ := scope
      exact binder_step_checked cx param self _ bindings true _ name type body info hash context before good
        aligned (children type (by simp; omega) typeScope) (children body (by simp; omega) bodyScope)
        (fun _ _ typeRel bodyRel => .all name info hash typeRel bodyRel)
    | letE name type value body nonDep hash =>
      obtain ⟨typeScope, valueScope, bodyScope⟩ := scope
      exact let_step_checked cx param self _ bindings _ name type value body nonDep hash context before good
        aligned (children type (by simp; omega) typeScope) (children value (by simp; omega) valueScope)
        (children body (by simp; omega) bodyScope)
        (fun _ _ _ typeRel valueRel bodyRel => .letE name nonDep hash typeRel valueRel bodyRel)
    | lit value hash =>
      cases value with
      | natVal value =>
        exact nat_step_checked cx param self _ bindings _ value hash context before good aligned (.nat value hash)
      | strVal value =>
        exact string_step_checked cx param self _ bindings _ value hash context before good aligned
          (.str value hash)
    | proj name field value hash =>
      exact projection_step_checked cx param self _ bindings _ name field value hash context before good
        aligned names external (children value (by simp; omega) scope)
        (fun _ _ nameRel valueRel => .proj field hash nameRel valueRel)
    | mdata data value hash =>
      exact metadata_step_checked cx param self _ bindings _ data value hash context before good aligned
        (children value (by simp; omega) scope)
        (fun plain _ valueRel => .mdata data hash plain valueRel)
        (fun frame c read _ _ valueRel lowered => .contract data hash c frame read valueRel lowered)
    | fvar name hash =>
      exact checked_error cx param self _ bindings _ good (ExpressionRead.Extends.refl _)
    | mvar name hash =>
      exact checked_error cx param self _ bindings _ good (ExpressionRead.Extends.refl _)

/-- **The ordinary expression compiler reads back as its source**, for a
self map that is correct on every member of the block. -/
theorem compileExprNoSurgery_checked {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names) :
    ∀ source before,
      Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before →
      Checked cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings source before
        (rawRun (compileExprNoSurgery source) context before) :=
  fun source => compileExprNoSurgery_scoped cx param self names σ bindings context aligned external source
    (constsSatisfy_of_forall (fun name => selfSound name) source)

/-- A successful run of the ordinary compiler reads as a related term. -/
theorem compileExprNoSurgery_read {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (source : Ix.Expr) (before : BlockState)
    (good : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExprNoSurgery source) context before = (.ok value, after)) :
    ∃ target, Related names (LevelMeaning context.2.univCtx σ param) source target ∧
      (ExpressionRead.blockReader cx param self after).read value.1 = .ok target := by
  have checked := compileExprNoSurgery_checked cx param self names σ bindings context aligned external
    selfSound source before good
  rw [ran] at checked
  exact checked.2.2 value rfl

/-- **The production expression compiler is the ordinary one.** -/
theorem compileExpr_surgeryFree (source : Ix.Expr) (context : CompileEnv × BlockEnv)
    (before : BlockState) :
    rawRun (compileExpr source) context before = rawRun (compileExprNoSurgery source) context before :=
  rfl

/-- **The production expression compiler reads back as its source.** -/
theorem compileExpr_read {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (source : Ix.Expr) (before : BlockState)
    (good : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExpr source) context before = (.ok value, after)) :
    ∃ target, Related names (LevelMeaning context.2.univCtx σ param) source target ∧
      (ExpressionRead.blockReader cx param self after).read value.1 = .ok target := by
  rw [compileExpr_surgeryFree source context] at ran
  exact compileExprNoSurgery_read cx param self names σ bindings context aligned external selfSound source
    before good ran

/-- Fresh memos and tables; the binding view and blobs are the seed's. -/
def initialState (seed : BlockState) : BlockState :=
  { seed with
    exprCache := {}, univCache := {}, canonUnivCache := {},
    refs := #[], refsIndex := {}, univs := #[], univsIndex := {}, metaUnivs := #[], metaUnivsIndex := {} }

theorem initialState_good {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (related : Ix.Expr → CExpr md → Prop) (seed : BlockState) :
    Good cx param self related (bindingView seed) (initialState seed) := by
  refine ⟨⟨⟨CacheSound.empty _, fun _ _ found => by simp [initialState] at found,
    ⟨Interning.IndexSound.empty, Interning.IndexSound.empty⟩⟩, Interning.IndexSound.empty, rfl⟩, ?_⟩
  exact CacheSound.empty _

/-- **No state premise**: from fresh memos and tables, a successful run of
the ordinary compiler reads as a related term. -/
theorem compileExprNoSurgery_initial_read {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (context : CompileEnv × BlockEnv) (seed : BlockState)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 (bindingView seed) cx names)
    (selfSound : SelfCorrect context.2 self names) (source : Ix.Expr)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExprNoSurgery source) context (initialState seed) = (.ok value, after)) :
    ∃ target, Related names (LevelMeaning context.2.univCtx σ param) source target ∧
      (ExpressionRead.blockReader cx param self after).read value.1 = .ok target :=
  compileExprNoSurgery_read cx param self names σ (bindingView seed) context aligned external selfSound source
    (initialState seed) (initialState_good cx param self _ seed) ran

end Ix.CompileCert.ExpressionState
