import Ix.CompileCert.ExpressionMetadata

/-! Whole-run correctness of the actual ordinary expression compiler.
Every source expression is covered under explicit prefix, self-binding, table
and cache invariants. Successful outputs read as related kernel expressions;
errors retain state validity and earlier readings. Empty initialization
discharges table/cache premises. Declaration construction, compiler rewrites,
sharing/serialization and whole-DAG composition remain separate obligations. -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.CompileCert.ExpressionCacheRun (Meaning Valid)

section Constructors

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
  (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
  (related : Ix.Expr → Kernel.Expr → Prop) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx base param self
local notation "meaning" => ExpressionRead.Reading related reader

theorem bvar_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (index : Nat) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (rel : related (.bvar index hash) (.bvar index)) :
    Checked cx base param self related bindings (.bvar index hash) before
      (rawRun (compileExprTotalStep compile (.bvar index hash)) context before) := by
  by_cases bounded : index < UInt64.size
  · obtain ⟨value, after, ran, read, frame⟩ :=
      ExpressionLeaves.bvar_step_total_read compile index hash context before bounded cx base param self
    rw [ran]
    have same := ExpressionLeaves.withoutExprMetadata_reader cx base param self frame
    refine ⟨good_metadata cx base param self related bindings frame good, ?_, ?_⟩
    · rw [same]; exact extends_refl _
    · intro result success
      cases Except.ok.inj success
      exact ⟨.bvar index, rel, read⟩
  · rw [ExpressionIndices.bvar_step_refuses compile index hash context before (Nat.le_of_not_gt bounded)]
    exact ⟨good, extends_refl _, by intro result bad; cases bad⟩

theorem sort_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Level) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (params : List Kernel.Name) (parameterMap : param = Kernel.Reader.paramOf params)
    (arity : params.length = context.2.univCtx.length)
    (sortRelated : ∀ level, ExpressionLeaves.LevelMeaning context.2.univCtx params source level →
      related (.sort source hash) (.sort level)) :
    Checked cx base param self related bindings (.sort source hash) before
      (rawRun (compileExprTotalStep compile (.sort source hash)) context before) := by
  rw [ExpressionLeaves.sort_step_eq, rawRun_bind]
  have head := compileLevel_good cx base param self related bindings source context before good params parameterMap arity
  cases ran : rawRun (compileAndInternUnivCanon source) context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact ⟨head.1, head.2.1, by intro result bad; cases bad⟩
    | ok value =>
      obtain ⟨level, readLevel, levelMeaning⟩ := head.2.2 value rfl
      obtain ⟨root, after, finished, frame⟩ := ExpressionLeaves.finishSort_returns value.1 value.2 context middle
      dsimp only
      rw [finished]
      have same := ExpressionLeaves.withoutExprMetadata_reader cx base param self frame
      refine ⟨good_metadata cx base param self related bindings frame head.1, ?_, ?_⟩
      · rw [same]; exact head.2.1
      · intro result success
        cases Except.ok.inj success
        refine ⟨.sort level, sortRelated level levelMeaning, ?_⟩
        rw [same]
        change (do pure (Kernel.Expr.sort (← (reader middle).ecx.level value.1))) = _
        rw [readLevel]
        rfl


end Constructors

theorem compileExprPartial_checked (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names) :
    ∀ source before, Good cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings before →
      Checked cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings source before
        (rawRun (compileExprPartial source) context before) := by
  let rel := Related names context.2.univCtx params
  let param := Kernel.Reader.paramOf params
  suffices checked : ∀ source, True → ∀ before, Good cx base param self rel bindings before →
      Checked cx base param self rel bindings source before (rawRun (compileExprPartial source) context before) from
    fun source before good => checked source trivial before good
  apply partial_checked_of_step cx base param self rel bindings (fun _ => True) context
  intro source _ ih before good _
  cases source with
  | bvar index hash =>
    exact bvar_step_checked cx base param self rel bindings _ index hash context before good (.bvar index hash)
  | sort level hash =>
    exact sort_step_checked cx base param self rel bindings _ level hash context before good params rfl arity
      (fun level meaning => .sort hash meaning)
  | const name levels hash =>
    exact const_step_checked cx base param self rel bindings _ name levels hash context before good params rfl arity aligned names
      external selfSound (fun _ targetLevels nameRel levelRel => .const hash levels targetLevels nameRel levelRel)
  | app fn arg hash =>
    apply app_step_checked cx base param self rel bindings _ fn arg hash context before good
    · intro child smaller state valid
      exact ih child smaller trivial state valid
    · intro _ _ hash _ _ fnRel argRel
      exact .app hash fnRel argRel
  | lam name type body info hash =>
    apply binder_step_checked cx base param self rel bindings false _ name type body info hash context before good aligned
    · intro state valid
      exact ih type (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro state valid
      exact ih body (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro _ _ typeRel bodyRel
      exact .lam name info hash typeRel bodyRel
  | forallE name type body info hash =>
    apply binder_step_checked cx base param self rel bindings true _ name type body info hash context before good aligned
    · intro state valid
      exact ih type (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro state valid
      exact ih body (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro _ _ typeRel bodyRel
      exact .all name info hash typeRel bodyRel
  | letE name type value body nonDep hash =>
    apply let_step_checked cx base param self rel bindings _ name type value body nonDep hash context before good aligned
    · intro state valid
      exact ih type (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro state valid
      exact ih value (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro state valid
      exact ih body (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro _ _ _ typeRel valueRel bodyRel
      exact .letE name nonDep hash typeRel valueRel bodyRel
  | lit value hash =>
    cases value with
    | natVal value => exact nat_step_checked cx base param self rel bindings _ value hash context before good aligned (.nat value hash)
    | strVal value => exact string_step_checked cx base param self rel bindings _ value hash context before good aligned (.str value hash)
  | proj name field source hash =>
    apply projection_step_checked cx base param self rel bindings _ name field source hash context before good aligned names external
    · intro state valid
      exact ih source (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro _ _ nameRel sourceRel
      exact .proj field hash nameRel sourceRel
  | mdata data source hash =>
    apply metadata_step_checked cx base param self rel bindings _ data source hash context before good aligned
    · intro state valid
      exact ih source (by simp only [exprCompileDepth]; omega) trivial state valid
    · intro _ sourceRel
      exact .mdata data hash sourceRel
  | fvar name hash => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩
  | mvar name hash => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩

theorem compileExprTotal_checked (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (source : Ix.Expr) (before : BlockState)
    (good : Good cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings before) :
    Checked cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings source before
      (rawRun (compileExprTotal source) context before) := by
  rw [compileExprTotal_eq_partial]
  exact compileExprPartial_checked cx base self names params bindings context arity aligned external selfSound source before good

/-- Fresh ordinary expression tables and memos. Prefix bindings and blob
state stay supplied by the declaration unit; failures still preserve them. -/
def initialState (seed : BlockState) : BlockState :=
  { seed with
    exprCache := {}, univCache := {}, canonUnivCache := {},
    refs := #[], refsIndex := {}, p3MetaRefs := #[], p3MetaRefsIndex := {},
    univs := #[], univsIndex := {}, metaUnivs := #[], metaUnivsIndex := {} }

theorem initialState_good (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name) (related : Ix.Expr → Kernel.Expr → Prop)
    (seed : BlockState) : Good cx base param self related (bindingView seed) (initialState seed) := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, rfl⟩, ?_⟩
  · intro key value found; simp [initialState] at found
  · intro key value found; simp [initialState] at found
  · exact ⟨Interning.IndexSound.empty, Interning.IndexSound.empty⟩
  · exact Interning.IndexSound.empty
  · exact Interning.IndexSound.empty
  · intro source value found; simp [initialState] at found

theorem compileExprPartial_initial (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (context : CompileEnv × BlockEnv) (seed : BlockState)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 (bindingView seed) cx names) (selfSound : SelfCorrect context.2 self names)
    (source : Ix.Expr) :
    Checked cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) (bindingView seed)
      source (initialState seed) (rawRun (compileExprPartial source) context (initialState seed)) :=
  compileExprPartial_checked cx base self names params (bindingView seed) context arity aligned external selfSound
    source (initialState seed) (initialState_good cx base (Kernel.Reader.paramOf params) self _ seed)

/-- A directly usable successful-run conclusion for the actual compiler and
reader, without requiring an output certificate or a constructor-step premise. -/
theorem compileExprPartial_read (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (source : Ix.Expr) (before : BlockState)
    (good : Good cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings before)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExprPartial source) context before = (.ok value, after)) :
    ∃ target, Related names context.2.univCtx params source target ∧
      (ExpressionRead.blockReader cx base (Kernel.Reader.paramOf params) self after).read value.1 = .ok target := by
  have checked := compileExprPartial_checked cx base self names params bindings context arity aligned external selfSound source before good
  rw [ran] at checked
  exact checked.2.2 value rfl


end Ix.CompileCert.ExpressionState
