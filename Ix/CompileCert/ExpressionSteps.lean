import Ix.CompileCert.ExpressionTables

/-! Production application, binder, constant, projection and literal
transitions. Recursive cases use only child contracts and preserve earlier
child readings. The cache induction carries all state and reader invariants. -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.CompileCert.ExpressionCacheRun (Meaning Valid)

section Constructors

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
  (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
  (related : Ix.Expr → Kernel.Expr → Prop) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx base param self
local notation "meaning" => ExpressionRead.Reading related reader

theorem meaning_grows {before after : BlockState}
    (growth : ExpressionRead.Extends (reader before).ecx (reader after).ecx)
    {source : Ix.Expr} {value : Ixon.Expr × UInt64} (prior : meaning before source value) :
    meaning after source value := by
  apply ExpressionRead.Reading.of_growth growth ?_ prior
  intro index value found
  change (#[] : Array (Kernel.Reader.ReadM Kernel.Expr))[index]? = some (.ok value) at found
  simp at found

def finishApp (fn arg : Ixon.Expr × UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.app fn.2 arg.2)
  pure (.app fn.1 arg.1, root)

theorem finishApp_checked (fn arg : Ix.Expr) (hash : Address)
    (targetFn targetArg : Ixon.Expr × UInt64) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before)
    (fnRead : meaning before fn targetFn) (argRead : meaning before arg targetArg)
    (congruent : ∀ f a, related fn f → related arg a → related (.app fn arg hash) (.app f a)) :
    Checked cx base param self related bindings (.app fn arg hash) before
      (rawRun (finishApp targetFn targetArg) context before) := by
  let after := { before with arena := { nodes := before.arena.nodes.push (.app targetFn.2 targetArg.2) } }
  change Checked cx base param self related bindings (.app fn arg hash) before
    (.ok (.app targetFn.1 targetArg.1, before.arena.nodes.size.toUInt64), after)
  have frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := rfl
  refine ⟨good_metadata cx base param self related bindings frame good, extends_refl _, ?_⟩
  intro value success
  cases Except.ok.inj success
  obtain ⟨f, rf, readFn⟩ := fnRead
  obtain ⟨a, ra, readArg⟩ := argRead
  refine ⟨.app f a, congruent f a rf ra, ?_⟩
  change (do pure (Kernel.Expr.app (← (reader before).read targetFn.1) (← (reader before).read targetArg.1))) = _
  rw [readFn, readArg]
  rfl

/-- The actual application transition. The first child may be an uncached
application spine; its reading survives compilation of the second child. -/
theorem app_pair_checked (fn arg : Ix.Expr) (hash : Address)
    (compileFn compileArg : CompileM (Ixon.Expr × UInt64)) (context : CompileEnv × BlockEnv)
    (before : BlockState)
    (first : Checked cx base param self related bindings fn before (rawRun compileFn context before))
    (second : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings arg state (rawRun compileArg context state))
    (congruent : ∀ f a, related fn f → related arg a → related (.app fn arg hash) (.app f a)) :
    Checked cx base param self related bindings (.app fn arg hash) before
      (rawRun (do let f ← compileFn; let a ← compileArg; finishApp f a) context before) := by
  rw [rawRun_bind]
  cases firstRun : rawRun compileFn context before with
  | mk outcome middle =>
    rw [firstRun] at first
    cases outcome with
    | error error => exact ⟨first.1, first.2.1, by intro value bad; cases bad⟩
    | ok targetFn =>
      dsimp only
      rw [rawRun_bind]
      have next := second middle first.1
      cases secondRun : rawRun compileArg context middle with
      | mk outcome nextState =>
        rw [secondRun] at next
        cases outcome with
        | error error => exact ⟨next.1, extends_trans first.2.1 next.2.1, by intro value bad; cases bad⟩
        | ok targetArg =>
          have oldFn := meaning_grows cx base param self related next.2.1 (first.2.2 targetFn rfl)
          have finished := finishApp_checked cx base param self related bindings fn arg hash targetFn targetArg context nextState
            next.1 oldFn (next.2.2 targetArg rfl) congruent
          exact ⟨finished.1, extends_trans (extends_trans first.2.1 next.2.1) finished.2.1, finished.2.2⟩

theorem appTotal_app_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (fn arg : Ix.Expr) (hash : Address) :
    compileAppTotal compile (.app fn arg hash) = (do
      let f ← compileAppTotal compile fn
      let a ← compile arg
      finishApp f a) := rfl

/-- A bounded induction over the actual uncached left application spine.
The callback contract is needed only for expressions within the supplied
bound; the outer expression theorem chooses a strictly smaller bound. -/
theorem appTotal_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (context : CompileEnv × BlockEnv)
    (bound : Nat)
    (recursive : ∀ source, exprCompileDepth source ≤ bound → ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings source state (rawRun (compile source) context state))
    (applications : ∀ fn arg hash f a, related fn f → related arg a → related (.app fn arg hash) (.app f a)) :
    ∀ source, exprCompileDepth source ≤ bound → ∀ before, Good cx base param self related bindings before →
      Checked cx base param self related bindings source before (rawRun (compileAppTotal compile source) context before) := by
  intro source
  induction source with
  | app fn arg hash ihfn _ =>
    intro depth before good
    have fnDepth : exprCompileDepth fn ≤ bound := by simp only [exprCompileDepth] at depth; omega
    have argDepth : exprCompileDepth arg ≤ bound := by simp only [exprCompileDepth] at depth; omega
    rw [appTotal_app_eq]
    exact app_pair_checked cx base param self related bindings fn arg hash _ _ context before
      (ihfn fnDepth before good) (recursive arg argDepth) (applications fn arg hash)
  | _ => intros; exact recursive _ (by assumption) _ (by assumption)

/-- Full application-spine correctness uses only strict-child contracts, as
required by the actual expression compiler's induction rule. -/
theorem app_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (fn arg : Ix.Expr) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx base param self related bindings before)
    (children : ∀ child, exprCompileDepth child < exprCompileDepth (.app fn arg hash) →
      ∀ state, Good cx base param self related bindings state →
        Checked cx base param self related bindings child state (rawRun (compile child) context state))
    (applications : ∀ f a h tf ta, related f tf → related a ta → related (.app f a h) (.app tf ta)) :
    Checked cx base param self related bindings (.app fn arg hash) before
      (rawRun (compileExprTotalStep compile (.app fn arg hash)) context before) := by
  change Checked cx base param self related bindings (.app fn arg hash) before
    (rawRun (compileAppTotal compile (.app fn arg hash)) context before)
  rw [appTotal_app_eq]
  apply app_pair_checked cx base param self related bindings fn arg hash _ _ context before
  · apply appTotal_checked cx base param self related bindings compile context (max (exprCompileDepth fn) (exprCompileDepth arg))
    · intro child depth state valid
      apply children child ?_ state valid
      simp only [exprCompileDepth]
      omega
    · exact applications
    · exact Nat.le_max_left _ _
    · exact good
  · apply children arg
    simp only [exprCompileDepth]
    omega
  · exact applications fn arg hash

theorem sequence_pair_checked (source firstSource secondSource : Ix.Expr)
    (firstAction secondAction : CompileM (Ixon.Expr × UInt64))
    (finish : (Ixon.Expr × UInt64) → (Ixon.Expr × UInt64) → CompileM (Ixon.Expr × UInt64))
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (first : Checked cx base param self related bindings firstSource before (rawRun firstAction context before))
    (second : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings secondSource state (rawRun secondAction context state))
    (finishCorrect : ∀ firstValue secondValue state, Good cx base param self related bindings state →
      meaning state firstSource firstValue → meaning state secondSource secondValue →
      Checked cx base param self related bindings source state (rawRun (finish firstValue secondValue) context state)) :
    Checked cx base param self related bindings source before
      (rawRun (do let a ← firstAction; let b ← secondAction; finish a b) context before) := by
  rw [rawRun_bind]
  cases firstRun : rawRun firstAction context before with
  | mk outcome middle =>
    rw [firstRun] at first
    cases outcome with
    | error error => exact ⟨first.1, first.2.1, by intro value bad; cases bad⟩
    | ok firstValue =>
      dsimp only
      rw [rawRun_bind]
      have next := second middle first.1
      cases secondRun : rawRun secondAction context middle with
      | mk outcome nextState =>
        rw [secondRun] at next
        cases outcome with
        | error error => exact ⟨next.1, extends_trans first.2.1 next.2.1, by intro value bad; cases bad⟩
        | ok secondValue =>
          have oldValue := meaning_grows cx base param self related next.2.1 (first.2.2 firstValue rfl)
          have finished := finishCorrect firstValue secondValue nextState next.1 oldValue (next.2.2 secondValue rfl)
          exact ⟨finished.1, extends_trans (extends_trans first.2.1 next.2.1) finished.2.1, finished.2.2⟩

theorem compileName_good (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    let after := (rawRun (compileName name) context before).2
    Good cx base param self related bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx := by
  have preserved := BlobWrites.compileName_preserves name context before
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, BlobWrites.compileName_reading name context before cx base param self aligned⟩
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
  · exact BlobWrites.cache_preserved context.1.blobs before _ preserved.1 preserved.2
      cx base param self aligned related good.2

theorem name_then_checked (source : Ix.Expr) (name : Ix.Name) (body : CompileM (Ixon.Expr × UInt64))
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (bodyCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings source state (rawRun body context state)) :
    Checked cx base param self related bindings source before (rawRun (do compileName name; body) context before) := by
  have head := compileName_good cx base param self related bindings name context before good aligned
  rw [rawRun_bind]
  cases named : rawRun (compileName name) context before with
  | mk outcome middle =>
    rw [named] at head
    cases outcome with
    | error error => exact ⟨head.1, head.2, by intro value bad; cases bad⟩
    | ok _done =>
      have tail := bodyCorrect middle head.1
      exact ⟨tail.1, extends_trans head.2 tail.2.1, tail.2.2⟩

/-- The full ordinary constant transition, using only the declaration-prefix
name/reference correspondence and current mutual-unit self correspondence. -/
theorem const_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (sources : Array Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx base param self related bindings before)
    (params : List Kernel.Name) (parameterMap : param = Kernel.Reader.paramOf params)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (names : Ix.Name → Kernel.Name → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (selfSound : SelfCorrect context.2 self names)
    (constantRelated : ∀ target levels, names name target →
      List.Forall₂ (ExpressionLeaves.LevelMeaning context.2.univCtx params) sources.toList levels →
      related (.const name sources hash) (.const target levels)) :
    Checked cx base param self related bindings (.const name sources hash) before
      (rawRun (compileExprTotalStep compile (.const name sources hash)) context before) := by
  rw [ExpressionIndices.constant_step_eq, compileConstExprRaw_eq]
  simp only [rawRun_bind, UniverseMeaning.rawRun_readBlock]
  have levelResult := compileLevels_good cx base param self related bindings sources context before good params parameterMap arity
  cases compiledRun : rawRun (sources.mapM compileAndInternUnivCanon) context before with
  | mk outcome leveled =>
    rw [compiledRun] at levelResult
    cases outcome with
    | error error => exact ⟨levelResult.1, levelResult.2.1, by intro value bad; cases bad⟩
    | ok compiled =>
      dsimp only
      obtain ⟨levels, relatedLevels, readLevels⟩ := levelResult.2.2 compiled rfl
      have named := compileName_good cx base param self related bindings name context leveled levelResult.1 aligned
      cases namedRun : rawRun (compileName name) context leveled with
      | mk outcome afterName =>
        rw [namedRun] at named
        cases outcome with
        | error error => exact ⟨named.1, extends_trans levelResult.2.1 named.2, by intro value bad; cases bad⟩
        | ok _done =>
          have retainedLevels := named.2.levels (compiled.map Prod.fst) levels readLevels
          have body := constBody_checked cx base param self related bindings name sources hash compiled levels context afterName
            named.1 names external selfSound retainedLevels (fun target nameRel => constantRelated target levels nameRel relatedLevels)
          exact ⟨body.1, extends_trans (extends_trans levelResult.2.1 named.2) body.2.1, body.2.2⟩

def binderSource (isAll : Bool) (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo) (hash : Address) : Ix.Expr :=
  if isAll then .forallE name type body info hash else .lam name type body info hash

def binderTarget (isAll : Bool) (type body : Kernel.Expr) : Kernel.Expr :=
  if isAll then .forallE type body ⟨.never⟩ else .lam type body ⟨.never⟩

def finishBinder (isAll : Bool) (name : Ix.Name) (info : Lean.BinderInfo)
    (type body : Ixon.Expr × UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.binder name.getHash info type.2 body.2)
  pure ((if isAll then .leanAll type.1 body.1 else .leanLam type.1 body.1), root)

theorem finishBinder_checked (isAll : Bool) (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo) (hash : Address)
    (targetType targetBody : Ixon.Expr × UInt64) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before)
    (typeRead : meaning before type targetType) (bodyRead : meaning before body targetBody)
    (congruent : ∀ t b, related type t → related body b →
      related (binderSource isAll name type body info hash) (binderTarget isAll t b)) :
    Checked cx base param self related bindings (binderSource isAll name type body info hash) before
      (rawRun (finishBinder isAll name info targetType targetBody) context before) := by
  let after := { before with arena := { nodes := before.arena.nodes.push (.binder name.getHash info targetType.2 targetBody.2) } }
  change Checked cx base param self related bindings (binderSource isAll name type body info hash) before
    (.ok ((if isAll then .leanAll targetType.1 targetBody.1 else .leanLam targetType.1 targetBody.1),
      before.arena.nodes.size.toUInt64), after)
  have frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := rfl
  refine ⟨good_metadata cx base param self related bindings frame good, extends_refl _, ?_⟩
  intro value success
  cases Except.ok.inj success
  obtain ⟨t, rt, readType⟩ := typeRead
  obtain ⟨b, rb, readBody⟩ := bodyRead
  refine ⟨binderTarget isAll t b, congruent t b rt rb, ?_⟩
  cases isAll with
  | false =>
    change (do pure (Kernel.Expr.lam (← (reader before).read targetType.1) (← (reader before).read targetBody.1) ⟨.never⟩)) = _
    rw [readType, readBody]
    rfl
  | true =>
    change (do pure (Kernel.Expr.forallE (← (reader before).read targetType.1) (← (reader before).read targetBody.1) ⟨.never⟩)) = _
    rw [readType, readBody]
    rfl

theorem binder_step_eq (isAll : Bool) (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo) (hash : Address) :
    compileExprTotalStep compile (binderSource isAll name type body info hash) = (do
      compileName name
      let t ← compile type
      let b ← compile body
      finishBinder isAll name info t b) := by cases isAll <;> rfl

/-- Lambda and forall emission, including checked name metadata, both child
compilations, reader growth, cache validity and error states. -/
theorem binder_step_checked (isAll : Bool) (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (typeCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings type state (rawRun (compile type) context state))
    (bodyCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings body state (rawRun (compile body) context state))
    (congruent : ∀ t b, related type t → related body b →
      related (binderSource isAll name type body info hash) (binderTarget isAll t b)) :
    Checked cx base param self related bindings (binderSource isAll name type body info hash) before
      (rawRun (compileExprTotalStep compile (binderSource isAll name type body info hash)) context before) := by
  rw [binder_step_eq]
  apply name_then_checked cx base param self related bindings _ name _ context before good aligned
  intro state valid
  apply sequence_pair_checked cx base param self related bindings _ type body _ _ _ context state
    (typeCorrect state valid) bodyCorrect
  intro targetType targetBody next nextGood typeRead bodyRead
  exact finishBinder_checked cx base param self related bindings isAll name type body info hash
    targetType targetBody context next nextGood typeRead bodyRead congruent

def finishLet (name : Ix.Name) (nonDep : Bool) (type value body : Ixon.Expr × UInt64) :
    CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.letBinder name.getHash type.2 value.2 body.2)
  pure (.leanLet nonDep type.1 value.1 body.1, root)

theorem finishLet_checked (name : Ix.Name) (type value body : Ix.Expr) (nonDep : Bool) (hash : Address)
    (targetType targetValue targetBody : Ixon.Expr × UInt64) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before)
    (typeRead : meaning before type targetType) (valueRead : meaning before value targetValue) (bodyRead : meaning before body targetBody)
    (congruent : ∀ t v b, related type t → related value v → related body b →
      related (.letE name type value body nonDep hash) (.letE t v b)) :
    Checked cx base param self related bindings (.letE name type value body nonDep hash) before
      (rawRun (finishLet name nonDep targetType targetValue targetBody) context before) := by
  let after := { before with arena :=
    { nodes := before.arena.nodes.push (.letBinder name.getHash targetType.2 targetValue.2 targetBody.2) } }
  change Checked cx base param self related bindings (.letE name type value body nonDep hash) before
    (.ok (.leanLet nonDep targetType.1 targetValue.1 targetBody.1, before.arena.nodes.size.toUInt64), after)
  have frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := rfl
  refine ⟨good_metadata cx base param self related bindings frame good, extends_refl _, ?_⟩
  intro result success
  cases Except.ok.inj success
  obtain ⟨t, rt, readType⟩ := typeRead
  obtain ⟨v, rv, readValue⟩ := valueRead
  obtain ⟨b, rb, readBody⟩ := bodyRead
  refine ⟨.letE t v b, congruent t v b rt rv rb, ?_⟩
  change (do pure (Kernel.Expr.letE (← (reader before).read targetType.1)
    (← (reader before).read targetValue.1) (← (reader before).read targetBody.1))) = _
  rw [readType, readValue, readBody]
  rfl

theorem let_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type value body : Ix.Expr) (nonDep : Bool) (hash : Address) :
    compileExprTotalStep compile (.letE name type value body nonDep hash) = (do
      compileName name
      let t ← compile type
      let v ← compile value
      let b ← compile body
      finishLet name nonDep t v b) := rfl

/-- The let transition retains the type reading across both later children
and the value reading across the body, including all intermediate failures. -/
theorem let_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type value body : Ix.Expr) (nonDep : Bool) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (typeCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings type state (rawRun (compile type) context state))
    (valueCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings value state (rawRun (compile value) context state))
    (bodyCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings body state (rawRun (compile body) context state))
    (congruent : ∀ t v b, related type t → related value v → related body b →
      related (.letE name type value body nonDep hash) (.letE t v b)) :
    Checked cx base param self related bindings (.letE name type value body nonDep hash) before
      (rawRun (compileExprTotalStep compile (.letE name type value body nonDep hash)) context before) := by
  rw [let_step_eq]
  apply name_then_checked cx base param self related bindings _ name _ context before good aligned
  intro named namedGood
  rw [rawRun_bind]
  have typeResult := typeCorrect named namedGood
  cases ranType : rawRun (compile type) context named with
  | mk outcome typed =>
    rw [ranType] at typeResult
    cases outcome with
    | error error => exact ⟨typeResult.1, typeResult.2.1, by intro result bad; cases bad⟩
    | ok targetType =>
      dsimp only
      rw [rawRun_bind]
      have valueResult := valueCorrect typed typeResult.1
      cases ranValue : rawRun (compile value) context typed with
      | mk outcome valued =>
        rw [ranValue] at valueResult
        have firstGrowth := extends_trans typeResult.2.1 valueResult.2.1
        cases outcome with
        | error error => exact ⟨valueResult.1, firstGrowth, by intro result bad; cases bad⟩
        | ok targetValue =>
          dsimp only
          rw [rawRun_bind]
          have bodyResult := bodyCorrect valued valueResult.1
          cases ranBody : rawRun (compile body) context valued with
          | mk outcome bodied =>
            rw [ranBody] at bodyResult
            have growth := extends_trans firstGrowth bodyResult.2.1
            cases outcome with
            | error error => exact ⟨bodyResult.1, growth, by intro result bad; cases bad⟩
            | ok targetBody =>
              have typeRead := meaning_grows cx base param self related
                (extends_trans valueResult.2.1 bodyResult.2.1) (typeResult.2.2 targetType rfl)
              have valueRead := meaning_grows cx base param self related bodyResult.2.1 (valueResult.2.2 targetValue rfl)
              have finished := finishLet_checked cx base param self related bindings name type value body nonDep hash
                targetType targetValue targetBody context bodied bodyResult.1 typeRead valueRead
                (bodyResult.2.2 targetBody rfl) congruent
              exact ⟨finished.1, extends_trans growth finished.2.1, finished.2.2⟩

/-- Memo insertion preserves both the state invariant and the accumulated
reader extension. Cache hits retain the original state and its reading. -/
theorem cached_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Expr)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (step : before.exprCache.get? source = none →
      Checked cx base param self related bindings source before (rawRun (compile source) context before)) :
    Checked cx base param self related bindings source before (rawRun (ExpressionRuntime.cached compile source) context before) := by
  have correct := cached_correct (StateSound bindings) (state_cacheBlind bindings) meaning
    (ExpressionRead.reading_cache_blind related cx base param self) compile source context before good.1 good.2
    (fun missing => ⟨(step missing).1.1, (step missing).1.2, (step missing).2.2⟩)
  refine ⟨⟨correct.1, correct.2.1⟩, ?_, correct.2.2⟩
  simp only [ExpressionRuntime.cached, rawRun_bind, rawRun_get]
  cases found : before.exprCache.get? source with
  | some value => exact extends_refl _
  | none =>
    have growth := (step found).2.1
    simp only [rawRun_bind]
    cases ran : rawRun (compile source) context before with
    | mk outcome after =>
      rw [ran] at growth
      cases outcome with
      | error error => exact growth
      | ok value =>
        cases value with
        | mk expr root =>
          simp only [rawRun_modify, rawRun_pure]
          exact growth

theorem partial_checked (source : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before)
    (step : before.exprCache.get? source = none → Checked cx base param self related bindings source before
      (rawRun (compileExprTotalStep compileExprPartial source) context before)) :
    Checked cx base param self related bindings source before (rawRun (compileExprPartial source) context before) := by
  rw [ExpressionRuntime.partial_unfold]
  exact cached_checked cx base param self related bindings (compileExprTotalStep compileExprPartial) source context before good step

/-- Domain-aware induction for the actual compiler. The caller must supply
an independently defined source domain and establish each constructor rule;
the result includes preservation of earlier expression readings on errors. -/
theorem partial_checked_of_step (domain : Ix.Expr → Prop) (context : CompileEnv × BlockEnv)
    (step : ∀ source, domain source →
      (∀ child, exprCompileDepth child < exprCompileDepth source → domain child →
        ∀ before, Good cx base param self related bindings before →
          Checked cx base param self related bindings child before (rawRun (compileExprPartial child) context before)) →
      ∀ before, Good cx base param self related bindings before → before.exprCache.get? source = none →
        Checked cx base param self related bindings source before
          (rawRun (compileExprTotalStep compileExprPartial source) context before)) :
    ∀ source, domain source → ∀ before, Good cx base param self related bindings before →
      Checked cx base param self related bindings source before (rawRun (compileExprPartial source) context before) := by
  intro source
  induction source using (measure exprCompileDepth).wf.induction with
  | h source ih =>
    intro supported before good
    exact partial_checked cx base param self related bindings source context before good (step source supported ih before good)

def finishProjection (name : Ix.Name) (reference field : UInt64) (value : Ixon.Expr × UInt64) :
    CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.prj name.getHash value.2)
  pure (.prj reference field value.1, root)

theorem finishProjection_checked (source : Ix.Expr) (name : Ix.Name) (reference field : UInt64)
    (value : Ixon.Expr × UInt64) (target : Kernel.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (rel : related source target)
    (read : (reader before).read (.prj reference field value.1) = .ok target) :
    Checked cx base param self related bindings source before
      (rawRun (finishProjection name reference field value) context before) := by
  let after := { before with arena := { nodes := before.arena.nodes.push (.prj name.getHash value.2) } }
  change Checked cx base param self related bindings source before
    (.ok (.prj reference field value.1, before.arena.nodes.size.toUInt64), after)
  have frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := rfl
  refine ⟨good_metadata cx base param self related bindings frame good, extends_refl _, ?_⟩
  intro result success
  cases Except.ok.inj success
  exact ⟨target, rel, read⟩

theorem projection_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address) :
    compileExprTotalStep compile (.proj name field source hash) = (do
      let slot ← checkedTableIndex "projection field" field
      compileName name
      let address ← lookupConstAddr name
      let reference ← internRef address
      let value ← compile source
      finishProjection name reference slot value) := rfl

theorem projection_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (names : Ix.Name → Kernel.Name → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (childCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings source state (rawRun (compile source) context state))
    (projectionRelated : ∀ targetName target, names name targetName → related source target →
      related (.proj name field source hash) (.proj targetName field target)) :
    Checked cx base param self related bindings (.proj name field source hash) before
      (rawRun (compileExprTotalStep compile (.proj name field source hash)) context before) := by
  rw [projection_step_eq, rawRun_bind]
  have unchanged := Interning.checkedTableIndex_state "projection field" field context before
  cases checked : rawRun (checkedTableIndex "projection field" field) context before with
  | mk outcome checkedState =>
    rw [checked] at unchanged
    dsimp only at unchanged
    subst checkedState
    cases outcome with
    | error error => exact ⟨good, extends_refl _, by intro result bad; cases bad⟩
    | ok slot =>
      have slotValue := (Interning.checkedTableIndex_value "projection field" field context before (congrArg Prod.fst checked)).1
      dsimp only
      apply name_then_checked cx base param self related bindings _ name _ context before good aligned
      intro named namedGood
      rw [rawRun_bind]
      have nameFrame := lookupConstAddr_state name context named
      cases looked : rawRun (lookupConstAddr name) context named with
      | mk outcome foundState =>
        rw [looked] at nameFrame
        dsimp only at nameFrame
        subst foundState
        cases outcome with
        | error error => exact ⟨namedGood, extends_refl _, by intro result bad; cases bad⟩
        | ok address =>
          obtain ⟨ref, resolved, nameRel⟩ := lookupConstAddr_correct name context named bindings namedGood.1.2.2.2
            cx names external (congrArg Prod.fst looked)
          dsimp only
          rw [rawRun_bind]
          have interned := internRef_good cx base param self related bindings address context named namedGood
          cases internRun : rawRun (internRef address) context named with
          | mk outcome referenced =>
            rw [internRun] at interned
            cases outcome with
            | error error => exact ⟨interned.1, interned.2.1, by intro result bad; cases bad⟩
            | ok reference =>
              have readRef := blockReader_ref cx base param self referenced (interned.2.2 reference rfl) resolved
              dsimp only
              rw [rawRun_bind]
              have child := childCorrect referenced interned.1
              cases childRun : rawRun (compile source) context referenced with
              | mk outcome afterChild =>
                rw [childRun] at child
                have growth := extends_trans interned.2.1 child.2.1
                cases outcome with
                | error error => exact ⟨child.1, growth, by intro result bad; cases bad⟩
                | ok value =>
                  obtain ⟨target, targetRel, readTarget⟩ := child.2.2 value rfl
                  have retainedRef := child.2.1.ref reference ref readRef
                  have finished := finishProjection_checked cx base param self related bindings _ name reference slot value
                    (.proj (cx.nameOf ref) field target) context afterChild child.1 (projectionRelated _ _ nameRel targetRel) (by
                      change (do
                        let resolvedRef ← (reader afterChild).ecx.refAt reference
                        pure (Kernel.Expr.proj (cx.nameOf resolvedRef) slot.toNat (← (reader afterChild).read value.1))) = _
                      rw [retainedRef, slotValue, readTarget]
                      rfl)
                  exact ⟨finished.1, extends_trans growth finished.2.1, finished.2.2⟩

def finishLiteral (wire : UInt64 → Ixon.Expr) (index : UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode .leaf
  pure (wire index, root)

theorem finishLiteral_checked (source : Ix.Expr) (wire : UInt64 → Ixon.Expr) (index : UInt64)
    (target : Kernel.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (rel : related source target)
    (read : (reader before).read (wire index) = .ok target) :
    Checked cx base param self related bindings source before (rawRun (finishLiteral wire index) context before) := by
  let after := { before with arena := { nodes := before.arena.nodes.push .leaf } }
  change Checked cx base param self related bindings source before
    (.ok (wire index, before.arena.nodes.size.toUInt64), after)
  have frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := rfl
  refine ⟨good_metadata cx base param self related bindings frame good, extends_refl _, ?_⟩
  intro result success
  cases Except.ok.inj success
  exact ⟨target, rel, read⟩

def compileLiteral (bytes : ByteArray) (wire : UInt64 → Ixon.Expr) : CompileM (Ixon.Expr × UInt64) := do
  let address ← storeBlob bytes
  let index ← internRef address
  finishLiteral wire index

theorem literal_checked (source : Ix.Expr) (bytes : ByteArray) (wire : UInt64 → Ixon.Expr)
    (target : Kernel.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (rel : related source target)
    (decode : ∀ state index, (reader state).ecx.blobAt index = .ok bytes →
      (reader state).read (wire index) = .ok target) :
    Checked cx base param self related bindings source before (rawRun (compileLiteral bytes wire) context before) := by
  unfold compileLiteral
  rw [rawRun_bind]
  have blob := storeBlob_good cx base param self related bindings bytes context before good aligned
  cases blobRun : rawRun (storeBlob bytes) context before with
  | mk outcome stored =>
    rw [blobRun] at blob
    cases outcome with
    | error error => exact ⟨blob.1, blob.2.1, by intro result bad; cases bad⟩
    | ok address =>
      dsimp only
      rw [rawRun_bind]
      have reference := internRef_good cx base param self related bindings address context stored blob.1
      have frame := internRef_frame address context stored
      cases refRun : rawRun (internRef address) context stored with
      | mk outcome referenced =>
        rw [refRun] at reference frame
        have growth := extends_trans blob.2.1 reference.2.1
        cases outcome with
        | error error => exact ⟨reference.1, growth, by intro result bad; cases bad⟩
        | ok index =>
          have sameBlobs := congrArg BlockState.blockBlobs frame
          change referenced.blockBlobs = stored.blockBlobs at sameBlobs
          have bytesFound : referenced.blockBlobs.get? address = some bytes := by
            rw [sameBlobs]
            exact blob.2.2 address rfl
          have reads := blockReader_blob cx base param self referenced (reference.2.2 index rfl) bytesFound
          have finished := finishLiteral_checked cx base param self related bindings source wire index target context referenced
            reference.1 rel (decode referenced index reads)
          exact ⟨finished.1, extends_trans growth finished.2.1, finished.2.2⟩

theorem nat_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (value : Nat) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (rel : related (.lit (.natVal value) hash) (.lit (.natVal value))) :
    Checked cx base param self related bindings (.lit (.natVal value) hash) before
      (rawRun (compileExprTotalStep compile (.lit (.natVal value) hash)) context before) := by
  change Checked cx base param self related bindings (.lit (.natVal value) hash) before
    (rawRun (compileLiteral (ByteArray.mk (Nat.toBytesLE value)) .nat) context before)
  apply literal_checked cx base param self related bindings _ _ _ _ context before good aligned rel
  intro state index read
  change (do pure (Kernel.Expr.lit (.natVal (Kernel.Reader.natural (← (reader state).ecx.blobAt index))))) = _
  rw [read]
  simp only [bind, Except.bind, pure, Except.pure, natural_toBytes]

theorem string_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (value : String) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (rel : related (.lit (.strVal value) hash) (.lit (.strVal value))) :
    Checked cx base param self related bindings (.lit (.strVal value) hash) before
      (rawRun (compileExprTotalStep compile (.lit (.strVal value) hash)) context before) := by
  change Checked cx base param self related bindings (.lit (.strVal value) hash) before
    (rawRun (compileLiteral value.toUTF8 .str) context before)
  apply literal_checked cx base param self related bindings _ _ _ _ context before good aligned rel
  intro state index read
  change (do
    let bytes ← (reader state).ecx.blobAt index
    let some text := String.fromUTF8? bytes | Kernel.Reader.malformed "string literal is not valid UTF-8"
    pure (Kernel.Expr.lit (.strVal text))) = _
  rw [read]
  simp only [bind, Except.bind, pure, Except.pure, string_toBytes]


end Constructors

end Ix.CompileCert.ExpressionState
