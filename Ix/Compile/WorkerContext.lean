module

public import Ix.CompileM
import all Ix.CompileM
import Init.Data.Array.Monadic
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.SolveByElim

/-! # The environment read by a block worker

Workers read source declarations, primary addresses, ambient blobs and sharing
limits. Output registries and accounting belong to the driver. The frame
proofs below preserve both the outcome and the complete local state, including
on refusals, when those four inputs agree. This permits projecting the worker
snapshot before spawning tasks without changing compilation or error order.
-/

public section

namespace Ix.Compile.WorkerContext

open Ix.CompileM

/-- Exact agreement on every global input observed by block compilation. -/
structure SameReads (left right : CompileEnv) : Prop where
  env : left.env = right.env
  addresses : left.nameToAddr = right.nameToAddr
  blobs : left.blobs = right.blobs
  sharing : left.sharingLimits = right.sharingLimits

/-- Keep the worker's inputs and release the driver's output-only fields. -/
@[expose] def project (env : CompileEnv) : CompileEnv :=
  { CompileEnv.new env.env with
    nameToAddr := env.nameToAddr, blobs := env.blobs, sharingLimits := env.sharingLimits }

theorem project_same (env : CompileEnv) : SameReads env (project env) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Include the local state retained on failures in the comparison. -/
def run (action : CompileM α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    Except CompileError α × BlockState := (action context).run state

theorem run_bind (action : CompileM α) (next : α → CompileM β)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    run (action >>= next) context state =
      match run action context state with
      | (.ok value, after) => run (next value) context after
      | (.error error, after) => (.error error, after) := by
  rcases result : (action context).run state with ⟨outcome, after⟩
  change action context state = (outcome, after) at result
  cases outcome <;>
    simp [run, ExceptT.run, ExceptT.mk, bind, ReaderT.bind, ExceptT.bind, StateT.bind,
      ExceptT.bindCont, pure, StateT.pure, result]

/-- Changing output-only environment fields changes no part of a run. -/
def Stable (action : CompileM α) : Prop :=
  ∀ left right, SameReads left right → ∀ block state,
    run action (left, block) state = run action (right, block) state

theorem Stable.pure (value : α) : Stable (pure value) := by
  intro left right same block state; rfl
theorem Stable.throw (error : CompileError) : Stable (throw error : CompileM α) := by
  intro left right same block state; rfl
theorem Stable.get : Stable getBlockState := by
  intro left right same block state; rfl
theorem Stable.read : Stable getBlockEnv := by
  intro left right same block state; rfl
theorem Stable.modify (update : BlockState → BlockState) : Stable (modifyBlockState update) := by
  intro left right same block state; rfl
theorem Stable.modifyGet (update : BlockState → α × BlockState) : Stable (modifyGetBlockState update) := by
  intro left right same block state; rfl

theorem Stable.applyState (result : Except CompileError BlockState) : Stable (applyBlockState result) := by
  cases result <;> intro left right same block state <;> rfl

theorem Stable.liftSharing (result : Except CompileError Ixon.Constant) : Stable (liftSharing result) := by
  cases result <;> intro left right same block state <;> rfl

theorem Stable.bind {action : CompileM α} {next : α → CompileM β}
    (first : Stable action) (later : ∀ value, Stable (next value)) : Stable (action >>= next) := by
  intro left right same block state
  rw [run_bind, run_bind, first left right same]
  cases run action (right, block) state with
  | mk outcome after =>
    cases outcome with
    | error error => rfl
    | ok value => exact later value left right same block after

theorem Stable.map (f : α → β) {action : CompileM α} (stable : Stable action) :
    Stable (f <$> action) :=
  Stable.bind stable (fun value => Stable.pure (f value))

theorem Stable.discard {action : CompileM α} (stable : Stable action) : Stable (discard action) := by
  change Stable ((fun _ => PUnit.unit) <$> action)
  exact Stable.map _ stable

theorem Stable.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α}
    (stable : Stable action) : Stable (withBlockEnv update action) := by
  intro left right same block state
  exact stable left right same (update block) state

theorem Stable.mapM_list (items : List α) (action : α → CompileM β)
    (stable : ∀ item ∈ items, Stable (action item)) : Stable (items.mapM action) := by
  induction items with
  | nil => exact Stable.pure []
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply Stable.bind (stable item (by simp))
    intro value
    apply Stable.bind (ih (fun item mem => stable item (List.mem_cons_of_mem _ mem)))
    intro values
    exact Stable.pure (value :: values)

theorem Stable.mapM_array (items : Array α) (action : α → CompileM β)
    (stable : ∀ item ∈ items, Stable (action item)) : Stable (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Stable.map _ (Stable.mapM_list items.toList action (fun item mem => stable item (by simpa using mem)))

theorem Stable.forIn'_list (items : List α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (stable : ∀ item mem acc, Stable (body item mem acc)) :
    Stable (forIn' items initial body) := by
  induction items generalizing initial with
  | nil => exact Stable.pure initial
  | cons item rest ih =>
    rw [List.forIn'_cons]
    apply Stable.bind (stable item (by simp) initial)
    intro result
    cases result with
    | done value => exact Stable.pure value
    | yield value => exact ih value _ (fun item mem acc => stable item _ acc)

theorem Stable.forIn'_array (items : Array α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (stable : ∀ item mem acc, Stable (body item mem acc)) :
    Stable (forIn' items initial body) := by
  have listStable := Stable.forIn'_list items.toList initial
    (fun item mem acc => body item (Array.mem_toList_iff.mp mem) acc)
    (fun item mem acc => stable item _ acc)
  simpa only [Array.forIn'_toList] using listStable

theorem Stable.forIn_list (items : List α) (initial : β)
    (body : α → β → CompileM (ForInStep β)) (stable : ∀ item acc, Stable (body item acc)) :
    Stable (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Stable.pure initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Stable.bind (stable item initial)
    intro result
    cases result with
    | done value => exact Stable.pure value
    | yield value => exact ih value

theorem Stable.forIn_array (items : Array α) (initial : β)
    (body : α → β → CompileM (ForInStep β)) (stable : ∀ item acc, Stable (body item acc)) :
    Stable (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact Stable.forIn_list items.toList initial body stable

theorem lookupConstAddr_stable (name : Ix.Name) : Stable (lookupConstAddr name) := by
  intro left right same block state
  change run (match state.blockNameToAddr.get? name with
      | some address => pure address
      | none => match left.nameToAddr.get? name with
        | some address => pure address
        | none => throw (CompileError.missingConstant s!"{name}")) (left, block) state =
    run (match state.blockNameToAddr.get? name with
      | some address => pure address
      | none => match right.nameToAddr.get? name with
        | some address => pure address
        | none => throw (CompileError.missingConstant s!"{name}")) (right, block) state
  rw [same.addresses]
  cases state.blockNameToAddr.get? name <;> cases right.nameToAddr.get? name <;> rfl

theorem findConst_stable (name : Ix.Name) : Stable (findConst name) := by
  intro left right same block state
  change run (match left.env.get? name with
      | some constant => pure constant
      | none => throw (CompileError.missingConstant s!"{name}")) (left, block) state =
    run (match right.env.get? name with
      | some constant => pure constant
      | none => throw (CompileError.missingConstant s!"{name}")) (right, block) state
  rw [same.env]
  cases right.env.get? name <;> rfl

theorem storeBlob_stable (bytes : ByteArray) : Stable (storeBlob bytes) := by
  intro left right same block state
  change run (applyBlockState (state.storeBlob left.blobs (Address.admissionHash bytes) bytes) >>= fun _ =>
    pure (Address.admissionHash bytes)) (left, block) state =
    run (applyBlockState (state.storeBlob right.blobs (Address.admissionHash bytes) bytes) >>= fun _ =>
      pure (Address.admissionHash bytes)) (right, block) state
  rw [same.blobs]
  exact Stable.bind (Stable.applyState _) (fun _ => Stable.pure _) left right same block state

theorem compileName_stable (name : Ix.Name) : Stable (compileName name) := by
  intro left right same block state
  change run (applyBlockState (state.compileName left.blobs name)) (left, block) state =
    run (applyBlockState (state.compileName right.blobs name)) (right, block) state
  rw [same.blobs]
  exact Stable.applyState _ left right same block state

theorem compileNames_stable (names : Array Ix.Name) : Stable (compileNames names) := by
  intro left right same block state
  change run (applyBlockState (state.compileNames left.blobs names)) (left, block) state =
    run (applyBlockState (state.compileNames right.blobs names)) (right, block) state
  rw [same.blobs]
  exact Stable.applyState _ left right same block state

theorem buildBlockConstant_stable (info : Ixon.ConstantInfo) (refs : Array Address)
    (univs : Array Ixon.Univ) : Stable (buildBlockConstant info refs univs) := by
  intro left right same block state
  change run (liftSharing (buildConstantWithSharing left.sharingLimits info refs univs))
    (left, block) state = run (liftSharing (buildConstantWithSharing right.sharingLimits info refs univs))
      (right, block) state
  rw [same.sharing]
  exact Stable.liftSharing _ left right same block state

scoped macro "stable_step" : tactic => `(tactic|
  first
    | assumption
    | exact Stable.pure _
    | exact Stable.throw _
    | exact Stable.get
    | exact Stable.read
    | exact Stable.modify _
    | exact Stable.modifyGet _
    | exact Stable.applyState _
    | exact Stable.liftSharing _
    | exact lookupConstAddr_stable _
    | exact findConst_stable _
    | exact storeBlob_stable _
    | exact compileName_stable _
    | exact compileNames_stable _
    | exact buildBlockConstant_stable _ _ _
    | apply Stable.discard
    | refine Stable.bind ?_ (fun _ => ?_)
    | refine Stable.mapM_array _ _ (fun _ _ => ?_)
    | refine Stable.forIn'_array _ _ _ (fun _ _ _ => ?_)
    | refine Stable.forIn_array _ _ _ (fun _ _ => ?_)
    | apply Stable.withBlockEnv
    | unfold checkedTableIndex
    | unfold checkedTableCount
    | dsimp only
    | split)

scoped macro "stable_steps" : tactic => `(tactic| with_reducible repeat' stable_step)

theorem compileUniv_stable (source : Ix.Level) : Stable (compileUniv source) := by
  induction source <;> rw [compileUniv]
  all_goals stable_steps

theorem internUniv_stable (value : Ixon.Univ) : Stable (internUniv value) := by
  unfold internUniv
  stable_steps

theorem canonUnivCached_stable (value : Ixon.Univ) : Stable (canonUnivCached value) := by
  unfold canonUnivCached
  stable_steps

theorem internMetaUniv_stable (value : Ixon.Univ) : Stable (internMetaUniv value) := by
  unfold internMetaUniv
  stable_steps

theorem compileAndInternUnivCanon_stable (source : Ix.Level) :
    Stable (compileAndInternUnivCanon source) := by
  unfold compileAndInternUnivCanon
  with_reducible repeat' first
    | exact compileUniv_stable _
    | exact canonUnivCached_stable _
    | exact internUniv_stable _
    | exact internMetaUniv_stable _
    | stable_step

theorem internRef_stable (address : Address) : Stable (internRef address) := by
  unfold internRef
  stable_steps

theorem allocArenaNode_stable (node : Ixon.ExprMetaData) : Stable (allocArenaNode node) := by
  unfold allocArenaNode
  stable_steps

theorem takeArena_stable : Stable takeArena := by
  unfold takeArena
  stable_steps

theorem resetArena_stable : Stable resetArena := by
  unfold resetArena
  stable_steps

theorem clearExprCache_stable : Stable clearExprCache := by
  unfold clearExprCache
  stable_steps

theorem pushUnivPatch_stable (arenaIdx : UInt64) (univIdxs : Array UInt64) :
    Stable (pushUnivPatch arenaIdx univIdxs) := by
  unfold pushUnivPatch
  stable_steps

theorem takeUnivPatches_stable : Stable takeUnivPatches := by
  unfold takeUnivPatches
  stable_steps

theorem recordDefHints_stable (name : Ix.Name) (hints : Lean.ReducibilityHints) :
    Stable (recordDefHints name hints) := by
  unfold recordDefHints
  stable_steps

theorem Stable.withUnivCtx (params : List Ix.Name) {action : CompileM α}
    (stable : Stable action) : Stable (Ix.CompileM.withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  exact Stable.bind (Stable.modify _) (fun _ => stable.withBlockEnv _)

scoped macro "core_step" : tactic => `(tactic|
  first
    | exact compileUniv_stable _
    | exact internUniv_stable _
    | exact canonUnivCached_stable _
    | exact internMetaUniv_stable _
    | exact compileAndInternUnivCanon_stable _
    | exact internRef_stable _
    | exact allocArenaNode_stable _
    | exact takeArena_stable
    | exact resetArena_stable
    | exact clearExprCache_stable
    | exact pushUnivPatch_stable _ _
    | exact takeUnivPatches_stable
    | exact recordDefHints_stable _ _
    | apply Stable.withUnivCtx
    | stable_step)

scoped macro "core_steps" : tactic => `(tactic| with_reducible repeat' core_step)

theorem storeString_stable (value : String) : Stable (storeString value) :=
  storeBlob_stable _

theorem serializeIxSubstring_stable (value : Ix.Substring) : Stable (serializeIxSubstring value) := by
  unfold serializeIxSubstring
  exact Stable.bind (storeString_stable _) (fun _ => Stable.pure _)

theorem serializeIxSourceInfo_stable (value : Ix.SourceInfo) : Stable (serializeIxSourceInfo value) := by
  cases value <;> unfold serializeIxSourceInfo
  all_goals with_reducible repeat' first
    | exact serializeIxSubstring_stable _
    | core_step

theorem serializeIxSyntaxPreresolved_stable (value : Ix.SyntaxPreresolved) :
    Stable (serializeIxSyntaxPreresolved value) := by
  cases value <;> unfold serializeIxSyntaxPreresolved
  all_goals with_reducible repeat' first
    | exact storeString_stable _
    | core_step

theorem serializeIxSyntax_stable (source : Ix.Syntax) : Stable (serializeIxSyntax source) := by
  induction source using (measure (fun value : Ix.Syntax => sizeOf value)).wf.induction with
  | h source ih =>
    cases source <;> rw [serializeIxSyntax]
    all_goals with_reducible repeat' first
      | exact serializeIxSourceInfo_stable _
      | exact serializeIxSubstring_stable _
      | exact serializeIxSyntaxPreresolved_stable _
      | exact storeString_stable _
      | core_step
    apply ih
    rename_i arg member
    exact Nat.lt_trans (Array.sizeOf_lt_of_mem arg.property) (by simp; omega)

theorem compileDataValue_stable (value : Ix.DataValue) : Stable (compileDataValue value) := by
  cases value <;> unfold compileDataValue
  all_goals with_reducible repeat' first
    | exact serializeIxSyntax_stable _
    | core_step

theorem compileKVMap_stable (values : Array (Ix.Name × Ix.DataValue)) : Stable (compileKVMap values) := by
  unfold compileKVMap
  with_reducible repeat' first
    | exact compileDataValue_stable _
    | core_step

theorem compileExprStep_stable (source : Ix.Expr)
    (compile : (child : Ix.Expr) → sizeOf child < sizeOf source → CompileM (Ixon.Expr × UInt64))
    (stable : ∀ child smaller, Stable (compile child smaller)) :
    Stable (compileExprStep source compile) := by
  cases source
  case' lit literal hash => cases literal
  all_goals unfold compileExprStep
  all_goals with_reducible repeat' first
    | exact stable _ _
    | exact compileKVMap_stable _
    | core_step

theorem compileExpr_stable (source : Ix.Expr) : Stable (compileExpr source) := by
  induction source using (measure (fun value : Ix.Expr => sizeOf value)).wf.induction with
  | h source ih =>
    rw [compileExpr]
    core_steps
    exact compileExprStep_stable source (fun child _ => compileExpr child)
      (fun child smaller => ih child smaller)

theorem collectExprTableUnivs_stable (sources : List Ix.Level) (initial : Array Ixon.Univ) :
    Stable (collectExprTableUnivs sources initial) := by
  induction sources generalizing initial with
  | nil => exact Stable.pure _
  | cons source rest ih =>
    rw [collectExprTableUnivs]
    exact Stable.bind (compileUniv_stable source) (fun value => ih (initial.push value))

theorem collectExprTablesStructural_stable (key : Address) (mutCtx : Ix.MutCtx)
    (params : List Ix.Name) (source : Ix.Expr) (initial : ExprTableCollection) :
    Stable (collectExprTablesStructural key mutCtx params source initial) := by
  obtain ⟨refs, univs, seen⟩ := initial
  induction source generalizing refs univs seen
  case' lit literal hash => cases literal
  all_goals rw [collectExprTablesStructural]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact collectExprTableUnivs_stable _ _
    | core_step

theorem collectExprTables_stable (source : Ix.Expr) (key : Address) (initial : ExprTableCollection) :
    Stable (collectExprTables source key initial) := by
  unfold collectExprTables
  with_reducible repeat' first
    | exact collectExprTablesStructural_stable _ _ _ _ _
    | core_step

theorem collectPreseedExprs_stable (sources : List (Ix.Expr × List Ix.Name))
    (initial : ExprTableCollection) : Stable (collectPreseedExprs sources initial) := by
  induction sources generalizing initial with
  | nil => exact Stable.pure _
  | cons source rest ih =>
    obtain ⟨expr, params⟩ := source
    rw [collectPreseedExprs]
    exact Stable.bind ((collectExprTables_stable _ _ _).withUnivCtx params) (fun result => ih result)

theorem internPreseedRefs_stable (refs : List Address) (previous : Option Address) :
    Stable (internPreseedRefs refs previous) := by
  induction refs generalizing previous <;> rw [internPreseedRefs]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | core_step

theorem canonPreseedUnivs_stable (univs : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Stable (canonPreseedUnivs univs initial) := by
  induction univs generalizing initial <;> rw [canonPreseedUnivs]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | core_step

theorem internPreseedUnivs_stable (univs : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    Stable (internPreseedUnivs univs previous) := by
  induction univs generalizing previous with
  | nil => exact Stable.pure _
  | cons entry rest ih =>
    obtain ⟨key, univ⟩ := entry
    rw [internPreseedUnivs]
    with_reducible repeat' first
      | exact ih _
      | core_step

theorem preseedExprTables_stable (sources : Array (Ix.Expr × List Ix.Name)) :
    Stable (preseedExprTables sources) := by
  unfold preseedExprTables
  with_reducible repeat' first
    | exact collectPreseedExprs_stable _ _
    | exact internPreseedRefs_stable _ _
    | exact canonPreseedUnivs_stable _ _
    | exact internPreseedUnivs_stable _ _
    | unfold checkPreseedUnivs
    | core_step

theorem internalIndexError_stable (what : String) (index size : Nat) :
    Stable (internalIndexError (α := α) what index size) := by
  unfold internalIndexError
  core_steps

theorem arrIdx_stable (values : Array α) (index : Nat) (what : String) :
    Stable (arrIdx values index what) := by
  unfold arrIdx
  with_reducible repeat' first
    | exact internalIndexError_stable _ _ _
    | core_step

theorem getMutCtxAddrs_stable : Stable getMutCtxAddrs := by
  unfold getMutCtxAddrs
  core_steps

scoped macro "declaration_step" : tactic => `(tactic|
  first
    | exact compileExpr_stable _
    | exact preseedExprTables_stable _
    | exact internalIndexError_stable _ _ _
    | exact arrIdx_stable _ _ _
    | exact getMutCtxAddrs_stable
    | unfold withCurrent
    | unfold withMutCtx
    | unfold withAll
    | core_step)

scoped macro "declaration_steps" : tactic => `(tactic| with_reducible repeat' declaration_step)

theorem finishDefinitionDataCompilation_stable (value : Ix.Def)
    (typ : Ixon.Expr) (tyRoot : UInt64) (body : Ixon.Expr) (bodyRoot : UInt64) :
    Stable (finishDefinitionDataCompilation value typ tyRoot body bodyRoot) := by
  unfold finishDefinitionDataCompilation
  declaration_steps

theorem finishAxiomCompilation_stable (value : Ix.AxiomVal) (typ : Ixon.Expr) (root : UInt64) :
    Stable (finishAxiomCompilation value typ root) := by
  unfold finishAxiomCompilation
  declaration_steps

theorem finishQuotientCompilation_stable (value : Ix.QuotVal) (typ : Ixon.Expr) (root : UInt64) :
    Stable (finishQuotientCompilation value typ root) := by
  unfold finishQuotientCompilation
  declaration_steps

theorem finishConstructorCompilation_stable (value : Ix.ConstructorVal) (typ : Ixon.Expr) (root : UInt64) :
    Stable (finishConstructorCompilation value typ root) := by
  unfold finishConstructorCompilation
  declaration_steps

theorem finishRecursorCompilation_stable (value : Ix.RecursorVal) (typ : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) : Stable (finishRecursorCompilation value typ root rules) := by
  unfold finishRecursorCompilation
  declaration_steps

theorem finishInductiveCompilation_stable (value : Ix.InductiveVal) (typ : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (ctors : InductiveConstructorCompileState) :
    Stable (finishInductiveCompilation value typ root metadata ctors) := by
  unfold finishInductiveCompilation
  declaration_steps

theorem finishInductiveDataCompilation_stable (value : Ix.Ind) (typ : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (ctors : InductiveConstructorCompileState) :
    Stable (finishInductiveDataCompilation value typ root metadata ctors) := by
  unfold finishInductiveDataCompilation
  declaration_steps

theorem takeInductiveTypeCompileMeta_stable : Stable takeInductiveTypeCompileMeta := by
  unfold takeInductiveTypeCompileMeta
  declaration_steps

theorem compileRecursorRule_stable (value : Ix.RecursorRule) : Stable (compileRecursorRule value) := by
  unfold compileRecursorRule
  declaration_steps

theorem compileRecursorRules_stable (values : List Ix.RecursorRule) (initial : RecursorRuleCompileState) :
    Stable (compileRecursorRules values initial) := by
  induction values generalizing initial <;> rw [compileRecursorRules]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact compileRecursorRule_stable _
    | declaration_step

scoped macro "finish_step" : tactic => `(tactic|
  first
    | exact finishDefinitionDataCompilation_stable _ _ _ _ _
    | exact finishAxiomCompilation_stable _ _ _
    | exact finishQuotientCompilation_stable _ _ _
    | exact finishConstructorCompilation_stable _ _ _
    | exact finishRecursorCompilation_stable _ _ _ _
    | exact finishInductiveCompilation_stable _ _ _ _ _
    | exact finishInductiveDataCompilation_stable _ _ _ _ _
    | exact takeInductiveTypeCompileMeta_stable
    | exact compileRecursorRules_stable _ _
    | unfold finishDefinitionCompilation
    | unfold finishTheoremCompilation
    | unfold finishOpaqueCompilation
    | declaration_step)

scoped macro "finish_steps" : tactic => `(tactic| with_reducible repeat' finish_step)

theorem compileDefinition_stable (value : Ix.DefinitionVal) : Stable (compileDefinition value) := by
  unfold compileDefinition
  finish_steps

theorem compileDefinitionData_stable (value : Ix.Def) : Stable (compileDefinitionData value) := by
  unfold compileDefinitionData
  finish_steps

theorem compileAxiom_stable (value : Ix.AxiomVal) : Stable (compileAxiom value) := by
  unfold compileAxiom
  finish_steps

theorem compileQuotient_stable (value : Ix.QuotVal) : Stable (compileQuotient value) := by
  unfold compileQuotient
  finish_steps

theorem compileConstructor_stable (value : Ix.ConstructorVal) : Stable (compileConstructor value) := by
  unfold compileConstructor
  finish_steps

theorem compileRecursor_stable (value : Ix.RecursorVal) : Stable (compileRecursor value) := by
  unfold compileRecursor
  finish_steps

theorem compileInductiveConstructors_stable (values : List Ix.ConstructorVal)
    (initial : InductiveConstructorCompileState) : Stable (compileInductiveConstructors values initial) := by
  induction values generalizing initial <;> rw [compileInductiveConstructors]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact compileConstructor_stable _
    | finish_step

theorem compileInductive_stable (value : Ix.InductiveVal) (ctors : Array Ix.ConstructorVal) :
    Stable (compileInductive value ctors) := by
  unfold compileInductive
  with_reducible repeat' first
    | exact compileInductiveConstructors_stable _ _
    | finish_step

theorem compileInductiveData_stable (value : Ix.Ind) : Stable (compileInductiveData value) := by
  unfold compileInductiveData
  with_reducible repeat' first
    | exact compileInductiveConstructors_stable _ _
    | finish_step

theorem collectInductiveConstructors_stable (names : List Ix.Name) (initial : Array Ix.ConstructorVal) :
    Stable (collectInductiveConstructors names initial) := by
  induction names generalizing initial <;> rw [collectInductiveConstructors]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | finish_step

theorem collectMutConstConstructors_stable (names : List Ix.Name) (initial : Array Ix.ConstructorVal) :
    Stable (collectMutConstConstructors names initial) := by
  induction names generalizing initial <;> rw [collectMutConstConstructors]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | finish_step

theorem mkIndc_stable (value : Ix.InductiveVal) : Stable (Ix.CompileM.MutConst.mkIndc value) := by
  unfold Ix.CompileM.MutConst.mkIndc
  exact Stable.bind (collectMutConstConstructors_stable _ _) (fun _ => Stable.pure _)

theorem finishConstantWithSharing_stable (info : Ixon.ConstantInfo) (metadata : Ixon.ConstantMeta) :
    Stable (finishConstantWithSharing info metadata) := by
  unfold finishConstantWithSharing
  finish_steps

theorem finishInductiveFamilyBlock_stable (value : Ix.InductiveVal) (payload : Ixon.Inductive)
    (metadata : Ixon.ConstantMeta) (ctors : Array (Ix.Name × Ixon.ConstantMeta)) :
    Stable (finishInductiveFamilyBlock value payload metadata ctors) := by
  unfold finishInductiveFamilyBlock
  finish_steps

theorem compileInductiveInfo_stable (value : Ix.InductiveVal) : Stable (compileInductiveInfo value) := by
  unfold compileInductiveInfo lookupInductiveConstructors compileInductiveFamilyInfo compileInductiveFamilyBlock
  with_reducible repeat' first
    | exact collectInductiveConstructors_stable _ _
    | exact compileInductive_stable _ _
    | exact finishInductiveFamilyBlock_stable _ _ _ _
    | finish_step

theorem compileConstructorInfo_stable (value : Ix.ConstructorVal) : Stable (compileConstructorInfo value) := by
  unfold compileConstructorInfo
  with_reducible repeat' first
    | exact compileInductiveInfo_stable _
    | finish_step

theorem compileConstantInfo_stable (value : Ix.ConstantInfo) : Stable (compileConstantInfo value) := by
  cases value <;>
    simp only [compileConstantInfo, compileConstantInfoCore, compileDefinitionConstantInfo,
      compileTheoremConstantInfo, compileOpaqueConstantInfo, compileQuotientConstantInfo,
      compileRecursorConstantInfo, compileInductiveConstantInfo, compileConstructorConstantInfo,
      compileDefinitionInfo, compileDefinitionBlock, compileTheoremInfo, compileOpaqueInfo,
      compileDefinitionDataInfo, compileDefinitionDataBlock, compileAxiomInfo, compileAxiomBlock,
      compileQuotientInfo, compileQuotientBlock, compileRecursorInfo, compileRecursorBlock,
      finishConstantInfoWithSharing]
  all_goals with_reducible repeat' first
    | exact compileDefinition_stable _
    | exact compileDefinitionData_stable _
    | exact compileAxiom_stable _
    | exact compileQuotient_stable _
    | exact compileRecursor_stable _
    | exact compileInductiveInfo_stable _
    | exact compileConstructorInfo_stable _
    | exact finishConstantWithSharing_stable _ _
    | finish_step

theorem compileMutConstMember_stable (value : Ix.MutConst) : Stable (compileMutConstMember value) := by
  cases value <;> unfold compileMutConstMember
  all_goals with_reducible repeat' first
    | exact compileDefinitionData_stable _
    | exact compileInductiveData_stable _
    | exact compileRecursor_stable _
    | unfold compileRecursorData
    | finish_step

theorem compileMutConstMembers_stable (values : List Ix.MutConst) (initial : MutConstCompileState) :
    Stable (compileMutConstMembers values initial) := by
  induction values generalizing initial <;> rw [compileMutConstMembers]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact compileMutConstMember_stable _
    | finish_step

theorem compileMutConsts_stable (values : List Ix.MutConst) : Stable (compileMutConsts values) := by
  unfold compileMutConsts
  exact Stable.bind (compileMutConstMembers_stable _ _) (fun _ => Stable.pure _)

theorem checkMutConstArrayCounts_stable (value : Ixon.MutConst) : Stable (checkMutConstArrayCounts value) := by
  cases value <;> unfold checkMutConstArrayCounts
  all_goals finish_steps

theorem checkMutualPayloadCounts_stable (values : Array Ixon.MutConst) : Stable (checkMutualPayloadCounts values) := by
  unfold checkMutualPayloadCounts
  with_reducible repeat' first
    | exact checkMutConstArrayCounts_stable _
    | finish_step

theorem finishMutualCompilation_stable (sources : List Ix.MutConst)
    (payloads : Array Ixon.MutConst) (metas : Array (Ix.Name × Ixon.ConstantMeta)) :
    Stable (finishMutualCompilation sources payloads metas) := by
  unfold finishMutualCompilation
  apply Stable.bind (checkMutualPayloadCounts_stable _)
  intro _
  apply Stable.bind Stable.get
  intro cache left right same block state
  change run (match buildCompiledMutualBlock left.sharingLimits sources payloads metas cache with
      | .ok result => pure result
      | .error error => throw error) (left, block) state =
    run (match buildCompiledMutualBlock right.sharingLimits sources payloads metas cache with
      | .ok result => pure result
      | .error error => throw error) (right, block) state
  rw [same.sharing]
  cases buildCompiledMutualBlock right.sharingLimits sources payloads metas cache <;> rfl

theorem compileMutualBlock_stable (sources : List Ix.MutConst) : Stable (compileMutualBlock sources) := by
  unfold compileMutualBlock compileMutualPayload
  with_reducible repeat' first
    | exact compileMutConsts_stable _
    | exact finishMutualCompilation_stable _ _ _
    | finish_step

end Ix.Compile.WorkerContext
