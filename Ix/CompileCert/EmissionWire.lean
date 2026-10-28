import Ix.CompileCert.FinalUniverses
import Ix.CompileCert.PreseedWire

/-! # Successful compilation keeps the primary tables on the wire

The primary reference and universe tables of a block are representable by
the constant wire format (`Ix.Sharing.Verify.BlockWireTablesWF`) after every
successful run of the expression compiler and of every payload emitter,
when they were before and the preseed has finalized the universe table
(`Valid`):

* a universe compile after the final flag leaves the universe table as it
  was (`FinalUniverses.compile_no_growth`, the production guard);
* every reference the compiler interns is 32 bytes: the interner refuses
  any other width (`Interning.internRef_narrow`);
* the serializers, the metadata arena and the drains touch neither table.

The facts are success-only (`Safe`): a failing universe miss may write its
candidate before the guard refuses it, so wire validity is not an invariant
of every run (unlike `ExpressionState.Good`). This traversal follows the
well-founded expression compiler, with a successful preseed establishing
`Valid` (`seeded_valid`). -/

namespace Ix.CompileCert.EmissionWire

open Ix.CompileM Ix.CompileCert
open Ix.Sharing.Verify (BlockWireTablesWF)



/-- The primary tables are on the wire and the universe table is final. -/
def Valid (state : BlockState) : Prop :=
  BlockWireTablesWF state ∧ state.univsFinal = true

/-- The fields `Valid` reads. -/
def view (state : BlockState) :=
  (state.refs, state.univs, state.univsFinal)

theorem Valid.of_view {before after : BlockState}
    (valid : Valid before) (same : view after = view before) : Valid after := by
  simp only [view, Prod.mk.injEq] at same
  obtain ⟨refs, univs, flag⟩ := same
  exact ⟨WireTables.of_same valid.1 refs univs, flag.trans valid.2⟩

/-- Every successful run from a `Valid` state ends `Valid` and returns a value
satisfying `post`. -/
def Safe (action : CompileM α) (post : α → Prop := fun _ => True) : Prop :=
  ∀ (context : CompileEnv × BlockEnv) before value after, Valid before →
    rawRun action context before = (.ok value, after) → Valid after ∧ post value

/-! ## Combinators -/

theorem Safe.framed {action : CompileM α} (frame : Preserves view action) : Safe action := by
  intro context before value after valid ran
  have same := frame context before
  rw [ran] at same
  exact ⟨valid.of_view same, trivial⟩

theorem Safe.pure (value : α) : Safe (Pure.pure value : CompileM α) := Safe.framed (Preserves.pure _ _)

theorem Safe.returns {value : α} {post : α → Prop} (holds : post value) :
    Safe (Pure.pure value : CompileM α) post := by
  intro context before result after valid ran
  cases ran
  exact ⟨valid, holds⟩

theorem Safe.throw (error : CompileError) {post : α → Prop} : Safe (throw error : CompileM α) post := by
  intro context before value after valid ran
  cases ran

theorem Safe.bind {action : CompileM α} {next : α → CompileM β} {first : α → Prop} {last : β → Prop}
    (head : Safe action first) (tail : ∀ value, first value → Safe (next value) last) :
    Safe (action >>= next) last := by
  intro context before output after valid ran
  obtain ⟨middle, state, firstRan, lastRan⟩ := bind_ok ran
  have checked := head context before middle state valid firstRan
  exact tail middle checked.2 context state output after checked.1 lastRan

/-- A failure followed by anything. -/
theorem Safe.throwBind (error : CompileError) (next : α → CompileM β) {post : β → Prop} :
    Safe (MonadExceptOf.throw error >>= next) post :=
  Safe.bind (Safe.throw error (post := fun _ => False)) (fun _ impossible => impossible.elim)

theorem Safe.forget {action : CompileM α} {post : α → Prop} (safe : Safe action post) : Safe action := by
  intro context before value after valid ran
  exact ⟨(safe context before value after valid ran).1, trivial⟩

theorem Safe.seq {action : CompileM α} {next : α → CompileM β} {post : β → Prop}
    (head : Safe action) (tail : ∀ value, Safe (next value) post) : Safe (action >>= next) post :=
  Safe.bind head (fun value _ => tail value)

theorem Safe.get : Safe getBlockState := Safe.framed (Preserves.get _)
theorem Safe.readCompile : Safe getCompileEnv := Safe.framed (Preserves.readCompile _)
theorem Safe.readBlock : Safe getBlockEnv := Safe.framed (Preserves.read _)

theorem Safe.modify (update : BlockState → BlockState) (same : ∀ before, view (update before) = view before) :
    Safe (modifyBlockState update) := Safe.framed (Preserves.modify _ _ same)

theorem Safe.modifyGet (update : BlockState → α × BlockState)
    (same : ∀ before, view (update before).2 = view before) :
    Safe (modifyGetBlockState update) := Safe.framed (Preserves.modifyGet _ _ same)

theorem Safe.map {action : CompileM α} {post : α → Prop} (safe : Safe action post) (f : α → β) :
    Safe (f <$> action) := by
  rw [map_eq_pure_bind]
  exact Safe.bind safe (fun _ _ => Safe.pure _)

theorem Safe.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} {post : α → Prop}
    (safe : Safe action post) : Safe (withBlockEnv update action) post := by
  intro context before value after valid ran
  rw [rawRun_withBlockEnv] at ran
  exact safe (context.1, update context.2) before value after valid ran

theorem Safe.withCurrent (name : Ix.Name) {action : CompileM α} {post : α → Prop}
    (safe : Safe action post) : Safe (withCurrent name action) post := Safe.withBlockEnv _ safe

theorem Safe.withMutCtx (mutCtx : MutCtx) {action : CompileM α} {post : α → Prop}
    (safe : Safe action post) : Safe (withMutCtx mutCtx action) post := Safe.withBlockEnv _ safe

theorem Safe.withUnivCtx (params : List Ix.Name) {action : CompileM α} {post : α → Prop}
    (safe : Safe action post) : Safe (withUnivCtx params action) post := by
  unfold Ix.CompileM.withUnivCtx
  exact Safe.bind (Safe.modify _ (fun _ => rfl)) (fun _ _ => Safe.withBlockEnv _ safe)

theorem Safe.checkedIndex (table : String) (index : Nat) : Safe (checkedTableIndex table index) :=
  Safe.framed fun context before => by rw [Interning.checkedTableIndex_state]

theorem Safe.checkedCount (table : String) (count : Nat) : Safe (checkedTableCount table count) :=
  Safe.framed fun context before => by rw [Interning.checkedTableCount_state]

theorem Safe.mapM_list (items : List α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Safe (action item)) : Safe (items.mapM action) := by
  induction items with
  | nil => exact Safe.pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact Safe.seq (each item (by simp)) fun _ =>
      Safe.seq (ih (fun item member => each item (List.mem_cons_of_mem _ member))) fun _ => Safe.pure _

theorem Safe.mapM_array (items : Array α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Safe (action item)) : Safe (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Safe.map (Safe.mapM_list _ action (fun item member => each item (by simpa using member))) _

theorem Safe.forIn_list (items : List α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item ∈ items, ∀ acc, Safe (body item acc)) : Safe (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Safe.pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Safe.seq (each item (by simp) initial)
    intro step
    cases step with
    | done value => exact Safe.pure value
    | yield value => exact ih value (fun item member acc => each item (List.mem_cons_of_mem _ member) acc)

theorem Safe.forIn_array (items : Array α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item ∈ items, ∀ acc, Safe (body item acc)) : Safe (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact Safe.forIn_list _ initial body (fun item member acc => each item (by simpa using member) acc)

/-! ## The leaves -/

/-- A universe compile after the final flag keeps the tables (the production
guard), the bindings and the reference table. -/
theorem Safe.compileLevel (source : Ix.Level) : Safe (compileAndInternUnivCanon source) := by
  intro context before output after valid ran
  have frozen := FinalUniverses.compile_no_growth source context valid.2 ran
  have frame := UniversePipeline.compileAndInternUnivCanon_frame source context before
  rw [ran] at frame
  have refs : after.refs = before.refs := by have same := congrArg BlockState.refs frame; exact same
  exact ⟨⟨WireTables.of_same valid.1 refs frozen.1, frozen.2⟩, trivial⟩

/-- Interning an address keeps the tables on the wire (the interner refuses
an address that is not 32 bytes). -/
theorem Safe.internRef (address : Address) : Safe (internRef address) := by
  intro context before output after valid ran
  have wire := WireTables.internRef_preserves context before address valid.1
  have frame := ExpressionState.internRef_frame address context before
  rw [ran] at wire frame
  have flag : after.univsFinal = before.univsFinal := by
    have same := congrArg BlockState.univsFinal frame; exact same
  exact ⟨⟨wire, flag.trans valid.2⟩, trivial⟩

/-- Resolving a name leaves the state as it was. -/
theorem Safe.lookup (name : Ix.Name) : Safe (lookupConstAddr name) := by
  intro context before output after valid ran
  have same : after = before := by
    have state := ExpressionState.lookupConstAddr_state name context before
    rw [ran] at state
    exact state
  rw [same]
  exact ⟨valid, trivial⟩

/-- Storing a blob writes neither table. -/
theorem Safe.blob (bytes : ByteArray) : Safe (storeBlob bytes) := by
  intro context before output after valid ran
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  rw [ran] at frame
  have same := congrArg view frame
  exact ⟨valid.of_view same, trivial⟩

/-- A step that writes only names and blobs. -/
theorem Safe.namesBlobs {action : CompileM α} (framed : Serializers.NamesBlobs action) : Safe action :=
  Safe.framed (framed.preserves view (fun _ => rfl))

theorem Safe.compileName (name : Ix.Name) : Safe (compileName name) :=
  Safe.namesBlobs (Serializers.NamesBlobs.compileName name)

theorem Safe.compileNames (names : Array Ix.Name) : Safe (compileNames names) :=
  Safe.namesBlobs (Serializers.NamesBlobs.compileNames names)

theorem Safe.kvmap (data : Array (Ix.Name × Ix.DataValue)) : Safe (compileKVMap data) :=
  Safe.namesBlobs (Serializers.NamesBlobs.compileKVMap data)

theorem Safe.alloc (node : Ixon.ExprMetaData) : Safe (allocArenaNode node) := by
  unfold allocArenaNode
  exact Safe.modifyGet _ (fun _ => rfl)

theorem Safe.patch (root : UInt64) (indices : Array UInt64) : Safe (pushUnivPatch root indices) := by
  unfold pushUnivPatch
  exact Safe.modify _ (fun _ => rfl)

theorem Safe.finishReference (name : Ix.Name) (levels : Array (UInt64 × Option UInt64)) (value : Ixon.Expr) :
    Safe (ExpressionState.finishReference name levels value) := by
  unfold ExpressionState.finishReference
  refine Safe.seq (Safe.alloc _) fun _ => ?_
  split
  · exact Safe.seq (Safe.patch _ _) fun _ => Safe.pure _
  · exact Safe.pure _

/-! ## The expression compiler -/

/-- **One step keeps the tables on the wire** on success, given the same of
the recursive compile on every strict subterm. -/
theorem Safe.step (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Expr)
    (each : ∀ child, sizeOf child < sizeOf source → Safe (compile child)) :
    Safe (ExpressionState.step compile source) := by
  cases source with
  | bvar index hash =>
    rw [ExpressionState.bvar_step_eq]
    exact Safe.seq (Safe.checkedIndex _ _) fun _ => Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | sort level hash =>
    rw [ExpressionState.sort_step_eq]
    refine Safe.seq (Safe.compileLevel _) fun result => ?_
    obtain ⟨index, patch⟩ := result
    dsimp only
    unfold ExpressionState.finishSort
    refine Safe.seq (Safe.alloc _) fun _ => ?_
    split
    · exact Safe.seq (Safe.patch _ _) fun _ => Safe.pure _
    · exact Safe.pure _
  | const name levels hash =>
    rw [ExpressionState.const_step_eq, ExpressionState.compileConstExprRaw_eq]
    refine Safe.seq Safe.readBlock fun block => ?_
    dsimp only
    refine Safe.seq (Safe.mapM_array _ _ fun _ _ => Safe.compileLevel _) fun compiled =>
      Safe.seq (Safe.compileName _) fun _ => ?_
    unfold ExpressionState.constBody
    split
    · exact Safe.seq (Safe.checkedIndex _ _) fun _ => Safe.finishReference _ _ _
    · exact Safe.bind (Safe.lookup _) fun address _ =>
        Safe.seq (Safe.internRef address) fun _ => Safe.finishReference _ _ _
  | app fn arg hash =>
    rw [ExpressionState.app_step_eq]
    refine Safe.seq (each _ (Ix.CompileM.decomposeApps_app_head_lt fn arg hash)) (fun head => ?_)
    rw [forIn'_eq_forIn _ _ _ (fun x acc => ExpressionState.appBody compile acc x) (fun _ _ _ => rfl)]
    refine Safe.seq (Safe.forIn_array _ _ _ (fun x member acc => ?_)) (fun _ => Safe.pure _)
    unfold ExpressionState.appBody
    exact Safe.seq (each x (Ix.CompileM.decomposeApps_app_mem_lt fn arg hash member)) fun _ =>
      Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | lam name type body info hash =>
    rw [show ExpressionState.step compile (.lam name type body info hash) = _ from
      ExpressionState.binder_step_eq false compile name type body info hash]
    unfold ExpressionState.finishBinder
    exact Safe.seq (Safe.compileName _) fun _ => Safe.seq (each type (by simp; omega)) fun _ =>
      Safe.seq (each body (by simp; omega)) fun _ => Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | forallE name type body info hash =>
    rw [show ExpressionState.step compile (.forallE name type body info hash) = _ from
      ExpressionState.binder_step_eq true compile name type body info hash]
    unfold ExpressionState.finishBinder
    exact Safe.seq (Safe.compileName _) fun _ => Safe.seq (each type (by simp; omega)) fun _ =>
      Safe.seq (each body (by simp; omega)) fun _ => Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | letE name type value body nonDep hash =>
    rw [ExpressionState.let_step_eq]
    unfold ExpressionState.finishLet
    exact Safe.seq (Safe.compileName _) fun _ => Safe.seq (each type (by simp; omega)) fun _ =>
      Safe.seq (each value (by simp; omega)) fun _ => Safe.seq (each body (by simp; omega)) fun _ =>
        Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | lit literal hash =>
    cases literal
    · rw [ExpressionState.nat_step_eq]
      unfold ExpressionState.compileLiteral ExpressionState.finishLiteral
      exact Safe.bind (Safe.blob _) fun address _ => Safe.seq (Safe.internRef address) fun _ =>
        Safe.seq (Safe.alloc _) fun _ => Safe.pure _
    · rw [ExpressionState.string_step_eq]
      unfold ExpressionState.compileLiteral ExpressionState.finishLiteral
      exact Safe.bind (Safe.blob _) fun address _ => Safe.seq (Safe.internRef address) fun _ =>
        Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | proj name field value hash =>
    rw [ExpressionState.projection_step_eq]
    unfold ExpressionState.finishProjection
    exact Safe.seq (Safe.checkedIndex _ _) fun _ => Safe.seq (Safe.compileName _) fun _ =>
      Safe.bind (Safe.lookup _) fun address _ => Safe.seq (Safe.internRef address) fun _ =>
        Safe.seq (each value (by simp; omega)) fun _ => Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | mdata data value hash =>
    unfold ExpressionState.step compileExprStep
    dsimp only
    have child := each value (by simp; omega)
    split
    · split
      · refine Safe.seq (Safe.pure _) fun _ => Safe.seq child fun _ => ?_
        split
        · exact Safe.pure _
        · exact Safe.throwBind _ _
      · exact Safe.throwBind _ _
    · exact Safe.seq (Safe.kvmap _) fun _ => Safe.seq child fun _ => Safe.seq (Safe.alloc _) fun _ =>
        Safe.pure _
  | fvar name hash =>
    unfold ExpressionState.step compileExprStep
    exact Safe.throw _
  | mvar name hash =>
    unfold ExpressionState.step compileExprStep
    exact Safe.throw _

/-- **The expression compiler keeps the tables on the wire** on
success. -/
theorem Safe.expression (source : Ix.Expr) : Safe (compileExpr source) := by
  induction source using (measure (fun e : Ix.Expr => sizeOf e)).wf.induction with
  | h source ih =>
    rw [compileExpr]
    refine Safe.seq Safe.get (fun state => ?_)
    split
    · exact Safe.pure _
    · rw [show (compileExprStep source fun x _h => compileExpr x) =
        ExpressionState.step compileExpr source from rfl]
      refine Safe.seq (Safe.step compileExpr source (fun child smaller => ih child smaller))
        (fun value => ?_)
      exact Safe.seq (Safe.modify _ (fun _ => rfl)) (fun _ => Safe.pure _)

/-! ## The drains -/

theorem Safe.takeArena : Safe takeArena := by
  unfold Ix.CompileM.takeArena; exact Safe.modifyGet _ (fun _ => rfl)

theorem Safe.takeUnivPatches : Safe takeUnivPatches := by
  unfold Ix.CompileM.takeUnivPatches; exact Safe.modifyGet _ (fun _ => rfl)

theorem Safe.clearExprCache : Safe clearExprCache := by
  unfold Ix.CompileM.clearExprCache; exact Safe.modify _ (fun _ => rfl)

theorem Safe.resetArena : Safe resetArena := by
  unfold Ix.CompileM.resetArena; exact Safe.modify _ (fun _ => rfl)

theorem Safe.recordDefHints (name : Ix.Name) (hints : Lean.ReducibilityHints) :
    Safe (recordDefHints name hints) := by
  unfold Ix.CompileM.recordDefHints; exact Safe.modify _ (fun _ => rfl)

theorem Safe.mutCtxAddrs : Safe getMutCtxAddrs := by
  unfold getMutCtxAddrs
  exact Safe.seq Safe.readBlock (fun _ => Safe.pure _)

/-- The finishers' metadata steps. -/
local macro "safe_finish" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Safe.pure _
    | exact Safe.takeArena
    | exact Safe.takeUnivPatches
    | exact Safe.clearExprCache
    | exact Safe.checkedCount _ _
    | exact Safe.checkedIndex _ _
    | exact Safe.compileName _
    | exact Safe.compileNames _
    | exact Safe.recordDefHints _ _
    | exact Safe.mutCtxAddrs
    | exact Safe.readBlock
    | refine Safe.seq ?_ (fun _ => ?_)
    | dsimp only)

/-! ## The emitters -/

theorem Safe.finishDefinition (source : Ix.Def) (type : Ixon.Expr) (typeRoot : UInt64)
    (value : Ixon.Expr) (valueRoot : UInt64) :
    Safe (finishDefinitionDataCompilation source type typeRoot value valueRoot) := by
  unfold finishDefinitionDataCompilation
  safe_finish

theorem Safe.definitionData (source : Ix.Def) : Safe (compileDefinitionData source) := by
  unfold compileDefinitionData
  refine Safe.withCurrent _ (Safe.withUnivCtx _ ?_)
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.seq (Safe.expression _) fun value => Safe.finishDefinition source type.1 type.2 value.1 value.2

theorem Safe.finishAxiom (source : AxiomVal) (type : Ixon.Expr) (root : UInt64) :
    Safe (finishAxiomCompilation source type root) := by
  unfold finishAxiomCompilation
  safe_finish

theorem Safe.axiomPayload (source : AxiomVal) : Safe (compileAxiom source) := by
  unfold compileAxiom
  refine Safe.withCurrent _ (Safe.withUnivCtx _ ?_)
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.finishAxiom source type.1 type.2

theorem Safe.finishQuotient (source : QuotVal) (type : Ixon.Expr) (root : UInt64) :
    Safe (finishQuotientCompilation source type root) := by
  unfold finishQuotientCompilation
  safe_finish

theorem Safe.quotientPayload (source : QuotVal) : Safe (compileQuotient source) := by
  unfold compileQuotient
  refine Safe.withCurrent _ (Safe.withUnivCtx _ ?_)
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.finishQuotient source type.1 type.2

theorem Safe.rule (source : RecursorRule) : Safe (compileRecursorRule source) := by
  unfold compileRecursorRule
  exact Safe.seq (Safe.expression _) fun _ => Safe.seq (Safe.checkedCount _ _) fun _ => Safe.pure _

theorem Safe.rules (sources : List RecursorRule) (initial : RecursorRuleCompileState) :
    Safe (compileRecursorRules sources initial) := by
  induction sources generalizing initial with
  | nil => exact Safe.pure _
  | cons source rest ih =>
    rw [compileRecursorRules]
    exact Safe.seq (Safe.rule source) (fun _ => ih _)

theorem Safe.finishRecursor (source : RecursorVal) (type : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) : Safe (finishRecursorCompilation source type root rules) := by
  unfold finishRecursorCompilation
  safe_finish

theorem Safe.recursorPayload (source : RecursorVal) : Safe (compileRecursor source) := by
  unfold compileRecursor
  refine Safe.withCurrent _ (Safe.withUnivCtx _ ?_)
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.seq (Safe.rules _ _) fun rules => Safe.finishRecursor source type.1 type.2 rules

theorem Safe.finishConstructor (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) :
    Safe (finishConstructorCompilation source type root) := by
  unfold finishConstructorCompilation
  safe_finish

theorem Safe.constructorPayload (source : ConstructorVal) : Safe (compileConstructor source) := by
  unfold compileConstructor
  refine Safe.withCurrent _ ?_
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.finishConstructor source type.1 type.2

theorem Safe.constructors (sources : List ConstructorVal) (initial : InductiveConstructorCompileState) :
    Safe (compileInductiveConstructors sources initial) := by
  induction sources generalizing initial with
  | nil => exact Safe.pure _
  | cons source rest ih =>
    rw [compileInductiveConstructors]
    exact Safe.seq (Safe.constructorPayload source) (fun _ => ih _)

theorem Safe.inductiveMetadata : Safe takeInductiveTypeCompileMeta := by
  unfold takeInductiveTypeCompileMeta
  safe_finish

theorem Safe.finishInductive (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Safe (finishInductiveCompilation source type root metadata constructors) := by
  unfold finishInductiveCompilation
  safe_finish

theorem Safe.inductivePayload (source : InductiveVal) (constructors : Array ConstructorVal) :
    Safe (compileInductive source constructors) := by
  unfold compileInductive
  refine Safe.withCurrent _ (Safe.withUnivCtx _ ?_)
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.seq Safe.inductiveMetadata fun metadata => Safe.seq (Safe.constructors _ _) fun built =>
      Safe.finishInductive source type.1 type.2 metadata built

theorem Safe.finishInductiveData (source : Ix.Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Safe (finishInductiveDataCompilation source type root metadata constructors) := by
  unfold finishInductiveDataCompilation
  safe_finish

theorem Safe.inductiveData (source : Ix.Ind) : Safe (compileInductiveData source) := by
  unfold compileInductiveData
  refine Safe.withCurrent _ (Safe.withUnivCtx _ ?_)
  exact Safe.seq Safe.resetArena fun _ => Safe.seq (Safe.expression _) fun type =>
    Safe.seq Safe.inductiveMetadata fun metadata => Safe.seq (Safe.constructors _ _) fun built =>
      Safe.finishInductiveData source type.1 type.2 metadata built

theorem Safe.member (source : MutConst) : Safe (compileMutConstMember source) := by
  cases source <;> unfold compileMutConstMember
  · exact Safe.seq (Safe.withCurrent _ (Safe.definitionData _)) fun _ => Safe.pure _
  · exact Safe.seq (Safe.withCurrent _ (Safe.inductiveData _)) fun _ => Safe.pure _
  · exact Safe.seq (Safe.withCurrent _ (Safe.recursorPayload _)) fun _ => Safe.pure _

theorem Safe.equivalents (sources : List MutConst) (initial : MutConstCompileState) :
    Safe (compileEquivalentMutConsts sources initial) := by
  induction sources generalizing initial with
  | nil => exact Safe.pure _
  | cons source rest ih =>
    rw [compileEquivalentMutConsts]
    exact Safe.seq (Safe.member source) (fun _ => ih _)

theorem Safe.constClass (sources : List MutConst) (initial : MutConstCompileState) :
    Safe (compileMutConstClass sources initial) := by
  cases sources with
  | nil => exact Safe.pure _
  | cons source rest =>
    rw [compileMutConstClass]
    exact Safe.seq (Safe.member source) (fun _ => Safe.equivalents rest _)

theorem Safe.classes (sources : List (List MutConst)) (initial : MutConstCompileState) :
    Safe (compileMutConstClasses sources initial) := by
  induction sources generalizing initial with
  | nil => exact Safe.pure _
  | cons source rest ih =>
    rw [compileMutConstClasses]
    exact Safe.seq (Safe.constClass source initial) (fun _ => ih _)

/-- **Every mutual payload keeps the tables on the wire** on success. -/
theorem Safe.mutConsts (sources : List (List MutConst)) : Safe (compileMutConsts sources) := by
  unfold compileMutConsts
  exact Safe.seq (Safe.classes sources {}) (fun _ => Safe.pure _)

/-! ## The preseed establishes `Valid` -/

/-- **A successful preseed leaves a `Valid` state** when the tables were on
the wire. -/
theorem seeded_valid (roots : Array (Ix.Expr × List Ix.Name)) (context : CompileEnv × BlockEnv)
    {before after : BlockState} (wire : BlockWireTablesWF before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) : Valid after :=
  ⟨PreseedWire.preseed_wire context roots wire ran, PreseedState.preseed_final roots context ran⟩

end Ix.CompileCert.EmissionWire
