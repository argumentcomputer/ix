import Ix.CompileCert.EmissionWire
import Ix.CompileCert.SharingRoots

/-! # The payload emitters read back as their sources

Every declaration emitter of `Ix.CompileM` has one shape (R07-08): it enters
the declaration's context (`withCurrent`, and `withUnivCtx` with its level
parameters, which clears the raw universe memo), resets the arena, compiles
its root expressions with `compileExpr`, and finishes: the finisher drains
the per-declaration metadata (arena, call-site sharing, spelling patches),
clears the expression memo, checks the header counts, records names, and
returns the payload. This module proves, for the definition, axiom,
quotient, recursor, constructor and inductive emitters:

* the finishers, once: every successful run keeps the expression
  invariant's state part and extends the in-flight reader, and leaves an
  empty memo (`Clean`), through one invariant (`Tidy`) and one set of
  leaf frames (`Frame`); the header counts are the source's (`Yields`,
  the production guards: CT-15's `DeclarationHeaders`);
* the emitters: from a state satisfying `ExpressionState.Good` (for the
  declaration's own relation, whose levels mean the declaration's level
  parameters), a successful run returns the payload the source describes,
  with its roots read by the in-flight reader as terms `Related` to the
  source's (`SharingRoots.RootsRead`), ends `Clean`, and extends the
  reader. The recursor's rules keep the warm memo across the rule loop;
  the inductive's constructors start and end clean (CT-15's `*Emission`).

Every theorem assumes an environment without Pass 3 records
(`CompileEnv.surgeryFree`), until CQ3.5 deletes the surgery. -/

namespace Ix.CompileCert.Emission

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)


/-! ## Clean states -/

/-- The state between two declarations: the expression invariant's state
part, and an empty expression memo. No source relation or block environment
enters it. -/
def Clean (bindings : Bindings) (state : BlockState) : Prop :=
  StateSound bindings state ∧ state.exprCache = {}

theorem Clean.good {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (related : Ix.Expr → CExpr md → Prop)
    {bindings : Bindings} {state : BlockState} (clean : Clean bindings state) :
    Good cx param self related bindings state := by
  refine ⟨clean.1, ?_⟩
  rw [clean.2]
  exact CacheSound.empty _

/-! ## Finishers -/

section Finish

variable {md : Mode} {cx : Ctx md} {param : Nat → LevelParam} {self : Nat → Option (ReadM (CName md))}
  {bindings : Bindings} {context : CompileEnv × BlockEnv}

local notation "reader" => ExpressionRead.blockReader cx param self

variable (cx param self bindings) in
/-- The finishers' invariant: the expression invariant's state part, the
reader extending `base`, and (once `cleared`) an empty memo. -/
def Tidy (base : Ix.Kernel.Reader.ECx md) (cleared : Prop) (state : BlockState) : Prop :=
  StateSound bindings state ∧ ExpressionRead.Extends base (reader state).ecx ∧ (cleared → state.exprCache = {})

variable (cx param self bindings context) in
/-- Every run keeps the state part, extends the reader and keeps the memo. -/
def Frame (action : CompileM α) : Prop :=
  ∀ state, StateSound bindings state →
    StateSound bindings (rawRun action context state).2 ∧
      ExpressionRead.Extends (reader state).ecx (reader (rawRun action context state).2).ecx ∧
      (rawRun action context state).2.exprCache = state.exprCache

theorem Frame.tidy {action : CompileM α} (frame : Frame cx param self bindings context action)
    {base : Ix.Kernel.Reader.ECx md} {cleared : Prop} :
    Triple context (Tidy cx param self bindings base cleared) action
      (fun _ => Tidy cx param self bindings base cleared) := by
  intro before value after ready ran
  have kept := frame before ready.1
  rw [ran] at kept
  exact ⟨kept.1, extends_trans ready.2.1 kept.2.1, fun cleared => kept.2.2.trans (ready.2.2 cleared)⟩

theorem Frame.same {action : CompileM α} (same : ∀ state, (rawRun action context state).2 = state) :
    Frame cx param self bindings context action := by
  intro state sound
  rw [same]
  exact ⟨sound, ExpressionRead.Extends.refl _, rfl⟩

/-- The display-only fields: the arena, the spelling patches, the call-site
sharing and the reducibility hints. -/
def withoutDisplay (state : BlockState) : BlockState :=
  { state with arena := {}, univPatches := #[], surgerySharing := #[], defHints := {} }

theorem Frame.display {action : CompileM α} (frame : Preserves withoutDisplay action) :
    Frame cx param self bindings context action := by
  intro state sound
  have same := frame context state
  have univs : univView (rawRun action context state).2 = univView state := by
    have view := congrArg univView same; exact view
  have binding : bindingView (rawRun action context state).2 = bindingView state := by
    have view := congrArg bindingView same; exact view
  have readerSame : reader (rawRun action context state).2 = reader state := by
    have view := congrArg (ExpressionRead.blockReader cx param self) same; exact view
  have cache : (rawRun action context state).2.exprCache = state.exprCache := by
    have view := congrArg BlockState.exprCache same; exact view
  refine ⟨⟨Sound.of_view univs sound.1, (congrArg Interning.RefIndexSound same).mpr sound.2.1,
    binding.trans sound.2.2⟩, ?_, cache⟩
  rw [readerSame]
  exact ExpressionRead.Extends.refl _

theorem Frame.namesBlobs {action : CompileM α} (framed : Serializers.NamesBlobs action)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Frame cx param self bindings context action := by
  intro state sound
  have facts := framed context state
  have univs : univView (rawRun action context state).2 = univView state := by
    have view := congrArg univView facts.1; exact view
  have binding : bindingView (rawRun action context state).2 = bindingView state := by
    have view := congrArg bindingView facts.1; exact view
  have cache : (rawRun action context state).2.exprCache = state.exprCache := by
    have view := congrArg BlockState.exprCache facts.1; exact view
  exact ⟨⟨Sound.of_view univs sound.1, (congrArg Interning.RefIndexSound facts.1).mpr sound.2.1,
    binding.trans sound.2.2⟩,
    BlobWrites.reader_extends context.1.blobs state _ facts.1 facts.2 cx param self aligned, cache⟩

theorem Frame.compileName (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (name : Ix.Name) : Frame cx param self bindings context (Ix.CompileM.compileName name) :=
  Frame.namesBlobs (Serializers.NamesBlobs.compileName name) aligned

theorem Frame.compileNames (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (names : Array Ix.Name) : Frame cx param self bindings context (Ix.CompileM.compileNames names) :=
  Frame.namesBlobs (Serializers.NamesBlobs.compileNames names) aligned

theorem Frame.checkedCount (table : String) (count : Nat) :
    Frame cx param self bindings context (checkedTableCount table count) :=
  Frame.same fun state => Interning.checkedTableCount_state table count context state

theorem Frame.checkedIndex (table : String) (index : Nat) :
    Frame cx param self bindings context (checkedTableIndex table index) :=
  Frame.same fun state => Interning.checkedTableIndex_state table index context state

theorem Frame.readBlock : Frame cx param self bindings context getBlockEnv :=
  Frame.same fun _ => rfl

theorem Frame.mutCtxAddrs : Frame cx param self bindings context getMutCtxAddrs :=
  Frame.same fun _ => rfl

theorem Frame.takeArena : Frame cx param self bindings context Ix.CompileM.takeArena := by
  unfold Ix.CompileM.takeArena
  exact Frame.display (Preserves.modifyGet _ _ (fun _ => rfl))

theorem Frame.takeSurgerySharing : Frame cx param self bindings context Ix.CompileM.takeSurgerySharing := by
  unfold Ix.CompileM.takeSurgerySharing
  exact Frame.display (Preserves.modifyGet _ _ (fun _ => rfl))

theorem Frame.recordDefHints (name : Ix.Name) (hints : Lean.ReducibilityHints) :
    Frame cx param self bindings context (Ix.CompileM.recordDefHints name hints) := by
  unfold Ix.CompileM.recordDefHints
  exact Frame.display (Preserves.modify _ _ (fun _ => rfl))

/-- Draining the spelling channels empties the extension table. -/
theorem Frame.takeUnivPatches : Frame cx param self bindings context Ix.CompileM.takeUnivPatches := by
  unfold Ix.CompileM.takeUnivPatches
  intro state sound
  rw [rawRun_modifyGet]
  exact ⟨⟨⟨sound.1.rawCache, sound.1.canonCache, ⟨sound.1.tables.1, Interning.IndexSound.empty⟩⟩,
    sound.2.1, sound.2.2⟩, ExpressionRead.Extends.refl _, rfl⟩

/-- Clearing the memo keeps the state part and the reader. -/
theorem clear_tidy {base : Ix.Kernel.Reader.ECx md} {cleared : Prop} :
    Triple context (Tidy cx param self bindings base cleared) Ix.CompileM.clearExprCache
      (fun _ => Tidy cx param self bindings base True) := by
  intro before value after ready ran
  unfold Ix.CompileM.clearExprCache at ran
  rw [rawRun_modify] at ran
  cases ran
  exact ⟨⟨Sound.of_view (before := before) rfl ready.1.1, ready.1.2.1, ready.1.2.2⟩, ready.2.1, fun _ => rfl⟩

/-- The finishers' steps. -/
local macro "tidy_steps" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Frame.tidy Frame.takeArena
    | exact Frame.tidy Frame.takeSurgerySharing
    | exact Frame.tidy Frame.takeUnivPatches
    | exact clear_tidy
    | exact Frame.tidy (Frame.checkedCount _ _)
    | exact Frame.tidy (Frame.checkedIndex _ _)
    | exact Frame.tidy (Frame.compileName (by assumption) _)
    | exact Frame.tidy (Frame.compileNames (by assumption) _)
    | exact Frame.tidy (Frame.recordDefHints _ _)
    | exact Frame.tidy Frame.mutCtxAddrs
    | exact Frame.tidy Frame.readBlock
    | apply Triple.bind
    | intro _
    | dsimp only
    | split)

/-- The payload a definition-like declaration's finisher assembles. -/
def definitionPayload (source : Ix.Def) (type value : Ixon.Expr) : Ixon.Definition :=
  { kind := source.kind, safety := source.safety, lvls := source.levelParams.size.toUInt64, typ := type, value }

def axiomPayload (source : AxiomVal) (type : Ixon.Expr) : Ixon.Axiom :=
  { isUnsafe := source.isUnsafe, lvls := source.cnst.levelParams.size.toUInt64, typ := type }

def quotientPayload (source : QuotVal) (type : Ixon.Expr) : Ixon.Quotient :=
  { kind := convertQuotKind source.kind, lvls := source.cnst.levelParams.size.toUInt64, typ := type }

def constructorPayload (source : ConstructorVal) (type : Ixon.Expr) : Ixon.Constructor :=
  { isUnsafe := source.isUnsafe, lvls := source.cnst.levelParams.size.toUInt64, cidx := source.cidx.toUInt64,
    params := source.numParams.toUInt64, fields := source.numFields.toUInt64, typ := type }

def recursorPayload (source : RecursorVal) (type : Ixon.Expr) (rules : Array Ixon.RecursorRule) :
    Ixon.Recursor :=
  { k := source.k, isUnsafe := source.isUnsafe, lvls := source.cnst.levelParams.size.toUInt64,
    params := source.numParams.toUInt64, indices := source.numIndices.toUInt64,
    motives := source.numMotives.toUInt64, minors := source.numMinors.toUInt64, typ := type, rules }

def inductivePayload (source : Ix.Ind) (type : Ixon.Expr) (ctors : Array Ixon.Constructor) : Ixon.Inductive :=
  { isUnsafe := source.isUnsafe, lvls := source.levelParams.size.toUInt64, params := source.numParams.toUInt64,
    indices := source.numIndices.toUInt64, typ := type, ctors }

/-- **The definition-like finisher** keeps the state part, extends the
reader, clears the memo and returns the payload. -/
theorem finishDefinition_tidy (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (source : Ix.Def) (type : Ixon.Expr) (typeRoot : UInt64) (value : Ixon.Expr) (valueRoot : UInt64)
    (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base False)
      (finishDefinitionDataCompilation source type typeRoot value valueRoot)
      (fun output state => Tidy cx param self bindings base True state ∧
        output.1 = definitionPayload source type value ∧ output.2.2 = (type, value)) := by
  unfold finishDefinitionDataCompilation
  tidy_steps
  exact Triple.pure _ fun _ ready => ⟨ready, rfl, rfl⟩

theorem finishAxiom_tidy (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (source : AxiomVal) (type : Ixon.Expr) (root : UInt64) (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base False) (finishAxiomCompilation source type root)
      (fun output state => Tidy cx param self bindings base True state ∧
        output.1 = axiomPayload source type ∧ output.2.2 = type) := by
  unfold finishAxiomCompilation
  tidy_steps
  exact Triple.pure _ fun _ ready => ⟨ready, rfl, rfl⟩

theorem finishQuotient_tidy (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (source : QuotVal) (type : Ixon.Expr) (root : UInt64) (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base False) (finishQuotientCompilation source type root)
      (fun output state => Tidy cx param self bindings base True state ∧
        output.1 = quotientPayload source type ∧ output.2.2 = type) := by
  unfold finishQuotientCompilation
  tidy_steps
  exact Triple.pure _ fun _ ready => ⟨ready, rfl, rfl⟩

theorem finishConstructor_tidy (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base False) (finishConstructorCompilation source type root)
      (fun output state => Tidy cx param self bindings base True state ∧
        output.1 = constructorPayload source type ∧ output.2.2 = type) := by
  unfold finishConstructorCompilation
  tidy_steps
  exact Triple.pure _ fun _ ready => ⟨ready, rfl, rfl⟩

theorem finishRecursor_tidy (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (source : RecursorVal) (type : Ixon.Expr) (root : UInt64) (rules : RecursorRuleCompileState)
    (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base False) (finishRecursorCompilation source type root rules)
      (fun output state => Tidy cx param self bindings base True state ∧
        output.1 = recursorPayload source type rules.rules ∧ output.2.2 = type) := by
  unfold finishRecursorCompilation
  tidy_steps
  exact Triple.pure _ fun _ ready => ⟨ready, rfl, rfl⟩

theorem inductiveMetadata_tidy (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base False) takeInductiveTypeCompileMeta
      (fun _ state => Tidy cx param self bindings base True state) := by
  unfold takeInductiveTypeCompileMeta
  tidy_steps
  exact Triple.pure _ fun _ ready => ready

theorem finishInductiveData_tidy (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (source : Ix.Ind) (type : Ixon.Expr) (root : UInt64) (metadata : InductiveTypeCompileMeta)
    (constructors : InductiveConstructorCompileState) (base : Ix.Kernel.Reader.ECx md) :
    Triple context (Tidy cx param self bindings base True)
      (finishInductiveDataCompilation source type root metadata constructors)
      (fun output state => Tidy cx param self bindings base True state ∧
        output.1 = inductivePayload source type constructors.ctors ∧
        output.2.2 = (constructors.ctorMetaPairs, constructors.ctorExprs)) := by
  unfold finishInductiveDataCompilation
  tidy_steps
  exact Triple.pure _ fun _ ready => ⟨ready, rfl, rfl⟩

/-- A finisher run from a state satisfying the state part ends `Clean` and
extends the reader. -/
theorem finish_clean {action : CompileM β} {post : β → Prop}
    (finishes : ∀ base, Triple context (Tidy cx param self bindings base False) action
      (fun output state => Tidy cx param self bindings base True state ∧ post output))
    {before after : BlockState} {output : β} (sound : StateSound bindings before)
    (ran : rawRun action context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧ post output := by
  have done := finishes (reader before).ecx before output after
    ⟨sound, ExpressionRead.Extends.refl _, False.elim⟩ ran
  exact ⟨⟨done.1.1, done.1.2.2 trivial⟩, done.1.2.1, done.2⟩

end Finish

/-! ## Header counts

The finishers' guards make every header field the source's natural number
(CT-15's `DeclarationHeaders`). -/

/-- Every successful run returns a value satisfying `post`. -/
def Yields (action : CompileM α) (post : α → Prop) : Prop :=
  ∀ context before output after, rawRun action context before = (.ok output, after) → post output

theorem Yields.pure {output : α} {post : α → Prop} (valid : post output) : Yields (pure output) post := by
  intro context before value after ran
  cases ran
  exact valid

theorem Yields.bind {action : CompileM α} {next : α → CompileM β} {first : α → Prop} {last : β → Prop}
    (head : Yields action first) (tail : ∀ value, first value → Yields (next value) last) :
    Yields (action >>= next) last := by
  intro context before output after ran
  obtain ⟨value, middle, headRan, tailRan⟩ := bind_ok ran
  exact tail value (head context before value middle headRan) context middle output after tailRan

theorem Yields.bindAny (action : CompileM α) {next : α → CompileM β} {post : β → Prop}
    (tail : ∀ value, Yields (next value) post) : Yields (action >>= next) post := by
  intro context before output after ran
  obtain ⟨value, middle, _, tailRan⟩ := bind_ok ran
  exact tail value context middle output after tailRan

theorem Yields.count (label : String) (count : Nat) :
    Yields (checkedTableCount label count) (fun _ => count < UInt64.size) := by
  intro context before output after ran
  exact (Interning.checkedTableCount_value label count context before (congrArg Prod.fst ran)).2

theorem Yields.index (label : String) (index : Nat) :
    Yields (checkedTableIndex label index) (fun _ => index < UInt64.size) := by
  intro context before output after ran
  exact (Interning.checkedTableIndex_value label index context before (congrArg Prod.fst ran)).2

theorem exact_header (count : Nat) (bounded : count < UInt64.size) : count.toUInt64.toNat = count :=
  UInt64.toNat_ofNat_of_lt' bounded

local macro "header_proof" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Yields.pure (by repeat' first | constructor | assumption | apply exact_header; assumption)
    | refine Yields.bind (Yields.count _ _) (fun _ bounded => ?_)
    | refine Yields.bind (Yields.index _ _) (fun _ bounded => ?_)
    | refine Yields.bindAny _ (fun _ => ?_)
    | dsimp only
    | split)

theorem definitionHeader (source : Ix.Def) (type : Ixon.Expr) (typeRoot : UInt64) (value : Ixon.Expr)
    (valueRoot : UInt64) :
    Yields (finishDefinitionDataCompilation source type typeRoot value valueRoot)
      (fun output => output.1.lvls.toNat = source.levelParams.size) := by
  unfold finishDefinitionDataCompilation
  header_proof

theorem axiomHeader (source : AxiomVal) (type : Ixon.Expr) (root : UInt64) :
    Yields (finishAxiomCompilation source type root)
      (fun output => output.1.lvls.toNat = source.cnst.levelParams.size) := by
  unfold finishAxiomCompilation
  header_proof

theorem quotientHeader (source : QuotVal) (type : Ixon.Expr) (root : UInt64) :
    Yields (finishQuotientCompilation source type root)
      (fun output => output.1.lvls.toNat = source.cnst.levelParams.size) := by
  unfold finishQuotientCompilation
  header_proof

theorem recursorRuleHeader (source : RecursorRule) :
    Yields (compileRecursorRule source) (fun output => output.1.fields.toNat = source.nfields) := by
  unfold compileRecursorRule
  header_proof

theorem recursorHeader (source : RecursorVal) (type : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) :
    Yields (finishRecursorCompilation source type root rules) (fun output =>
      output.1.lvls.toNat = source.cnst.levelParams.size ∧ output.1.params.toNat = source.numParams ∧
      output.1.indices.toNat = source.numIndices ∧ output.1.motives.toNat = source.numMotives ∧
      output.1.minors.toNat = source.numMinors ∧ output.1.rules.size < UInt64.size) := by
  unfold finishRecursorCompilation
  header_proof

theorem constructorHeader (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) :
    Yields (finishConstructorCompilation source type root) (fun output =>
      output.1.lvls.toNat = source.cnst.levelParams.size ∧ output.1.cidx.toNat = source.cidx ∧
      output.1.params.toNat = source.numParams ∧ output.1.fields.toNat = source.numFields) := by
  unfold finishConstructorCompilation
  header_proof

theorem inductiveDataHeader (source : Ix.Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Yields (finishInductiveDataCompilation source type root metadata constructors) (fun output =>
      output.1.lvls.toNat = source.levelParams.size ∧ output.1.params.toNat = source.numParams ∧
      output.1.indices.toNat = source.numIndices ∧ output.1.ctors.size < UInt64.size) := by
  unfold finishInductiveDataCompilation
  header_proof

theorem Yields.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} {post : α → Prop}
    (holds : Yields action post) : Yields (withBlockEnv update action) post :=
  fun context before output after ran => holds (context.1, update context.2) before output after ran

theorem Yields.withCurrent (name : Ix.Name) {action : CompileM α} {post : α → Prop}
    (holds : Yields action post) : Yields (withCurrent name action) post := Yields.withBlockEnv _ holds

theorem Yields.withUnivCtx (params : List Ix.Name) {action : CompileM α} {post : α → Prop}
    (holds : Yields action post) : Yields (withUnivCtx params action) post :=
  Yields.bindAny _ (fun _ => Yields.withBlockEnv _ holds)

/-! ## The emitters -/

/-- The declaration context `withCurrent` and `withUnivCtx` install. -/
def inner (name : Ix.Name) (params : List Ix.Name) (context : CompileEnv × BlockEnv) :
    CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := name, univCtx := params })

/-- The context `withCurrent` alone installs. -/
def current (name : Ix.Name) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := name })

/-- The state `withUnivCtx` and `resetArena` leave. -/
def prepared (state : BlockState) : BlockState :=
  { state with univCache := {}, arena := {}, metaUnivs := #[], metaUnivsIndex := {}, univPatches := #[] }

/-- The state `resetArena` alone leaves (a constructor keeps its family's
universe context). -/
def reset (state : BlockState) : BlockState :=
  { state with arena := {}, metaUnivs := #[], metaUnivsIndex := {}, univPatches := #[] }

/-- A successful declaration entry runs its body in the declaration's
context from the prepared state. -/
theorem enter_ok {name : Ix.Name} {params : List Ix.Name} {action : CompileM α}
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : α}
    (ran : rawRun (withCurrent name (withUnivCtx params (resetArena >>= fun _ => action))) context before =
      (.ok output, after)) :
    rawRun action (inner name params context) (prepared before) = (.ok output, after) := by
  unfold withCurrent at ran
  rw [rawRun_withBlockEnv] at ran
  unfold Ix.CompileM.withUnivCtx at ran
  obtain ⟨_, cleared, clearRan, ran⟩ := bind_ok ran
  rw [rawRun_modify] at clearRan
  cases clearRan
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, reseted, resetRan, ran⟩ := bind_ok ran
  unfold resetArena at resetRan
  rw [rawRun_modify] at resetRan
  cases resetRan
  exact ran

/-- A successful constructor entry runs its body in the constructor's
context from the reset state. -/
theorem current_ok {name : Ix.Name} {action : CompileM α} {context : CompileEnv × BlockEnv}
    {before after : BlockState} {output : α}
    (ran : rawRun (withCurrent name (resetArena >>= fun _ => action)) context before = (.ok output, after)) :
    rawRun action (current name context) (reset before) = (.ok output, after) := by
  unfold withCurrent at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, reseted, resetRan, ran⟩ := bind_ok ran
  unfold resetArena at resetRan
  rw [rawRun_modify] at resetRan
  cases resetRan
  exact ran

section Emitters

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self

/-- The declaration's source relation: levels mean the context's level
parameters. -/
abbrev related (context : CompileEnv × BlockEnv) : Ix.Expr → CExpr md → Prop :=
  Related names (LevelMeaning context.2.univCtx σ param)

theorem prepared_good {related : Ix.Expr → CExpr md → Prop} {state : BlockState}
    (good : Good cx param self related bindings state) : Good cx param self related bindings (prepared state) :=
  ⟨⟨⟨CacheSound.empty _, good.1.1.canonCache, ⟨good.1.1.tables.1, Interning.IndexSound.empty⟩⟩,
    good.1.2.1, good.1.2.2⟩, good.2⟩

theorem reset_good {related : Ix.Expr → CExpr md → Prop} {state : BlockState}
    (good : Good cx param self related bindings state) : Good cx param self related bindings (reset state) :=
  ⟨⟨⟨good.1.1.rawCache, good.1.1.canonCache, ⟨good.1.1.tables.1, Interning.IndexSound.empty⟩⟩,
    good.1.2.1, good.1.2.2⟩, good.2⟩

/-- The production entry compiles a source expression to a value the
reader reads as a related term (`ExpressionState.compileExprNoSurgery_scoped`
under `surgeryFree`). -/
theorem compileExpr_checked (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : Ix.Expr)
    (scope : ConstsSatisfy (SelfName context.2 self names) source) (before : BlockState)
    (good : Good cx param self (related param names σ context) bindings before) :
    Checked cx param self (related param names σ context) bindings source before
      (rawRun (compileExpr source) context before) := by
  rw [compileExpr_surgeryFree source context free]
  exact compileExprNoSurgery_scoped cx param self names σ bindings context aligned external source scope
    before good

/-- One compiled root: a successful run of `compileExpr` keeps `Good`,
extends the reader and reads as a related term. -/
theorem compiled_root (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) {source : Ix.Expr}
    (scope : ConstsSatisfy (SelfName context.2 self names) source) {before middle : BlockState}
    {value : Ixon.Expr × UInt64} (good : Good cx param self (related param names σ context) bindings before)
    (ran : rawRun (compileExpr source) context before = (.ok value, middle)) :
    Good cx param self (related param names σ context) bindings middle ∧
      ExpressionRead.Extends (reader before).ecx (reader middle).ecx ∧
      ∃ target, related param names σ context source target ∧ (reader middle).read value.1 = .ok target := by
  have checked := compileExpr_checked cx param self names σ bindings context free aligned external source scope
    before good
  rw [ran] at checked
  exact ⟨checked.1, checked.2.1, checked.2.2 value rfl⟩

/-! ### Definitions -/

/-- **The definition-like emitter reads back as its source**: from `Good`
(for the declaration's relation), a successful run returns the payload the
source describes, whose type and value read as terms related to the
source's, ends `Clean`, and extends the reader. -/
theorem definition_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : Ix.Def)
    (typeScope : ConstsSatisfy (SelfName context.2 self names) source.type)
    (valueScope : ConstsSatisfy (SelfName context.2 self names) source.value)
    {before after : BlockState} {output : Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr}
    (good : Good cx param self (related param names σ (inner source.name source.levelParams.toList context))
      bindings before)
    (ran : rawRun (compileDefinitionData source) context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      output.1 = definitionPayload source output.1.typ output.1.value ∧
      output.2.2 = (output.1.typ, output.1.value) ∧
      SharingRoots.RootsRead (reader after)
        (related param names σ (inner source.name source.levelParams.toList context))
        [source.type, source.value] [output.1.typ, output.1.value] := by
  unfold compileDefinitionData at ran
  have body := enter_ok ran
  have start := prepared_good cx param self bindings good
  obtain ⟨typed, middle, typeRan, rest⟩ := bind_ok body
  obtain ⟨typeGood, typeGrowth, typeTarget, typeRel, typeRead⟩ :=
    compiled_root cx param self names σ bindings (inner source.name source.levelParams.toList context) free
      aligned external typeScope start typeRan
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only at rest
  obtain ⟨valued, compiled, valueRan, finished⟩ := bind_ok rest
  obtain ⟨valueGood, valueGrowth, valueTarget, valueRel, valueRead⟩ :=
    compiled_root cx param self names σ bindings (inner source.name source.levelParams.toList context) free
      aligned external valueScope typeGood valueRan
  obtain ⟨valueExpr, valueRoot⟩ := valued
  dsimp only at finished
  obtain ⟨clean, finalGrowth, shape, roots⟩ :=
    finish_clean (fun base => finishDefinition_tidy (context := inner source.name source.levelParams.toList context)
      aligned source typeExpr typeRoot valueExpr valueRoot base)
      valueGood.1 finished
  have typeFinal := read_grows cx param self (extends_trans valueGrowth finalGrowth) typeRead
  have valueFinal := read_grows cx param self finalGrowth valueRead
  rw [shape]
  refine ⟨clean, extends_trans typeGrowth (extends_trans valueGrowth finalGrowth), rfl, roots, ?_⟩
  exact .cons ⟨typeTarget, typeRel, typeFinal⟩ (.cons ⟨valueTarget, valueRel, valueFinal⟩ .nil)

theorem definitionData_header (source : Ix.Def) :
    Yields (compileDefinitionData source) (fun output => output.1.lvls.toNat = source.levelParams.size) := by
  unfold compileDefinitionData
  refine Yields.withCurrent _ (Yields.withUnivCtx _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Yields.bindAny _ fun valued => ?_
  obtain ⟨valueExpr, valueRoot⟩ := valued
  exact definitionHeader source typeExpr typeRoot valueExpr valueRoot

/-! ### One-root emitters: axioms, quotients, constructors -/

/-- **A one-root emitter reads back as its source**: compile the root, then
a finisher of the `Tidy` shape. -/
theorem single_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) {source : Ix.Expr}
    (scope : ConstsSatisfy (SelfName context.2 self names) source)
    {finish : Ixon.Expr → UInt64 → CompileM β} {shape : Ixon.Expr → β → Prop}
    (finishes : ∀ type root base, Triple context (Tidy cx param self bindings base False) (finish type root)
      (fun output state => Tidy cx param self bindings base True state ∧ shape type output))
    {before after : BlockState} {output : β}
    (good : Good cx param self (related param names σ context) bindings before)
    (ran : rawRun (compileExpr source >>= fun result => finish result.1 result.2) context before =
      (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      ∃ type, shape type output ∧
        SharingRoots.RootsRead (reader after) (related param names σ context) [source] [type] := by
  obtain ⟨typed, middle, typeRan, finished⟩ := bind_ok ran
  obtain ⟨typeGood, typeGrowth, typeTarget, typeRel, typeRead⟩ :=
    compiled_root cx param self names σ bindings context free aligned external scope good typeRan
  obtain ⟨clean, finalGrowth, shaped⟩ :=
    finish_clean (fun base => finishes typed.1 typed.2 base) typeGood.1 finished
  exact ⟨clean, extends_trans typeGrowth finalGrowth, typed.1, shaped,
    .cons ⟨typeTarget, typeRel, read_grows cx param self finalGrowth typeRead⟩ .nil⟩

theorem axiom_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : AxiomVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : Ixon.Axiom × Ixon.ConstantMeta × Ixon.Expr}
    (good : Good cx param self
      (related param names σ (inner source.cnst.name source.cnst.levelParams.toList context)) bindings before)
    (ran : rawRun (compileAxiom source) context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      output.1 = axiomPayload source output.1.typ ∧ output.2.2 = output.1.typ ∧
      SharingRoots.RootsRead (reader after)
        (related param names σ (inner source.cnst.name source.cnst.levelParams.toList context))
        [source.cnst.type] [output.1.typ] := by
  unfold compileAxiom at ran
  obtain ⟨clean, growth, type, ⟨shape, root⟩, roots⟩ := single_correct cx param self names σ bindings
    (inner source.cnst.name source.cnst.levelParams.toList context) free aligned external scope
    (fun type root base => finishAxiom_tidy
      (context := inner source.cnst.name source.cnst.levelParams.toList context) aligned source type root base)
    (prepared_good cx param self bindings good) (enter_ok ran)
  rw [shape, root]
  exact ⟨clean, growth, rfl, rfl, roots⟩

theorem axiomPayload_header (source : AxiomVal) :
    Yields (compileAxiom source) (fun output => output.1.lvls.toNat = source.cnst.levelParams.size) := by
  unfold compileAxiom
  exact Yields.withCurrent _ (Yields.withUnivCtx _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun typed =>
    axiomHeader source typed.1 typed.2))

theorem quotient_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : QuotVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : Ixon.Quotient × Ixon.ConstantMeta × Ixon.Expr}
    (good : Good cx param self
      (related param names σ (inner source.cnst.name source.cnst.levelParams.toList context)) bindings before)
    (ran : rawRun (compileQuotient source) context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      output.1 = quotientPayload source output.1.typ ∧ output.2.2 = output.1.typ ∧
      SharingRoots.RootsRead (reader after)
        (related param names σ (inner source.cnst.name source.cnst.levelParams.toList context))
        [source.cnst.type] [output.1.typ] := by
  unfold compileQuotient at ran
  obtain ⟨clean, growth, type, ⟨shape, root⟩, roots⟩ := single_correct cx param self names σ bindings
    (inner source.cnst.name source.cnst.levelParams.toList context) free aligned external scope
    (fun type root base => finishQuotient_tidy
      (context := inner source.cnst.name source.cnst.levelParams.toList context) aligned source type root base)
    (prepared_good cx param self bindings good) (enter_ok ran)
  rw [shape, root]
  exact ⟨clean, growth, rfl, rfl, roots⟩

theorem quotientPayload_header (source : QuotVal) :
    Yields (compileQuotient source) (fun output => output.1.lvls.toNat = source.cnst.levelParams.size) := by
  unfold compileQuotient
  exact Yields.withCurrent _ (Yields.withUnivCtx _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun typed =>
    quotientHeader source typed.1 typed.2))

/-- **A constructor reads back as its source**, in its family's universe
context, from a clean state to a clean state. -/
theorem constructor_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : ConstructorVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr}
    (clean : Clean bindings before)
    (ran : rawRun (compileConstructor source) context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      output.1 = constructorPayload source output.1.typ ∧ output.2.2 = output.1.typ ∧
      SharingRoots.RootsRead (reader after) (related param names σ context) [source.cnst.type] [output.1.typ] := by
  unfold compileConstructor at ran
  obtain ⟨cleaned, growth, type, ⟨shape, root⟩, roots⟩ := single_correct cx param self names σ bindings
    (current source.cnst.name context) free aligned external scope
    (fun type root base => finishConstructor_tidy (context := current source.cnst.name context) aligned
      source type root base)
    (reset_good cx param self bindings (clean.good cx param self _)) (current_ok ran)
  rw [shape, root]
  exact ⟨cleaned, growth, rfl, rfl, roots⟩

/-- **The constructor loop**: from a clean state, every constructor reads
back as its source in the final reader, in source order, and the loop
appends exactly their payloads and types. -/
theorem constructors_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) :
    ∀ (sources : List ConstructorVal),
      (∀ source ∈ sources, ConstsSatisfy (SelfName context.2 self names) source.cnst.type) →
      ∀ (initial : InductiveConstructorCompileState) {before after : BlockState}
        {output : InductiveConstructorCompileState}, Clean bindings before →
      rawRun (compileInductiveConstructors sources initial) context before = (.ok output, after) →
      Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
        ∃ targets : List Ixon.Constructor, output.ctors.toList = initial.ctors.toList ++ targets ∧
          output.ctorExprs.toList = initial.ctorExprs.toList ++ targets.map (·.typ) ∧
          List.Forall₂ (fun source target => target = constructorPayload source target.typ) sources targets ∧
          SharingRoots.RootsRead (reader after) (related param names σ context) (sources.map (·.cnst.type))
            (targets.map (·.typ)) := by
  intro sources
  induction sources with
  | nil =>
    intro _ initial before after output clean ran
    cases ran
    exact ⟨clean, ExpressionRead.Extends.refl _, [], by simp, by simp, .nil, .nil⟩
  | cons source rest ih =>
    intro scope initial before after output clean ran
    rw [compileInductiveConstructors] at ran
    obtain ⟨compiled, middle, first, last⟩ := bind_ok ran
    obtain ⟨headClean, headGrowth, shape, root, headRoots⟩ := constructor_correct cx param self names σ bindings
      context free aligned external source (scope source (by simp)) clean first
    obtain ⟨tailClean, tailGrowth, targets, payloads, exprs, shapes, tailRoots⟩ :=
      ih (fun source member => scope source (List.mem_cons_of_mem _ member)) _ headClean last
    refine ⟨tailClean, extends_trans headGrowth tailGrowth, compiled.1 :: targets, ?_, ?_, .cons shape shapes, ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using payloads
    · simpa only [Array.toList_push, root, List.map_cons, List.append_assoc, List.singleton_append] using exprs
    · exact (SharingRoots.RootsRead.grow tailGrowth headRoots).append tailRoots

/-! ### Inductives -/

/-- The source data of a standalone inductive and its constructors. -/
def sourceData (source : InductiveVal) (constructors : Array ConstructorVal) : Ix.Ind :=
  ⟨source.cnst.name, source.cnst.levelParams, source.cnst.type, source.numParams, source.numIndices,
    source.all, constructors, source.numNested, source.isRec, source.isReflexive, source.isUnsafe⟩

theorem compileInductive_eq (source : InductiveVal) (constructors : Array ConstructorVal) :
    compileInductive source constructors = compileInductiveData (sourceData source constructors) := rfl

/-- **The inductive emitter reads back as its source**: the type and every
constructor, in source order, read as related terms in the final reader;
the payload is the one the source describes; its expression roots are the
type then the constructor types. -/
theorem inductiveData_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : Ix.Ind)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.type)
    (ctorScope : ∀ ctor ∈ source.ctors.toList, ConstsSatisfy (SelfName context.2 self names) ctor.cnst.type)
    {before after : BlockState}
    {output : Ixon.Inductive × Ixon.ConstantMeta × Array (Ix.Name × Ixon.ConstantMeta) × Array Ixon.Expr}
    (good : Good cx param self (related param names σ (inner source.name source.levelParams.toList context))
      bindings before)
    (ran : rawRun (compileInductiveData source) context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      output.1 = inductivePayload source output.1.typ output.1.ctors ∧
      List.Forall₂ (fun ctor target => target = constructorPayload ctor target.typ) source.ctors.toList
        output.1.ctors.toList ∧
      output.2.2.2.toList = output.1.typ :: output.1.ctors.toList.map (·.typ) ∧
      SharingRoots.RootsRead (reader after)
        (related param names σ (inner source.name source.levelParams.toList context))
        (source.type :: source.ctors.toList.map (·.cnst.type)) (output.1.typ :: output.1.ctors.toList.map (·.typ)) := by
  unfold compileInductiveData at ran
  have body := enter_ok ran
  have start := prepared_good cx param self bindings good
  obtain ⟨typed, middle, typeRan, rest⟩ := bind_ok body
  obtain ⟨typeGood, typeGrowth, typeTarget, typeRel, typeRead⟩ :=
    compiled_root cx param self names σ bindings (inner source.name source.levelParams.toList context) free
      aligned external scope start typeRan
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only at rest
  obtain ⟨metadata, drained, drainRan, rest⟩ := bind_ok rest
  have drainDone := inductiveMetadata_tidy (cx := cx) (param := param) (self := self) (bindings := bindings)
    (reader middle).ecx middle metadata drained ⟨typeGood.1, ExpressionRead.Extends.refl _, False.elim⟩ drainRan
  obtain ⟨built, compiled, ctorRan, finished⟩ := bind_ok rest
  obtain ⟨ctorClean, ctorGrowth, targets, payloads, exprs, shapes, ctorRoots⟩ :=
    constructors_correct cx param self names σ bindings (inner source.name source.levelParams.toList context)
      free aligned external source.ctors.toList ctorScope { ctorExprs := #[typeExpr] }
      ⟨drainDone.1, drainDone.2.2 trivial⟩ ctorRan
  have finalDone := finishInductiveData_tidy (context := inner source.name source.levelParams.toList context)
    aligned source typeExpr typeRoot metadata built (reader compiled).ecx
    compiled output after ⟨ctorClean.1, ExpressionRead.Extends.refl _, fun _ => ctorClean.2⟩ finished
  obtain ⟨⟨finalSound, finalGrowth, finalCache⟩, shape, rootsShape⟩ := finalDone
  have ctorsEq : built.ctors.toList = targets := by simpa using payloads
  have exprsEq : built.ctorExprs.toList = typeExpr :: targets.map (·.typ) := by simpa using exprs
  have middleToCompiled := extends_trans drainDone.2.1 ctorGrowth
  rw [shape]
  refine ⟨⟨finalSound, finalCache trivial⟩,
    extends_trans typeGrowth (extends_trans middleToCompiled finalGrowth), rfl, ?_, ?_, ?_⟩
  · change List.Forall₂ _ source.ctors.toList built.ctors.toList
    rw [ctorsEq]
    exact shapes
  · rw [rootsShape]
    change built.ctorExprs.toList = typeExpr :: built.ctors.toList.map (·.typ)
    rw [ctorsEq, exprsEq]
  · change SharingRoots.RootsRead _ _ _ (typeExpr :: built.ctors.toList.map (·.typ))
    rw [ctorsEq]
    exact .cons ⟨typeTarget, typeRel,
      read_grows cx param self (extends_trans middleToCompiled finalGrowth) typeRead⟩
      (SharingRoots.RootsRead.grow finalGrowth ctorRoots)

/-! ### Recursors -/

/-- **The rule loop**: with the warm memo, every rule body reads as a term
related to the source's in the final reader, in source order, and the loop
appends exactly the rules with their field counts. -/
theorem rules_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) :
    ∀ (sources : List RecursorRule),
      (∀ rule ∈ sources, ConstsSatisfy (SelfName context.2 self names) rule.rhs) →
      ∀ (initial : RecursorRuleCompileState) {before after : BlockState} {output : RecursorRuleCompileState},
      Good cx param self (related param names σ context) bindings before →
      rawRun (compileRecursorRules sources initial) context before = (.ok output, after) →
      Good cx param self (related param names σ context) bindings after ∧
        ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
        ∃ targets : List Ixon.RecursorRule, output.rules.toList = initial.rules.toList ++ targets ∧
          targets.map (·.fields) = sources.map (fun rule => rule.nfields.toUInt64) ∧
          SharingRoots.RootsRead (reader after) (related param names σ context) (sources.map (·.rhs))
            (targets.map (·.rhs)) := by
  intro sources
  induction sources with
  | nil =>
    intro _ initial before after output good ran
    cases ran
    exact ⟨good, ExpressionRead.Extends.refl _, [], by simp, rfl, .nil⟩
  | cons source rest ih =>
    intro scope initial before after output good ran
    rw [compileRecursorRules] at ran
    obtain ⟨compiled, middle, first, last⟩ := bind_ok ran
    unfold compileRecursorRule at first
    obtain ⟨body, bodyState, bodyRan, ruleRest⟩ := bind_ok first
    obtain ⟨headGood, headGrowth, target, rel, read⟩ :=
      compiled_root cx param self names σ bindings context free aligned external (scope source (by simp)) good
        bodyRan
    obtain ⟨rhs, root⟩ := body
    dsimp only at ruleRest
    obtain ⟨_, counted, countRan, returned⟩ := bind_ok ruleRest
    have same : counted = bodyState := by
      have state := Interning.checkedTableCount_state "recursor rule fields" source.nfields context bodyState
      rw [countRan] at state
      exact state
    subst same
    cases returned
    obtain ⟨tailGood, tailGrowth, targets, rules, fields, roots⟩ :=
      ih (fun rule member => scope rule (List.mem_cons_of_mem _ member)) _ headGood last
    refine ⟨tailGood, extends_trans headGrowth tailGrowth, { fields := source.nfields.toUInt64, rhs } :: targets,
      ?_, by simp [fields], ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using rules
    · exact .cons ⟨target, rel, read_grows cx param self tailGrowth read⟩ roots

/-- **The recursor emitter reads back as its source**: the type and every
rule body, in source order, read as related terms in the final reader, with
the memo kept warm across the rule loop; the payload is the one the source
describes, with the rules' field counts. -/
theorem recursor_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : RecursorVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    (ruleScope : ∀ rule ∈ source.rules.toList, ConstsSatisfy (SelfName context.2 self names) rule.rhs)
    {before after : BlockState} {output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr}
    (good : Good cx param self
      (related param names σ (inner source.cnst.name source.cnst.levelParams.toList context)) bindings before)
    (ran : rawRun (compileRecursor source) context before = (.ok output, after)) :
    Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      output.1 = recursorPayload source output.1.typ output.1.rules ∧
      output.1.rules.toList.map (·.fields) = source.rules.toList.map (fun rule => rule.nfields.toUInt64) ∧
      output.2.2 = output.1.typ ∧
      SharingRoots.RootsRead (reader after)
        (related param names σ (inner source.cnst.name source.cnst.levelParams.toList context))
        (source.cnst.type :: source.rules.toList.map (·.rhs)) (output.1.typ :: output.1.rules.toList.map (·.rhs)) := by
  unfold compileRecursor at ran
  have body := enter_ok ran
  have start := prepared_good cx param self bindings good
  obtain ⟨typed, middle, typeRan, rest⟩ := bind_ok body
  obtain ⟨typeGood, typeGrowth, typeTarget, typeRel, typeRead⟩ :=
    compiled_root cx param self names σ bindings (inner source.cnst.name source.cnst.levelParams.toList context)
      free aligned external scope start typeRan
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only at rest
  obtain ⟨rules, ruled, rulesRan, finished⟩ := bind_ok rest
  obtain ⟨rulesGood, rulesGrowth, targets, ruleList, fields, ruleRoots⟩ :=
    rules_correct cx param self names σ bindings (inner source.cnst.name source.cnst.levelParams.toList context)
      free aligned external source.rules.toList ruleScope {} typeGood rulesRan
  obtain ⟨clean, finalGrowth, shape, root⟩ :=
    finish_clean (fun base => finishRecursor_tidy
      (context := inner source.cnst.name source.cnst.levelParams.toList context) aligned source typeExpr typeRoot rules
      base) rulesGood.1 finished
  have rulesEq : rules.rules.toList = targets := by simpa using ruleList
  rw [shape, root]
  refine ⟨clean, extends_trans typeGrowth (extends_trans rulesGrowth finalGrowth), rfl, ?_, rfl, ?_⟩
  · change rules.rules.toList.map (·.fields) = _
    rw [rulesEq, fields]
  · change SharingRoots.RootsRead _ _ _ (typeExpr :: rules.rules.toList.map (·.rhs))
    rw [rulesEq]
    exact .cons ⟨typeTarget, typeRel,
      read_grows cx param self (extends_trans rulesGrowth finalGrowth) typeRead⟩
      (SharingRoots.RootsRead.grow finalGrowth ruleRoots)

end Emitters

end Ix.CompileCert.Emission
