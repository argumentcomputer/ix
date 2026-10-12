import Ix.CompileCert.ProductionExpression

/-! Declaration payload assembly preserves the certified reading of its type
and value. Presentation metadata is not part of the result relation. -/

namespace Ix.CompileCert.DefinitionEmission

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

def drained (state : BlockState) : BlockState :=
  { state with
    arena := {}, metaSharing := #[], p3MetaRefs := #[], p3MetaRefsIndex := {},
    metaUnivs := #[], metaUnivsIndex := {}, univPatches := #[], exprCache := {} }

def Clean (bindings : ExpressionState.Bindings) (state : BlockState) : Prop :=
  ExpressionState.StateSound bindings state ∧ state.exprCache = {} ∧ state.p3MetaMode = false

/-- Entry conditions on retained state only. The production initializer
discards old raw-universe and metadata tables, so their validity is not assumed. -/
structure Ready (bindings : ExpressionState.Bindings) (state : BlockState) : Prop where
  refs : Interning.RefIndexSound state
  univs : Interning.UnivIndexSound state
  canon : UniversePipeline.CanonCacheExact state
  bindings : ExpressionState.bindingView state = bindings
  cache : state.exprCache = {}
  mode : state.p3MetaMode = false

theorem Clean.ready {bindings : ExpressionState.Bindings} {state : BlockState}
    (clean : Clean bindings state) : Ready bindings state :=
  ⟨clean.1.2.1, clean.1.1.tables.1, clean.1.1.canonCache, clean.1.2.2.2, clean.2.1, clean.2.2⟩

theorem drained_clean (bindings : ExpressionState.Bindings) (state : BlockState)
    (sound : ExpressionState.StateSound bindings state) (mode : state.p3MetaMode = false) :
    Clean bindings (drained state) :=
  ⟨⟨⟨sound.1.rawCache, sound.1.canonCache, sound.1.tables.1, Interning.IndexSound.empty⟩,
    sound.2.1, Interning.IndexSound.empty, sound.2.2.2⟩, rfl, mode⟩

theorem Clean.good (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (related : Ix.Expr → Kernel.Expr → Prop)
    {bindings : ExpressionState.Bindings} {state : BlockState} (clean : Clean bindings state) :
    ExpressionState.Good cx base param self related bindings state := by
  refine ⟨clean.1, ?_⟩
  intro source value found
  change state.exprCache.get? source = some value at found
  rw [clean.2.1] at found
  simp at found

section Finalization

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
  (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings)
  (context : CompileEnv × BlockEnv)
local notation "reader" => ExpressionRead.blockReader cx base param self

theorem drained_reader (state : BlockState) (mode : state.p3MetaMode = false) :
    reader (drained state) = reader state := by
  simp only [ExpressionRead.blockReader, drained, mode, Bool.false_eq_true, ↓reduceIte]

def Preserves (action : CompileM α) : Prop :=
  ∀ before, Clean bindings before →
    Clean bindings (rawRun action context before).2 ∧
      ExpressionRead.Extends (reader before).ecx (reader (rawRun action context before).2).ecx

theorem Preserves.pure (value : α) : Preserves cx base param self bindings context (pure value) :=
  fun _ clean => ⟨clean, ExpressionState.extends_refl _⟩

theorem Preserves.bind {action : CompileM α} {next : α → CompileM β}
    (first : Preserves cx base param self bindings context action)
    (last : ∀ value, Preserves cx base param self bindings context (next value)) :
    Preserves cx base param self bindings context (action >>= next) := by
  intro before clean
  have head := first before clean
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact head
    | ok value =>
      have tail := last value middle head.1
      exact ⟨tail.1, ExpressionState.extends_trans head.2 tail.2⟩

theorem names_clean {before after : BlockState}
    (frame : BlobWrites.withoutNamesBlobs after = BlobWrites.withoutNamesBlobs before)
    (clean : Clean bindings before) : Clean bindings after := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (congrArg UniverseMeaning.CacheSound frame).mpr clean.1.1.rawCache
  · exact (congrArg UniversePipeline.CanonCacheExact frame).mpr clean.1.1.canonCache
  · exact (congrArg UniversePipeline.TablesSound frame).mpr clean.1.1.tables
  · exact (congrArg Interning.RefIndexSound frame).mpr clean.1.2.1
  · exact (congrArg Interning.MetaRefIndexSound frame).mpr clean.1.2.2.1
  · exact (congrArg ExpressionState.bindingView frame).trans clean.1.2.2.2
  · exact (congrArg BlockState.exprCache frame).trans clean.2.1
  · exact (congrArg BlockState.p3MetaMode frame).trans clean.2.2

theorem Preserves.names (action : CompileM α)
    (framed : ∀ before, BlobWrites.withoutNamesBlobs (rawRun action context before).2 =
        BlobWrites.withoutNamesBlobs before ∧ BlobWrites.Extends context.1.blobs before (rawRun action context before).2)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Preserves cx base param self bindings context action := by
  intro before clean
  have facts := framed before
  exact ⟨names_clean bindings facts.1 clean,
    BlobWrites.reader_extends context.1.blobs before _ facts.1 facts.2 cx base param self aligned⟩

theorem Preserves.compileName (name : Ix.Name)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Preserves cx base param self bindings context (compileName name) :=
  Preserves.names cx base param self bindings context _ (BlobWrites.compileName_preserves name context) aligned

theorem Preserves.compileNames (names : Array Ix.Name)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Preserves cx base param self bindings context (compileNames names) :=
  Preserves.names cx base param self bindings context _ (BlobWrites.compileNames_preserves names context) aligned

theorem Preserves.recordDefHints (name : Ix.Name) (hints : Lean.ReducibilityHints) :
    Preserves cx base param self bindings context (recordDefHints name hints) := by
  intro before clean
  exact ⟨⟨⟨⟨clean.1.1.rawCache, clean.1.1.canonCache, clean.1.1.tables⟩,
    clean.1.2.1, clean.1.2.2.1, clean.1.2.2.2⟩, clean.2.1, clean.2.2⟩, ExpressionState.extends_refl _⟩

end Finalization

def definitionPayload (d : Ix.Def) (type value : Ixon.Expr) : Ixon.Definition :=
  { kind := d.kind, safety := d.safety, lvls := d.levelParams.size.toUInt64, typ := type, value }

def definitionMetadata (d : Ix.Def) (block : BlockEnv) (before : BlockState)
    (typeRoot valueRoot : UInt64) : Ixon.ConstantMeta :=
  { Ixon.ConstantMeta.new (.defn d.name.getHash (d.levelParams.map (·.getHash)) (d.all.map (·.getHash))
      (block.mutCtx.toList.toArray.qsort (fun a b =>
        if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map (·.1.getHash))
      before.arena typeRoot valueRoot) with
    metaSharing := before.metaSharing, metaRefs := before.p3MetaRefs,
    metaUnivs := before.metaUnivs, univPatches := before.univPatches }

def finishNames (d : Ix.Def) (block : BlockEnv) : CompileM Unit := do
  compileName d.name
  compileNames d.levelParams
  compileNames d.all
  compileNames (block.mutCtx.toList.toArray.map (·.1))
  recordDefHints d.name (match d.kind with | .defn => d.hints | .thm | .opaq => .opaque)

theorem finishDefinitionDataCompilation_run (d : Ix.Def) (type value : Ixon.Expr) (typeRoot valueRoot : UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (finishDefinitionDataCompilation d type typeRoot value valueRoot) context before =
      rawRun (do
        finishNames d context.2
        pure (definitionPayload d type value, definitionMetadata d context.2 before typeRoot valueRoot, type, value))
        context (drained before) := by
  simp only [finishDefinitionDataCompilation, finishNames, takeArena, takeMetaSharing,
    takeMetaRefs, takeUnivPatches, clearExprCache, getMutCtxAddrs, bind_assoc,
    rawRun_bind, Interning.rawRun_modifyGet, rawRun_modify, UniverseMeaning.rawRun_readBlock,
    rawRun_pure, drained, definitionPayload, definitionMetadata]
  rfl

theorem finishNames_preserves (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) (d : Ix.Def) :
    Preserves cx base param self bindings context (finishNames d context.2) := by
  unfold finishNames
  with_reducible repeat' first
    | exact Preserves.compileName cx base param self bindings context _ aligned
    | exact Preserves.compileNames cx base param self bindings context _ aligned
    | exact Preserves.recordDefHints cx base param self bindings context _ _
    | refine Preserves.bind cx base param self bindings context ?_ (fun _ => ?_)

theorem finishDefinition_correct (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (d : Ix.Def) (type value : Ixon.Expr) (typeRoot valueRoot : UInt64)
    (before : BlockState) (sound : ExpressionState.StateSound bindings before) (mode : before.p3MetaMode = false) :
    let result := rawRun (finishDefinitionDataCompilation d type typeRoot value valueRoot) context before
    Clean bindings result.2 ∧
      ExpressionRead.Extends (ExpressionRead.blockReader cx base param self before).ecx
        (ExpressionRead.blockReader cx base param self result.2).ecx ∧
      ∀ output, result.1 = .ok output → output.1 = definitionPayload d type value ∧
        output.2.2 = (type, value) := by
  dsimp only
  rw [finishDefinitionDataCompilation_run, rawRun_bind]
  have tail := finishNames_preserves cx base param self bindings context aligned d (drained before)
    (drained_clean bindings before sound mode)
  rw [drained_reader cx base param self before mode] at tail
  cases ran : rawRun (finishNames d context.2) context (drained before) with
  | mk outcome after =>
    rw [ran] at tail
    cases outcome with
    | error error => exact ⟨tail.1, tail.2, by intro output bad; cases bad⟩
    | ok doneValue =>
      refine ⟨tail.1, tail.2, ?_⟩
      intro output success
      cases Except.ok.inj success
      exact ⟨rfl, rfl⟩

def body (d : Ix.Def) : CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) := do
  let (typeExpr, typeRoot) ← compileExpr d.type
  let (valueExpr, valueRoot) ← compileExpr d.value
  finishDefinitionDataCompilation d typeExpr typeRoot valueExpr valueRoot

def PayloadRelated (names : Ix.Name → Kernel.Name → Prop) (sourceParams : List Ix.Name)
    (params : List Kernel.Name) (reader : Kernel.Reader.MemberReader) (source : Ix.Def) (target : Ixon.Definition) : Prop :=
  target.kind = source.kind ∧ target.safety = source.safety ∧
    target.lvls = source.levelParams.size.toUInt64 ∧
    ∃ type value, ExpressionState.Related names sourceParams params source.type type ∧
      ExpressionState.Related names sourceParams params source.value value ∧
      reader.read target.typ = .ok type ∧ reader.read target.value = .ok value

/-- Full natural-number arity additionally requires the wire-capacity bound.
The production header still uses `Nat.toUInt64`; this is not a totality proof. -/
theorem PayloadRelated.levels {names : Ix.Name → Kernel.Name → Prop} {sourceParams : List Ix.Name}
    {params : List Kernel.Name} {reader : Kernel.Reader.MemberReader} {source : Ix.Def} {target : Ixon.Definition}
    (related : PayloadRelated names sourceParams params reader source target)
    (bounded : source.levelParams.size < UInt64.size) : target.lvls.toNat = source.levelParams.size := by
  rw [related.2.2.1]
  exact UInt64.toNat_ofNat_of_lt' bounded

section Body

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
  (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
  (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
local notation "param" => Kernel.Reader.paramOf params
local notation "related" => ExpressionState.Related names (BlockEnv.univCtx (Prod.snd context)) params
local notation "reader" => ExpressionRead.blockReader cx base param self
local notation "Good" => ExpressionState.Good cx base param self related bindings

def Result (source : Ix.Def) (before : BlockState)
    (result : Except CompileError (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) × BlockState) : Prop :=
  Good result.2 ∧ ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
    ∀ output, result.1 = .ok output → Clean bindings result.2 ∧
      PayloadRelated names context.2.univCtx params (reader result.2) source output.1 ∧
      output.2.2 = (output.1.typ, output.1.value)

theorem body_correct (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (d : Ix.Def) (before : BlockState) (good : Good before) (mode : before.p3MetaMode = false) :
    Result cx base self names params bindings context d before (rawRun (body d) context before) := by
  unfold Result body
  rw [rawRun_bind]
  have typeChecked := MetadataMode.compileExpr_checked cx base self names params bindings context arity aligned external selfSound
    d.type before good mode
  cases typeRan : rawRun (compileExpr d.type) context before with
  | mk typeOutcome middle =>
    rw [typeRan] at typeChecked
    cases typeOutcome with
    | error error => exact ⟨typeChecked.1.1, typeChecked.1.2.1, by intro output bad; cases bad⟩
    | ok typeResult =>
      rcases typeResult with ⟨typeExpr, typeRoot⟩
      dsimp only
      rw [rawRun_bind]
      have valueChecked := MetadataMode.compileExpr_checked cx base self names params bindings context arity aligned external selfSound
        d.value middle typeChecked.1.1 (typeChecked.2 _ rfl)
      cases valueRan : rawRun (compileExpr d.value) context middle with
      | mk valueOutcome compiled =>
        rw [valueRan] at valueChecked
        cases valueOutcome with
        | error error => exact ⟨valueChecked.1.1, ExpressionState.extends_trans typeChecked.1.2.1 valueChecked.1.2.1,
            by intro output bad; cases bad⟩
        | ok valueResult =>
          rcases valueResult with ⟨valueExpr, valueRoot⟩
          dsimp only
          have finished := finishDefinition_correct cx base param self bindings context aligned d typeExpr valueExpr
            typeRoot valueRoot compiled valueChecked.1.1.1 (valueChecked.2 _ rfl)
          have typeRead := ExpressionState.meaning_grows cx base param self related
            (ExpressionState.extends_trans valueChecked.1.2.1 finished.2.1) (typeChecked.1.2.2 _ rfl)
          have valueRead := ExpressionState.meaning_grows cx base param self related finished.2.1 (valueChecked.1.2.2 _ rfl)
          refine ⟨finished.1.good cx base param self related,
            ExpressionState.extends_trans typeChecked.1.2.1 (ExpressionState.extends_trans valueChecked.1.2.1 finished.2.1), ?_⟩
          intro output success
          have shape := finished.2.2 output success
          refine ⟨finished.1, ?_, ?_⟩
          · rw [shape.1]
            obtain ⟨targetType, relatedType, readType⟩ := typeRead
            obtain ⟨targetValue, relatedValue, readValue⟩ := valueRead
            exact ⟨rfl, rfl, rfl, targetType, targetValue, relatedType, relatedValue, readType, readValue⟩
          · rw [shape.1]
            exact shape.2

end Body

/-- State actually installed by `withUnivCtx` followed by `resetArena`.
Primary tables remain preseeded; the old raw-universe memo is discarded. -/
def prepared (state : BlockState) : BlockState :=
  { state with
    univCache := {}, arena := {}, metaUnivs := #[], metaUnivsIndex := {}, univPatches := #[],
    p3MetaRefs := #[], p3MetaRefsIndex := {}, p3Records := {} }

def contextFor (d : Ix.Def) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := d.name, univCtx := d.levelParams.toList })

theorem prepared_clean (bindings : ExpressionState.Bindings) (before : BlockState)
    (ready : Ready bindings before) : Clean bindings (prepared before) := by
  refine ⟨⟨⟨?_, ready.canon, ready.univs, Interning.IndexSound.empty⟩,
    ready.refs, Interning.IndexSound.empty, ready.bindings⟩, ready.cache, ready.mode⟩
  intro key value found
  simp [prepared] at found

theorem prepared_reader (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (before : BlockState) (mode : before.p3MetaMode = false) :
    ExpressionRead.blockReader cx base param self (prepared before) = ExpressionRead.blockReader cx base param self before := by
  simp only [ExpressionRead.blockReader, prepared, mode, Bool.false_eq_true, ↓reduceIte]

theorem rawRun_withBlockEnv (update : BlockEnv → BlockEnv) (action : CompileM α)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (withBlockEnv update action) context before = rawRun action (context.1, update context.2) before := rfl

theorem compileDefinitionData_run (d : Ix.Def) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compileDefinitionData d) context before = rawRun (body d) (contextFor d context) (prepared before) := by
  simp only [compileDefinitionData, withCurrent, withUnivCtx, resetArena, body,
    rawRun_withBlockEnv, rawRun_bind, rawRun_modify, contextFor, prepared]

theorem compileDefinition_eq (d : Ix.DefinitionVal) : compileDefinition d = compileDefinitionData (definitionValData d) := rfl
theorem compileTheorem_eq (d : Ix.TheoremVal) : compileTheorem d = compileDefinitionData (theoremValData d) := rfl
theorem compileOpaque_eq (d : Ix.OpaqueVal) : compileOpaque d = compileDefinitionData (opaqueValData d) := rfl

theorem compileDefinitionData_correct (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (d : Ix.Def)
    (arity : params.length = d.levelParams.size)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before : BlockState) (ready : Ready bindings before) :
    Result cx base self names params bindings (contextFor d context) d before
      (rawRun (compileDefinitionData d) context before) := by
  rw [compileDefinitionData_run]
  have initial := prepared_clean bindings before ready
  have checked := body_correct cx base self names params bindings (contextFor d context)
    (by simpa [contextFor] using arity) aligned external selfSound d (prepared before)
    (initial.good cx base (Kernel.Reader.paramOf params) self _) initial.2.2
  change ExpressionState.Good _ _ _ _ _ _ _ ∧ _ ∧ _ at checked ⊢
  rw [prepared_reader cx base (Kernel.Reader.paramOf params) self before ready.mode] at checked
  exact checked

theorem compileDefinition_correct (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (d : Ix.DefinitionVal)
    (arity : params.length = d.cnst.levelParams.size)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before : BlockState) (ready : Ready bindings before) :
    Result cx base self names params bindings (contextFor (definitionValData d) context) (definitionValData d) before
      (rawRun (compileDefinition d) context before) :=
  compileDefinitionData_correct cx base self names params bindings context (definitionValData d)
    arity aligned external selfSound before ready

theorem compileTheorem_correct (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (d : Ix.TheoremVal)
    (arity : params.length = d.cnst.levelParams.size)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before : BlockState) (ready : Ready bindings before) :
    Result cx base self names params bindings (contextFor (theoremValData d) context) (theoremValData d) before
      (rawRun (compileTheorem d) context before) :=
  compileDefinitionData_correct cx base self names params bindings context (theoremValData d)
    arity aligned external selfSound before ready

theorem compileOpaque_correct (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (d : Ix.OpaqueVal)
    (arity : params.length = d.cnst.levelParams.size)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before : BlockState) (ready : Ready bindings before) :
    Result cx base self names params bindings (contextFor (opaqueValData d) context) (opaqueValData d) before
      (rawRun (compileOpaque d) context before) :=
  compileDefinitionData_correct cx base self names params bindings context (opaqueValData d)
    arity aligned external selfSound before ready

end Ix.CompileCert.DefinitionEmission
