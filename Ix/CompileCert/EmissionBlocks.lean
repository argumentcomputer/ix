import Ix.CompileCert.Emission

/-! # The singleton blocks read back as their sources, and decode exactly

The singleton block compilers wrap an emitter (`Ix.CompileCert.Emission`)
in the block finisher: the payload goes through the canonical sharing
builder over the block's primary tables and is serialized and addressed
once (`BlockResult.mk'`). This module composes, for the definition-like,
axiom, quotient, recursor and standalone inductive-family blocks:

* one block-finisher inversion (`block_ok`, R07-17): the payload's run, the
  sharing build and the exact wrapper;
* the emitter's root readings with the generic sharing read
  (`SharingRoots.build_read`, R07-01): the emitted record keeps the
  payload's skeleton (`SharingRoots.erase`: everything but the roots, which
  is what the source fixes) and its actual member reader reads its roots
  as terms related to the source's, in order;
* the preseed (`*Info`), which keeps the expression invariant
  (`PreseedState.preseed_good`), so every block theorem holds from a clean
  state;
* the codec: a successful block from a state whose tables are on the wire
  decodes exactly (`Ix.Sharing.Verify.BlockResultCodecWF`), through the
  success-only wire traversal (`EmissionWire`) and the builder's
  `buildConstantWithSharing_wireWF_headers` (R07-10).

`DefinitionBlock`,
`HeaderBlock`, `RecursorBlock`, `InductiveBlock` and the block half of
`FamilyWire`. -/

namespace Ix.CompileCert.EmissionBlocks

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM MemberReader)
open Ix.Sharing.Verify (BlockWireTablesWF ConstantInfoHeaderWF BlockResultCodecWF)

/-! ## The block finisher -/

theorem finish_run (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta) (context : CompileEnv × BlockEnv)
    (state : BlockState) :
    rawRun (finishConstantInfoWithSharing info blockMeta) context state =
      ((buildConstantWithSharing context.1.sharingLimits info state.refs state.univs).map
        (fun block => BlockResult.mk' block blockMeta), state) := by
  have readRun : rawRun (read : CompileM (CompileEnv × BlockEnv)) context state = (.ok context, state) := rfl
  simp only [finishConstantInfoWithSharing, finishConstantWithSharing, buildBlockConstant, rawRun_bind,
    rawRun_get, readRun]
  cases buildConstantWithSharing context.1.sharingLimits info state.refs state.univs <;> rfl

theorem build_block_run (info : Ixon.ConstantInfo) (refs : Array Address) (univs : Array Ixon.Univ)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (buildBlockConstant info refs univs) context state =
      (buildConstantWithSharing context.1.sharingLimits info refs univs, state) := by
  have readRun : rawRun (read : CompileM (CompileEnv × BlockEnv)) context state = (.ok context, state) := rfl
  simp only [buildBlockConstant, rawRun_bind, readRun]
  cases buildConstantWithSharing context.1.sharingLimits info refs univs <;> rfl

/-- **The block finisher's inversion**: a successful block ran its payload,
built the payload's sharing over the final tables, and wraps the built
constant with its exact serialization and address. -/
theorem block_ok {action : CompileM α} {next : α → CompileM BlockResult}
    (info : α → Ixon.ConstantInfo) (blockMeta : α → Ixon.ConstantMeta)
    (shape : ∀ value, next value = finishConstantInfoWithSharing (info value) (blockMeta value))
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    (ran : rawRun (action >>= next) context before = (.ok output, after)) :
    ∃ value, rawRun action context before = (.ok value, after) ∧
      buildConstantWithSharing context.1.sharingLimits (info value) after.refs after.univs = .ok output.block ∧
      output = BlockResult.mk' output.block (blockMeta value) := by
  obtain ⟨value, middle, first, last⟩ := bind_ok ran
  rw [shape, finish_run] at last
  cases built : buildConstantWithSharing context.1.sharingLimits (info value) middle.refs middle.univs with
  | error error => rw [built] at last; cases last
  | ok block =>
    rw [built] at last
    simp only [Except.map, Prod.mk.injEq, Except.ok.injEq] at last
    obtain ⟨rfl, rfl⟩ := last
    exact ⟨value, first, built, rfl⟩

/-- A built block with header-valid payload and wire-valid tables decodes
exactly. -/
theorem block_codec {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo} {state : BlockState}
    {block : Ixon.Constant} (header : ConstantInfoHeaderWF info) (tables : BlockWireTablesWF state)
    (built : buildConstantWithSharing limits info state.refs state.univs = .ok block)
    (blockMeta : Ixon.ConstantMeta) (projections : Array (Ix.Name × Ixon.Constant × Ixon.ConstantMeta)) :
    BlockResultCodecWF (BlockResult.mk' block blockMeta projections) :=
  Ix.Sharing.Verify.BlockResult.mk'_codecWF _ _ _
    (Ix.Sharing.Verify.buildConstantWithSharing_wireWF_headers header tables built)

/-! ## Skeletons: what the source fixes of each payload -/

def definitionSkeleton (source : Ix.Def) : Ixon.ConstantInfo :=
  .defn (Emission.definitionPayload source (.sort 0) (.sort 0))

def axiomSkeleton (source : AxiomVal) : Ixon.ConstantInfo :=
  .axio (Emission.axiomPayload source (.sort 0))

def quotientSkeleton (source : QuotVal) : Ixon.ConstantInfo :=
  .quot (Emission.quotientPayload source (.sort 0))

def recursorSkeleton (source : RecursorVal) : Ixon.ConstantInfo :=
  .recr (Emission.recursorPayload source (.sort 0)
    (source.rules.map fun rule => { fields := rule.nfields.toUInt64, rhs := .sort 0 }))

def inductiveSkeleton (source : Ix.Ind) : Ixon.ConstantInfo :=
  .muts #[.indc (Emission.inductivePayload source (.sort 0)
    (source.ctors.map fun ctor => Emission.constructorPayload ctor (.sort 0)))]

theorem rules_skeleton {rules : Array Ixon.RecursorRule} {source : RecursorVal}
    (fields : rules.toList.map (·.fields) = source.rules.toList.map (fun rule => rule.nfields.toUInt64)) :
    rules.map (fun rule => { rule with rhs := Ixon.Expr.sort 0 }) =
      source.rules.map (fun rule => { fields := rule.nfields.toUInt64, rhs := .sort 0 }) := by
  apply Array.ext'
  simp only [Array.toList_map]
  suffices ∀ (targets : List Ixon.RecursorRule) (sources : List RecursorRule),
      targets.map (·.fields) = sources.map (fun rule => rule.nfields.toUInt64) →
      targets.map (fun rule => { rule with rhs := Ixon.Expr.sort 0 }) =
        sources.map (fun rule => { fields := rule.nfields.toUInt64, rhs := .sort 0 }) from
    this _ _ fields
  intro targets
  induction targets with
  | nil => intro sources same; cases sources <;> simp_all
  | cons target targets ih =>
    intro sources same
    cases sources with
    | nil => simp at same
    | cons source sources =>
      simp only [List.map_cons, List.cons.injEq] at same ⊢
      refine ⟨?_, ih sources same.2⟩
      rw [← same.1]

theorem ctors_skeleton {ctors : Array Ixon.Constructor} {sources : Array ConstructorVal}
    (shapes : List.Forall₂ (fun source target => target = Emission.constructorPayload source target.typ)
      sources.toList ctors.toList) :
    ctors.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) =
      sources.map (fun ctor => Emission.constructorPayload ctor (.sort 0)) := by
  apply Array.ext'
  simp only [Array.toList_map]
  suffices ∀ (sources : List ConstructorVal) (targets : List Ixon.Constructor),
      List.Forall₂ (fun source target => target = Emission.constructorPayload source target.typ) sources targets →
      targets.map (fun ctor => { ctor with typ := Ixon.Expr.sort 0 }) =
        sources.map (fun ctor => Emission.constructorPayload ctor (.sort 0)) from
    this _ _ shapes
  intro sources targets related
  induction related with
  | nil => rfl
  | cons head _ ih =>
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih⟩
    rw [head]
    rfl

theorem definition_erase (source : Ix.Def) (type value : Ixon.Expr) :
    SharingRoots.erase (.defn (Emission.definitionPayload source type value)) =
      SharingRoots.erase (definitionSkeleton source) := rfl

theorem axiom_erase (source : AxiomVal) (type : Ixon.Expr) :
    SharingRoots.erase (.axio (Emission.axiomPayload source type)) = SharingRoots.erase (axiomSkeleton source) :=
  rfl

theorem quotient_erase (source : QuotVal) (type : Ixon.Expr) :
    SharingRoots.erase (.quot (Emission.quotientPayload source type)) =
      SharingRoots.erase (quotientSkeleton source) := rfl

theorem recursor_erase (source : RecursorVal) (type : Ixon.Expr) (rules : Array Ixon.RecursorRule)
    (fields : rules.toList.map (·.fields) = source.rules.toList.map (fun rule => rule.nfields.toUInt64)) :
    SharingRoots.erase (.recr (Emission.recursorPayload source type rules)) =
      SharingRoots.erase (recursorSkeleton source) := by
  simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, recursorSkeleton, Emission.recursorPayload,
    rules_skeleton fields, Array.map_map]
  rfl

theorem inductive_erase (source : Ix.Ind) (type : Ixon.Expr) (ctors : Array Ixon.Constructor)
    (shapes : List.Forall₂ (fun ctor target => target = Emission.constructorPayload ctor target.typ)
      source.ctors.toList ctors.toList) :
    SharingRoots.erase (.muts #[.indc (Emission.inductivePayload source type ctors)]) =
      SharingRoots.erase (inductiveSkeleton source) := by
  simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, inductiveSkeleton, Emission.inductivePayload,
    List.map_toArray, List.map_cons, List.map_nil, Ix.Sharing.Exact.mapMutConstRoots, ctors_skeleton shapes,
    Array.map_map]
  rfl

theorem family_roots (payload : Ixon.Inductive) :
    (constantInfoRootExprs (.muts #[.indc payload])).toList = payload.typ :: payload.ctors.toList.map (·.typ) := by
  simp [constantInfoRootExprs, mutConstRootExprs]

/-! ## The blocks -/

section Blocks

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self

/-- The actual member reader of an emitted record, with the block's blobs
overlaid on the context's (as the compiler's in-flight reader has them). -/
abbrev recordReader (state : BlockState) (record : Ixon.Constant) : MemberReader md :=
  MemberReader.mk' (ExpressionRead.withBlockBlobs cx state) record param self

/-- Preseeding keeps the expression invariant and extends the reader. -/
theorem preseed_then {related : Ix.Expr → CExpr md → Prop} {context : CompileEnv × BlockEnv}
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    {roots : Array (Ix.Expr × List Ix.Name)} {before middle : BlockState}
    (good : Good cx param self related bindings before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), middle)) :
    Good cx param self related bindings middle ∧ ExpressionRead.Extends (reader before).ecx (reader middle).ecx := by
  have kept : Good cx param self related bindings (rawRun (preseedExprTables roots) context before).2 ∧
      ExpressionRead.Extends (reader before).ecx (reader (rawRun (preseedExprTables roots) context before).2).ecx :=
    PreseedState.preseed_good (cx := cx) (param := param) (self := self) (related := related)
      (bindings := bindings) aligned roots context.2 before good
  rw [ran] at kept
  exact kept

/-! ### Definition-like blocks -/

/-- **A definition-like block reads back as its source**: the emitted
record keeps the source's skeleton, and its actual member reader reads its
type and value as terms related to the source's. -/
theorem definitionBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : Ix.Def)
    (typeScope : ConstsSatisfy (SelfName context.2 self names) source.type)
    (valueScope : ConstsSatisfy (SelfName context.2 self names) source.value)
    {before after : BlockState} {output : BlockResult}
    (good : Good cx param self
      (Emission.related param names σ (Emission.inner source.name source.levelParams.toList context)) bindings before)
    (ran : rawRun (compileDefinitionDataBlock source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (definitionSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.name source.levelParams.toList context))
        [source.type, source.value] (constantInfoRootExprs output.block.info).toList := by
  unfold compileDefinitionDataBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .defn payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _, _⟩ := payload; rfl) ran
  obtain ⟨clean, growth, shape, _, roots⟩ := Emission.definition_correct cx param self names σ bindings context
    aligned external source typeScope valueScope good compiled
  obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self after context.1.sharingLimits (.defn payload.1)
    output.block built roots
  refine ⟨clean, growth, ⟨_, wrapped⟩, ?_, read⟩
  rw [erased, shape]
  exact definition_erase _ _ _

theorem definitionBlock_codec (context : CompileEnv × BlockEnv)
    (source : Ix.Def) {before after : BlockState} {output : BlockResult}
    (valid : EmissionWire.Valid before)
    (ran : rawRun (compileDefinitionDataBlock source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileDefinitionDataBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .defn payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _, _⟩ := payload; rfl) ran
  have tables := (EmissionWire.Safe.definitionData source context before payload after valid compiled).1.1
  rw [wrapped]
  exact block_codec (info := .defn payload.1) trivial tables built _ _

/-- **The preseeded definition-like block reads back as its source**, from
a clean state. -/
theorem definitionInfo_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : Ix.Def)
    (typeScope : ConstsSatisfy (SelfName context.2 self names) source.type)
    (valueScope : ConstsSatisfy (SelfName context.2 self names) source.value)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (definitionSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.name source.levelParams.toList context))
        [source.type, source.value] (constantInfoRootExprs output.block.info).toList := by
  unfold compileDefinitionDataInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  have kept := preseed_then cx param self bindings
    (related := Emission.related param names σ (Emission.inner source.name source.levelParams.toList context))
    aligned (clean.good cx param self _) seeded
  obtain ⟨cleaned, growth, rest⟩ := definitionBlock_correct cx param self names σ bindings context aligned
    external source typeScope valueScope kept.1 compiled
  exact ⟨cleaned, ExpressionState.extends_trans kept.2 growth, rest⟩

theorem definitionInfo_codec (context : CompileEnv × BlockEnv)
    (source : Ix.Def) {before after : BlockState} {output : BlockResult} (wire : BlockWireTablesWF before)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileDefinitionDataInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  exact definitionBlock_codec context source (EmissionWire.seeded_valid _ context wire seeded) compiled

/-! ### Axiom and quotient blocks -/

theorem axiomBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : AxiomVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : BlockResult}
    (good : Good cx param self
      (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
      bindings before)
    (ran : rawRun (compileAxiomBlock source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (axiomSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        [source.cnst.type] (constantInfoRootExprs output.block.info).toList := by
  unfold compileAxiomBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .axio payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) ran
  obtain ⟨clean, growth, shape, _, roots⟩ := Emission.axiom_correct cx param self names σ bindings context
    aligned external source scope good compiled
  obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self after context.1.sharingLimits (.axio payload.1)
    output.block built roots
  refine ⟨clean, growth, ⟨_, wrapped⟩, ?_, read⟩
  rw [erased, shape]
  exact axiom_erase _ _

theorem axiomBlock_codec (context : CompileEnv × BlockEnv)
    (source : AxiomVal) {before after : BlockState} {output : BlockResult}
    (valid : EmissionWire.Valid before)
    (ran : rawRun (compileAxiomBlock source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileAxiomBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .axio payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) ran
  have tables := (EmissionWire.Safe.axiomPayload source context before payload after valid compiled).1.1
  rw [wrapped]
  exact block_codec (info := .axio payload.1) trivial tables built _ _

theorem axiomInfo_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : AxiomVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileAxiomInfo source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (axiomSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        [source.cnst.type] (constantInfoRootExprs output.block.info).toList := by
  unfold compileAxiomInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  have kept := preseed_then cx param self bindings
    (related := Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
    aligned (clean.good cx param self _) seeded
  obtain ⟨cleaned, growth, rest⟩ := axiomBlock_correct cx param self names σ bindings context aligned
    external source scope kept.1 compiled
  exact ⟨cleaned, ExpressionState.extends_trans kept.2 growth, rest⟩

theorem axiomInfo_codec (context : CompileEnv × BlockEnv)
    (source : AxiomVal) {before after : BlockState} {output : BlockResult} (wire : BlockWireTablesWF before)
    (ran : rawRun (compileAxiomInfo source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileAxiomInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  exact axiomBlock_codec context source (EmissionWire.seeded_valid _ context wire seeded) compiled

theorem quotientBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : QuotVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : BlockResult}
    (good : Good cx param self
      (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
      bindings before)
    (ran : rawRun (compileQuotientBlock source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (quotientSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        [source.cnst.type] (constantInfoRootExprs output.block.info).toList := by
  unfold compileQuotientBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .quot payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) ran
  obtain ⟨clean, growth, shape, _, roots⟩ := Emission.quotient_correct cx param self names σ bindings context
    aligned external source scope good compiled
  obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self after context.1.sharingLimits (.quot payload.1)
    output.block built roots
  refine ⟨clean, growth, ⟨_, wrapped⟩, ?_, read⟩
  rw [erased, shape]
  exact quotient_erase _ _

theorem quotientBlock_codec (context : CompileEnv × BlockEnv)
    (source : QuotVal) {before after : BlockState} {output : BlockResult}
    (valid : EmissionWire.Valid before)
    (ran : rawRun (compileQuotientBlock source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileQuotientBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .quot payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) ran
  have tables := (EmissionWire.Safe.quotientPayload source context before payload after valid compiled).1.1
  rw [wrapped]
  exact block_codec (info := .quot payload.1) trivial tables built _ _

theorem quotientInfo_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : QuotVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileQuotientInfo source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (quotientSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        [source.cnst.type] (constantInfoRootExprs output.block.info).toList := by
  unfold compileQuotientInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  have kept := preseed_then cx param self bindings
    (related := Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
    aligned (clean.good cx param self _) seeded
  obtain ⟨cleaned, growth, rest⟩ := quotientBlock_correct cx param self names σ bindings context aligned
    external source scope kept.1 compiled
  exact ⟨cleaned, ExpressionState.extends_trans kept.2 growth, rest⟩

theorem quotientInfo_codec (context : CompileEnv × BlockEnv)
    (source : QuotVal) {before after : BlockState} {output : BlockResult} (wire : BlockWireTablesWF before)
    (ran : rawRun (compileQuotientInfo source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileQuotientInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  exact quotientBlock_codec context source (EmissionWire.seeded_valid _ context wire seeded) compiled

/-! ### Recursor blocks -/

theorem recursorPayload_rules (source : RecursorVal) :
    Emission.Yields (compileRecursor source) (fun output => output.1.rules.size < UInt64.size) := by
  unfold compileRecursor
  refine Emission.Yields.withCurrent _ (Emission.Yields.withUnivCtx _
    (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Emission.Yields.bindAny _ fun rules => ?_
  intro context before output after ran
  exact (Emission.recursorHeader source typeExpr typeRoot rules context before output after ran).2.2.2.2.2

theorem recursorBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : RecursorVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    (ruleScope : ∀ rule ∈ source.rules.toList, ConstsSatisfy (SelfName context.2 self names) rule.rhs)
    {before after : BlockState} {output : BlockResult}
    (good : Good cx param self
      (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
      bindings before)
    (ran : rawRun (compileRecursorBlock source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (recursorSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        (source.cnst.type :: source.rules.toList.map (·.rhs)) (constantInfoRootExprs output.block.info).toList := by
  unfold compileRecursorBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .recr payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) ran
  obtain ⟨clean, growth, shape, fields, _, roots⟩ := Emission.recursor_correct cx param self names σ bindings
    context aligned external source scope ruleScope good compiled
  obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self after context.1.sharingLimits (.recr payload.1)
    output.block built roots
  refine ⟨clean, growth, ⟨_, wrapped⟩, ?_, read⟩
  rw [erased, shape]
  exact recursor_erase _ _ _ fields

theorem recursorBlock_codec (context : CompileEnv × BlockEnv)
    (source : RecursorVal) {before after : BlockState} {output : BlockResult}
    (valid : EmissionWire.Valid before)
    (ran : rawRun (compileRecursorBlock source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileRecursorBlock at ran
  obtain ⟨payload, compiled, built, wrapped⟩ := block_ok (fun payload => .recr payload.1) (fun payload => payload.2.1)
    (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) ran
  have tables := (EmissionWire.Safe.recursorPayload source context before payload after valid compiled).1.1
  have header := recursorPayload_rules source context before payload after compiled
  rw [wrapped]
  exact block_codec (info := .recr payload.1) header tables built _ _

theorem recursorInfo_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : RecursorVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    (ruleScope : ∀ rule ∈ source.rules.toList, ConstsSatisfy (SelfName context.2 self names) rule.rhs)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileRecursorInfo source) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (recursorSkeleton source) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        (source.cnst.type :: source.rules.toList.map (·.rhs)) (constantInfoRootExprs output.block.info).toList := by
  unfold compileRecursorInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  have kept := preseed_then cx param self bindings
    (related := Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
    aligned (clean.good cx param self _) seeded
  obtain ⟨cleaned, growth, rest⟩ := recursorBlock_correct cx param self names σ bindings context aligned
    external source scope ruleScope kept.1 compiled
  exact ⟨cleaned, ExpressionState.extends_trans kept.2 growth, rest⟩

theorem recursorInfo_codec (context : CompileEnv × BlockEnv)
    (source : RecursorVal) {before after : BlockState} {output : BlockResult} (wire : BlockWireTablesWF before)
    (ran : rawRun (compileRecursorInfo source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileRecursorInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  exact recursorBlock_codec context source (EmissionWire.seeded_valid _ context wire seeded) compiled

/-! ### Standalone inductive-family blocks -/

/-- **The family finisher's inversion**: it changes no state, builds the
one-member mutual payload's sharing over the tables, and wraps it with the
family's projections at the built block's address. -/
theorem familyFinish_ok (source : InductiveVal) (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (pairs : Array (Ix.Name × Ixon.ConstantMeta)) {context : CompileEnv × BlockEnv}
    {before after : BlockState} {output : BlockResult}
    (ran : rawRun (finishInductiveFamilyBlock source ind indMeta pairs) context before = (.ok output, after)) :
    after = before ∧
      buildConstantWithSharing context.1.sharingLimits (.muts #[.indc ind]) before.refs before.univs =
        .ok output.block ∧
      output = BlockResult.mk' output.block .empty
        (buildInductiveProjections source indMeta pairs (Address.admissionHash (Ixon.ser output.block))) := by
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨_, middle, guarded, rest⟩ := bind_ok ran
  have same : middle = before := by
    have state := Interning.checkedTableCount_state "inductive constructors" source.ctors.size context before
    rw [guarded] at state
    exact state
  subst middle
  obtain ⟨_, middle, guarded, rest⟩ := bind_ok rest
  have same : middle = before := by
    have state := Interning.checkedTableCount_state "constructor projections" pairs.size context before
    rw [guarded] at state
    exact state
  subst middle
  obtain ⟨cache, cached, getRan, rest⟩ := bind_ok rest
  rw [rawRun_get] at getRan
  cases getRan
  obtain ⟨block, built, buildRan, returned⟩ := bind_ok rest
  rw [build_block_run] at buildRan
  obtain ⟨buildEq, stateEq⟩ := Prod.mk.inj buildRan
  subst stateEq
  dsimp only at returned
  rw [rawRun_pure] at returned
  obtain ⟨outputEq, afterEq⟩ := Prod.mk.inj returned
  cases Except.ok.inj outputEq
  exact ⟨afterEq.symm, buildEq, rfl⟩

theorem inductiveData_ctors (source : Ix.Ind) :
    Emission.Yields (compileInductiveData source) (fun output => output.1.ctors.size < UInt64.size) := by
  unfold compileInductiveData
  refine Emission.Yields.withCurrent _ (Emission.Yields.withUnivCtx _
    (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Emission.Yields.bindAny _ fun metadata => Emission.Yields.bindAny _ fun built => ?_
  intro context before output after ran
  exact (Emission.inductiveDataHeader source typeExpr typeRoot metadata built context before output after ran).2.2.2

/-- **A standalone inductive-family block reads back as its source**: the
emitted record keeps the family's skeleton (headers and constructor
headers), and its actual member reader reads the type and every
constructor type, in source order, as terms related to the source's. -/
theorem familyBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : InductiveVal)
    (constructors : Array ConstructorVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors.toList, ConstsSatisfy (SelfName context.2 self names) ctor.cnst.type)
    {before after : BlockState} {output : BlockResult}
    (good : Good cx param self
      (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
      bindings before)
    (ran : rawRun (compileInductiveFamilyBlock source constructors) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ indMeta pairs, output = BlockResult.mk' output.block .empty
        (buildInductiveProjections source indMeta pairs (Address.admissionHash (Ixon.ser output.block)))) ∧
      SharingRoots.erase output.block.info =
        SharingRoots.erase (inductiveSkeleton (Emission.sourceData source constructors)) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        (source.cnst.type :: constructors.toList.map (·.cnst.type))
        (constantInfoRootExprs output.block.info).toList := by
  unfold compileInductiveFamilyBlock at ran
  obtain ⟨payload, middle, compiled, finished⟩ := bind_ok ran
  rw [Emission.compileInductive_eq] at compiled
  obtain ⟨ind, indMeta, pairs, exprs⟩ := payload
  dsimp only at finished
  obtain ⟨same, built, wrapped⟩ := familyFinish_ok source ind indMeta pairs finished
  subst same
  obtain ⟨clean, growth, shape, ctorShapes, _, roots⟩ := Emission.inductiveData_correct cx param self names σ
    bindings context aligned external (Emission.sourceData source constructors) scope ctorScope good compiled
  dsimp only at shape ctorShapes roots
  have rootsList := family_roots ind
  rw [← rootsList] at roots
  obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self after context.1.sharingLimits
    (.muts #[.indc ind]) output.block built roots
  refine ⟨clean, growth, ⟨indMeta, pairs, wrapped⟩, ?_, read⟩
  rw [erased, shape]
  exact inductive_erase _ _ _ ctorShapes

theorem familyBlock_codec (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal) {before after : BlockState}
    {output : BlockResult} (valid : EmissionWire.Valid before)
    (ran : rawRun (compileInductiveFamilyBlock source constructors) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileInductiveFamilyBlock at ran
  obtain ⟨payload, middle, compiled, finished⟩ := bind_ok ran
  have tables := (EmissionWire.Safe.inductivePayload source constructors context before payload middle valid
    compiled).1.1
  rw [Emission.compileInductive_eq] at compiled
  have bounded := inductiveData_ctors (Emission.sourceData source constructors) context before payload middle compiled
  obtain ⟨ind, indMeta, pairs, exprs⟩ := payload
  dsimp only at finished
  obtain ⟨same, built, wrapped⟩ := familyFinish_ok source ind indMeta pairs finished
  subst same
  have header : ConstantInfoHeaderWF (.muts #[.indc ind]) := by
    refine ⟨by change 1 < UInt64.size; decide, ?_⟩
    intro member present
    have memberEq : member = .indc ind := by simpa using present
    subst memberEq
    exact bounded
  rw [wrapped]
  exact block_codec header tables built _ _

theorem familyInfo_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : InductiveVal)
    (constructors : Array ConstructorVal)
    (scope : ConstsSatisfy (SelfName context.2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors.toList, ConstsSatisfy (SelfName context.2 self names) ctor.cnst.type)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileInductiveFamilyInfo source constructors) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ indMeta pairs, output = BlockResult.mk' output.block .empty
        (buildInductiveProjections source indMeta pairs (Address.admissionHash (Ixon.ser output.block)))) ∧
      SharingRoots.erase output.block.info =
        SharingRoots.erase (inductiveSkeleton (Emission.sourceData source constructors)) ∧
      SharingRoots.RootsRead (recordReader cx param self after output.block)
        (Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
        (source.cnst.type :: constructors.toList.map (·.cnst.type))
        (constantInfoRootExprs output.block.info).toList := by
  unfold compileInductiveFamilyInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  have kept := preseed_then cx param self bindings
    (related := Emission.related param names σ (Emission.inner source.cnst.name source.cnst.levelParams.toList context))
    aligned (clean.good cx param self _) seeded
  obtain ⟨cleaned, growth, rest⟩ := familyBlock_correct cx param self names σ bindings context aligned
    external source constructors scope ctorScope kept.1 compiled
  exact ⟨cleaned, ExpressionState.extends_trans kept.2 growth, rest⟩

theorem familyInfo_codec (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal) {before after : BlockState}
    {output : BlockResult} (wire : BlockWireTablesWF before)
    (ran : rawRun (compileInductiveFamilyInfo source constructors) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileInductiveFamilyInfo at ran
  obtain ⟨_, middle, seeded, compiled⟩ := bind_ok ran
  exact familyBlock_codec context source constructors (EmissionWire.seeded_valid _ context wire seeded)
    compiled

end Blocks

end Ix.CompileCert.EmissionBlocks
