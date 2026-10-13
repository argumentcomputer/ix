import Ix.CompileCert.FinalUniverses
import Ix.CompileCert.PreseedWire

/-! Primary-table wire validity for successful production payload emission.
The universe table is frozen by the checked production guard. Reference
insertions use dependency widths or the hash wrapper's output-width theorem.
Failed runs are deliberately not claimed wire-valid: a rejected universe
miss may have written its candidate before the guard reports the error. -/

namespace Ix.CompileCert.EmissionWire

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open UniversePipeline (Preserves)
open Ix.Sharing.Verify (BlockWireTablesWF)
open private Ix.CompileM.compileKVMap.match_5
  Ix.CompileM.compileKVMap._sparseCasesOn_5 from Ix.CompileM

def Valid (environment : CompileEnv) (state : BlockState) : Prop :=
  ReferenceWidths.LookupWidths environment state ∧ BlockWireTablesWF state ∧ state.univsFinal = true

def view (state : BlockState) :=
  (ExpressionState.bindingView state, state.refs, state.univs, state.univsFinal)

theorem Valid.of_view {environment : CompileEnv} {before after : BlockState}
    (valid : Valid environment before) (same : view after = view before) : Valid environment after := by
  have bindings := congrArg Prod.fst same
  have refs := congrArg (fun state => state.2.1) same
  have univs := congrArg (fun state => state.2.2.1) same
  have flag := congrArg (fun state => state.2.2.2) same
  change ExpressionState.bindingView after = ExpressionState.bindingView before at bindings
  refine ⟨?_, WireTables.of_same valid.2.1 refs univs, flag.trans valid.2.2⟩
  intro name address found
  rw [bindings] at found
  exact valid.1 name address found

def Safe (action : CompileM α) (post : α → Prop := fun _ => True) : Prop :=
  ∀ context before, Valid context.1 before → ∀ value after,
    rawRun action context before = (.ok value, after) → Valid context.1 after ∧ post value

theorem Safe.framed {action : CompileM α} (frame : Preserves view action) : Safe action := by
  intro context before valid value after ran
  have same := frame context before
  rw [ran] at same
  exact ⟨valid.of_view same, trivial⟩

theorem Safe.pure (value : α) : Safe (pure value) := Safe.framed (Preserves.pure _ _)

theorem Safe.throw (error : CompileError) : Safe (throw error : CompileM α) :=
  Safe.framed (Preserves.throw _ _)

theorem Safe.bind {action : CompileM α} {next : α → CompileM β} {first : α → Prop} {last : β → Prop}
    (head : Safe action first) (tail : ∀ value, first value → Safe (next value) last) : Safe (action >>= next) last := by
  intro context before valid output after ran
  obtain ⟨middle, state, firstRan, lastRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have checked := head context before valid middle state firstRan
  exact tail middle checked.2 context state checked.1 output after lastRan

theorem Safe.forget {action : CompileM α} {post : α → Prop} (safe : Safe action post) : Safe action := by
  intro context before valid value after ran
  exact ⟨(safe context before valid value after ran).1, trivial⟩

theorem Safe.seq {action : CompileM α} {next : α → CompileM β}
    (head : Safe action) (tail : ∀ value, Safe (next value)) : Safe (action >>= next) :=
  Safe.bind head (fun value _ => tail value)

theorem Safe.get : Safe getBlockState := Safe.framed (Preserves.get _)
theorem Safe.read : Safe getCompileEnv := Safe.framed (fun _ _ => rfl)
theorem Safe.readBlock : Safe getBlockEnv := Safe.framed (Preserves.read _)

theorem Safe.modify (update : BlockState → BlockState) (same : ∀ before, view (update before) = view before) :
    Safe (modifyBlockState update) := Safe.framed (Preserves.modify _ _ same)

theorem Safe.modifyGet (update : BlockState → α × BlockState) (same : ∀ before, view (update before).2 = view before) :
    Safe (modifyGetBlockState update) := Safe.framed (fun _ before => same before)

theorem Safe.checkedIndex (table : String) (index : Nat) : Safe (checkedTableIndex table index) := by
  apply Safe.framed
  intro context before
  rw [Interning.checkedTableIndex_state]

theorem Safe.checkedCount (table : String) (count : Nat) : Safe (checkedTableCount table count) := by
  apply Safe.framed
  intro context before
  rw [Interning.checkedTableCount_state]

theorem Safe.mapM_list (items : List α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Safe (action item)) : Safe (items.mapM action) := by
  induction items with
  | nil => exact Safe.pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact Safe.bind (each item (by simp)) fun _ _ =>
      Safe.bind (ih (fun item member => each item (by simp [member]))) fun _ _ => Safe.pure _

theorem Safe.map {action : CompileM α} {post : α → Prop} (safe : Safe action post) (f : α → β) : Safe (f <$> action) := by
  rw [map_eq_pure_bind]
  exact Safe.bind safe (fun _ _ => Safe.pure _)

theorem Safe.mapM_array (items : Array α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Safe (action item)) : Safe (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Safe.map (Safe.mapM_list _ action (fun item member => each item (by simpa using member))) _

theorem Safe.compileLevel (source : Level) : Safe (compileAndInternUnivCanon source) := by
  intro context before valid output after ran
  have frozen := FinalUniverses.compile_no_growth source context before after valid.2.2 output ran
  have frame := ExpressionLeaves.compileAndInternUnivCanon_frame source context before
  rw [ran] at frame
  have widths := congrArg (ReferenceWidths.LookupWidths context.1) frame
  have refs := congrArg BlockState.refs frame
  exact ⟨⟨widths.mpr valid.1, WireTables.of_same valid.2.1 refs frozen.1, frozen.2⟩, trivial⟩

theorem Safe.internRef (address : Address) (width : address.hash.size = 32) : Safe (internRef address) := by
  intro context before valid output after ran
  have wire := WireTables.internRef_preserves context before address valid.2.1 width
  have frame := ExpressionState.internRef_frame address context before
  rw [ran] at wire frame
  have widths := congrArg (ReferenceWidths.LookupWidths context.1) frame
  have flag := congrArg BlockState.univsFinal frame
  exact ⟨⟨widths.mpr valid.1, wire, flag.trans valid.2.2⟩, trivial⟩

theorem Safe.lookup (name : Name) : Safe (lookupConstAddr name) (fun address => address.hash.size = 32) := by
  intro context before valid output after ran
  have state := ExpressionState.lookupConstAddr_state name context before
  rw [ran] at state
  have width := ReferenceWidths.Safe.lookup name context before valid.1
  rw [ran] at width
  refine ⟨?_, width.2 output rfl⟩
  rw [show after = before from state]
  exact valid

theorem Safe.blob (bytes : ByteArray) : Safe (storeBlob bytes) (fun address => address.hash.size = 32) := by
  intro context before valid output after ran
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  rw [ran] at frame
  have same := congrArg view frame
  have width := ReferenceWidths.Safe.blob bytes context before valid.1
  rw [ran] at width
  exact ⟨valid.of_view same, width.2 output rfl⟩

theorem Safe.compileName (name : Name) : Safe (compileName name) := by
  apply Safe.framed
  intro context before
  have same := congrArg view (BlobWrites.compileName_preserves name context before).1
  exact same

theorem Safe.alloc (node : Ixon.ExprMetaData) : Safe (allocArenaNode node) := Safe.modifyGet _ (fun _ => rfl)
theorem Safe.patch (root : UInt64) (indices : Array UInt64) : Safe (pushUnivPatch root indices) := Safe.modify _ (fun _ => rfl)

theorem Safe.storeString (text : String) : Safe (storeString text) (fun address => address.hash.size = 32) := Safe.blob _

theorem Safe.substring (value : Ix.Substring) : Safe (serializeIxSubstring value) :=
  Safe.bind (Safe.storeString _) (fun _ _ => Safe.pure _)

theorem Safe.sourceInfo (value : Ix.SourceInfo) : Safe (serializeIxSourceInfo value) := by
  cases value <;> unfold Ix.CompileM.serializeIxSourceInfo
  · exact Safe.bind (Safe.substring _) fun _ _ => Safe.bind (Safe.substring _) fun _ _ => Safe.pure _
  all_goals exact Safe.pure _

theorem Safe.preresolved (value : Ix.SyntaxPreresolved) : Safe (serializeIxSyntaxPreresolved value) := by
  cases value <;> unfold Ix.CompileM.serializeIxSyntaxPreresolved
  all_goals apply Safe.bind (Safe.compileName _); intro _ _
  · exact Safe.pure _
  · apply Safe.bind
    · apply Safe.mapM_array
      intro _ _
      exact (Safe.storeString _).forget
    · intro _ _; exact Safe.pure _

theorem Safe.syntax (value : Ix.Syntax) : Safe (serializeIxSyntax value) := by
  induction value using Ix.CompileM.serializeIxSyntax.induct with
  | case1 => rw [Ix.CompileM.serializeIxSyntax]; exact Safe.pure _
  | case2 info kind args ih =>
    rw [Ix.CompileM.serializeIxSyntax]
    apply Safe.bind (Safe.compileName _)
    intro _ _
    apply Safe.bind (Safe.sourceInfo _)
    intro _ _
    apply Safe.bind
    · apply Safe.mapM_array
      intro arg _
      exact ih arg
    · intro _ _; exact Safe.pure _
  | case3 info value =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Safe.bind (Safe.sourceInfo _) fun _ _ => Safe.bind (Safe.storeString _) fun _ _ => Safe.pure _
  | case4 info raw value resolved =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Safe.bind (Safe.compileName _) fun _ _ => Safe.bind (Safe.sourceInfo _) fun _ _ =>
      Safe.bind (Safe.substring _) fun _ _ =>
        Safe.bind (Safe.mapM_array _ _ (fun _ _ => Safe.preresolved _)) fun _ _ => Safe.pure _

theorem Safe.dataValue (value : Ix.DataValue) : Safe (compileDataValue value) := by
  cases value <;> unfold Ix.CompileM.compileDataValue
  all_goals with_reducible repeat' first
    | exact Safe.pure _
    | exact Safe.compileName _
    | exact Safe.syntax _
    | exact (Safe.blob _).forget
    | refine Safe.seq ?_ (fun _ => ?_)

theorem Safe.kvmap (values : Array (Ix.Name × Ix.DataValue)) : Safe (compileKVMap values) := by
  rcases values with ⟨_ | ⟨⟨name, value⟩, _ | ⟨next, rest⟩⟩⟩ <;> try cases value
  all_goals unfold Ix.CompileM.compileKVMap
  all_goals delta Ix.CompileM.compileKVMap.match_5
  all_goals simp only [Array.size, List.length_cons, List.length_nil,
    Nat.succ.injEq, Nat.add_one_ne_zero, Nat.reduceEqDiff, ↓reduceDIte]
  all_goals try delta Ix.CompileM.compileKVMap._sparseCasesOn_5
  all_goals try simp only [← Array.getElem_toList, List.getElem_cons_zero]
  all_goals with_reducible repeat' first
    | exact Safe.pure _
    | exact Safe.throw _
    | exact Safe.read
    | exact Safe.get
    | exact Safe.compileName _
    | exact Safe.dataValue _
    | refine Safe.seq ?_ (fun _ => ?_)
    | refine Safe.mapM_array _ _ (fun _ _ => ?_)
    | dsimp only
    | split

theorem Safe.app (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (each : ∀ source, Safe (compile source)) (source : Expr) : Safe (compileAppTotal compile source) := by
  induction source with
  | app fn arg hash fnIH _ =>
    rw [compileAppTotal]
    exact Safe.seq fnIH fun _ => Safe.seq (each arg) fun _ => Safe.seq (Safe.alloc _) fun _ => Safe.pure _
  | _ => exact each _

theorem Safe.step (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (each : ∀ source, Safe (compile source)) (source : Expr) : Safe (compileExprTotalStep compile source) := by
  cases source <;> (try cases ‹Lean.Literal›) <;> rw [compileExprTotalStep]
  all_goals with_reducible repeat' first
    | exact Safe.pure _
    | exact Safe.throw _
    | exact Safe.get
    | exact Safe.read
    | exact Safe.readBlock
    | exact Safe.checkedIndex _ _
    | exact Safe.compileLevel _
    | exact Safe.compileName _
    | exact Safe.alloc _
    | exact Safe.patch _ _
    | exact Safe.kvmap _
    | exact Safe.internRef _ (by assumption)
    | exact Safe.app compile each _
    | exact each _
    | refine Safe.bind (Safe.lookup _) (fun _ _ => ?_)
    | refine Safe.bind (Safe.blob _) (fun _ _ => ?_)
    | refine Safe.seq ?_ (fun _ => ?_)
    | refine Safe.mapM_array _ _ (fun _ _ => ?_)
    | dsimp only
    | split

theorem Safe.fuel (fuel : Nat) (source : Expr) : Safe (compileExprTotalFuel fuel source) := by
  induction fuel generalizing source with
  | zero => exact Safe.throw _
  | succ fuel ih =>
    rw [compileExprTotalFuel]
    apply Safe.seq Safe.get
    intro state
    split
    · exact Safe.pure _
    · apply Safe.seq (Safe.step (compileExprTotalFuel fuel) ih source)
      rintro ⟨value, root⟩
      exact Safe.seq (Safe.modify _ (fun _ => rfl)) (fun _ => Safe.pure _)

theorem Safe.partial (source : Expr) : Safe (compileExprPartial source) := by
  rw [← compileExprTotal_eq_partial]
  exact Safe.fuel _ source

theorem Safe.total (source : Expr) : Safe (compileExprTotal source) := Safe.fuel _ source

theorem Safe.forIn_list (items : List α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item state, Safe (body item state)) : Safe (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Safe.pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Safe.seq (each item initial)
    intro step
    cases step with
    | done value => exact Safe.pure value
    | yield value => exact ih value

theorem Safe.forIn_array (items : Array α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item state, Safe (body item state)) : Safe (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact Safe.forIn_list _ initial body each

theorem Safe.records (source : Expr) : Safe (pass3CompileRecords source) := by
  rw [pass3CompileRecords]
  apply Safe.seq Safe.read
  intro environment
  apply Safe.seq
  · apply Safe.forIn_array
    intro index state
    with_reducible repeat' first
      | exact Safe.pure _
      | exact Safe.throw _
      | exact Safe.get
      | exact Safe.partial _
      | exact Safe.modify _ (fun _ => rfl)
      | refine Safe.seq ?_ (fun _ => ?_)
      | dsimp only
      | split
  · intro _; exact Safe.pure _

theorem Safe.expression (source : Expr) : Safe (compileExpr source) := by
  rw [compileExpr]
  apply Safe.seq Safe.read
  intro environment
  with_reducible repeat' first
    | exact Safe.records _
    | exact Safe.partial _
    | exact Safe.total _
    | exact Safe.pure _
    | refine Safe.seq ?_ (fun _ => ?_)
    | dsimp only
    | split

theorem Safe.compileNames (names : Array Name) : Safe (compileNames names) := by
  apply Safe.framed
  intro context before
  have same := congrArg view (BlobWrites.compileNames_preserves names context before).1
  exact same

theorem Safe.finishNames (source : Def) (block : BlockEnv) : Safe (DefinitionEmission.finishNames source block) := by
  rw [DefinitionEmission.finishNames]
  unfold recordDefHints
  with_reducible repeat' first
    | exact Safe.compileName _
    | exact Safe.compileNames _
    | exact Safe.modify _ (fun _ => rfl)
    | refine Safe.seq ?_ (fun _ => ?_)

theorem Safe.finishDefinition (source : Def) (type value : Ixon.Expr) (typeRoot valueRoot : UInt64) :
    Safe (finishDefinitionDataCompilation source type typeRoot value valueRoot) := by
  intro context before valid output after ran
  rw [DefinitionEmission.finishDefinitionDataCompilation_run] at ran
  have validDrained : Valid context.1 (DefinitionEmission.drained before) := valid.of_view rfl
  exact Safe.seq (Safe.checkedCount _ _) (fun _ =>
    Safe.seq (Safe.finishNames source context.2) (fun _ => Safe.pure _)) context _ validDrained output after ran

theorem Safe.body (source : Def) : Safe (DefinitionEmission.body source) := by
  rw [DefinitionEmission.body]
  exact Safe.seq (Safe.expression source.type) fun type =>
    Safe.seq (Safe.expression source.value) fun value => Safe.finishDefinition source type.1 value.1 type.2 value.2

theorem Safe.definition (source : Def) : Safe (compileDefinitionData source) := by
  intro context before valid output after ran
  rw [DefinitionEmission.compileDefinitionData_run] at ran
  have validPrepared : Valid context.1 (DefinitionEmission.prepared before) := valid.of_view rfl
  exact Safe.body source (DefinitionEmission.contextFor source context) _ validPrepared output after ran

theorem definitionBlock_wire (context : CompileEnv × BlockEnv) (source : Def)
    (before after : BlockState) (valid : Valid context.1 before) (output : BlockResult)
    (ran : rawRun (compileDefinitionDataBlock source) context before = (.ok output, after)) : BlockWireTablesWF after := by
  obtain ⟨payload, payloadRan, _, _⟩ := DefinitionBlock.compileDefinitionDataBlock_eq_ok context source before output after ran
  exact (Safe.definition source context before valid payload after payloadRan).1.2.1

/-- Actual singleton bytes round-trip, deriving the final table-wire premise
from input tables, dependency widths and executable universe admission.
This does not infer source validity or successful compilation from those inputs. -/
theorem compileDefinitionDataInfo_codec_checked (context : CompileEnv × BlockEnv) (source : Def)
    (bindings : ExpressionState.Bindings) (before after : BlockState)
    (ready : DefinitionEmission.Ready bindings before) (wire : BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (output : BlockResult)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    BlockWireTablesWF after ∧ output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block := by
  rw [compileDefinitionDataInfo] at ran
  obtain ⟨done, seededState, seeded, emitted⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  have seedWire := PreseedWire.preseed_wire_checked context _ before seededState wire widths seeded
  have seedReady := PreseedState.preseed_ready_checked context _ bindings before seededState ready seeded
  have same := congrArg Prod.fst (PreseedState.Frame.preseed
    #[(source.type, source.levelParams.toList), (source.value, source.levelParams.toList)] context before)
  rw [seeded] at same
  change ExpressionState.bindingView seededState = ExpressionState.bindingView before at same
  have seedWidths : ReferenceWidths.LookupWidths context.1 seededState := by
    intro name address found
    rw [same] at found
    exact widths name address found
  have finalWire := definitionBlock_wire context source seededState after ⟨seedWidths, seedWire, seedReady.2.1⟩ output emitted
  exact ⟨finalWire, DefinitionBlock.compileDefinitionDataBlock_codec context source seededState output after emitted finalWire⟩

/-- Compatibility interface retaining the original source-bound premises. -/
theorem compileDefinitionDataInfo_codec (context : CompileEnv × BlockEnv) (source : Def)
    (bindings : ExpressionState.Bindings) (before after : BlockState)
    (ready : DefinitionEmission.Ready bindings before) (wire : BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (output : BlockResult)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    BlockWireTablesWF after ∧ output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block :=
  (fun _ _ => compileDefinitionDataInfo_codec_checked context source bindings before after ready wire widths output ran) typeBound valueBound

/-- Source-related anonymous readings and lossless returned bytes for the
complete production singleton definition-like path. Header interpretation,
declaration admission and source-domain totality remain separate. -/
theorem compileDefinitionDataInfo_reading_codec_checked (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Def) (arity : params.length = source.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (ready : DefinitionEmission.Ready bindings before)
    (wire : BlockWireTablesWF before) (widths : ReferenceWidths.LookupWidths context.1 before)
    (output : BlockResult) (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Related reader self names params after source output ∧
      output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block := by
  have semantics := PreseedState.compileDefinitionDataInfo_correct_checked reader base self names params bindings context source arity
    aligned external selfSound before ready output after ran
  have codec := compileDefinitionDataInfo_codec_checked context source bindings before after ready wire widths output ran
  exact ⟨semantics.1, semantics.2, codec.2⟩

theorem compileDefinitionDataInfo_reading_codec (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Def) (arity : params.length = source.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (ready : DefinitionEmission.Ready bindings before)
    (wire : BlockWireTablesWF before) (widths : ReferenceWidths.LookupWidths context.1 before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (output : BlockResult) (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Related reader self names params after source output ∧
      output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block :=
  (fun _ _ => compileDefinitionDataInfo_reading_codec_checked reader base self names params bindings context source arity
    aligned external selfSound before after ready wire widths output ran) typeBound valueBound

end Ix.CompileCert.EmissionWire
