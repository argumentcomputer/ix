import Ix.CompileCert.ExpressionCorrectness

/-! The actual ordinary expression compiler preserves its mode, including
errors. In metadata mode it preserves the primary reference/universe tables
exactly; extension tables may grow. These frame facts require no cache or
source-validity premise. -/

namespace Ix.CompileCert.MetadataMode

open Ix.CompileM Ix.CompileCert.HeadWriterFrame
open private Ix.CompileM.compileKVMap.match_5
  Ix.CompileM.compileKVMap._sparseCasesOn_5 from Ix.CompileM

def view (state : BlockState) := (state.p3MetaMode, state.refs, state.univs)

def Fixed (before after : BlockState) : Prop :=
  after.p3MetaMode = before.p3MetaMode ∧
    (before.p3MetaMode = true → after.refs = before.refs ∧ after.univs = before.univs)

theorem Fixed.refl (state : BlockState) : Fixed state state := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem Fixed.of_view {before after : BlockState} (same : view after = view before) : Fixed before after := by
  have parts := Prod.mk.inj same
  exact ⟨parts.1, fun _ => Prod.mk.inj parts.2⟩

theorem Fixed.trans {before middle after : BlockState} (first : Fixed before middle) (last : Fixed middle after) :
    Fixed before after := by
  refine ⟨last.1.trans first.1, ?_⟩
  intro mode
  have nextMode : middle.p3MetaMode = true := first.1.trans mode
  exact ⟨(last.2 nextMode).1.trans (first.2 mode).1, (last.2 nextMode).2.trans (first.2 mode).2⟩

def Frame (action : CompileM α) : Prop := ∀ context before, Fixed before (rawRun action context before).2

theorem Frame.pure (value : α) : Frame (pure value) := fun _ before => .refl before
theorem Frame.throw (error : CompileError) : Frame (throw error : CompileM α) := fun _ before => .refl before
theorem Frame.get : Frame getBlockState := fun _ before => .refl before
theorem Frame.read : Frame getCompileEnv := fun _ before => .refl before
theorem Frame.readBlock : Frame getBlockEnv := fun _ before => .refl before

theorem Frame.bind {action : CompileM α} {next : α → CompileM β}
    (first : Frame action) (tail : ∀ value, Frame (next value)) : Frame (action >>= next) := by
  intro context before
  rw [rawRun_bind]
  have head := first context before
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact head
    | ok value => exact head.trans (tail value context middle)

theorem Frame.modify (update : BlockState → BlockState) (keeps : ∀ before, view (update before) = view before) :
    Frame (modifyBlockState update) := fun _ before => Fixed.of_view (keeps before)

theorem Frame.modifyGet (update : BlockState → α × BlockState) (keeps : ∀ before, view (update before).2 = view before) :
    Frame (modifyGetBlockState update) := fun _ before => Fixed.of_view (keeps before)

theorem Frame.map {action : CompileM α} (framed : Frame action) (f : α → β) : Frame (f <$> action) := by
  rw [map_eq_pure_bind]
  exact Frame.bind framed (fun _ => Frame.pure _)

theorem Frame.checkedIndex (table : String) (index : Nat) : Frame (checkedTableIndex table index) := by
  intro context before
  rw [Interning.checkedTableIndex_state]
  exact .refl _

theorem Frame.compileUniv (source : Ix.Level) : Frame (compileUniv source) := by
  intro context before
  have same := congrArg view (UniversePipeline.compileUniv_frame source context before)
  exact Fixed.of_view same

theorem Frame.canonUnivCached (source : Ixon.Univ) : Frame (canonUnivCached source) := by
  intro context before
  rw [UniversePipeline.canonUnivCached_run]
  cases before.canonUnivCache.get? source <;> exact Fixed.of_view rfl

theorem Frame.internMetaUniv (source : Ixon.Univ) : Frame (internMetaUniv source) := by
  intro context before
  have other := UniversePipeline.internMetaUniv_frame source context before
  have mode := congrArg BlockState.p3MetaMode other
  have refs := congrArg BlockState.refs other
  exact ⟨mode, fun _ => ⟨refs, UniversePipeline.internMetaUniv_primary source context before⟩⟩

theorem Frame.finishSpelling (raw canon : Ixon.Univ) (index : UInt64) :
    Frame (UniversePipeline.finishSpelling raw canon index) := by
  unfold UniversePipeline.finishSpelling
  split
  · exact Frame.pure _
  · exact Frame.bind (Frame.internMetaUniv _) (fun _ => Frame.pure _)

theorem internPrimary_fixed (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (route : before.p3MetaMode = false ∨ before.univsIndex.contains canon = true) :
    Fixed before (rawRun (UniversePipeline.internPrimaryCanonical raw canon) context before).2 := by
  rcases route with mode | hit
  · have frame : UniversePipeline.Preserves UniversePipeline.withoutUnivTables
        (UniversePipeline.internPrimaryCanonical raw canon) := by
      unfold UniversePipeline.internPrimaryCanonical
      with_reducible repeat' first
        | exact UniversePipeline.Preserves.pure _ _
        | exact UniversePipeline.Preserves.throw _ _
        | exact UniversePipeline.Preserves.get _
        | exact UniversePipeline.internUniv_frame _
        | refine UniversePipeline.Preserves.bind ?_ (fun _ => ?_)
        | dsimp only
        | split
      all_goals
        unfold UniversePipeline.finishSpelling
        split
        · exact UniversePipeline.Preserves.pure _ _
        · exact UniversePipeline.Preserves.bind (UniversePipeline.internMetaUniv_frame _) (fun _ => UniversePipeline.Preserves.pure _ _)
    have same := congrArg BlockState.p3MetaMode (frame context before)
    refine ⟨same, ?_⟩
    intro bad
    rw [mode] at bad
    cases bad
  · rw [Std.HashMap.contains_eq_isSome_getElem?] at hit
    change (before.univsIndex.get? canon).isSome = true at hit
    cases found : before.univsIndex.get? canon with
    | none => rw [found] at hit; cases hit
    | some index =>
      unfold UniversePipeline.internPrimaryCanonical
      simp only [rawRun_bind, rawRun_get, Interning.internUniv_hit canon context before found,
        bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact Frame.finishSpelling raw canon index context before

theorem Frame.internCanonical (raw canon : Ixon.Univ) : Frame (UniversePipeline.internCanonical raw canon) := by
  intro context before
  unfold UniversePipeline.internCanonical
  simp only [rawRun_bind, rawRun_get]
  cases mode : before.p3MetaMode with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact internPrimary_fixed raw canon context before (.inl mode)
  | true =>
    simp only [↓reduceIte, rawRun_bind, rawRun_get]
    by_cases hit : before.univsIndex.contains canon = true
    · simp only [hit, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact internPrimary_fixed raw canon context before (.inr hit)
    · have missing : before.univsIndex.contains canon = false := Bool.eq_false_iff.mpr hit
      simp only [missing, Bool.not_false, ↓reduceIte]
      exact Frame.bind (Frame.internMetaUniv _) (fun index => Frame.finishSpelling raw canon index) context before

theorem Frame.compileAndInternUnivCanon (source : Ix.Level) : Frame (compileAndInternUnivCanon source) := by
  rw [UniversePipeline.compileAndInternUnivCanon_eq]
  exact Frame.bind (Frame.compileUniv _) fun raw =>
    Frame.bind (Frame.canonUnivCached _) fun canon => Frame.internCanonical raw canon

theorem Frame.internRef (address : Address) : Frame (internRef address) := by
  intro context before
  have frame := ExpressionState.internRef_frame address context before
  have mode := congrArg BlockState.p3MetaMode frame
  have univs := congrArg BlockState.univs frame
  refine ⟨mode, ?_⟩
  intro metadata
  refine ⟨?_, univs⟩
  rw [Interning.internRef_meta_run address context before metadata]
  cases primary : before.refsIndex.get? address with
  | some index => rw [Interning.internRefMeta_primary_hit address context before primary]
  | none =>
    cases found : before.p3MetaRefsIndex.get? address with
    | some slot => rw [Interning.internRefMeta_extension_hit address context before primary found, Interning.checkedTableIndex_state]
    | none => rw [Interning.internRefMeta_miss address context before primary found]; split <;> rfl

theorem Frame.lookupConstAddr (name : Ix.Name) : Frame (lookupConstAddr name) := by
  intro context before
  rw [ExpressionState.lookupConstAddr_state]
  exact .refl _

theorem Frame.storeBlob (bytes : ByteArray) : Frame (storeBlob bytes) := by
  intro context before
  have same := congrArg view (BlobWrites.storeBlob_preserves bytes context before).1
  exact Fixed.of_view same

theorem Frame.compileName (name : Ix.Name) : Frame (compileName name) := by
  intro context before
  have same := congrArg view (BlobWrites.compileName_preserves name context before).1
  exact Fixed.of_view same

theorem Frame.allocArenaNode (node : Ixon.ExprMetaData) : Frame (allocArenaNode node) := Frame.modifyGet _ (fun _ => rfl)
theorem Frame.pushUnivPatch (root : UInt64) (indices : Array UInt64) : Frame (pushUnivPatch root indices) :=
  Frame.modify _ (fun _ => rfl)

theorem Frame.mapM_list (items : List α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Frame (action item)) : Frame (items.mapM action) := by
  induction items with
  | nil => exact Frame.pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact Frame.bind (each item (by simp)) fun _ =>
      Frame.bind (ih (fun item member => each item (by simp [member]))) fun _ => Frame.pure _

theorem Frame.mapM_array (items : Array α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Frame (action item)) : Frame (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Frame.map (Frame.mapM_list _ action (fun item member => each item (by simpa using member))) _

theorem Frame.forIn'_list (items : List α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (each : ∀ item member acc, Frame (body item member acc)) : Frame (forIn' items initial body) := by
  induction items generalizing initial with
  | nil => exact Frame.pure _
  | cons item rest ih =>
    rw [List.forIn'_cons]
    apply Frame.bind (each item (by simp) initial)
    intro step
    cases step with
    | done value => exact Frame.pure value
    | yield value => exact ih value _ (fun item member acc => each item _ acc)

theorem Frame.forIn'_array (items : Array α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (each : ∀ item member acc, Frame (body item member acc)) : Frame (forIn' items initial body) := by
  have framed := Frame.forIn'_list items.toList initial
    (fun item member acc => body item (Array.mem_toList_iff.mp member) acc) (fun item member acc => each item _ acc)
  simpa only [Array.forIn'_toList] using framed

theorem Frame.storeString (text : String) : Frame (storeString text) := Frame.storeBlob _

theorem Frame.serializeIxSubstring (value : Ix.Substring) : Frame (serializeIxSubstring value) :=
  Frame.bind (Frame.storeString _) (fun _ => Frame.pure _)

theorem Frame.serializeIxSourceInfo (value : Ix.SourceInfo) : Frame (serializeIxSourceInfo value) := by
  cases value <;> unfold Ix.CompileM.serializeIxSourceInfo
  · exact Frame.bind (Frame.serializeIxSubstring _) fun _ => Frame.bind (Frame.serializeIxSubstring _) fun _ => Frame.pure _
  all_goals exact Frame.pure _

theorem Frame.serializeIxSyntaxPreresolved (value : Ix.SyntaxPreresolved) : Frame (serializeIxSyntaxPreresolved value) := by
  cases value <;> unfold Ix.CompileM.serializeIxSyntaxPreresolved
  all_goals apply Frame.bind (Frame.compileName _); intro _
  · exact Frame.pure _
  · exact Frame.bind (Frame.mapM_array _ _ (fun _ _ => Frame.storeString _)) (fun _ => Frame.pure _)

theorem Frame.serializeIxSyntax (value : Ix.Syntax) : Frame (serializeIxSyntax value) := by
  induction value using Ix.CompileM.serializeIxSyntax.induct with
  | case1 => rw [Ix.CompileM.serializeIxSyntax]; exact Frame.pure _
  | case2 info kind args ih =>
    rw [Ix.CompileM.serializeIxSyntax]
    apply Frame.bind (Frame.compileName _)
    intro _
    apply Frame.bind (Frame.serializeIxSourceInfo _)
    intro _
    apply Frame.bind
    · apply Frame.mapM_array
      intro arg _
      exact ih arg
    · intro _; exact Frame.pure _
  | case3 info value =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Frame.bind (Frame.serializeIxSourceInfo _) fun _ => Frame.bind (Frame.storeString _) fun _ => Frame.pure _
  | case4 info raw value resolved =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Frame.bind (Frame.compileName _) fun _ => Frame.bind (Frame.serializeIxSourceInfo _) fun _ =>
      Frame.bind (Frame.serializeIxSubstring _) fun _ =>
        Frame.bind (Frame.mapM_array _ _ (fun _ _ => Frame.serializeIxSyntaxPreresolved _)) fun _ => Frame.pure _

theorem Frame.compileDataValue (value : Ix.DataValue) : Frame (compileDataValue value) := by
  cases value <;> unfold Ix.CompileM.compileDataValue
  all_goals with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.compileName _
    | exact Frame.serializeIxSyntax _
    | exact Frame.storeBlob _
    | refine Frame.bind ?_ (fun _ => ?_)

theorem Frame.compileKVMap (values : Array (Ix.Name × Ix.DataValue)) : Frame (compileKVMap values) := by
  rcases values with ⟨_ | ⟨⟨name, value⟩, _ | ⟨next, rest⟩⟩⟩ <;> try cases value
  all_goals unfold Ix.CompileM.compileKVMap
  all_goals delta Ix.CompileM.compileKVMap.match_5
  all_goals simp only [Array.size, List.length_cons, List.length_nil,
    Nat.succ.injEq, Nat.add_one_ne_zero, Nat.reduceEqDiff, ↓reduceDIte]
  all_goals try delta Ix.CompileM.compileKVMap._sparseCasesOn_5
  all_goals try simp only [← Array.getElem_toList, List.getElem_cons_zero]
  all_goals with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.throw _
    | exact Frame.read
    | exact Frame.get
    | exact Frame.compileName _
    | exact Frame.compileDataValue _
    | refine Frame.bind ?_ (fun _ => ?_)
    | refine Frame.mapM_array _ _ (fun _ _ => ?_)
    | dsimp only
    | split

theorem Frame.compileConstExprRaw (name : Ix.Name) (levels : Array Ix.Level) : Frame (compileConstExprRaw name levels) := by
  unfold Ix.CompileM.compileConstExprRaw
  with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.readBlock
    | exact Frame.checkedIndex _ _
    | exact Frame.compileName _
    | exact Frame.compileAndInternUnivCanon _
    | exact Frame.allocArenaNode _
    | exact Frame.pushUnivPatch _ _
    | exact Frame.lookupConstAddr _
    | exact Frame.internRef _
    | refine Frame.bind ?_ (fun _ => ?_)
    | refine Frame.mapM_array _ _ (fun _ _ => ?_)
    | dsimp only
    | split

/-- Metadata-mode expression compilation cannot move a primary table slot.
The mode itself is unchanged even on errors. -/
theorem Frame.compileExprPartial (source : Ix.Expr) : Frame (compileExprPartial source) := by
  induction source using Ix.CompileM.compileExprPartial.induct with
  | case1 source ih =>
    rw [Ix.CompileM.compileExprPartial]
    apply Frame.bind Frame.get
    intro before
    split
    · exact Frame.pure _
    · cases source <;> (try cases ‹Lean.Literal›) <;> dsimp only at ih ⊢
      all_goals with_reducible repeat' first
        | exact Frame.pure _
        | exact Frame.throw _
        | exact Frame.checkedIndex _ _
        | exact Frame.allocArenaNode _
        | exact Frame.pushUnivPatch _ _
        | exact Frame.compileAndInternUnivCanon _
        | exact Frame.compileConstExprRaw _ _
        | exact Frame.compileName _
        | exact Frame.storeBlob _
        | exact Frame.internRef _
        | exact Frame.lookupConstAddr _
        | exact Frame.compileKVMap _
        | exact ih
        | exact ih.1
        | exact ih.2
        | exact ih.2.1
        | exact ih.2.2
        | exact ih.2 _ (by assumption)
        | refine Frame.bind ?_ (fun _ => ?_)
        | refine Frame.forIn'_array _ _ _ (fun _ _ _ => ?_)
        | apply Frame.modify; intro _; simp only [view]
        | dsimp only
        | split

end Ix.CompileCert.MetadataMode
