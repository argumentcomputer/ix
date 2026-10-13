import Ix.CompileCert.PreseedBounds
import Ix.CompileCert.DefinitionBlock

/-! Successful production preseeding establishes the retained-state contract
used by definition emission. Cache and binding preservation hold on errors
as well; output coverage additionally requires the source resource bound. -/

namespace Ix.CompileCert.PreseedState

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open UniversePipeline (CanonCacheExact Preserves)

def retained (state : BlockState) :=
  (ExpressionState.bindingView state, state.exprCache, state.p3MetaMode)

abbrev Frame (action : CompileM α) : Prop := Preserves retained action

theorem Frame.roots (roots : List (Expr × List Name)) (initial : ExprTableCollection) :
    Frame (collectPreseedExprs roots initial) := by
  intro context before
  have projected := congrArg retained (PreseedInsertion.CollectionFrame.roots roots initial context before)
  exact projected

theorem Frame.refs (refs : List Address) (previous : Option Address) : Frame (internPreseedRefs refs previous) := by
  intro context before
  have projected := congrArg retained (PreseedInsertion.refs_frame refs previous context before)
  exact projected

theorem Frame.univs (univs : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    Frame (internPreseedUnivs univs previous) := by
  intro context before
  have projected := congrArg retained (PreseedInsertion.univs_frame univs previous context before)
  exact projected

theorem Frame.canon (value : Ixon.Univ) : Frame (canonUnivCached value) := by
  intro context before
  rw [UniversePipeline.canonUnivCached_run]
  cases before.canonUnivCache.get? value <;> rfl

theorem Frame.canonicalize (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Frame (canonPreseedUnivs values initial) := by
  induction values generalizing initial with
  | nil => exact Preserves.pure _ _
  | cons value rest ih =>
    rw [canonPreseedUnivs]
    exact Preserves.bind (Frame.canon value) (fun value => ih (initial.push value))

theorem Frame.preseed (roots : Array (Expr × List Name)) : Frame (preseedExprTables roots) := by
  rw [preseedExprTables]
  apply Preserves.bind (Frame.roots roots.toList (#[], #[], {}))
  rintro ⟨refs, univs, _⟩
  apply Preserves.bind (Frame.refs _ none)
  intro _
  apply Preserves.bind (Frame.canonicalize _ _)
  intro canonical
  apply Preserves.bind (Frame.univs _ none)
  intro _
  exact Preserves.modify retained _ (fun _ => rfl)

def CanonSafe (action : CompileM α) : Prop :=
  ∀ context before, CanonCacheExact before → CanonCacheExact (rawRun action context before).2

theorem CanonSafe.pure (value : α) : CanonSafe (pure value) := fun _ _ exactCache => exactCache

theorem CanonSafe.bind {action : CompileM α} {next : α → CompileM β}
    (head : CanonSafe action) (tail : ∀ value, CanonSafe (next value)) : CanonSafe (action >>= next) := by
  intro context before exactCache
  have checked := head context before exactCache
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact checked
    | ok value => exact tail value context after checked

theorem CanonSafe.refs (refs : List Address) (previous : Option Address) : CanonSafe (internPreseedRefs refs previous) := by
  intro context before exactCache
  have same := congrArg CanonCacheExact (PreseedInsertion.refs_frame refs previous context before)
  exact same.mpr exactCache

theorem CanonSafe.univs (univs : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    CanonSafe (internPreseedUnivs univs previous) := by
  intro context before exactCache
  have same := congrArg CanonCacheExact (PreseedInsertion.univs_frame univs previous context before)
  exact same.mpr exactCache

theorem CanonSafe.canonicalize (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    CanonSafe (canonPreseedUnivs values initial) := by
  intro context before exactCache
  obtain ⟨after, ran, valid, _⟩ := PreseedCanonical.canonicalize values initial context before exactCache
  rw [ran]
  exact valid

theorem CanonSafe.preseed (roots : Array (Expr × List Name)) : CanonSafe (preseedExprTables roots) := by
  rw [preseedExprTables]
  apply CanonSafe.bind (PreseedCanonical.roots_cache roots.toList (#[], #[], {}))
  rintro ⟨refs, univs, _⟩
  apply CanonSafe.bind (CanonSafe.refs _ none)
  intro _
  apply CanonSafe.bind (CanonSafe.canonicalize _ _)
  intro canonical
  apply CanonSafe.bind (CanonSafe.univs _ none)
  intro _
  exact fun _ _ exactCache => exactCache

/-- The actual preseed entry preserves declaration-emission readiness and
establishes table coverage, with the wire premise derived from source bounds.
No separately supplied collection run or output-wire assertion is needed. -/
theorem preseed_ready (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (bounded : ∀ root ∈ roots, PreseedBounds.ExprBound root.1)
    (bindings : ExpressionState.Bindings) (before after : BlockState)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    DefinitionEmission.Ready bindings after ∧ after.univsFinal = true ∧
      (∀ root ∈ roots, PreseedReferences.Covered
        (ExpressionState.lookupBinding context.1 bindings) context.2.mutCtx after.refs root.1) ∧
      ∃ collection collectedState,
        rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok collection, collectedState) ∧
        (∀ root ∈ roots, PreseedUniverses.Covered root.2 collection.2.1 root.1) ∧
        (∀ value ∈ collection.2.1, PreseedInsertion.UnivPresent after (Ixon.canonUniv value)) := by
  have sequence := ran
  rw [preseedExprTables] at sequence
  obtain ⟨collection, collectedState, collected, _⟩ := PreseedReferences.bind_ok _ _ context before () after sequence
  have inserted := PreseedBounds.preseed_from_bounded_roots context roots bounded before collectedState after collection
    collected ready.mode ready.refs ready.univs ready.canon ran
  have reads := PreseedBounds.preseed_reads_bounded context roots bounded before collectedState after collection
    collected ready.mode ready.refs ready.univs ready.canon ran
  have frame := Frame.preseed roots context before
  rw [ran] at frame
  have bindingsSame := congrArg Prod.fst frame
  have cacheSame := congrArg (fun state => state.2.1) frame
  have canon := CanonSafe.preseed roots context before ready.canon
  rw [ran] at canon
  refine ⟨⟨inserted.2.2.1, inserted.2.2.2.1, canon,
    bindingsSame.trans ready.bindings, cacheSame.trans ready.cache, inserted.2.1⟩, inserted.1, ?_, ?_⟩
  · simpa only [ready.bindings] using reads.1
  · refine ⟨collection, collectedState, collected, ?_, inserted.2.2.2.2.2⟩
    intro root member
    exact PreseedUniverses.roots_initial context before collectedState roots.toList collection collected root (by simpa using member)

theorem compileDefinitionInfo_eq (source : DefinitionVal) :
    compileDefinitionInfo source = compileDefinitionDataInfo (definitionValData source) := rfl

/-- The production singleton definition-like entry, including preseeding,
payload emission, canonical sharing and the stored-byte wrapper. The caller
still supplies correct dependency bindings and the singleton mutual context;
this theorem does not assert source-domain totality or declaration admission. -/
theorem compileDefinitionDataInfo_correct (context : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (environment : CompileEnv × BlockEnv)
    (source : Def) (arity : params.length = source.levelParams.size)
    (aligned : ∀ address, context.blob address = environment.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect environment.1 bindings context names)
    (selfSound : ExpressionState.SelfCorrect environment.2 self names)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (before : BlockState) (ready : DefinitionEmission.Ready bindings before)
    (out : BlockResult) (after : BlockState)
    (compiled : rawRun (compileDefinitionDataInfo source) environment before = (.ok out, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Related context self names params after source out := by
  rw [compileDefinitionDataInfo] at compiled
  obtain ⟨done, seededState, seeded, blockRun⟩ := PreseedReferences.bind_ok _ _ environment before out after compiled
  cases done
  have bounds : ∀ root ∈ #[(source.type, source.levelParams.toList), (source.value, source.levelParams.toList)],
      PreseedBounds.ExprBound root.1 := by
    intro root member
    simp at member
    rcases member with rfl | rfl
    · exact typeBound
    · exact valueBound
  have prepared := preseed_ready environment _ bounds bindings before seededState ready seeded
  exact DefinitionBlock.compileDefinitionDataBlock_correct context base self names params bindings environment source
    arity aligned external selfSound seededState prepared.1 out after blockRun

end Ix.CompileCert.PreseedState
