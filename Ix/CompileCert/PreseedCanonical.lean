import Ix.CompileCert.PreseedUniverses

/-! Production collection preserves the canonical universe memo. The actual
canonicalization loop appends exactly the normalizer's outputs and preserves
the remaining block state. -/

namespace Ix.CompileCert.PreseedCanonical

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open UniversePipeline (CanonCacheExact withoutCanonCache)

abbrev Frame (action : CompileM α) : Prop := UniversePipeline.Preserves BlockState.canonUnivCache action

theorem Frame.compileUniv (source : Level) : Frame (compileUniv source) := by
  intro context before
  have frame := UniversePipeline.compileUniv_frame source context before
  have projected := congrArg BlockState.canonUnivCache frame
  exact projected

theorem Frame.lookup (name : Name) : Frame (lookupConstAddr name) := by
  intro context before
  rw [ExpressionState.lookupConstAddr_state]

theorem Frame.blob (bytes : ByteArray) : Frame (storeBlob bytes) := by
  intro context before
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  have projected := congrArg BlockState.canonUnivCache frame
  exact projected

theorem Frame.levels (levels : List Level) (initial : Array Ixon.Univ) : Frame (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact UniversePipeline.Preserves.bind (Frame.compileUniv level) (fun value => ih (initial.push value))

theorem Frame.structural (hint : Address) (mutualContext : MutCtx) (params : List Name)
    (source : Expr) (initial : ExprTableCollection) : Frame (collectExprTablesStructural hint mutualContext params source initial) := by
  induction source generalizing initial
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact UniversePipeline.Preserves.pure _ _
    · with_reducible repeat' first
        | exact UniversePipeline.Preserves.pure _ _
        | exact UniversePipeline.Preserves.throw _ _
        | exact Frame.compileUniv _
        | exact Frame.lookup _
        | exact Frame.blob _
        | exact Frame.levels _ _
        | refine UniversePipeline.Preserves.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem Frame.collect (source : Expr) (hint : Address) (initial : ExprTableCollection) :
    Frame (collectExprTables source hint initial) :=
  UniversePipeline.Preserves.bind (UniversePipeline.Preserves.read _) (fun block =>
    Frame.structural hint block.mutCtx block.univCtx source initial)

theorem Frame.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} (framed : Frame action) :
    Frame (withBlockEnv update action) := fun context before => framed (context.1, update context.2) before

theorem Frame.withUnivCtx (params : List Name) {action : CompileM α} (framed : Frame action) :
    Frame (withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  exact UniversePipeline.Preserves.bind (UniversePipeline.Preserves.modify _ _ (fun _ => rfl))
    (fun _ => Frame.withBlockEnv _ framed)

theorem Frame.roots (roots : List (Expr × List Name)) (initial : ExprTableCollection) :
    Frame (collectPreseedExprs roots initial) := by
  induction roots generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons root rest ih =>
    rcases root with ⟨source, params⟩
    rw [collectPreseedExprs]
    exact UniversePipeline.Preserves.bind (Frame.withUnivCtx params (Frame.collect source (univParamsKey params) initial))
      (fun next => ih next)

theorem roots_cache (roots : List (Expr × List Name)) (initial : ExprTableCollection)
    (context : CompileEnv × BlockEnv) (before : BlockState) (exactCache : CanonCacheExact before) :
    CanonCacheExact (rawRun (collectPreseedExprs roots initial) context before).2 := by
  intro source value found
  rw [Frame.roots roots initial context before] at found
  exact exactCache source value found

theorem canonicalize (sources : List Ixon.Univ) (initial : Array Ixon.Univ)
    (context : CompileEnv × BlockEnv) (before : BlockState) (exactCache : CanonCacheExact before) :
    ∃ after, rawRun (canonPreseedUnivs sources initial) context before =
        (.ok (initial ++ (sources.map Ixon.canonUniv).toArray), after) ∧
      CanonCacheExact after ∧ withoutCanonCache after = withoutCanonCache before := by
  induction sources generalizing initial before with
  | nil => exact ⟨before, by simp [canonPreseedUnivs, rawRun_pure], exactCache, rfl⟩
  | cons source rest ih =>
    obtain ⟨middle, compiled, exactMiddle, frame⟩ := UniversePipeline.canonUnivCached_correct source context before exactCache
    obtain ⟨after, restRan, exactAfter, restFrame⟩ := ih (initial.push (Ixon.canonUniv source)) middle exactMiddle
    refine ⟨after, ?_, exactAfter, restFrame.trans frame⟩
    rw [canonPreseedUnivs, rawRun_bind, compiled]
    dsimp only
    rw [restRan]
    congr 2
    apply Array.toList_inj.mp
    simp

end Ix.CompileCert.PreseedCanonical
