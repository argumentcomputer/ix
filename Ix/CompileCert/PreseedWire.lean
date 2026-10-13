import Ix.CompileCert.WireTables
import Ix.CompileCert.ExpressionState
import Ix.CompileCert.PreseedKeys
import Ix.CompileCert.ReferenceWidths

/-! Primary-table wire validity through actual collection and preseeding.
Checked universe admission and dependency reference widths derive the insertion
premises; the primary count guards preserve the wire-sized table counts. -/

namespace Ix.CompileCert.PreseedWire

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.Sharing.Verify (BlockWireTablesWF)

def Safe (action : CompileM α) : Prop :=
  ∀ context before, BlockWireTablesWF before → BlockWireTablesWF (rawRun action context before).2

theorem Safe.pure (value : α) : Safe (pure value) := fun _ _ wire => wire

theorem Safe.bind {action : CompileM α} {next : α → CompileM β}
    (head : Safe action) (tail : ∀ value, Safe (next value)) : Safe (action >>= next) := by
  intro context before wire
  have checked := head context before wire
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact checked
    | ok value => exact tail value context after checked

theorem Safe.discard {action : CompileM α} (safe : Safe action) : Safe (Functor.discard action) := by
  unfold Functor.discard
  exact Safe.bind safe (fun _ => Safe.pure ())

theorem Safe.ref (address : Address) (width : address.hash.size = 32) : Safe (internRef address) :=
  fun context before wire => WireTables.internRef_preserves context before address wire width

theorem Safe.univ (univ : Ixon.Univ) (wire : univ.wireWF) : Safe (internUniv univ) :=
  fun context before tables => WireTables.internUniv_preserves context before univ tables wire

theorem internRefs (refs : List Address) (previous : Option Address)
    (widths : ∀ address ∈ refs, address.hash.size = 32) : Safe (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact Safe.pure ()
  | cons address rest ih =>
    unfold internPreseedRefs
    have tail := ih (some address) (fun item member => widths item (by simp [member]))
    split
    · exact Safe.bind (Safe.discard (Safe.ref address (widths _ (by simp)))) (fun _ => tail)
    · exact tail

theorem internUnivs (univs : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray)
    (valid : ∀ entry ∈ univs, entry.2.wireWF) : Safe (internPreseedUnivs univs previous) := by
  induction univs generalizing previous with
  | nil => exact Safe.pure ()
  | cons entry rest ih =>
    rcases entry with ⟨key, univ⟩
    unfold internPreseedUnivs
    have tail := ih (some key) (fun item member => valid item (by simp [member]))
    split
    · exact Safe.bind (Safe.discard (Safe.univ univ (valid (key, univ) (by simp)))) (fun _ => tail)
    · exact tail

theorem Safe.canon (univ : Ixon.Univ) : Safe (canonUnivCached univ) := by
  intro context before wire
  rw [UniversePipeline.canonUnivCached_run]
  cases before.canonUnivCache.get? univ
  all_goals apply WireTables.of_same wire <;> rfl

theorem canonUnivs (univs : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Safe (canonPreseedUnivs univs initial) := by
  induction univs generalizing initial with
  | nil => exact Safe.pure initial
  | cons univ rest ih =>
    unfold canonPreseedUnivs
    exact Safe.bind (Safe.canon univ) (fun value => ih (initial.push value))

theorem Safe.throw (error : CompileError) : Safe (throw error : CompileM α) := fun _ _ wire => wire
theorem Safe.readBlock : Safe getBlockEnv := fun _ _ wire => wire

theorem Safe.compileUniv (source : Level) : Safe (compileUniv source) := by
  intro context before wire
  have frame := UniversePipeline.compileUniv_frame source context before
  have refs := congrArg BlockState.refs frame
  have univs := congrArg BlockState.univs frame
  exact WireTables.of_same wire refs univs

theorem Safe.lookup (name : Name) : Safe (lookupConstAddr name) := by
  intro context before wire
  rw [ExpressionState.lookupConstAddr_state]
  exact wire

theorem Safe.blob (bytes : ByteArray) : Safe (storeBlob bytes) := by
  intro context before wire
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  have refs := congrArg BlockState.refs frame
  have univs := congrArg BlockState.univs frame
  exact WireTables.of_same wire refs univs

theorem Safe.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} (safe : Safe action) :
    Safe (withBlockEnv update action) := fun context before wire => safe (context.1, update context.2) before wire

theorem Safe.withUnivCtx (params : List Name) {action : CompileM α} (safe : Safe action) :
    Safe (withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  apply Safe.bind
  · intro context before wire
    rw [rawRun_modify]
    apply WireTables.of_same wire <;> rfl
  · intro _
    exact Safe.withBlockEnv _ safe

theorem collectLevels (levels : List Level) (initial : Array Ixon.Univ) : Safe (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact Safe.pure initial
  | cons level levels ih =>
    rw [collectExprTableUnivs]
    exact Safe.bind (Safe.compileUniv level) (fun value => ih (initial.push value))

theorem collectStructural (context : Address) (mutualContext : MutCtx) (params : List Name)
    (expr : Expr) (acc : ExprTableCollection) :
    Safe (collectExprTablesStructural context mutualContext params expr acc) := by
  induction expr generalizing acc
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases acc with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact Safe.pure _
    · with_reducible repeat' first
        | exact Safe.pure _
        | exact Safe.throw _
        | exact Safe.compileUniv _
        | exact Safe.lookup _
        | exact Safe.blob _
        | exact collectLevels _ _
        | refine Safe.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem collect (expr : Expr) (context : Address) (acc : ExprTableCollection) : Safe (collectExprTables expr context acc) :=
  Safe.bind Safe.readBlock (fun block => collectStructural context block.mutCtx block.univCtx expr acc)

theorem collectRoots (roots : List (Expr × List Name)) (initial : ExprTableCollection) :
    Safe (collectPreseedExprs roots initial) := by
  induction roots generalizing initial with
  | nil => exact Safe.pure initial
  | cons root rest ih =>
    rcases root with ⟨expr, params⟩
    rw [collectPreseedExprs]
    exact Safe.bind (Safe.withUnivCtx params (collect expr (univParamsKey params) initial)) (fun next => ih next)

theorem preseed_wire_checked (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (before after : BlockState) (wire : BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) : BlockWireTablesWF after := by
  rw [preseedExprTables] at ran
  obtain ⟨collection, collectedState, collected, tail⟩ := PreseedReferences.bind_ok _ _ context before () after ran
  rcases collection with ⟨refs, univs, seen⟩
  dsimp only at tail
  obtain ⟨doneRefs, refState, refsRan, rest⟩ := PreseedReferences.bind_ok _ _ context collectedState () after tail
  cases doneRefs
  obtain ⟨canonical, canonState, canonRan, finish⟩ := PreseedReferences.bind_ok _ _ context refState () after rest
  obtain ⟨canonicalWire, finish⟩ := PreseedValidation.after_check canonical _ context canonState after () finish
  obtain ⟨doneUnivs, univState, univsRan, flagRan⟩ := PreseedReferences.bind_ok _ _ context canonState () after finish
  cases doneUnivs
  have collectedWire := collectRoots roots.toList (#[], #[], {}) context before wire
  rw [collected] at collectedWire
  have refWidths := ReferenceWidths.roots_initial context roots before collectedState (refs, univs, seen) widths collected
  have sortedWidths : ∀ address ∈ (refs.qsort (fun a b => a.cmpBytes b == .lt)).toList, address.hash.size = 32 := by
    intro address member
    apply refWidths address
    rw [Array.mem_toList_iff, Canon.mem_qsort] at member
    exact member
  have refWire := internRefs _ none sortedWidths context collectedState collectedWire
  rw [refsRan] at refWire
  have canonWire := canonUnivs univs.toList (Array.mkEmpty univs.size) context refState refWire
  rw [canonRan] at canonWire
  change rawRun (internPreseedUnivs (PreseedInsertion.sortedUnivs canonical).toList none) context canonState = (.ok (), univState) at univsRan
  have entriesWire : ∀ entry ∈ (PreseedInsertion.sortedUnivs canonical).toList, entry.2.wireWF := by
    intro entry member
    exact (PreseedInsertion.sortedUnivs_valid canonical canonicalWire entry (by simpa using member)).2
  have outputWire := internUnivs _ none entriesWire context canonState canonWire
  rw [univsRan] at outputWire
  rw [rawRun_modify] at flagRan
  have same := congrArg Prod.snd flagRan
  dsimp only at same
  subst after
  exact WireTables.of_same outputWire rfl rfl

/-- The original bounded-source interface follows from checked admission. -/
theorem preseed_wire (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (before after : BlockState) (wire : BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (bounded : ∀ root ∈ roots, PreseedBounds.ExprBound root.1)
    (canonExact : UniversePipeline.CanonCacheExact before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) : BlockWireTablesWF after := by
  exact (fun _ _ => preseed_wire_checked context roots before after wire widths ran) bounded canonExact

end Ix.CompileCert.PreseedWire
