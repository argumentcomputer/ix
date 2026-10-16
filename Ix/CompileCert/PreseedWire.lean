import Ix.CompileCert.PreseedState
import Ix.CompileCert.WireTables
import Ix.CompileCert.Canon.QSort

/-! # Preseeding keeps the primary tables on the wire

A successful `preseedExprTables` leaves the primary tables representable by
the constant wire format (`Ix.Sharing.Verify.BlockWireTablesWF`) when they
were before and the declaration prefix resolves names to 32-byte addresses
(`LookupWidths`): the collector writes neither table nor binding
(`collection_frame`); every reference it collects is 32 bytes (a resolved
name's, or a blob's admission hash: `collect_widths`); the universe guard
`checkPreseedUnivs` admits only wire-valid canonical universes; and the
interners keep the tables on the wire given those facts
(`Ix.CompileCert.WireTables`). The binding view, hence `LookupWidths`, is
untouched by every run (`preseed_widths`). CT-14's `PreseedWire` and
`ReferenceWidths`. -/

namespace Ix.CompileCert.PreseedWire

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Sharing.Verify (BlockWireTablesWF)

/-- The declaration prefix resolves every name to a 32-byte address. -/
def LookupWidths (environment : CompileEnv) (state : BlockState) : Prop :=
  ∀ name address, lookupBinding environment (bindingView state) name = some address →
    address.hash.size = 32

def AllWidths (refs : Array Address) : Prop := ∀ address ∈ refs, address.hash.size = 32

theorem AllWidths.push {refs : Array Address} {address : Address}
    (prior : AllWidths refs) (added : address.hash.size = 32) : AllWidths (refs.push address) := by
  intro query member
  rcases Array.mem_push.mp member with old | same
  · exact prior query old
  · exact same ▸ added

/-! ## The collector writes neither table nor binding -/

/-- The fields the collector leaves alone: the primary tables and the
binding view. -/
def collectionView (state : BlockState) := (state.refs, state.univs, bindingView state)

theorem frame_compileUniv (source : Ix.Level) : Preserves collectionView (compileUniv source) := by
  intro context before
  have same := congrArg collectionView (CanonUnivCache.compileUniv_frame source context before)
  exact same

theorem frame_lookup (name : Ix.Name) : Preserves collectionView (lookupConstAddr name) := by
  intro context before
  rw [lookupConstAddr_state]

theorem frame_blob (bytes : ByteArray) : Preserves collectionView (storeBlob bytes) := by
  intro context before
  have same := congrArg collectionView (BlobWrites.storeBlob_preserves bytes context before).1
  exact same

theorem frame_collectUnivs (levels : List Ix.Level) (initial : Array Ixon.Univ) :
    Preserves collectionView (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact Preserves.bind (frame_compileUniv level) (fun value => ih (initial.push value))

theorem frame_structural (context : Address) (mutualContext : MutCtx) (params : List Ix.Name)
    (expr : Ix.Expr) (acc : ExprTableCollection) :
    Preserves collectionView (collectExprTablesStructural context mutualContext params expr acc) := by
  induction expr generalizing acc
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases acc with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact Preserves.pure _ _
    · with_reducible repeat' first
        | exact Preserves.pure _ _
        | exact Preserves.throw _ _
        | exact frame_compileUniv _
        | exact frame_lookup _
        | exact frame_blob _
        | exact frame_collectUnivs _ _
        | refine Preserves.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem frame_collect (expr : Ix.Expr) (context : Address) (initial : ExprTableCollection) :
    Preserves collectionView (collectExprTables expr context initial) :=
  Preserves.bind (Preserves.read _) (fun block =>
    frame_structural context block.mutCtx block.univCtx expr initial)

theorem frame_withUnivCtx (params : List Ix.Name) {action : CompileM α}
    (framed : Preserves collectionView action) : Preserves collectionView (withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  exact Preserves.bind (Preserves.modify _ _ (fun _ => rfl)) (fun _ => framed.withBlockEnv _)

/-- **The collector writes neither primary table nor binding**, on every
run. -/
theorem collection_frame (roots : List (Ix.Expr × List Ix.Name)) (initial : ExprTableCollection) :
    Preserves collectionView (collectPreseedExprs roots initial) := by
  induction roots generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons root rest ih =>
    rcases root with ⟨expr, params⟩
    rw [collectPreseedExprs]
    exact Preserves.bind (frame_withUnivCtx params (frame_collect expr _ initial)) (fun next => ih next)

/-! ## Collected references are 32 bytes -/

/-- A successful run under `LookupWidths` returns a value satisfying `post`;
`LookupWidths` itself is kept by the frame. -/
def Widths (action : CompileM α) (post : α → Prop) : Prop :=
  ∀ context before value after, LookupWidths context.1 before →
    rawRun action context before = (.ok value, after) → post value

theorem Widths.pure {value : α} {post : α → Prop} (good : post value) : Widths (pure value) post := by
  intro context before result after _ ran
  cases ran
  exact good

theorem Widths.throw (error : CompileError) (post : α → Prop) : Widths (throw error : CompileM α) post := by
  intro context before result after _ ran
  cases ran

theorem Widths.forget {action : CompileM α} : Widths action (fun _ => True) :=
  fun _ _ _ _ _ _ => trivial

theorem Widths.bind {action : CompileM α} {next : α → CompileM β} {first : α → Prop} {last : β → Prop}
    (framed : Preserves collectionView action) (head : Widths action first)
    (tail : ∀ value, first value → Widths (next value) last) : Widths (action >>= next) last := by
  intro context before result after widths ran
  obtain ⟨value, middle, firstRan, nextRan⟩ := bind_ok ran
  have kept : LookupWidths context.1 middle := by
    have same := framed context before
    rw [firstRan] at same
    have binding : bindingView middle = bindingView before := by
      have view := congrArg (fun view => view.2.2) same
      exact view
    intro name address found
    rw [binding] at found
    exact widths name address found
  exact tail value (head context before value middle widths firstRan) context middle result after kept nextRan

theorem Widths.lookup (name : Ix.Name) : Widths (lookupConstAddr name) (fun address => address.hash.size = 32) := by
  intro context before address after widths ran
  rw [lookupConstAddr_run] at ran
  cases found : lookupBinding context.1 (bindingView before) name with
  | none => rw [found] at ran; cases ran
  | some actual =>
    rw [found] at ran
    cases ran
    exact widths name address found

theorem Widths.blob (bytes : ByteArray) : Widths (storeBlob bytes) (fun address => address.hash.size = 32) := by
  intro context before address after _ ran
  rw [BlobWrites.storeBlob_run] at ran
  cases wrote : before.storeBlob context.1.blobs (Address.admissionHash bytes) bytes
  all_goals rw [wrote] at ran
  · cases ran
  · have same := Except.ok.inj (Prod.mk.inj ran).1
    rw [← same]
    exact Ixon.Authenticated.admissionHash_width bytes

theorem widths_structural (context : Address) (mutualContext : MutCtx) (params : List Ix.Name)
    (expr : Ix.Expr) (initial : ExprTableCollection) (prior : AllWidths initial.1) :
    Widths (collectExprTablesStructural context mutualContext params expr initial)
      (fun result => AllWidths result.1) := by
  induction expr generalizing initial
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact Widths.pure prior
    dsimp only
  case bvar => exact Widths.pure prior
  case fvar => exact Widths.throw _ _
  case mvar => exact Widths.throw _ _
  case sort level hash _ =>
    exact Widths.bind (frame_compileUniv level) Widths.forget (fun _ _ => Widths.pure prior)
  case const name levels hash _ =>
    intro ctx state value final widths ran
    obtain ⟨values, middle, levelsRan, rest⟩ := bind_ok ran
    have kept : LookupWidths ctx.1 middle := by
      have same := frame_collectUnivs levels.toList univs ctx state
      rw [levelsRan] at same
      have binding : bindingView middle = bindingView state := by
        have view := congrArg (fun view => view.2.2) same; exact view
      intro other address found
      rw [binding] at found
      exact widths other address found
    split at rest
    · obtain ⟨address, looked, lookRan, pureRan⟩ := bind_ok rest
      have width := Widths.lookup name ctx middle address looked kept lookRan
      cases pureRan
      exact prior.push width
    · cases rest
      exact prior
  case app first last hash firstIH lastIH _ =>
    exact Widths.bind (frame_structural _ _ _ first _) (firstIH _ prior) (fun result valid => lastIH result valid)
  case lam name type body info hash firstIH lastIH _ =>
    exact Widths.bind (frame_structural _ _ _ type _) (firstIH _ prior) (fun result valid => lastIH result valid)
  case forallE name type body info hash firstIH lastIH _ =>
    exact Widths.bind (frame_structural _ _ _ type _) (firstIH _ prior) (fun result valid => lastIH result valid)
  case letE name type value body nonDep hash firstIH middleIH lastIH _ =>
    exact Widths.bind (frame_structural _ _ _ type _) (firstIH _ prior) (fun result valid =>
      Widths.bind (frame_structural _ _ _ value _) (middleIH result valid) (fun result valid => lastIH result valid))
  case lit literal hash _ =>
    cases literal
    all_goals exact Widths.bind (frame_blob _) (Widths.blob _) (fun _ width => Widths.pure (prior.push width))
  case mdata metadata child hash childIH _ => exact childIH _ prior
  case proj name index child hash childIH _ =>
    exact Widths.bind (frame_lookup name) (Widths.lookup name) (fun _ width => childIH _ (prior.push width))

theorem widths_collect (expr : Ix.Expr) (params : List Ix.Name) (initial : ExprTableCollection)
    (prior : AllWidths initial.1) :
    Widths (withUnivCtx params (collectExprTables expr (univParamsKey params) initial))
      (fun result => AllWidths result.1) := by
  intro context before value after widths ran
  unfold Ix.CompileM.withUnivCtx at ran
  obtain ⟨_, reset, resetRan, collected⟩ := bind_ok ran
  rw [rawRun_modify] at resetRan
  cases resetRan
  rw [rawRun_withBlockEnv] at collected
  unfold collectExprTables at collected
  obtain ⟨block, same, blockRan, structural⟩ := bind_ok collected
  rw [rawRun_readBlock] at blockRan
  cases blockRan
  exact widths_structural (univParamsKey params) _ _ expr initial prior _ _ value after
    (by intro name address found; exact widths name address found) structural

/-- **Every collected reference is 32 bytes.** -/
theorem collect_widths (roots : List (Ix.Expr × List Ix.Name)) (initial : ExprTableCollection)
    (prior : AllWidths initial.1) :
    Widths (collectPreseedExprs roots initial) (fun result => AllWidths result.1) := by
  induction roots generalizing initial with
  | nil => exact Widths.pure prior
  | cons root rest ih =>
    rcases root with ⟨expr, params⟩
    rw [collectPreseedExprs]
    exact Widths.bind (frame_withUnivCtx params (frame_collect expr _ initial))
      (widths_collect expr params initial prior) (fun next valid => ih next valid)

/-! ## The inserters and the whole preseed -/

/-- The primary tables stay on the wire, on every run. -/
def Wire (action : CompileM α) : Prop :=
  ∀ context before, BlockWireTablesWF before → BlockWireTablesWF (rawRun action context before).2

theorem Wire.pure (value : α) : Wire (pure value) := fun _ _ wire => wire

theorem Wire.bind {action : CompileM α} {next : α → CompileM β}
    (head : Wire action) (tail : ∀ value, Wire (next value)) : Wire (action >>= next) := by
  intro context before wire
  have checked := head context before wire
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact checked
    | ok value => exact tail value context after checked

theorem Wire.of_frame {action : CompileM α} (framed : Preserves collectionView action) : Wire action := by
  intro context before wire
  have same := framed context before
  have refs : (rawRun action context before).2.refs = before.refs := by
    have view := congrArg (fun view => view.1) same; exact view
  have univs : (rawRun action context before).2.univs = before.univs := by
    have view := congrArg (fun view => view.2.1) same; exact view
  exact WireTables.of_same wire refs univs

theorem Wire.discard {action : CompileM α} (inner : Wire action) : Wire (Functor.discard action) := by
  unfold Functor.discard
  exact Wire.bind inner (fun _ => Wire.pure ())

theorem internRefs_wire (refs : List Address) (previous : Option Address)
    (widths : ∀ address ∈ refs, address.hash.size = 32) : Wire (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact Wire.pure ()
  | cons address rest ih =>
    unfold internPreseedRefs
    have tail := ih (some address) (fun item member => widths item (by simp [member]))
    split
    · exact Wire.bind (Wire.discard (fun context before wire =>
        WireTables.internRef_preserves context before address wire (widths _ (by simp)))) (fun _ => tail)
    · exact tail

theorem internUnivs_wire (entries : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray)
    (valid : ∀ entry ∈ entries, entry.2.wireWF) : Wire (internPreseedUnivs entries previous) := by
  induction entries generalizing previous with
  | nil => exact Wire.pure ()
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    unfold internPreseedUnivs
    have tail := ih (some key) (fun item member => valid item (by simp [member]))
    split
    · exact Wire.bind (Wire.discard (fun context before wire =>
        WireTables.internUniv_preserves context before value wire (valid (key, value) (by simp)))) (fun _ => tail)
    · exact tail

theorem canonUnivs_wire (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Wire (canonPreseedUnivs values initial) := by
  induction values generalizing initial with
  | nil => exact Wire.pure initial
  | cons value rest ih =>
    unfold canonPreseedUnivs
    refine Wire.bind ?_ (fun canonical => ih (initial.push canonical))
    intro context before wire
    rw [CanonUnivCache.canonUnivCached_run]
    cases before.canonUnivCache.get? value
    all_goals exact WireTables.of_same wire rfl rfl

/-- **A successful preseed keeps the primary tables on the wire** when the
declaration prefix resolves names to 32-byte addresses. -/
theorem preseed_wire (context : CompileEnv × BlockEnv) (roots : Array (Ix.Expr × List Ix.Name))
    {before after : BlockState} (wire : BlockWireTablesWF before) (widths : LookupWidths context.1 before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) : BlockWireTablesWF after := by
  rw [preseedExprTables] at ran
  obtain ⟨collection, collectedState, collected, tail⟩ := bind_ok ran
  rcases collection with ⟨refs, univs, seen⟩
  dsimp only at tail
  obtain ⟨_, refState, refsRan, rest⟩ := bind_ok tail
  obtain ⟨canonical, canonState, canonRan, finish⟩ := bind_ok rest
  obtain ⟨canonicalWire, finish⟩ := PreseedValidation.after_check canonical _ context canonState after () finish
  obtain ⟨_, univState, univsRan, flagRan⟩ := bind_ok finish
  have collectedWire := Wire.of_frame (collection_frame roots.toList (#[], #[], {})) context before wire
  rw [collected] at collectedWire
  have refWidths := collect_widths roots.toList (#[], #[], {}) (by intro address member; simp at member)
    context before _ collectedState widths collected
  have sortedWidths : ∀ address ∈ (refs.qsort (fun a b => a.cmpBytes b == .lt)).toList,
      address.hash.size = 32 := by
    intro address member
    apply refWidths address
    rw [Array.mem_toList_iff, Canon.mem_qsort] at member
    exact member
  have refWire := internRefs_wire _ none sortedWidths context collectedState collectedWire
  rw [refsRan] at refWire
  have canonWire := canonUnivs_wire univs.toList (Array.mkEmpty univs.size) context refState refWire
  rw [canonRan] at canonWire
  have entriesWire : ∀ entry ∈ ((canonical.map fun u => (univSortKey u, u)).qsort
      (fun entry other => byteArrayCmp entry.1 other.1 == .lt)).toList, entry.2.wireWF := by
    intro entry member
    rw [Array.mem_toList_iff, Canon.mem_qsort, Array.mem_map] at member
    obtain ⟨value, inside, rfl⟩ := member
    exact canonicalWire value inside
  have outputWire := internUnivs_wire _ none entriesWire context canonState canonWire
  rw [univsRan] at outputWire
  rw [rawRun_modify] at flagRan
  cases flagRan
  exact WireTables.of_same outputWire rfl rfl

/-! ## The binding view -/

theorem binding_internRefs (refs : List Address) (previous : Option Address) :
    Preserves bindingView (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact Preserves.pure _ ()
  | cons address rest ih =>
    unfold internPreseedRefs
    split
    · refine Preserves.bind ?_ (fun _ => ih (some address))
      unfold Functor.discard
      refine Preserves.bind ?_ (fun _ => Preserves.pure _ _)
      intro context before
      have same := congrArg bindingView (internRef_frame address context before)
      exact same
    · exact ih (some address)

theorem binding_internUnivs (entries : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    Preserves bindingView (internPreseedUnivs entries previous) := by
  induction entries generalizing previous with
  | nil => exact Preserves.pure _ ()
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    unfold internPreseedUnivs
    split
    · refine Preserves.bind ?_ (fun _ => ih (some key))
      unfold Functor.discard
      refine Preserves.bind ?_ (fun _ => Preserves.pure _ _)
      intro context before
      have same := congrArg bindingView (UniversePipeline.internUniv_frame value context before)
      exact same
    · exact ih (some key)

theorem binding_canonUnivs (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Preserves bindingView (canonPreseedUnivs values initial) := by
  induction values generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons value rest ih =>
    unfold canonPreseedUnivs
    refine Preserves.bind ?_ (fun canonical => ih (initial.push canonical))
    intro context before
    have same := congrArg bindingView (UniversePipeline.canonUnivCached_frame value context before)
    exact same

/-- The preseed keeps the binding view, on every run. -/
theorem preseed_binding (roots : Array (Ix.Expr × List Ix.Name)) :
    Preserves bindingView (preseedExprTables roots) := by
  rw [preseedExprTables]
  refine Preserves.bind (fun context before => ?_) (fun collection => ?_)
  · have same := congrArg (fun view => view.2.2) (collection_frame roots.toList (#[], #[], {}) context before)
    exact same
  rcases collection with ⟨refs, univs, _⟩
  apply Preserves.bind (binding_internRefs _ none)
  intro _
  apply Preserves.bind (binding_canonUnivs _ _)
  intro canonical
  refine Preserves.bind (fun context before => ?_) (fun _ => ?_)
  · rw [PreseedValidation.state]
  apply Preserves.bind (binding_internUnivs _ none)
  intro _
  exact Preserves.modify _ _ (fun _ => rfl)

/-- The preseed keeps `LookupWidths`, on every run. -/
theorem preseed_widths (context : CompileEnv × BlockEnv) (roots : Array (Ix.Expr × List Ix.Name))
    (before : BlockState) (widths : LookupWidths context.1 before) :
    LookupWidths context.1 (rawRun (preseedExprTables roots) context before).2 := by
  intro name address found
  rw [preseed_binding roots context before] at found
  exact widths name address found

end Ix.CompileCert.PreseedWire
