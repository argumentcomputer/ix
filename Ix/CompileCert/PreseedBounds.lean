import Ix.CompileCert.CanonUnivWire
import Ix.CompileCert.PreseedInsertion

/-! Derive canonical-universe wire bounds from source-expression bounds
through the actual collector, including raw cache reuse and root resets. -/

namespace Ix.CompileCert.PreseedBounds

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open UniverseExact (CacheExact Safe)

/-- A source resource bound, independent of compilation or validity checks. -/
def LevelBound (source : Level) : Prop :=
  ∀ value, ixLevelEval (fun _ => 1) source = some value → value < UInt64.size

/-- Bounds on source universes in every expression position. This predicate
does not assert source typing, closedness or successful compilation. -/
def ExprBound : Expr → Prop
  | .sort level _ => LevelBound level
  | .const _ levels _ => ∀ level ∈ levels, LevelBound level
  | .app first last _ | .lam _ first last _ _ | .forallE _ first last _ _ =>
    ExprBound first ∧ ExprBound last
  | .letE _ first middle last _ _ => ExprBound first ∧ ExprBound middle ∧ ExprBound last
  | .proj _ _ child _ | .mdata _ child _ => ExprBound child
  | .bvar .. | .fvar .. | .mvar .. | .lit .. => True

def UnivBound (value : Ixon.Univ) : Prop := univEval (fun _ => 1) value < UInt64.size

def AllBound (values : Array Ixon.Univ) : Prop := ∀ value ∈ values, UnivBound value

theorem lower_bound {params : List Name} {source : Level} {value : Ixon.Univ}
    (bounded : LevelBound source) (lowered : UniverseExact.lower params source = some value) : UnivBound value := by
  have represented := UniverseExact.lower_represents params source value lowered
  exact bounded _ (represented.eval (fun _ => 1) (fun _ => 1) (by intros; rfl))

theorem AllBound.push {values : Array Ixon.Univ} {value : Ixon.Univ}
    (prior : AllBound values) (added : UnivBound value) : AllBound (values.push value) := by
  intro query member
  rcases Array.mem_push.mp member with old | same
  · exact prior query old
  · exact same ▸ added

theorem Safe.weaken {action : CompileM α} {context : CompileEnv × BlockEnv} {first last : α → Prop}
    (safe : Safe action context first) (implies : ∀ value, first value → last value) : Safe action context last := by
  intro before exactCache
  have checked := safe before exactCache
  exact ⟨checked.1, fun value ran => implies value (checked.2 value ran)⟩

theorem Safe.compile (source : Level) (context : CompileEnv × BlockEnv) (bounded : LevelBound source) :
    Safe (compileUniv source) context UnivBound :=
  Safe.weaken (UniverseExact.compileUniv_exact source context) (fun _ lowered => lower_bound bounded lowered)

theorem Safe.lookup (name : Name) (context : CompileEnv × BlockEnv) :
    Safe (lookupConstAddr name) context (fun _ => True) := by
  intro before exactCache
  exact ⟨PreseedUniverses.CacheSafe.lookup name context before exactCache, by intros; trivial⟩

theorem Safe.blob (bytes : ByteArray) (context : CompileEnv × BlockEnv) :
    Safe (storeBlob bytes) context (fun _ => True) := by
  intro before exactCache
  exact ⟨PreseedUniverses.CacheSafe.blob bytes context before exactCache, by intros; trivial⟩

theorem levels_bound (context : CompileEnv × BlockEnv) (levels : List Level)
    (bounded : ∀ level ∈ levels, LevelBound level) (initial : Array Ixon.Univ) (prior : AllBound initial) :
    Safe (collectExprTableUnivs levels initial) context AllBound := by
  induction levels generalizing initial with
  | nil => exact UniverseExact.Safe.pure context prior
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    apply UniverseExact.Safe.bind (Safe.compile level context (bounded level (by simp)))
    intro value valid
    exact ih (fun level member => bounded level (by simp [member])) (initial.push value) (prior.push valid)

theorem structural_bound (context : CompileEnv × BlockEnv) (hint : Address) (mutualContext : MutCtx)
    (params : List Name) (source : Expr) (bounded : ExprBound source)
    (initial : ExprTableCollection) (prior : AllBound initial.2.1) :
    Safe (collectExprTablesStructural hint mutualContext params source initial) context (fun result => AllBound result.2.1) := by
  induction source generalizing initial
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact UniverseExact.Safe.pure context prior
  case bvar => exact UniverseExact.Safe.pure context prior
  case fvar => exact UniverseExact.Safe.throw context _ _
  case mvar => exact UniverseExact.Safe.throw context _ _
  case sort level hash _ =>
    exact UniverseExact.Safe.bind (Safe.compile level context bounded) (fun _ valid =>
      UniverseExact.Safe.pure context (prior.push valid))
  case const name levels hash _ =>
    apply UniverseExact.Safe.bind (levels_bound context levels.toList (by simpa [ExprBound] using bounded) univs prior)
    intro values valid
    split
    · exact UniverseExact.Safe.bind (Safe.lookup name context) (fun _ _ => UniverseExact.Safe.pure context valid)
    · exact UniverseExact.Safe.pure context valid
  case app first last hash firstIH lastIH _ =>
    exact UniverseExact.Safe.bind (firstIH bounded.1 _ prior) (fun result valid => lastIH bounded.2 result valid)
  case lam name type body info hash firstIH lastIH _ =>
    exact UniverseExact.Safe.bind (firstIH bounded.1 _ prior) (fun result valid => lastIH bounded.2 result valid)
  case forallE name type body info hash firstIH lastIH _ =>
    exact UniverseExact.Safe.bind (firstIH bounded.1 _ prior) (fun result valid => lastIH bounded.2 result valid)
  case letE name type value body nonDep hash firstIH middleIH lastIH _ =>
    exact UniverseExact.Safe.bind (firstIH bounded.1 _ prior) (fun result valid =>
      UniverseExact.Safe.bind (middleIH bounded.2.1 result valid) (fun result valid => lastIH bounded.2.2 result valid))
  case lit literal hash _ =>
    cases literal
    all_goals exact UniverseExact.Safe.bind (Safe.blob _ context) (fun _ _ => UniverseExact.Safe.pure context prior)
  case mdata metadata child hash childIH _ => exact childIH bounded _ prior
  case proj name index child hash childIH _ =>
    exact UniverseExact.Safe.bind (Safe.lookup name context) (fun _ _ => childIH bounded _ prior)

theorem root_bound (context : CompileEnv × BlockEnv) (before after : BlockState)
    (source : Expr) (params : List Name) (bounded : ExprBound source)
    (initial output : ExprTableCollection) (prior : AllBound initial.2.1)
    (ran : rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before = (.ok output, after)) :
    AllBound output.2.1 := by
  rw [PreseedReferences.root_run] at ran
  have checked := structural_bound (context.1, { context.2 with univCtx := params }) (univParamsKey params)
    context.2.mutCtx params source bounded initial prior { before with univCache := {} } (UniverseExact.cache_empty before)
  exact checked.2 output (congrArg Prod.fst ran)

theorem roots_bound (context : CompileEnv × BlockEnv) (roots : List (Expr × List Name))
    (bounded : ∀ root ∈ roots, ExprBound root.1) (before after : BlockState)
    (initial output : ExprTableCollection) (prior : AllBound initial.2.1)
    (ran : rawRun (collectPreseedExprs roots initial) context before = (.ok output, after)) : AllBound output.2.1 := by
  induction roots generalizing before initial with
  | nil =>
    rw [collectPreseedExprs, rawRun_pure] at ran
    cases Except.ok.inj (congrArg Prod.fst ran)
    exact prior
  | cons root rest ih =>
    rcases root with ⟨source, params⟩
    rw [collectPreseedExprs] at ran
    obtain ⟨middle, state, rootRan, restRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have next := root_bound context before state source params (bounded (source, params) (by simp)) initial middle prior rootRan
    exact ih (fun root member => bounded root (by simp [member])) state middle next restRan

theorem roots_wire (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (bounded : ∀ root ∈ roots, ExprBound root.1) (before after : BlockState) (output : ExprTableCollection)
    (ran : rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok output, after)) :
    ∀ value ∈ output.2.1, (Ixon.canonUniv value).wireWF := by
  have checked := roots_bound context roots.toList (by simpa using bounded) before after _ output (by simp [AllBound]) ran
  intro value member
  exact CanonUnivWire.canonUniv_wire value (checked value member)

/-- Actual table construction derives its canonical wire premise from the
source roots. The source bound is an explicit resource condition, not a
consequence of source typing. -/
theorem preseed_from_bounded_roots (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (bounded : ∀ root ∈ roots, ExprBound root.1) (before collectedState after : BlockState)
    (collection : ExprTableCollection)
    (collected : rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok collection, collectedState))
    (ordinary : before.p3MetaMode = false) (refsSound : Interning.RefIndexSound before)
    (univsSound : Interning.UnivIndexSound before) (canonExact : UniversePipeline.CanonCacheExact before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    after.univsFinal = true ∧ after.p3MetaMode = false ∧
      Interning.RefIndexSound after ∧ Interning.UnivIndexSound after ∧
      (∀ address ∈ collection.1, PreseedInsertion.RefPresent after address) ∧
      (∀ value ∈ collection.2.1, PreseedInsertion.UnivPresent after (Ixon.canonUniv value)) :=
  PreseedInsertion.preseed_from_collection context roots before collectedState after collection collected ordinary
    refsSound univsSound canonExact (roots_wire context roots bounded before collectedState collection collected) ran

theorem preseed_reads_bounded (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (bounded : ∀ root ∈ roots, ExprBound root.1) (before collectedState after : BlockState)
    (collection : ExprTableCollection)
    (collected : rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok collection, collectedState))
    (ordinary : before.p3MetaMode = false) (refsSound : Interning.RefIndexSound before)
    (univsSound : Interning.UnivIndexSound before) (canonExact : UniversePipeline.CanonCacheExact before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    (∀ root ∈ roots, PreseedReferences.Covered
      (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx after.refs root.1) ∧
    (∀ params level, PreseedUniverses.Present params collection.2.1 level →
      ∃ raw index, UniverseExact.lower params level = some raw ∧
        after.univsIndex.get? (Ixon.canonUniv raw) = some index ∧
        after.univs[index.toNat]? = some (Ixon.canonUniv raw)) :=
  PreseedInsertion.preseed_reads context roots before collectedState after collection collected ordinary
    refsSound univsSound canonExact (roots_wire context roots bounded before collectedState collection collected) ran

end Ix.CompileCert.PreseedBounds
