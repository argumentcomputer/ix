import Ix.CompileCert.PreseedState

/-! Actual metadata compilation preserves the ordinary reader and its state
invariant, including on errors. This does not interpret metadata expressions
through primary tables or erase semantic contracts. -/
namespace Ix.CompileCert.RecordState
open Ix.CompileM Ix.CompileCert ExpressionState UniversePipeline PreseedState
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

def primary (s : BlockState) :=
  (s.refs, s.refsIndex, s.univs, s.univsIndex, s.exprCache, bindingView s)
private def core (s : BlockState) :=
  (univView s, s.refs, s.refsIndex, bindingView s, s.exprCache, s.blockBlobs)

variable {md : Mode} {cx : Ctx md} {param : Nat → LevelParam}
  {self : Nat → Option (ReadM (CName md))} {related : Ix.Expr → CExpr md → Prop}
  {bindings : Bindings} {env : CompileEnv}

structure Step (cx : Ctx md) (param : Nat → LevelParam)
    (member : Nat → Option (ReadM (CName md))) (related : Ix.Expr → CExpr md → Prop)
    (bindings : Bindings) (env : CompileEnv) (action : CompileM α) : Prop where
  good : GoodStep cx param member related bindings env action
  frame : Preserves primary action

local notation "S" => Step cx param self related bindings env

theorem Step.pure (v : α) : S (pure v) :=
  ⟨GoodStep.pure v, Preserves.pure primary v⟩
theorem Step.bind {a : CompileM α} {f : α → CompileM β} (h : S a)
    (t : ∀ v, S (f v)) : S (a >>= f) :=
  ⟨GoodStep.bind h.good (fun v => (t v).good), Preserves.bind h.frame (fun v => (t v).frame)⟩

private theorem same {action : CompileM α} (h : Preserves core action) : S action := by
  constructor
  · intro block before good
    have eq := h (env, block) before
    simp only [core, Prod.mk.injEq] at eq
    exact good_of_same eq.1 eq.2.1 eq.2.2.1 eq.2.2.2.1 eq.2.2.2.2.1 eq.2.2.2.2.2 good
  · intro context before
    exact congrArg (fun v => (v.2.1, v.2.2.1, v.1.2.2.1, v.1.2.2.2.1,
      v.2.2.2.2.1, v.2.2.2.1)) (h context before)

private theorem names {action : CompileM α} (h : Serializers.NamesBlobs action)
    (aligned : ∀ a, cx.blob a = env.blobs.get? a) : S action := by
  refine ⟨fun block before good => good_namesBlobs cx param self related bindings
    (env, block) (h (env, block) before).1 (h (env, block) before).2 aligned good, ?_⟩
  exact h.preserves primary (fun _ => rfl)

private theorem metaUniv (u : Ixon.Univ) : S (internMetaUniv u) := by
  constructor
  · intro block before good
    have valid := Interning.internMetaUniv_correct u (env, block) before good.1.1.tables.1 good.1.1.tables.2
    have frame := internMetaUniv_frame u (env, block) before
    refine ⟨⟨⟨⟨?_, ?_, valid.1, valid.2.1⟩, ?_, ?_⟩,
      Interning.internMetaUniv_cache_sound u (env, block) before cx param self related good.2⟩,
      Interning.internMetaUniv_reading u (env, block) before cx param self⟩
    · exact (congrArg UniverseMeaning.UnivCacheExact frame).mpr good.1.1.rawCache
    · exact (congrArg CanonUnivCache.CanonCacheExact frame).mpr good.1.1.canonCache
    · exact (congrArg Interning.RefIndexSound frame).mpr good.1.2.1
    · exact (congrArg bindingView frame).trans good.1.2.2
  · intro context before
    have frame := internMetaUniv_frame u context before
    have tables := Interning.internMetaUniv_tables u context before
    simp only [primary, Prod.mk.injEq]
    exact ⟨tables.1, by have h := congrArg BlockState.refsIndex frame; exact h,
      tables.2.1, tables.2.2.1, tables.2.2.2.2, by have h := congrArg bindingView frame; exact h⟩

private theorem univ (u : Ix.Level) : S (compileAndInternUnivMeta u) := by
  unfold compileAndInternUnivMeta
  apply Step.bind ⟨GoodStep.compileUniv u, fun context before =>
    by have h := congrArg primary (CanonUnivCache.compileUniv_frame u context before); exact h⟩
  intro raw
  apply Step.bind ⟨GoodStep.canon raw, fun context before =>
    by have h := congrArg primary (canonUnivCached_frame raw context before); exact h⟩
  intro canonical
  with_reducible repeat' first
    | exact Step.pure _
    | exact metaUniv _
    | exact same (Preserves.get core)
    | refine Step.bind ?_ (fun _ => ?_)
    | split

private theorem checked (table : String) (n : Nat) : Preserves core (checkedTableIndex table n) :=
  fun context before => congrArg core (Interning.checkedTableIndex_state table n context before)

private theorem ref (a : Address) : S (internRefMeta a) := by
  apply same
  unfold internRefMeta
  with_reducible repeat' first
    | exact Preserves.pure core _
    | exact Preserves.get core
    | exact Preserves.read core
    | exact checked _ _
    | exact Preserves.modify core _ (fun _ => rfl)
    | refine Preserves.bind ?_ (fun _ => ?_)
    | split
    | dsimp (config := { failIfUnchanged := true }) only

private theorem listLoop (xs : List α) (initial : β)
    (f : (x : α) → x ∈ xs → β → CompileM (ForInStep β))
    (h : ∀ x hx b, S (f x hx b)) : S (forIn' xs initial f) := by
  induction xs generalizing initial with
  | nil => exact Step.pure _
  | cons x xs ih =>
    rw [List.forIn'_cons]
    apply Step.bind (h x (by simp) initial)
    intro result
    cases result with
    | done _ => exact Step.pure _
    | yield _ => exact ih _ _ (fun x hx b => h x _ b)

private theorem arrayLoop (xs : Array α) (initial : β)
    (f : (x : α) → x ∈ xs → β → CompileM (ForInStep β))
    (h : ∀ x hx b, S (f x hx b)) : S (forIn' xs initial f) := by
  simpa only [Array.forIn'_toList] using listLoop xs.toList initial
    (fun x hx b => f x (Array.mem_toList_iff.mp hx) b) (fun x hx b => h x _ b)

private theorem mapped (xs : List α) (f : α → CompileM β) (h : ∀ x, S (f x)) : S (xs.mapM f) := by
  induction xs with
  | nil => exact Step.pure _
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact Step.bind (h x) (fun _ => Step.bind ih (fun _ => Step.pure _))
private theorem mapArray (xs : Array α) (f : α → CompileM β) (h : ∀ x, S (f x)) : S (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Step.bind (mapped xs.toList f h) (fun _ => Step.pure _)
private theorem alloc (node : Ixon.ExprMetaData) : S (allocArenaNode node) := same (fun _ _ => rfl)
private theorem patch (root : UInt64) (indices : Array UInt64) : S (pushUnivPatch root indices) :=
  same (fun _ _ => rfl)
private theorem lookup (n : Ix.Name) : S (lookupConstAddr n) :=
  same (fun context before => congrArg core (lookupConstAddr_state n context before))

private theorem constructorStep (aligned : ∀ a, cx.blob a = env.blobs.get? a)
    (e : Ix.Expr) (recur : (x : Ix.Expr) → sizeOf x < sizeOf e → CompileM (Ixon.Expr × UInt64))
    (children : ∀ x hx, S (recur x hx)) : S (compileExprMetaStep e recur) := by
  cases e <;> try cases ‹Lean.Literal›
  all_goals rw [compileExprMetaStep]
  all_goals with_reducible repeat' first
    | exact Step.pure _
    | exact same (action := throw _) (Preserves.throw core _)
    | exact same (action := getBlockState) (Preserves.get core)
    | exact same (action := getBlockEnv) (Preserves.read core)
    | exact same (action := checkedTableIndex _ _) (checked _ _)
    | exact alloc _
    | exact patch _ _
    | exact ref _
    | exact univ _
    | exact mapArray _ _ (fun _ => univ _)
    | exact names (action := compileName _) (Serializers.NamesBlobs.compileName _) aligned
    | exact names (action := compileKVMap _) (Serializers.NamesBlobs.compileKVMap _) aligned
    | exact names (action := storeBlob _) (Serializers.NamesBlobs.storeBlob _) aligned
    | exact lookup _
    | exact children _ _
    | refine Step.bind ?_ (fun _ => ?_)
    | apply arrayLoop; intros
    | split

/-- Actual recursive metadata compilation, through both exact caches and
every constructor. Its returned metadata value is deliberately not interpreted. -/
theorem compileExprMeta_preserves (aligned : ∀ a, cx.blob a = env.blobs.get? a)
    (e : Ix.Expr) : S (compileExprMeta e) := by
  induction e using compileExprMeta.induct
  rename_i e ih
  rw [compileExprMeta]
  apply Step.bind (same (Preserves.get core))
  intro state
  split
  · exact Step.pure _
  · split
    · exact Step.pure _
    · apply Step.bind (constructorStep aligned e _ ih)
      rintro ⟨result, root⟩
      apply Step.bind
      · exact same (Preserves.modify core _ (fun _ => rfl))
      · intro _; exact Step.pure _

private theorem arrayPlain (xs : Array α) (initial : β) (f : α → β → CompileM (ForInStep β))
    (h : ∀ x b, S (f x b)) : S (forIn xs initial f) :=
  arrayLoop xs initial (fun x _ b => f x b) (fun x _ b => h x b)

/-- The actual record loop preserves the ordinary invariant and primary
footprint on success and error, including after prior records have committed. -/
theorem compileRecords_preserves (aligned : ∀ a, cx.blob a = env.blobs.get? a)
    (ns : Array Nat) : S (compileRecords ns) := by
  unfold compileRecords
  with_reducible repeat' first
    | exact Step.pure _
    | exact same (action := throw _) (Preserves.throw core _)
    | exact same (action := getBlockState) (Preserves.get core)
    | exact same (action := getBlockEnv) (Preserves.read core)
    | exact same (action := getCompileEnv) (Preserves.readCompile core)
    | exact same (action := modifyBlockState _) (Preserves.modify core _ (fun _ => rfl))
    | exact compileExprMeta_preserves aligned _
    | refine Step.bind ?_ (fun _ => ?_)
    | apply arrayPlain; intros
    | split
    | dsimp (config := { failIfUnchanged := true }) only

end Ix.CompileCert.RecordState
