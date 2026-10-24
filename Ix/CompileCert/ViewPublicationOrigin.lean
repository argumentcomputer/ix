import Ix.CompileCert.OptShapeOrigin
import Ix.Cert.Resolution
import Ix.Cert.Claims
import IxC.Kernel.Verify.Rename.Installs

/-! # Actual view queries and the birth of new memo entries

The real local loop identifies each queried head and exact cached value or
fresh build. The publication's actual absence guard eliminates the cached
arm for every new entry, without a MemoSound or input-frame premise.
-/

namespace Ix.CompileCert.ViewPublicationOrigin

open Ix (Name)
open Ix.CompileM Ix.Compile.Pass
open Ix.Compile.ExactKey (ExactName)

def Built (cenv : CompileEnv) (key : Name) (view : BlockView) : Prop :=
  buildView (viewInput cenv) (blockAll cenv key) = .ok view

/-- An arbitrary local-map hit has no invented meaning. -/
theorem viewOf_origin {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {key : ExactName} {view : BlockView} (run : viewOf cenv views key = .ok view) :
    views.get? key = some view ∨ views.get? key = none ∧
      (cenv.p3Views.get? key = some view ∨ cenv.p3Views.get? key = none ∧ Built cenv key view) := by
  cases localHit : views.get? key with
  | some v =>
    change views[key]? = some v at localHit
    have equal : v = view := by simpa [viewOf, localHit, pure, Except.pure] using run
    subst view
    exact .inl rfl
  | none =>
    change views[key]? = none at localHit
    cases memoHit : cenv.p3Views.get? key with
    | some v =>
      change cenv.p3Views[key]? = some v at memoHit
      have equal : v = view := by simpa [viewOf, localHit, memoLookup, memoHit, pure, Except.pure] using run
      subst view
      exact .inr ⟨rfl, .inl rfl⟩
    | none =>
      change cenv.p3Views[key]? = none at memoHit
      exact .inr ⟨rfl, .inr ⟨rfl, by
        simpa [viewOf, localHit, memoLookup, memoHit, Built, pure, Except.pure] using run⟩⟩

def Origin (cenv : CompileEnv) (heads : List Name) (key : Name) (view : BlockView) : Prop :=
  ∃ h ∈ heads, cenv.p3Heads.get? h = some key ∧
    (cenv.p3Views.get? key = some view ∨ cenv.p3Views.get? key = none ∧ Built cenv key view)

def Origins (cenv : CompileEnv) (heads : List Name) (views : Std.HashMap ExactName BlockView) : Prop :=
  ∀ (key : ExactName) view, views.get? key = some view → Origin cenv heads key view

theorem Origins.mono {cenv heads more views} (held : Origins cenv heads views)
    (included : ∀ h ∈ heads, h ∈ more) : Origins cenv more views := by
  intro key view hit
  obtain ⟨h, member, owner, origin⟩ := held key view hit
  exact ⟨h, included h member, owner, origin⟩

theorem Origins.insert {cenv heads views} (held : Origins cenv heads views)
    {key : ExactName} {view : BlockView} (origin : Origin cenv heads key view) :
    Origins cenv heads (views.insert key view) := by
  intro k v hit
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hit
  split at hit
  · rename_i same
    have equal : key = k := eq_of_beq same
    subst k
    cases hit
    exact origin
  · rw [← Std.HashMap.get?_eq_getElem?] at hit
    exact held k v hit

/-- Every actual result retains a queried head/owner and its exact origin.
The loop starts empty; missing heads and duplicate owners preserve origins. -/
theorem viewsOf_origins {cenv : CompileEnv} {heads : Array Name} {views : Std.HashMap ExactName BlockView}
    (run : viewsOf cenv heads = .ok views) : Origins cenv heads.toList views := by
  unfold viewsOf at run
  obtain ⟨result, walk, returned⟩ := Loop.except_bind_ok.mp run
  cases returned
  refine Loop.forIn_inv_array (fun pre table => Origins cenv pre table) _ heads ?_ ?_ walk
  · intro pre h post table step _ held ran
    have kept := held.mono (fun n member => List.mem_append_left [h] member)
    split at ran
    · rename_i key owner
      dsimp only at ran
      split at ran
      · rename_i fresh
        obtain ⟨v, call, ran⟩ := Loop.except_bind_ok.mp ran
        cases ran
        refine ⟨table.insert key v, rfl, kept.insert ?_⟩
        have absent : table.get? key = none := by
          exact Std.HashMap.getElem?_eq_none_of_contains_eq_false (by simpa using fresh)
        rcases viewOf_origin call with localOrigin | ⟨_, old | ⟨missing, built⟩⟩
        · rw [absent] at localOrigin; cases localOrigin
        · exact ⟨h, by simp, owner, .inl old⟩
        · exact ⟨h, by simp, owner, .inr ⟨missing, built⟩⟩
      · cases ran; exact ⟨table, rfl, kept⟩
    · cases ran; exact ⟨table, rfl, kept⟩
  · intro key view impossible
    simp at impossible

theorem viewsOf_origin {cenv : CompileEnv} {heads : Array Name} {views : Std.HashMap ExactName BlockView}
    (run : viewsOf cenv heads = .ok views) {key : Name} {view : BlockView}
    (hit : views.get? key = some view) : Origin cenv heads.toList key view :=
  viewsOf_origins run key view hit

def NewEntries (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (entries : Array (Name × BlockView)) : Prop :=
  ∀ (key : Name) view, (key, view) ∈ entries →
    views.get? key = some view ∧ cenv.p3Views.get? key = none ∧ viewMemoable cenv key = true

/-- Structural membership in the actual publication fold retains both guards. -/
theorem newMemoViews_entries (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView) :
    NewEntries cenv views (newMemoViews cenv views) := by
  unfold newMemoViews
  rw [Std.HashMap.fold_eq_foldl_toList]
  apply List.foldlRecOn
  · intro key view impossible
    simp at impossible
  · intro entries held pair member
    split
    · rename_i accepted
      have guards : cenv.p3Views.contains pair.1 = false ∧ viewMemoable cenv pair.1 = true := by
        simpa only [Bool.and_eq_true, Bool.not_eq_true'] using accepted
      intro key view inserted
      rcases Array.mem_push.mp inserted with old | same
      · exact held key view old
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        refine ⟨Ix.Cert.Condense.get_of_mem_toList member BEq.rfl, ?_, guards.2⟩
        rw [Std.HashMap.get?_eq_getElem?]
        exact Std.HashMap.getElem?_eq_none_of_contains_eq_false guards.1
    · exact held

/-- A NEW published entry has an actual build at THIS producer snapshot.
The real absence guard rules out memo reuse; no MemoSound input is needed. -/
theorem newMemoViews_built {cenv : CompileEnv} {heads : Array Name} {views : Std.HashMap ExactName BlockView}
    (run : viewsOf cenv heads = .ok views) {key : Name} {view : BlockView}
    (member : (key, view) ∈ newMemoViews cenv views) :
    cenv.p3Views.get? key = none ∧ viewMemoable cenv key = true ∧ Built cenv key view := by
  obtain ⟨hit, absent, memoable⟩ := newMemoViews_entries cenv views key view member
  obtain ⟨_, _, _, origin⟩ := viewsOf_origin run hit
  rcases origin with cached | ⟨_, built⟩
  · rw [absent] at cached; cases cached
  · exact ⟨absent, memoable, built⟩

/-- Insert-once merging preserves the EXACT old value, not just its domain. -/
theorem memoMerge_keeps {table : Std.HashMap ExactName BlockView}
    (entries : Array (ExactName × BlockView)) {key : ExactName} {view : BlockView}
    (hit : table.get? key = some view) : (memoMerge table entries).get? key = some view := by
  unfold memoMerge
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun current : Std.HashMap ExactName BlockView =>
    current.get? key = some view) entries.toList _ hit
  intro current held pair _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insertIfNew]
  split
  · rename_i fresh
    have same : pair.1 = key := eq_of_beq fresh.1
    have absent : current[key]? = none := Std.HashMap.getElem?_eq_none (by simpa only [same] using fresh.2)
    have present : current[key]? = some view := held
    rw [present] at absent
    cases absent
  · exact held

def MemoOrigins (old : Std.HashMap ExactName BlockView) (entries : Array (ExactName × BlockView))
    (table : Std.HashMap ExactName BlockView) : Prop :=
  ∀ (key : ExactName) view, table.get? key = some view → old.get? key = some view ∨ (key, view) ∈ entries

theorem memoMerge_origin {table : Std.HashMap ExactName BlockView}
    {entries : Array (ExactName × BlockView)} {key : ExactName} {view : BlockView}
    (hit : (memoMerge table entries).get? key = some view) :
    table.get? key = some view ∨ (key, view) ∈ entries := by
  suffices MemoOrigins table entries (memoMerge table entries) from this key view hit
  unfold memoMerge
  rw [← Array.foldl_toList]
  apply List.foldlRecOn
  · intro k v old; exact .inl old
  · intro current held pair member k v found
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insertIfNew] at found
    split at found
    · rename_i fresh
      have same : pair.1 = k := eq_of_beq fresh.1
      subst k
      cases found
      exact .inr (Array.mem_toList_iff.mp member)
    · exact held k v found

/-- A new transition result is the old exact hit or a real producer build. -/
theorem memoMerge_views_origin {cenv : CompileEnv} {heads : Array Name} {views : Std.HashMap ExactName BlockView}
    (run : viewsOf cenv heads = .ok views) {key : ExactName} {view : BlockView}
    (hit : (memoMerge cenv.p3Views (newMemoViews cenv views)).get? key = some view) :
    cenv.p3Views.get? key = some view ∨
      cenv.p3Views.get? key = none ∧ viewMemoable cenv key = true ∧ Built cenv key view := by
  rcases memoMerge_origin hit with old | added
  · exact .inl old
  · exact .inr (newMemoViews_built run added)

set_option hygiene false in
local macro "finish_views" held:term : tactic => `(tactic| (
  refine Ix.Cert.Resolution.loop_bind
    (P := fun d : DriverAcc => d.cenv.p3Views = memoMerge acc.cenv.p3Views pub.views)
    (I := fun _ : Array Name => True) _ _ _ _ trivial (fun _ _ _ _ => trivial) ?_
  intro _ _
  exact $held))

set_option hygiene false in
local macro "merge_views_tail" held:term : tactic => `(tactic| (
  refine Ix.Cert.Resolution.loop_bind
    (P := fun d : DriverAcc => d.cenv.p3Views = memoMerge acc.cenv.p3Views pub.views)
    (I := fun c : CompileEnv => c.p3Views = acc.cenv.p3Views) _ _ _ _ $held
    (fun _ _ _ h => h) ?_
  intro L hL
  refine Ix.Cert.Resolution.loop_bind
    (P := fun d : DriverAcc => d.cenv.p3Views = memoMerge acc.cenv.p3Views pub.views)
    (I := fun c : CompileEnv => c.p3Views = acc.cenv.p3Views) _ _ _ _ hL ?_ ?_
  · intro _ _ _ h; split <;> exact h
  · intro L' hL'
    split
    · refine Ix.Cert.Resolution.loop_bind
        (P := fun d : DriverAcc => d.cenv.p3Views = memoMerge acc.cenv.p3Views pub.views)
        (I := fun c : CompileEnv => c.p3Views = memoMerge acc.cenv.p3Views pub.views) _ _ _ _ ?_ ?_ ?_
      · change memoMerge L'.p3Views pub.views = _
        rw [hL']
      · intro cls _ s hs
        exact Ix.Cert.Resolution.forIn_inv_array
          (fun c : CompileEnv => c.p3Views = memoMerge acc.cenv.p3Views pub.views)
          _ cls (by intro _ _ _ h; exact h) s hs
      · intro _ h; finish_views h
    · finish_views (by change memoMerge L'.p3Views pub.views = _; rw [hL'])))

/-- Only the memo component is identified; live input fields may change. -/
theorem mergeCompiledBlock_views (acc : DriverAcc) (lo : Name) (result : BlockResult)
    (cache : BlockState) (pub : Published) :
    (mergeCompiledBlock acc lo result cache pub).cenv.p3Views = memoMerge acc.cenv.p3Views pub.views := by
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · split <;> merge_views_tail rfl
  · refine Ix.Cert.Resolution.loop_bind
      (P := fun d : DriverAcc => d.cenv.p3Views = memoMerge acc.cenv.p3Views pub.views)
      (I := fun c : CompileEnv => c.p3Views = acc.cenv.p3Views) _ _ _ _ rfl ?_ ?_
    · intro _ _ _ h; split <;> exact h
    · intro _ h; merge_views_tail h

/-- Retention alone is not soundness or reachability of a warm view. -/
theorem failAuxPromotion_views (acc : DriverAcc) (all : Ix.Set Name) (message : String) :
    (failAuxPromotion acc all message).cenv.p3Views = acc.cenv.p3Views := by
  unfold failAuxPromotion
  simp only [Id.run, Loop.idBind, Loop.idPure]
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine Ix.Cert.Resolution.forIn_inv_list (fun state => state.cenv.p3Views = acc.cenv.p3Views)
    _ _ ?_ acc rfl
  intros
  assumption

/-- The post-failure query has a REAL surviving head/owner. Its reused arm
keeps the same pre-failure value; no current-build equality is inferred. -/
theorem after_failure_query_origin {acc : DriverAcc} {all : Ix.Set Name} {message : String}
    {heads : Array Name} {views : Std.HashMap ExactName BlockView}
    (run : viewsOf (failAuxPromotion acc all message).cenv heads = .ok views)
    {key : Name} {view : BlockView} (hit : views.get? key = some view) :
    ∃ h ∈ heads.toList, (failAuxPromotion acc all message).cenv.p3Heads.get? h = some key ∧
      (acc.cenv.p3Views.get? key = some view ∨
        Built (failAuxPromotion acc all message).cenv key view) := by
  obtain ⟨h, member, owner, old | ⟨_, built⟩⟩ := viewsOf_origin run hit
  · exact ⟨h, member, owner, .inl (by simpa only [failAuxPromotion_views] using old)⟩
  · exact ⟨h, member, owner, .inr built⟩

open Ix.Kernel (ExPost)

def PublicationOrigin (cenv : CompileEnv) (pub : Published) : Prop :=
  pub.views = #[] ∨ ∃ heads views, viewsOf cenv heads = .ok views ∧ pub.views = newMemoViews cenv views

theorem PublicationOrigin.entry_built {cenv pub} (origin : PublicationOrigin cenv pub)
    {key : Name} {view : BlockView} (member : (key, view) ∈ pub.views) :
    cenv.p3Views.get? key = none ∧ viewMemoable cenv key = true ∧ Built cenv key view := by
  rcases origin with empty | ⟨_, views, run, shape⟩
  · rw [empty] at member; simp at member
  · exact newMemoViews_built run (shape ▸ member)

private theorem post_bind_any {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {P : β → Prop}
    (next : ∀ a, ExPost (k a) P) : ExPost (x >>= k) P :=
  ExPost.post_bind.mpr (ExPost.of_forall next)

set_option hygiene false in
local macro "from_view_run" actual:term : tactic => `(tactic| (
  repeat' first
    | dsimp only
    | (with_reducible apply post_bind_any); intro _
    | (rw [ExPost.post_pure]; exact Or.inr ⟨_, _, $actual, rfl⟩)
    | exact ExPost.post_throw.mpr trivial
    | exact ExPost.post_error.mpr trivial
    | split))

/-- The clique publication is built at its INPUT snapshot, not an overlay. -/
theorem rewriteCliqueCanon_origin {cenv : CompileEnv} {sourceAll : Ix.Set Name} {name : Name}
    {ci next : Ix.ConstantInfo} {sources : Std.HashMap Nat Ix.Expr} {pub : Published}
    (run : rewriteCliqueCanon cenv sourceAll name ci = .ok (next, sources, pub)) :
    PublicationOrigin cenv pub := by
  have post : ExPost (rewriteCliqueCanon cenv sourceAll name ci) (fun r => PublicationOrigin cenv r.2.2) := by
    unfold rewriteCliqueCanon
    split
    · exact ExPost.post_pure.mpr (Or.inl rfl)
    · dsimp only
      split
      · exact ExPost.post_pure.mpr (Or.inl rfl)
      · rw [ExPost.post_bind]
        intro views read
        have actual := Ix.Cert.Claims.mapError_ok read
        from_view_run actual
  exact post _ run

set_option hygiene false in
local macro "collect_view_publication" : tactic => `(tactic| (
  with_reducible apply post_bind_any
  intro collection
  try dsimp only
  split
  · exact ExPost.post_pure.mpr (Or.inl rfl)
  · rw [ExPost.post_bind]
    intro views read
    have actual := Ix.Cert.Claims.mapError_ok read
    from_view_run actual))

/-- Hook2's returned overlay is not substituted for its actual build input. -/
theorem prepareBlock_origin {cenv next : CompileEnv} {all : Ix.Set Name} {lo : Name} {pub : Published}
    (run : prepareBlock cenv all lo = .ok (next, pub)) : PublicationOrigin cenv pub := by
  have post : ExPost (prepareBlock cenv all lo) (fun r => PublicationOrigin cenv r.2) := by
    unfold prepareBlock
    split
    · exact ExPost.post_pure.mpr (Or.inl rfl)
    · try dsimp only
      split
      · try dsimp only
        split
        · exact ExPost.post_pure.mpr (Or.inl rfl)
        · collect_view_publication
      · collect_view_publication
  exact post _ run

/-- Successful image compilation publishes only the views from its actual
input-snapshot viewsOf call, regardless of its later compilation rounds. -/
theorem compileImageBlock_origin {cenv : CompileEnv} {all : Ix.Set Name}
    {out : Array (Name × BlockResult × BlockState)} {pub : Published}
    (run : compileImageBlock cenv all = .ok (out, pub)) : PublicationOrigin cenv pub := by
  have post : ExPost (compileImageBlock cenv all) (fun r => PublicationOrigin cenv r.2) := by
    unfold compileImageBlock
    with_reducible apply post_bind_any
    intro _
    rw [ExPost.post_bind]
    intro views actual
    from_view_run actual
  exact post _ run

/-- The live merge keeps an exact old value or admits an entry built at its
ACTUAL producer snapshot. The two environments are deliberately not equated. -/
theorem merge_publication_origin {producer : CompileEnv} {acc : DriverAcc} {lo : Name}
    {result : BlockResult} {cache : BlockState} {pub : Published}
    (origin : PublicationOrigin producer pub) {key : ExactName} {view : BlockView}
    (hit : (mergeCompiledBlock acc lo result cache pub).cenv.p3Views.get? key = some view) :
    acc.cenv.p3Views.get? key = some view ∨
      producer.p3Views.get? key = none ∧ viewMemoable producer key = true ∧ Built producer key view := by
  rw [mergeCompiledBlock_views] at hit
  rcases memoMerge_origin hit with old | added
  · exact .inl old
  · exact .inr (origin.entry_built added)

end Ix.CompileCert.ViewPublicationOrigin
