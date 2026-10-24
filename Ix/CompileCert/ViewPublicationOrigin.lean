import Ix.CompileCert.OptShapeOrigin

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

end Ix.CompileCert.ViewPublicationOrigin
