import Aiur.Generic.ControlPatternFacts

namespace Aiur.Generic.ControlLower
open SourceSemantics
set_option linter.unusedSimpArgs false
variable {F : Type} {source target bs : Environment F Nat} {env bound : Renaming}

theorem lookup_mem {pairs : List (String × A)} (found : pairs.lookup name = some value) :
    (name, value) ∈ pairs := by
  obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem lookup_some {pairs : List (String × A)} (member : name ∈ pairs.map Prod.fst) :
    ∃ value, pairs.lookup name = some value := by
  have present : (pairs.lookup name).isSome := by
    obtain ⟨pair, hp, he⟩ := List.mem_map.mp member
    exact List.lookup_isSome_iff.mpr ⟨pair, hp, by simp [he]⟩
  cases h : pairs.lookup name with
  | none => simp [h] at present
  | some v => exact ⟨v, rfl⟩

theorem lookup_none {pairs : List (String × A)} (absent : name ∉ pairs.map Prod.fst) :
    pairs.lookup name = none := by
  cases found : pairs.lookup name with
  | none => rfl
  | some value => exact (absent (List.mem_map.mpr ⟨_, lookup_mem found, rfl⟩)).elim

theorem find_lookup (locals : Environment F Nat) (name : String) :
    locals.find? (·.1 == name) = (locals.lookup name).map (fun value => (name, value)) := by
  induction locals with
  | nil => rfl
  | cons pair locals ih =>
      rcases pair with ⟨key, value⟩
      by_cases same : name = key
      · subst key; simp
      · simp [List.find?_cons, List.lookup_cons, beq_eq_false_iff_ne.mpr same,
          beq_eq_false_iff_ne.mpr (Ne.symm same), ih]

theorem find_lookup_some (locals : Environment F Nat) (name : String) (value : SourceValue F) :
    locals.find? (·.1 == name) = some (name, value) ↔ locals.lookup name = some value := by
  rw [find_lookup]
  cases locals.lookup name <;> simp

/-- The source scope and generated scope agree under the current renaming.
Dead outer bindings need not be removed from either environment. -/
def ScopeRel (env : Renaming) (source target : Environment F Nat) : Prop :=
  ∀ name renamed, env.lookup name = some renamed → target.lookup renamed = source.lookup name

theorem ScopeRel.add (rel : ScopeRel env source target)
    (fresh : name ∉ env.map Prod.snd) (value : SourceValue F) :
    ScopeRel env source ((name, value) :: target) := by
  intro n renamed found
  have member : renamed ∈ env.map Prod.snd := List.mem_map.mpr ⟨_, lookup_mem found, rfl⟩
  have different : renamed ≠ name := fun same => fresh (same ▸ member)
  simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr different] using rel n renamed found

theorem ScopeRel.identity (names : List String) (locals : Environment F Nat) :
    ScopeRel (names.map fun name => (name, name)) locals locals := by
  intro name renamed found
  obtain ⟨n, _, eq⟩ := List.mem_map.mp (lookup_mem found)
  have same : name = renamed := by cases eq; rfl
  subst renamed
  rfl

theorem rename_found (found : env.lookup name = some value) : rename env name = value := by
  simp only [rename, found, Option.getD_some]

theorem rename_injective (unique : (env.map Prod.snd).Nodup)
    (left : name ∈ env.map Prod.fst) (right : other ∈ env.map Prod.fst) :
    rename env name = rename env other ↔ name = other := by
  constructor
  · intro same
    obtain ⟨x, hx⟩ := lookup_some left
    obtain ⟨y, hy⟩ := lookup_some right
    rw [rename_found hx, rename_found hy] at same
    have pair := List.inj_on_of_nodup_map unique (lookup_mem hx) (lookup_mem hy) same
    exact congrArg Prod.fst pair
  · intro same; cases same; rfl

theorem renameBindings_lookup (unique : (env.map Prod.snd).Nodup)
    (covered : ∀ n ∈ bs.map Prod.fst, n ∈ env.map Prod.fst)
    (found : env.lookup name = some renamed) :
    (renameBindings env bs).lookup renamed = bs.lookup name := by
  have named : name ∈ env.map Prod.fst := List.mem_map.mpr ⟨_, lookup_mem found, rfl⟩
  induction bs with
  | nil => rfl
  | cons pair bs ih =>
      rcases pair with ⟨key, value⟩
      have keyMember := covered key (by simp)
      have eq : renamed = rename env key ↔ name = key := by
        rw [← rename_found found]
        exact rename_injective unique named keyMember
      simp only [renameBindings, List.map_cons, List.lookup_cons]
      by_cases same : name = key
      · simp [same, eq.mpr same]
      · have ne : renamed ≠ rename env key := fun h => same (eq.mp h)
        simp only [beq_eq_false_iff_ne.mpr ne, beq_eq_false_iff_ne.mpr same]
        exact ih (fun n hn => covered n (by simp [hn]))

theorem renameBindings_names (covered : ∀ n ∈ bs.map Prod.fst, n ∈ env.map Prod.fst) :
    ∀ n ∈ (renameBindings env bs).map Prod.fst, n ∈ env.map Prod.snd := by
  intro n member
  simp only [renameBindings, List.map_map, List.mem_map] at member
  obtain ⟨⟨key, value⟩, member, rfl⟩ := member
  obtain ⟨renamed, found⟩ := lookup_some (covered key (List.mem_map.mpr ⟨_, member, rfl⟩))
  change rename env key ∈ env.map Prod.snd
  rw [rename_found found]
  exact List.mem_map.mpr ⟨_, lookup_mem found, rfl⟩

theorem ScopeRel.extend (rel : ScopeRel env source target)
    (unique : (bound.map Prod.snd).Nodup)
    (keys : ∀ n, n ∈ bound.map Prod.fst ↔ n ∈ bs.map Prod.fst)
    (fresh : ∀ n ∈ bound.map Prod.snd, n ∉ env.map Prod.snd) :
    ScopeRel (bound ++ env) (bs ++ source) (renameBindings bound bs ++ target) := by
  have covered := fun n hn => (keys n).mpr hn
  intro name renamed found
  simp only [List.lookup_append] at found ⊢
  cases binding : bound.lookup name with
  | some renamed' =>
      have same : renamed' = renamed := by simpa [binding] using found
      subst renamed'
      obtain ⟨value, valueFound⟩ := lookup_some ((keys name).mp
        (List.mem_map.mpr ⟨_, lookup_mem binding, rfl⟩))
      rw [renameBindings_lookup unique covered binding, valueFound]
      rfl
  | none =>
      have old : env.lookup name = some renamed := by simpa [binding] using found
      have absent : bs.lookup name = none := lookup_none (by
        intro member
        obtain ⟨v, hv⟩ := lookup_some ((keys name).mpr member)
        simp [binding] at hv)
      have targetAbsent : (renameBindings bound bs).lookup renamed = none := lookup_none (by
        intro member
        exact fresh _ (renameBindings_names covered _ member)
          (List.mem_map.mpr ⟨_, lookup_mem old, rfl⟩))
      rw [absent, targetAbsent]
      exact rel name renamed old

theorem fresh_ok (built : fresh used = .ok name) : name ∉ used := by
  simp only [fresh] at built
  split at built
  · cases built
  · obtain rfl := Except.ok.inj built
    assumption

theorem bindings_ok (built : bindings pat used = .ok bound) :
    Consts.dependencies pat = [] ∧ (bound.map Prod.snd).Nodup ∧
      (∀ n, n ∈ bound.map Prod.fst ↔ n ∈ pat.bindingNames) ∧
      (∀ n ∈ bound.map Prod.snd, n ∉ used) := by
  simp only [bindings] at built
  split at built
  · cases built
  · rename_i plain
    split at built
    · cases built
    · rename_i unique
      split at built
      · cases built
      · rename_i fresh
        obtain rfl := Except.ok.inj built
        refine ⟨by simpa using plain, by simpa using unique, ?_, ?_⟩
        · intro n
          simp only [List.map_map, Function.comp_def]
          rw [show (fun x : String × Nat => (x.1, PatternLowering.freshPrefix used ++ "control:" ++ toString x.2).1) = Prod.fst from rfl,
            List.zipIdx_map_fst]
          simp
        · have good : ∀ x ∈ pat.bindingNames.eraseDups.zipIdx,
              PatternLowering.freshPrefix used ++ "control:" ++ toString x.2 ∉ used := by simpa using fresh
          intro n member
          obtain ⟨pair, hPair, equal⟩ := List.mem_map.mp member
          obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hPair
          subst n
          exact good original hOriginal

end Aiur.Generic.ControlLower
