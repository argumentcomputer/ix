import Ix.CompileCert.Canon.SccMain
import Ix.CompileCert.Canon.Cache

/-!
# M7 L1, components over names: `sccsOf`

`Ix.Compile.Canon.sccsOf names refs` numbers the names by position (a `HashMap` under
`Ix.Name`'s `==`), turns `refs` into successor lists of positions (`HashSet.toArray`, the
positions of the referenced names that are nodes, `qsort`ed), runs `tarjan`, and reads the
components back as names. With the names pairwise distinct under `==` (`NodupB`, as the
compiler's node lists are), its components are the strongly connected components of the
name graph `NEdge` (an edge from node `a` to node `b` when `refs a` contains `b`):
`sccsOf_scc`, `sccsOf_cover`, `sccsOf_range`, `sccsOf_unique`.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name)

/-! ## Reachability along a relation -/

/-- The reflexive transitive closure of a relation on nodes. -/
inductive RelReach (R : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (u : Nat) : RelReach R u u
  | tail {u v w : Nat} : RelReach R u v → R v w → RelReach R u w

theorem reach_iff_relReach {G : Array (Array Nat)} {R : Nat → Nat → Prop}
    (h : ∀ u w, Edge G u w ↔ R u w) {u v : Nat} : Reach G u v ↔ RelReach R u v := by
  constructor
  · intro r; induction r with
    | refl => exact .refl _
    | tail _ e ih => exact .tail ih ((h _ _).1 e)
  · intro r; induction r with
    | refl => exact .refl _
    | tail _ e ih => exact .tail ih ((h _ _).2 e)

/-! ## The position index -/

/-- The names are pairwise distinct under `==`. -/
def NodupB (names : Array Name) : Prop :=
  ∀ (i j : Nat) (hi : i < names.size) (hj : j < names.size), (names[i] == names[j]) = true → i = j

/-- Inserting pairs with pairwise distinct keys: a key is found at its pair's value. -/
theorem foldl_insert_getElem? :
    ∀ (L : List (Name × Nat)) (m0 : Std.HashMap Name Nat),
      (L.map (·.1)).Pairwise (fun a b => (a == b) = false) → ∀ (x : Name) (i : Nat),
      (L.foldl (fun m p => m.insert p.1 p.2) m0)[x]? = some i ↔
        (∃ p ∈ L, (p.1 == x) = true ∧ p.2 = i) ∨ ((∀ p ∈ L, (p.1 == x) = false) ∧ m0[x]? = some i) := by
  intro L
  induction L with
  | nil =>
    intro m0 _ x i
    simp only [List.foldl_nil]
    constructor
    · intro h; exact .inr ⟨fun p hp => absurd hp List.not_mem_nil, h⟩
    · rintro (⟨p, hp, -⟩ | ⟨-, h⟩)
      · exact absurd hp List.not_mem_nil
      · exact h
  | cons p L ih =>
    intro m0 hd x i
    simp only [List.map_cons, List.pairwise_cons] at hd
    simp only [List.foldl_cons]
    rw [ih _ hd.2 x i, Std.HashMap.getElem?_insert]
    by_cases hp : (p.1 == x) = true
    · simp only [hp, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨-, h⟩)
        · -- `q` and `p` would be two keys `==` to `x`
          exfalso
          have := hd.1 q.1 (List.mem_map_of_mem hq)
          rw [BEq.trans hp (BEq.symm hqx)] at this; cases this
        · exact .inl ⟨p, by simp, hp, h⟩
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, -⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · have hall : ∀ q' ∈ L, (q'.1 == x) = false := fun q' hq' => by
              have := hd.1 q'.1 (List.mem_map_of_mem hq')
              cases hb : (q'.1 == x)
              · rfl
              · rw [BEq.trans hp (BEq.symm hb)] at this; cases this
            exact .inr ⟨hall, rfl⟩
          · exact .inl ⟨q, hq, hqx, rfl⟩
        · have := h p (by simp); rw [hp] at this; cases this
    · have hp' : (p.1 == x) = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · exact .inl ⟨q, List.mem_cons_of_mem _ hq, hqx, rfl⟩
        · refine .inr ⟨fun q hq => ?_, h'⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp'
          · exact h q hq
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · rw [hp'] at hqx; cases hqx
          · exact .inl ⟨q, hq, hqx, rfl⟩
        · exact .inr ⟨fun q hq => h q (List.mem_cons_of_mem _ hq), h'⟩

/-- The position index `sccsOf` builds. -/
def nameIdx (names : Array Name) : Std.HashMap Name Nat :=
  names.zipIdx.foldl (init := {}) fun m (nm, i) => m.insert nm i

theorem nameIdx_spec {names : Array Name} (hnd : NodupB names) (x : Name) (i : Nat) :
    (nameIdx names)[x]? = some i ↔ ∃ h : i < names.size, (names[i] == x) = true := by
  have e : nameIdx names =
      (names.toList.zipIdx).foldl (fun m p => m.insert p.1 p.2) ({} : Std.HashMap Name Nat) := by
    unfold nameIdx
    rw [← Array.foldl_toList, Array.toList_zipIdx]
  have hd : ((names.toList.zipIdx).map (·.1)).Pairwise (fun a b => (a == b) = false) := by
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.length_map, List.length_zipIdx, Array.length_toList] at ha hb
    simp only [List.getElem_map, List.getElem_zipIdx, Array.getElem_toList]
    cases h : (names[a] == names[b])
    · rfl
    · have := hnd a b ha hb h; omega
  rw [e, foldl_insert_getElem? _ _ hd x i]
  simp only [Std.HashMap.getElem?_empty, reduceCtorEq, and_false, or_false]
  constructor
  · rintro ⟨⟨nm, k⟩, hp, hx, rfl⟩
    have hg := List.mem_zipIdx_iff_getElem?.1 hp
    simp only [Array.getElem?_toList] at hg
    have hk : k < names.size := by
      rcases Nat.lt_or_ge k names.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hg; cases hg
    rw [Array.getElem?_eq_getElem hk] at hg
    simp only [Option.some.injEq] at hg
    exact ⟨hk, by rw [hg]; exact hx⟩
  · rintro ⟨hi, hx⟩
    exact ⟨(names[i], i), List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hi), hx, rfl⟩

/-! ## The successor lists -/

/-- The successor lists `sccsOf` builds. -/
def adjOf (names : Array Name) (refs : Name → Std.HashSet Name) : Array (Array Nat) :=
  names.map fun nm => ((refs nm).toArray.filterMap (nameIdx names).get?).qsort (· < ·)

/-- The name graph: an edge from node `a` to node `b` when `refs a` contains `b`. -/
def NEdge (names : Array Name) (refs : Name → Std.HashSet Name) (i j : Nat) : Prop :=
  ∃ a b, names[i]? = some a ∧ names[j]? = some b ∧ (refs a).contains b = true

theorem edge_adjOf {names : Array Name} (hnd : NodupB names) (refs : Name → Std.HashSet Name)
    (i j : Nat) : Edge (filt (adjOf names refs)) i j ↔ NEdge names refs i j := by
  rw [edge_filt]
  simp only [adjOf, Array.size_map, Array.getElem?_map, NEdge]
  cases hi : names[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    constructor
    · rintro ⟨h, -⟩; exact absurd h (Array.not_mem_empty _)
    · rintro ⟨a, b, h, -⟩; cases h
  | some a =>
    simp only [Option.map_some, Option.getD_some, mem_qsort, Array.mem_filterMap,
      Std.HashMap.get?_eq_getElem?, nameIdx_spec hnd]
    constructor
    · rintro ⟨⟨y, hy, hj, hjy⟩, -⟩
      refine ⟨a, names[j], rfl, Array.getElem?_eq_getElem hj, ?_⟩
      rw [Std.HashSet.contains_congr hjy]
      exact Std.HashSet.contains_of_mem_toArray hy
    · rintro ⟨a', b, ha', hb, hc⟩
      simp only [Option.some.injEq] at ha'
      subst ha'
      have hj : j < names.size := by
        rcases Nat.lt_or_ge j names.size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hb; cases hb
      have hbj : names[j] = b := by rw [Array.getElem?_eq_getElem hj] at hb; cases hb; rfl
      have hcon : (refs a).toArray.contains b = true := by rw [Std.HashSet.contains_toArray]; exact hc
      rw [Array.contains_iff_exists_mem_beq] at hcon
      obtain ⟨y, hy, hby⟩ := hcon
      exact ⟨⟨y, hy, hj, by rw [hbj]; exact hby⟩, hj⟩

/-! ## Reading the components back as names -/

theorem list_mapM_option_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ y, y ∈ l' ↔ ∃ x ∈ l, f x = some y := by
  intro l
  induction l with
  | nil => intro l' h y; simp at h; subst h; simp
  | cons a as ih =>
    intro l' h y
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      cases hs : as.mapM f with
      | none => rw [ha, hs] at h; cases h
      | some bs =>
        rw [ha, hs] at h
        simp only [Option.bind_some, Option.some.injEq, bind, pure] at h
        subst h
        rw [List.mem_cons, ih bs hs y]
        constructor
        · rintro (rfl | ⟨x, hx, hfx⟩)
          · exact ⟨a, by simp, ha⟩
          · exact ⟨x, by simp [hx], hfx⟩
        · rintro ⟨x, hx, hfx⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · rw [ha] at hfx; cases hfx; exact .inl rfl
          · exact .inr ⟨x, hx, hfx⟩

theorem array_mapM_option_mem {α β : Type} (f : α → Option β) (xs : Array α) (ys : Array β)
    (h : xs.mapM f = some ys) (y : β) : y ∈ ys ↔ ∃ x ∈ xs, f x = some y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h
    simp only [Functor.map, Option.map_some, Option.some.injEq] at h
    subst h
    rw [List.mem_toArray, list_mapM_option_mem f _ l' hl y]
    simp

theorem sccsOf_eq (names : Array Name) (refs : Name → Std.HashSet Name) :
    sccsOf names refs =
      (tarjan (adjOf names refs)).bind fun comps => comps.mapM fun c => c.mapM (names[·]?) := rfl

section
variable {names : Array Name} {refs : Name → Std.HashSet Name} {cs : Array (Array Name)}
  (hnd : NodupB names) (h : sccsOf names refs = some cs)
include hnd h

omit hnd in
/-- The condensation behind `sccsOf`, and how its components read as names. -/
theorem sccsOf_condensation : ∃ C, condensation (adjOf names refs) = some C ∧
    ∀ c, c ∈ cs ↔ ∃ c0 ∈ C.comps, c0.mapM (names[·]?) = some c := by
  rw [sccsOf_eq] at h
  cases ht : tarjan (adjOf names refs) with
  | none => rw [ht] at h; cases h
  | some comps =>
    rw [ht] at h
    simp only [Option.bind_some] at h
    unfold tarjan at ht
    cases hc : condensation (adjOf names refs) with
    | none => rw [hc] at ht; cases ht
    | some C =>
      rw [hc] at ht; simp only [Option.map_some, Option.some.injEq] at ht
      subst ht
      exact ⟨C, rfl, fun c => array_mapM_option_mem _ _ _ h c⟩

omit hnd h in
theorem mem_comp_names {c0 : Array Nat} {c : Array Name} (hm : c0.mapM (names[·]?) = some c)
    (x : Name) : x ∈ c ↔ ∃ j ∈ c0, names[j]? = some x :=
  array_mapM_option_mem _ _ _ hm x

omit h in
theorem names_eq_of {j j' : Nat} {x : Name} (h1 : names[j]? = some x) (h2 : names[j']? = some x) :
    j = j' := by
  have hj : j < names.size := by
    rcases Nat.lt_or_ge j names.size with hh | hh
    · exact hh
    · rw [Array.getElem?_eq_none hh] at h1; cases h1
  have hj' : j' < names.size := by
    rcases Nat.lt_or_ge j' names.size with hh | hh
    · exact hh
    · rw [Array.getElem?_eq_none hh] at h2; cases h2
  rw [Array.getElem?_eq_getElem hj] at h1; rw [Array.getElem?_eq_getElem hj'] at h2
  simp only [Option.some.injEq] at h1 h2
  exact hnd j j' hj hj' (by rw [h1, h2]; exact name_beq_refl x)

omit hnd in
/-- Every name is in a component. -/
theorem sccsOf_cover : ∀ a ∈ names, ∃ c ∈ cs, a ∈ c := by
  obtain ⟨C, hC, hcs⟩ := sccsOf_condensation h
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ha
  obtain ⟨c0, hc0, hic⟩ := condensation_cover hC i (by simpa [adjOf] using hi)
  have hr := condensation_range hC c0 hc0
  -- every index of a component reads back as a name
  have hm : ∃ c, c0.mapM (names[·]?) = some c := by
    rw [Array.mapM_eq_mapM_toList]
    have : ∀ l : List Nat, (∀ j ∈ l, j < names.size) → ∃ l', l.mapM (names[·]?) = some l' := by
      intro l hl
      induction l with
      | nil => exact ⟨[], rfl⟩
      | cons j js ih =>
        obtain ⟨l', hl'⟩ := ih fun j' hj' => hl j' (by simp [hj'])
        have hj := hl j (by simp)
        exact ⟨names[j] :: l', by rw [List.mapM_cons, Array.getElem?_eq_getElem hj, hl']; rfl⟩
    obtain ⟨l', hl'⟩ := this c0.toList fun j hj => by
      have := hr j (by simpa using hj); simpa [adjOf] using this
    exact ⟨l'.toArray, by rw [hl']; rfl⟩
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, (hcs c).2 ⟨c0, hc0, hc⟩, (mem_comp_names hc _).2 ⟨i, hic, Array.getElem?_eq_getElem hi⟩⟩

omit hnd in
/-- Components hold only the names. -/
theorem sccsOf_range : ∀ c ∈ cs, ∀ x ∈ c, x ∈ names := by
  obtain ⟨C, hC, hcs⟩ := sccsOf_condensation h
  intro c hc x hx
  obtain ⟨c0, hc0, hm⟩ := (hcs c).1 hc
  obtain ⟨j, -, hj⟩ := (mem_comp_names hm x).1 hx
  exact Array.mem_of_getElem? hj

/-- No name is in two components. -/
theorem sccsOf_unique : ∀ c ∈ cs, ∀ c' ∈ cs, ∀ x, x ∈ c → x ∈ c' → c = c' := by
  obtain ⟨C, hC, hcs⟩ := sccsOf_condensation h
  intro c hc c' hc' x hx hx'
  obtain ⟨c0, hc0, hm⟩ := (hcs c).1 hc
  obtain ⟨c0', hc0', hm'⟩ := (hcs c').1 hc'
  obtain ⟨j, hj, hjx⟩ := (mem_comp_names hm x).1 hx
  obtain ⟨j', hj', hjx'⟩ := (mem_comp_names hm' x).1 hx'
  have := names_eq_of hnd hjx hjx'
  subst this
  obtain ⟨k, hk⟩ := Array.getElem?_of_mem hc0
  obtain ⟨k', hk'⟩ := Array.getElem?_of_mem hc0'
  have := condensation_unique hC k k' c0 c0' j hk hk' hj hj'
  subst this
  rw [hk] at hk'; cases hk'
  rw [hm] at hm'; cases hm'; rfl

/-- **`sccsOf` returns the strongly connected components of the name graph.** -/
theorem sccsOf_scc (i j : Nat) (hi : i < names.size) (hj : j < names.size) :
    (∃ c ∈ cs, names[i] ∈ c ∧ names[j] ∈ c) ↔
      RelReach (NEdge names refs) i j ∧ RelReach (NEdge names refs) j i := by
  obtain ⟨C, hC, hcs⟩ := sccsOf_condensation h
  have hR : ∀ u v, Reach (filt (adjOf names refs)) u v ↔ RelReach (NEdge names refs) u v :=
    fun u v => reach_iff_relReach (edge_adjOf hnd refs)
  have hn : (adjOf names refs).size = names.size := by simp [adjOf]
  have key := condensation_scc hC i j
  rw [hn] at key
  have key' : (∃ c ∈ C.comps, i ∈ c ∧ j ∈ c) ↔
      Reach (filt (adjOf names refs)) i j ∧ Reach (filt (adjOf names refs)) j i := by
    rw [key]; simp [hi, hj]
  rw [← hR, ← hR, ← key']
  constructor
  · rintro ⟨c, hc, hic, hjc⟩
    obtain ⟨c0, hc0, hm⟩ := (hcs c).1 hc
    obtain ⟨i', hi', hix⟩ := (mem_comp_names hm _).1 hic
    obtain ⟨j', hj', hjx⟩ := (mem_comp_names hm _).1 hjc
    have := names_eq_of hnd hix (j' := i) (Array.getElem?_eq_getElem hi); subst this
    have := names_eq_of hnd hjx (j' := j) (Array.getElem?_eq_getElem hj); subst this
    exact ⟨c0, hc0, hi', hj'⟩
  · rintro ⟨c0, hc0, hic, hjc⟩
    obtain ⟨c, hc⟩ : ∃ c, c0.mapM (names[·]?) = some c := by
      obtain ⟨c', hc', hic'⟩ := sccsOf_cover h names[i] (Array.getElem_mem hi)
      obtain ⟨c0', hc0', hm'⟩ := (hcs c').1 hc'
      obtain ⟨i', hi', hix⟩ := (mem_comp_names hm' _).1 hic'
      have := names_eq_of hnd hix (j' := i) (Array.getElem?_eq_getElem hi); subst i'
      obtain ⟨k, hk⟩ := Array.getElem?_of_mem hc0
      obtain ⟨k', hk'⟩ := Array.getElem?_of_mem hc0'
      have := condensation_unique hC k k' c0 c0' i hk hk' hic hi'
      subst this; rw [hk] at hk'; cases hk'
      exact ⟨c', hm'⟩
    exact ⟨c, (hcs c).2 ⟨c0, hc0, hc⟩, (mem_comp_names hc _).2 ⟨i, hic, Array.getElem?_eq_getElem hi⟩,
      (mem_comp_names hc _).2 ⟨j, hjc, Array.getElem?_eq_getElem hj⟩⟩

end

end Ix.CompileCert.Canon
