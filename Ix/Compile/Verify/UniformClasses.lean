import Ix.Compile.Verify.UniformGain

/-!
# Stage 3: the certain classes

* **Slots.** In any writing, the inline occurrences of `t` plus its Shares
  are the top (if it is `t`) plus one per edge from a written node into `t`
  (`slots_edges`); the inline occurrences are the writes of `t`
  (`count_written`). Summed over an encoding: `writes t + refs t = root
  occurrences + [t stored] + Σ_y writes y · edges(y, t)`.
* **Visible counts.** Hence every encoding of a set `S ⊆ M` writes each
  `t ∉ S` at least `visibleCounts … M` times, at least the head count at head
  positions.
* **Certain-stored**, generalised to partial assignments: for any
  maybe-stored set `M ⊇ S` and `t ∉ S`, the gain under `uniformBounds … M`
  and the visible counts of `M` bounds the length drop of adding `t`, up to
  the growth of the count's `Tag0`; so a gain `≥ θ` puts `t` in every
  minimum (over any class containing `S ∪ {t}`) that lies in `M`.
* **Certain-excluded**: the removal exchange and `refs ≤ occ` in a minimum
  without unreferenced entries.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact

/-! ## Slots of a writing -/

/-- All edges from `y` into `t`. -/
def edgeAll (p : Prep) (y t : Nat) : Nat := edgeMult p y t false + edgeMult p y t true

theorem count_singleton' (a b : Nat) : [a].count b = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, List.count_singleton]
    simp only [beq_iff_eq]
    split <;> omega

theorem sharess_count (t : Nat) (l : List WTree) :
    (WTree.sharess l).count t = (l.map fun T => T.shares.count t).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.sharess, List.count_append, ih]

theorem writtens_count (p : Prep) (t : Nat) (l : List WTree) :
    (WTree.writtens p l).count t = (l.map fun T => (T.written p).count t).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.writtens, List.count_append, ih]

theorem count_zero_of_lt {l : List Nat} {t : Nat} (h : ∀ y ∈ l, y < t) : l.count t = 0 := by
  rw [List.count_eq_zero]
  intro ht
  have := h t ht
  omega

/-- Every written node of a writing of `x` is at most `x`. -/
theorem PrepWF.written_le {p : Prep} (hp : PrepWF p) {S : Nat → Bool} :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size → ∀ y ∈ T.written p, y ≤ x := by
  intro x T h
  induction h with
  | share _ => intro _ y hy; simp [WTree.written] at hy
  | @node x kids hf hlen _ ih =>
    intro hx y hy
    simp only [WTree.written] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_refl _
    · obtain ⟨T, hT, hyT⟩ := writtens_mem hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hc := hp.dag.childAt_lt hx (k := i) (by omega)
      have := ih i hi (by omega) y hyT
      omega
  | @teleCut x j sides hf hj1 hj hlen _ _ ih =>
    intro hx y hy
    simp only [WTree.written, List.append_nil, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      exact hp.spineAt_le hx hf (by rw [List.mem_range] at hk; omega)
    · obtain ⟨T, hT, hyT⟩ := writtens_mem hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      have := ih i hi (by omega) y hyT
      omega
  | @teleFull x sides tail hf hlen _ _ ih iht =>
    intro hx y hy
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    simp only [WTree.written, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      exact hp.spineAt_le hx hf (by rw [List.mem_range] at hk; omega)
    · obtain ⟨T, hT, hyT⟩ := writtens_mem hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      have := ih i hi (by omega) y hyT
      omega
    · have := iht (by omega) y hy
      omega

theorem PrepWF.spineHit_self {p : Prep} (hp : PrepWF p) {x j : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!) : spineHit p x j x = none := by
  cases hs : spineHit p x j x with
  | none => rfl
  | some k =>
    obtain ⟨hk1, hkj, hk⟩ := spineHit_spec hs
    have := hp.spineAt_strict hx hf (a := 0) (b := k) (by omega) (by omega)
    rw [hk] at this
    exact absurd this (Nat.lt_irrefl _)

/-- The spine prefix of length `j` writes `t` once if `t` is its top or one of
its inner nodes. -/
theorem PrepWF.spine_count {p : Prep} (hp : PrepWF p) {x j t : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!) (hj1 : 1 ≤ j) :
    ((List.range j).map (spineAt p x)).count t =
      (if x = t then 1 else 0) + (if (spineHit p x j t).isSome then 1 else 0) := by
  have huniq : ∀ a b, a < j → b < j → spineAt p x a = t → spineAt p x b = t → a = b := by
    intro a b ha hb hPa hPb
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · have := hp.spineAt_strict hx hf hab (by omega); omega
    · exact hab
    · have := hp.spineAt_strict hx hf hab (by omega); omega
  rw [List.count_eq_length_filter, filter_length_eq_sum, List.map_map]
  have hfun : ((fun i => if (i == t) = true then 1 else 0) ∘ spineAt p x) =
      fun k => if spineAt p x k = t then 1 else 0 := by
    funext k; simp [Function.comp_def]
  rw [hfun, sum_indicator_unique (fun k => spineAt p x k = t) j huniq]
  by_cases hxt : x = t
  · subst hxt
    have hnone : (spineHit p x j x).isSome = false := by
      cases hs : (spineHit p x j x).isSome
      · rfl
      · obtain ⟨k, hk1, hkj, hk⟩ := spineHit_isSome_iff.mp hs
        have := hp.spineAt_strict hx hf (a := 0) (b := k) (by omega) (by omega)
        rw [hk] at this
        exact absurd this (Nat.lt_irrefl _)
    rw [if_pos ⟨0, by omega, rfl⟩, if_pos rfl, hnone]
    rfl
  · rw [if_neg hxt, Nat.zero_add]
    congr 1
    apply propext
    rw [spineHit_isSome_iff]
    constructor
    · rintro ⟨k, hk, hkt⟩
      refine ⟨k, ?_, hk, hkt⟩
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; exact absurd hkt hxt
      · exact h0
    · rintro ⟨k, _, hk, hkt⟩
      exact ⟨k, hk, hkt⟩

/-- The writes of `t` in a writing are its inline occurrences. -/
theorem PrepWF.count_written {p : Prep} (hp : PrepWF p) {S : Nat → Bool} (t : Nat) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      (T.written p).count t = T.occH t + T.occC p t := by
  intro x T h
  induction h with
  | share _ => intro _; simp [WTree.written, WTree.occH, WTree.occC]
  | @node x kids hf hlen hkids ih =>
    intro hx
    by_cases hxt : x = t
    · subst hxt
      have hle := hp.written_le (.node hf hlen hkids) hx
      simp only [WTree.written, List.count_cons, WTree.occH, WTree.occC, if_true, beq_self_eq_true]
      have : (WTree.writtens p kids).count x = 0 := by
        apply count_zero_of_lt
        intro y hy
        obtain ⟨T, hT, hyT⟩ := writtens_mem hy
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        have hc := hp.dag.childAt_lt hx (k := i) (by omega)
        have := hp.written_le (hkids i hi) (by omega) y hyT
        omega
      simp [this]
    · simp only [WTree.written, List.count_cons, WTree.occH, WTree.occC, hxt, if_false,
        occHs_eq, occCs_eq, writtens_count, beq_iff_eq]
      rw [Nat.add_zero, ← sum_map_add']
      apply congrArg
      apply List.map_congr_left
      intro T hT
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hc := hp.dag.childAt_lt hx (k := i) (by omega)
      exact ih i hi (by omega)
  | @teleCut x j sides hf hj1 hj hlen hsides hS ih =>
    intro hx
    have hside : ∀ T ∈ sides, (T.written p).count t = T.occH t + T.occC p t ∧
        ∀ y ∈ T.written p, y < x := by
      intro T hT
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      exact ⟨ih i hi (by omega), fun y hy => by
        have := hp.written_le (hsides i hi) (by omega) y hy; omega⟩
    have hspine := hp.spine_count (t := t) hx hf (Nat.le_of_lt hj) hj1
    simp only [WTree.written, List.append_nil, List.count_append, hspine, writtens_count]
    by_cases hxt : x = t
    · subst hxt
      have hs0 : (sides.map fun T => (T.written p).count x).sum = 0 :=
        sum_map_eq_zero fun T hT => count_zero_of_lt (hside T hT).2
      rw [hs0]
      simp [WTree.occH, WTree.occC, hp.spineHit_self hx hf (Nat.le_of_lt hj)]
    · simp only [WTree.occH, WTree.occC, hxt, if_false, occHs_eq, occCs_eq, Nat.zero_add]
      rw [List.map_congr_left (fun T hT => (hside T hT).1), sum_map_add']
      simp [WTree.occH, WTree.occC]
      omega
  | @teleFull x sides tail hf hlen hsides htail ih iht =>
    intro hx
    obtain ⟨hl1, _, _, htl, _⟩ := hp.spine x hx hf
    have hside : ∀ T ∈ sides, (T.written p).count t = T.occH t + T.occC p t ∧
        ∀ y ∈ T.written p, y < x := by
      intro T hT
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      exact ⟨ih i hi (by omega), fun y hy => by
        have := hp.written_le (hsides i hi) (by omega) y hy; omega⟩
    have hspine := hp.spine_count (t := t) hx hf (Nat.le_refl _) (by omega)
    have htl' := iht (by omega)
    simp only [WTree.written, List.count_append, hspine, writtens_count, htl']
    by_cases hxt : x = t
    · subst hxt
      have hs0 : (sides.map fun T => (T.written p).count x).sum = 0 :=
        sum_map_eq_zero fun T hT => count_zero_of_lt (hside T hT).2
      have ht0 : (tail.written p).count x = 0 := by
        apply count_zero_of_lt
        intro y hy
        have := hp.written_le htail (by omega) y hy
        omega
      rw [← htl', hs0, ht0]
      simp [WTree.occH, WTree.occC, hp.spineHit_self hx hf (Nat.le_refl _)]
    · simp only [WTree.occH, WTree.occC, hxt, if_false, occHs_eq, occCs_eq, Nat.zero_add]
      rw [List.map_congr_left (fun T hT => (hside T hT).1), sum_map_add']
      omega

/-- The term a writing writes (or shares). -/
def WTree.label : WTree → Nat
  | .share x => x
  | .node x _ => x
  | .tele x _ _ _ => x

theorem label_eq {p : Prep} {S : Nat → Bool} {x : Nat} {T : WTree} (h : Valid p S x T) :
    T.label = x := by
  cases h <;> rfl

theorem PrepWF.shares_count_zero {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {x : Nat}
    {T : WTree} (h : Valid p S x T) (hx : x < p.dag.size) (hns : T.isShare = false) (t : Nat)
    (hxt : x ≤ t) : T.shares.count t = 0 :=
  count_zero_of_lt fun s hs => by have := (hp.shares_lt h hx s hs).2.2 hns; omega

theorem PrepWF.edgeAll_zero {p : Prep} (hp : PrepWF p) {t : Nat} (l : List Nat)
    (hl : ∀ y ∈ l, y ≤ t) : (l.map fun y => edgeAll p y t).sum = 0 :=
  sum_map_eq_zero fun y hy => by
    unfold edgeAll
    rw [edgeMult_zero_of_le hp (hl y hy), edgeMult_zero_of_le hp (hl y hy)]

/-- The head edges of a telescope prefix of length `j < spineLen` into `t`
are its side edges. -/
theorem PrepWF.spine_head_sides {p : Prep} (hp : PrepWF p) {x j t : Nat} (hx : x < p.dag.size)
    (ht : t < p.dag.size) (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!) :
    ((List.range j).map fun k => edgeMult p (spineAt p x k) t false).sum =
      ((List.range j).map fun k => if sideAt p x k = t then 1 else 0).sum +
        (if j = p.spineLen[x]! ∧ p.tail[x]! = t then 1 else 0) := by
  have hk : ∀ k ∈ List.range j, spineAt p x k < p.dag.size ∧ p.family[spineAt p x k]! ≠ .none := by
    intro k hk
    rw [List.mem_range] at hk
    obtain ⟨hts, htf, _⟩ := hp.spine_shift hx hf (k := k) (by omega)
    exact ⟨hts, by rw [htf]; exact hf⟩
  rw [List.map_congr_left fun k hk1 => (hp.edgeMult_tele (hk k hk1).1 ht (hk k hk1).2).2]
  rw [sum_map_add', hp.spine_head_edges hx hf hj]
  rfl

/-- The continuation edges of a telescope prefix cut at its node `j`: one if
`t` is among the nodes `1 … j`. -/
theorem PrepWF.spine_cont_cut {p : Prep} (hp : PrepWF p) {x j t : Nat} (hx : x < p.dag.size)
    (ht : t < p.dag.size) (hf : p.family[x]! ≠ .none) (hj : j < p.spineLen[x]!)
    (hj1 : 1 ≤ j) :
    ((List.range j).map fun k => edgeMult p (spineAt p x k) t true).sum =
      (if (spineHit p x j t).isSome then 1 else 0) + (if spineAt p x j = t then 1 else 0) := by
  have hk : ∀ k, k ≤ j → spineAt p x k < p.dag.size ∧ p.family[spineAt p x k]! ≠ .none := by
    intro k hk
    obtain ⟨hts, htf, _⟩ := hp.spine_shift hx hf (k := k) (by omega)
    exact ⟨hts, by rw [htf]; exact hf⟩
  have hcont : ∀ m, m ≤ j →
      ((List.range m).map fun k => edgeMult p (spineAt p x k) t true).sum =
        ((List.range m).map fun k =>
          if snext p (spineAt p x k) = t ∧ p.family[t]! = p.family[spineAt p x k]! then 1
          else 0).sum := by
    intro m hm
    apply congrArg
    apply List.map_congr_left
    intro k hk1
    rw [List.mem_range] at hk1
    exact (hp.edgeMult_tele (hk k (by omega)).1 ht (hk k (by omega)).2).1
  by_cases hjt : spineAt p x j = t
  · -- the cut node is `t`: its continuation edge is the last one
    have hlt : ∀ k, 1 ≤ k → k < j → spineAt p x k ≠ t := by
      intro k hk1 hkj h
      have := hp.spineAt_strict hx hf (a := k) (b := j) hkj (by omega)
      omega
    have hnone : (spineHit p x j t).isSome = false := by
      cases hs : (spineHit p x j t).isSome
      · rfl
      · obtain ⟨k, hk1, hkj, hk⟩ := spineHit_isSome_iff.mp hs
        exact absurd hk (hlt k hk1 hkj)
    have h1 := hp.spine_cont_edges hx hf (j := j + 1) (t := t) (by omega) (by
      intro _ h
      have := hp.spineAt_strict hx hf (a := j) (b := j + 1) (by omega) (by omega)
      omega)
    have hsome : (spineHit p x (j + 1) t).isSome = true :=
      spineHit_isSome_iff.mpr ⟨j, by omega, by omega, hjt⟩
    rw [hsome, sum_range_succ'] at h1
    have hlast : (if snext p (spineAt p x j) = t ∧ p.family[t]! = p.family[spineAt p x j]! then 1
        else 0) = 0 := by
      rw [if_neg]
      rintro ⟨h, _⟩
      rw [snext_spineAt] at h
      have := hp.spineAt_strict hx hf (a := j) (b := j + 1) (by omega) (by omega)
      omega
    simp only [if_true] at h1
    rw [hlast] at h1
    rw [hcont j (Nat.le_refl _), hnone, if_pos hjt]
    simp only [Bool.false_eq_true, if_false]
    omega
  · rw [hcont j (Nat.le_refl _), hp.spine_cont_edges hx hf (Nat.le_of_lt hj) (fun _ => hjt),
      if_neg hjt, Nat.add_zero]

/-- **Slots.** In a writing of `x`, the inline occurrences of `t` plus its
Shares are the top (if `x = t`) plus one per edge from a written node into
`t`. -/
theorem PrepWF.slots_edges {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {t : Nat}
    (htn : t < p.dag.size) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      T.occH t + T.occC p t + T.shares.count t =
        (if x = t then 1 else 0) + ((T.written p).map fun y => edgeAll p y t).sum := by
  intro x T h
  induction h with
  | share _ =>
    intro _
    simp [WTree.occH, WTree.occC, WTree.shares, WTree.written, count_singleton']
  | @node x kids hf hlen hkids ih =>
    intro hx
    have hT : Valid p S x (.node x kids) := .node hf hlen hkids
    by_cases hxt : x = t
    · subst hxt
      rw [hp.shares_count_zero hT hx rfl x (Nat.le_refl _),
        hp.edgeAll_zero _ (hp.written_le hT hx)]
      simp [WTree.occH, WTree.occC]
    · have hper : ∀ T ∈ kids, T.occH t + T.occC p t + T.shares.count t =
          (if T.label = t then 1 else 0) + ((T.written p).map fun y => edgeAll p y t).sum := by
        intro T hT
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        have hc := hp.dag.childAt_lt hx (k := i) (by omega)
        rw [ih i hi (by omega), label_eq (hkids i hi)]
      have hind : (kids.map fun T => if T.label = t then 1 else 0).sum = edgeAll p x t := by
        unfold edgeAll
        rw [(hp.edgeMult_node hx hf t).1, (hp.edgeMult_node hx hf t).2, Nat.add_zero,
          filter_length_eq_sum, sum_map_eq_range, hlen]
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, label_eq (hkids i (by omega))]
        simp
      simp only [WTree.occH, WTree.occC, WTree.shares, WTree.written, hxt, if_false,
        occHs_eq, occCs_eq, sharess_count, List.map_cons, List.sum_cons, writtens_sum]
      have e := congrArg List.sum (List.map_congr_left hper)
      simp only [sum_map_add'] at e
      omega
  | @teleCut x j sides hf hj1 hj hlen hsides hS ih =>
    intro hx
    have hT : Valid p S x (.tele x j sides (.share (spineAt p x j))) :=
      .teleCut hf hj1 hj hlen hsides hS
    by_cases hxt : x = t
    · subst hxt
      rw [hp.shares_count_zero hT hx rfl x (Nat.le_refl _),
        hp.edgeAll_zero _ (hp.written_le hT hx)]
      simp [WTree.occH, WTree.occC]
    · have hper : ∀ T ∈ sides, T.occH t + T.occC p t + T.shares.count t =
          (if T.label = t then 1 else 0) + ((T.written p).map fun y => edgeAll p y t).sum := by
        intro T hT
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
        rw [ih i hi (by omega), label_eq (hsides i hi)]
      have hind : (sides.map fun T => if T.label = t then 1 else 0).sum =
          ((List.range j).map fun k => if sideAt p x k = t then 1 else 0).sum := by
        rw [sum_map_eq_range, hlen]
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, label_eq (hsides i (by omega))]
      have hH := hp.spine_head_sides hx htn hf (Nat.le_of_lt hj)
      have hC := hp.spine_cont_cut hx htn hf hj hj1
      have hne : ¬(j = p.spineLen[x]! ∧ p.tail[x]! = t) := fun h => by omega
      rw [if_neg hne] at hH
      have e := congrArg List.sum (List.map_congr_left hper)
      simp only [sum_map_add'] at e
      have hsplit : (((List.range j).map (spineAt p x)).map fun y => edgeAll p y t).sum =
          ((List.range j).map fun k => edgeMult p (spineAt p x k) t false).sum +
            ((List.range j).map fun k => edgeMult p (spineAt p x k) t true).sum := by
        rw [List.map_map, ← sum_map_add']
        rfl
      simp only [WTree.occH, WTree.occC, WTree.shares, WTree.written, hxt, if_false, occHs_eq,
        occCs_eq, sharess_count, List.count_append, count_singleton', writtens_sum,
        List.map_append, List.sum_append, List.append_nil, Nat.zero_add, Nat.add_zero]
      rw [hsplit, hH, hC]
      omega
  | @teleFull x sides tail hf hlen hsides htail ih iht =>
    intro hx
    obtain ⟨hl1, _, _, htl, _⟩ := hp.spine x hx hf
    have hT : Valid p S x (.tele x p.spineLen[x]! sides tail) := .teleFull hf hlen hsides htail
    by_cases hxt : x = t
    · subst hxt
      rw [hp.shares_count_zero hT hx rfl x (Nat.le_refl _),
        hp.edgeAll_zero _ (hp.written_le hT hx)]
      simp [WTree.occH, WTree.occC]
    · have hper : ∀ T ∈ sides, T.occH t + T.occC p t + T.shares.count t =
          (if T.label = t then 1 else 0) + ((T.written p).map fun y => edgeAll p y t).sum := by
        intro T hT
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
        rw [ih i hi (by omega), label_eq (hsides i hi)]
      have hind : (sides.map fun T => if T.label = t then 1 else 0).sum =
          ((List.range p.spineLen[x]!).map fun k => if sideAt p x k = t then 1 else 0).sum := by
        rw [sum_map_eq_range, hlen]
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, label_eq (hsides i (by omega))]
      have htl' := iht (by omega)
      have hH := hp.spine_head_sides hx htn hf (Nat.le_refl _)
      have hC := (hp.spine_edges hx htn hf (Nat.le_refl _) (fun h => absurd h (Nat.lt_irrefl _))).2
      simp only [List.map_map, Function.comp_def] at hC
      have hti : (if p.spineLen[x]! = p.spineLen[x]! ∧ p.tail[x]! = t then 1 else 0) =
          (if p.tail[x]! = t then 1 else 0) := by
        by_cases h : p.tail[x]! = t
        · rw [if_pos ⟨rfl, h⟩, if_pos h]
        · rw [if_neg (fun h' => h h'.2), if_neg h]
      rw [hti] at hH
      have e := congrArg List.sum (List.map_congr_left hper)
      simp only [sum_map_add'] at e
      have hsplit : (((List.range p.spineLen[x]!).map (spineAt p x)).map fun y => edgeAll p y t).sum =
          ((List.range p.spineLen[x]!).map fun k => edgeMult p (spineAt p x k) t false).sum +
            ((List.range p.spineLen[x]!).map fun k => edgeMult p (spineAt p x k) t true).sum := by
        rw [List.map_map, ← sum_map_add']
        rfl
      simp only [WTree.occH, WTree.occC, WTree.shares, WTree.written, hxt, if_false, occHs_eq,
        occCs_eq, sharess_count, List.count_append, writtens_sum, List.map_append,
        List.sum_append, Nat.zero_add]
      rw [hsplit, hH, hC]
      omega

/-! ## Slots of an encoding -/

/-- The inline writes of `y` in an encoding (entries of `S`, root writings). -/
def encWrites (p : Prep) (S : List Nat) (E : Nat → WTree) (R : List WTree) (y : Nat) : Nat :=
  (S.map fun s => ((E s).written p).count y).sum + (R.map fun T => (T.written p).count y).sum

/-- The Shares of `y` in an encoding. -/
def encRefs (S : List Nat) (E : Nat → WTree) (R : List WTree) (y : Nat) : Nat :=
  (S.map fun s => (E s).shares.count y).sum + (R.map fun T => T.shares.count y).sum

theorem count_eq_sum_ind (l : List Nat) (t : Nat) :
    l.count t = (l.map fun s => if s = t then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons, ih, beq_iff_eq]
    omega

theorem sum_ind_range {n y : Nat} (hy : y < n) (f : Nat → Nat) :
    ((List.range n).map fun z => (if z = y then 1 else 0) * f z).sum = f y := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ']
    by_cases hyn : y = n
    · subst hyn
      rw [sum_zero_of_forall fun z hz => by rw [if_neg (by omega), Nat.zero_mul]]
      simp
    · rw [ih (by omega), if_neg (Ne.symm hyn)]
      simp

/-- A sum over a list of terms below `n` as a sum over `0 … n-1` weighted by
the counts. -/
theorem sum_eq_count_range : ∀ {l : List Nat} {n : Nat}, (∀ y ∈ l, y < n) → ∀ (f : Nat → Nat),
    (l.map f).sum = ((List.range n).map fun y => l.count y * f y).sum
  | [], n, _, f => by
    simp only [List.map_nil, List.sum_nil, List.count_nil, Nat.zero_mul]
    exact (sum_map_eq_zero fun _ _ => rfl).symm
  | x :: xs, n, hl, f => by
    rw [List.map_cons, List.sum_cons, sum_eq_count_range (fun y hy => hl y (List.mem_cons_of_mem _ hy)) f]
    have hx := hl x List.mem_cons_self
    have : ((List.range n).map fun y => (x :: xs).count y * f y).sum =
        ((List.range n).map fun y => (if y = x then 1 else 0) * f y).sum +
          ((List.range n).map fun y => xs.count y * f y).sum := by
      rw [← sum_map_add']
      apply congrArg
      apply List.map_congr_left
      intro y _
      rw [List.count_cons]
      by_cases hyx : y = x
      · subst hyx; simp [Nat.add_mul]; omega
      · simp [Ne.symm hyx, hyx]
    rw [this, sum_ind_range hx]

theorem sum_comm_range {α : Type} (l : List α) (n : Nat) (g : α → Nat → Nat) :
    (l.map fun a => ((List.range n).map fun y => g a y).sum).sum =
      ((List.range n).map fun y => (l.map fun a => g a y).sum).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (sum_map_eq_zero fun _ _ => rfl).symm
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← sum_map_add']

theorem sum_mul_right' {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem label_root {p : Prep} {S : Nat → Bool} (t : Nat) :
    ∀ {roots : List Nat} {rootsW : List WTree}, List.Forall₂ (Valid p S) roots rootsW →
      (rootsW.map fun T => if T.label = t then 1 else 0).sum = roots.count t
  | _, _, .nil => rfl
  | r :: rs, T :: Ts, .cons hv hs => by
    simp only [List.map_cons, List.sum_cons, List.count_cons, label_root t hs, label_eq hv,
      beq_iff_eq]
    omega

/-- One writing: its writes plus Shares of `t` are its top plus one per edge
from each written term. -/
theorem PrepWF.writing_slots {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {t : Nat}
    (htn : t < p.dag.size) {x : Nat} {T : WTree} (h : Valid p S x T) (hx : x < p.dag.size) :
    (T.written p).count t + T.shares.count t =
      (if x = t then 1 else 0) +
        ((List.range p.dag.size).map fun y => (T.written p).count y * edgeAll p y t).sum := by
  rw [hp.count_written t h hx, hp.slots_edges htn h hx,
    sum_eq_count_range (n := p.dag.size) (fun y hy => by have := hp.written_le h hx y hy; omega)]

/-- **Slots of an encoding.** `writes t + refs t = root occurrences + [t
stored] + Σ_y writes y · edges(y, t)`. -/
theorem PrepWF.enc_slots {p : Prep} (hp : PrepWF p) {A : Nat → Bool} {S : List Nat}
    {E : Nat → WTree} {roots : List Nat} {R : List WTree} (hEnc : EncodingWF p A S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size) {t : Nat}
    (htn : t < p.dag.size) :
    encWrites p S E R t + encRefs S E R t = roots.count t + S.count t +
      ((List.range p.dag.size).map fun y => encWrites p S E R y * edgeAll p y t).sum := by
  have hS : ∀ s ∈ S, ((E s).written p).count t + (E s).shares.count t =
      (if s = t then 1 else 0) +
        ((List.range p.dag.size).map fun y => ((E s).written p).count y * edgeAll p y t).sum :=
    fun s hs => hp.writing_slots htn (hEnc.1 s hs).1 (hSin s hs)
  have hR : ∀ T ∈ R, (T.written p).count t + T.shares.count t =
      (if T.label = t then 1 else 0) +
        ((List.range p.dag.size).map fun y => (T.written p).count y * edgeAll p y t).sum := by
    intro T hT
    obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
    rw [hp.writing_slots htn hr (hroots r hrm), label_eq hr]
  have eS := congrArg List.sum (List.map_congr_left hS)
  have eR := congrArg List.sum (List.map_congr_left hR)
  simp only [sum_map_add'] at eS eR
  rw [← count_eq_sum_ind] at eS
  rw [label_root t hEnc.2] at eR
  rw [sum_comm_range] at eS eR
  unfold encWrites encRefs
  have hsplit : ((List.range p.dag.size).map fun y =>
      ((S.map fun s => ((E s).written p).count y).sum +
        (R.map fun T => (T.written p).count y).sum) * edgeAll p y t).sum =
      ((List.range p.dag.size).map fun y =>
        (S.map fun s => ((E s).written p).count y * edgeAll p y t).sum).sum +
      ((List.range p.dag.size).map fun y =>
        (R.map fun T => (T.written p).count y * edgeAll p y t).sum).sum := by
    rw [← sum_map_add']
    apply congrArg
    apply List.map_congr_left
    intro y _
    rw [Nat.add_mul, sum_mul_right', sum_mul_right']
  rw [hsplit]
  omega

/-! ## Visible counts -/

theorem modify_addc_getElem! (acc : Array Nat) (c t a : Nat) :
    (acc.modify c (· + a))[t]! = acc[t]! + (if c = t ∧ c < acc.size then a else 0) := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases hct : c = t
  · subst hct
    by_cases hc : c < acc.size
    · simp [hc, Array.getElem?_eq_getElem hc]
    · simp [hc, Array.getElem?_eq_none (by omega : acc.size ≤ c)]
  · simp [hct]

/-- The weight of a parent in `visibleCounts`. -/
def visWeight (ms : Array Bool) (d : Array Nat) (y : Nat) : Nat :=
  if ms[y]! then 1 else min d[y]! visibleCap

/-- The inner loop of `visibleCounts`: a parent adds its weight per edge. -/
theorem vis_inner (ch : Nat → Nat) (ce : Nat → Bool) (wy : Nat) :
    ∀ (l : List Nat) (st : Array Nat × Array Nat),
      (∀ i ∈ l, ch i < st.1.size ∧ ch i < st.2.size) →
      (∀ c, (l.foldl (fun (st : Array Nat × Array Nat) i =>
          (st.1.modify (ch i) (· + wy), if ce i then st.2 else st.2.modify (ch i) (· + wy))) st).1[c]! =
        st.1[c]! + wy * (l.filter fun i => ch i == c).length) ∧
      (∀ c, (l.foldl (fun (st : Array Nat × Array Nat) i =>
          (st.1.modify (ch i) (· + wy), if ce i then st.2 else st.2.modify (ch i) (· + wy))) st).2[c]! =
        st.2[c]! + wy * (l.filter fun i => ch i == c && !ce i).length) ∧
      (l.foldl (fun (st : Array Nat × Array Nat) i =>
          (st.1.modify (ch i) (· + wy), if ce i then st.2 else st.2.modify (ch i) (· + wy))) st).1.size =
        st.1.size ∧
      (l.foldl (fun (st : Array Nat × Array Nat) i =>
          (st.1.modify (ch i) (· + wy), if ce i then st.2 else st.2.modify (ch i) (· + wy))) st).2.size =
        st.2.size := by
  intro l
  induction l with
  | nil => intro st _; simp
  | cons i is ih =>
    intro st hl
    rw [List.foldl_cons]
    have hi := hl i List.mem_cons_self
    have hsz2 : (if ce i then st.2 else st.2.modify (ch i) (· + wy)).size = st.2.size := by
      split <;> simp
    obtain ⟨h1, h2, h3, h4⟩ := ih (st.1.modify (ch i) (· + wy),
      if ce i then st.2 else st.2.modify (ch i) (· + wy)) (fun j hj => by
        have := hl j (List.mem_cons_of_mem _ hj)
        simp only [Array.size_modify, hsz2]
        exact this)
    refine ⟨fun c => ?_, fun c => ?_, by rw [h3]; simp, by rw [h4, hsz2]⟩
    · rw [h1, modify_addc_getElem!, List.filter_cons]
      by_cases hc : ch i = c
      · subst hc
        simp [hi.1, Nat.mul_add]
        omega
      · simp [hc]
    · rw [h2, List.filter_cons]
      by_cases hce : ce i
      · simp [hce]
      · simp only [hce, Bool.false_eq_true, if_false, Bool.not_false, Bool.and_true]
        rw [modify_addc_getElem!]
        by_cases hc : ch i = c
        · subst hc
          simp [hi.2, Nat.mul_add]
          omega
        · simp [hc]

/-- **Propagated counts.** `propagateCounts dag roots weight` gives every term
`t` its root occurrences plus, per edge from `y`, the weight of `y` at its
final count. -/
theorem propagateCounts_spec {dag : Dag} (h : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (weight : Nat → Nat → Nat) {t : Nat}
    (ht : t < dag.size) :
    (propagateCounts dag roots weight).1[t]! = roots.toList.count t +
        ((List.range dag.size).map fun y => edgeAll (Prep.ofDag dag) y t *
          weight y (propagateCounts dag roots weight).1[y]!).sum ∧
      (propagateCounts dag roots weight).2[t]! = roots.toList.count t +
        ((List.range dag.size).map fun y => edgeMult (Prep.ofDag dag) y t false *
          weight y (propagateCounts dag roots weight).1[y]!).sum := by
  have hroots' : ∀ c ∈ roots.toList, c < (Array.replicate dag.size (0 : Nat)).size := by
    intro c hc; simpa using hroots c hc
  let base := roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate dag.size 0)
  have hbase : ∀ t, base[t]! = roots.toList.count t ∧ base.size = dag.size := by
    intro t
    simp only [base]
    rw [← Array.foldl_toList]
    obtain ⟨h1, h2⟩ := foldl_modify_count roots.toList (Array.replicate dag.size 0) t hroots'
    refine ⟨?_, by rw [h2]; simp⟩
    rw [h1]
    have : (Array.replicate dag.size (0 : Nat))[t]! = 0 := by
      simp only [getElem!_def, Array.getElem?_replicate]
      by_cases ht : t < dag.size <;> simp [ht]
    rw [this, Nat.zero_add]
  let step := fun (st : Array Nat × Array Nat) (k : Nat) =>
    (List.range (dag.node (dag.size - 1 - k)).children.size).foldl
      (fun (st' : Array Nat × Array Nat) i =>
        (st'.1.modify ((dag.node (dag.size - 1 - k)).child i)
            (· + weight (dag.size - 1 - k) st.1[dag.size - 1 - k]!),
          if continuationEdge (dag.node (dag.size - 1 - k)) i
              (dag.node ((dag.node (dag.size - 1 - k)).child i)) then st'.2
          else st'.2.modify ((dag.node (dag.size - 1 - k)).child i)
            (· + weight (dag.size - 1 - k) st.1[dag.size - 1 - k]!))) st
  have hdef : propagateCounts dag roots weight = (List.range dag.size).foldl step (base, base) := by
    unfold propagateCounts
    rw [foldRange_zero]
  -- one step: the parent `y` adds its weight per edge
  have hstep : ∀ (st : Array Nat × Array Nat) (k : Nat), st.1.size = dag.size →
      st.2.size = dag.size → k < dag.size →
      (∀ c, (step st k).1[c]! = st.1[c]! + weight (dag.size - 1 - k) st.1[dag.size - 1 - k]! *
          edgeAll (Prep.ofDag dag) (dag.size - 1 - k) c) ∧
      (∀ c, (step st k).2[c]! = st.2[c]! + weight (dag.size - 1 - k) st.1[dag.size - 1 - k]! *
          edgeMult (Prep.ofDag dag) (dag.size - 1 - k) c false) ∧
      (step st k).1.size = dag.size ∧ (step st k).2.size = dag.size := by
    intro st k hs1 hs2 hk
    have hy : dag.size - 1 - k < dag.size := by omega
    have har := h.arity _ hy
    rw [← dag_node_eq hy] at har
    have hlt : ∀ i ∈ List.range (dag.node (dag.size - 1 - k)).children.size,
        (dag.node (dag.size - 1 - k)).child i < st.1.size ∧
          (dag.node (dag.size - 1 - k)).child i < st.2.size := by
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [Ix.Compile.Verify.SharingExact.child_eq_getElem _ i hi']
      have := h.child_lt hy (Array.getElem_mem hi')
      omega
    obtain ⟨h1, h2, h3, h4⟩ := vis_inner (dag.node (dag.size - 1 - k)).child
      (fun i => continuationEdge (dag.node (dag.size - 1 - k)) i
        (dag.node ((dag.node (dag.size - 1 - k)).child i)))
      (weight (dag.size - 1 - k) st.1[dag.size - 1 - k]!) _ st hlt
    refine ⟨fun c => ?_, fun c => ?_, by rw [h3, hs1], by rw [h4, hs2]⟩
    · rw [h1]
      congr 2
      unfold edgeAll edgeMult
      rw [ofDag_dag, ← har]
      rw [filter_length_split (fun i => (dag.node (dag.size - 1 - k)).child i == c)
        (fun i => continuationEdge (dag.node (dag.size - 1 - k)) i (dag.node c))]
    · rw [h2]
      congr 2
      unfold edgeMult
      rw [ofDag_dag, ← har]
      congr 1
      apply List.filter_congr
      intro i _
      by_cases hc : (dag.node (dag.size - 1 - k)).child i = c
      · rw [hc]; cases continuationEdge (dag.node (dag.size - 1 - k)) i (dag.node c) <;> simp
      · simp only [beq_eq_false_iff_ne.mpr hc, Bool.false_and]
  -- the invariant after `k` steps
  have hinv : ∀ k, k ≤ dag.size →
      ((List.range k).foldl step (base, base)).1.size = dag.size ∧
      ((List.range k).foldl step (base, base)).2.size = dag.size ∧
      ∀ t, t < dag.size →
        ((List.range k).foldl step (base, base)).1[t]! = roots.toList.count t +
          ((List.range dag.size).map fun y => if dag.size - k ≤ y then
            edgeAll (Prep.ofDag dag) y t *
              weight y ((List.range k).foldl step (base, base)).1[y]! else 0).sum ∧
        ((List.range k).foldl step (base, base)).2[t]! = roots.toList.count t +
          ((List.range dag.size).map fun y => if dag.size - k ≤ y then
            edgeMult (Prep.ofDag dag) y t false *
              weight y ((List.range k).foldl step (base, base)).1[y]! else 0).sum := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨(hbase 0).2, (hbase 0).2, fun t _ => ⟨?_, ?_⟩⟩
      · rw [(hbase t).1, sum_zero_of_forall fun y hy => if_neg (by omega), Nat.add_zero]
      · rw [(hbase t).1, sum_zero_of_forall fun y hy => if_neg (by omega), Nat.add_zero]
    | succ k ih =>
      intro hk
      obtain ⟨hs1, hs2, hv⟩ := ih (by omega)
      rw [foldl_range_succ]
      generalize hst : (List.range k).foldl step (base, base) = st at hs1 hs2 hv
      obtain ⟨h1, h2, h3, h4⟩ := hstep st k hs1 hs2 (by omega)
      have hw : ∀ y, dag.size - 1 - k ≤ y → weight y (step st k).1[y]! = weight y st.1[y]! := by
        intro y hy
        rw [h1 y]
        have : edgeAll (Prep.ofDag dag) (dag.size - 1 - k) y = 0 := by
          unfold edgeAll
          have hp := prepWF_ofDag h
          rw [edgeMult_zero_of_le hp hy, edgeMult_zero_of_le hp hy]
        rw [this, Nat.mul_zero, Nat.add_zero]
      have hsum : ∀ (e : Nat → Nat), ((List.range dag.size).map fun y =>
          if dag.size - (k + 1) ≤ y then e y * weight y (step st k).1[y]! else 0).sum =
          ((List.range dag.size).map fun y =>
            if dag.size - k ≤ y then e y * weight y st.1[y]! else 0).sum +
            weight (dag.size - 1 - k) st.1[dag.size - 1 - k]! * e (dag.size - 1 - k) := by
        intro e
        have hpt : ∀ y ∈ List.range dag.size,
            (if dag.size - (k + 1) ≤ y then e y * weight y (step st k).1[y]! else 0) =
              (if dag.size - k ≤ y then e y * weight y st.1[y]! else 0) +
                (if y = dag.size - 1 - k then 1 else 0) *
                  (weight (dag.size - 1 - k) st.1[dag.size - 1 - k]! * e (dag.size - 1 - k)) := by
          intro y hy
          rw [List.mem_range] at hy
          by_cases hy0 : y = dag.size - 1 - k
          · subst hy0
            rw [if_pos (by omega), if_neg (by omega), if_pos rfl, hw _ (Nat.le_refl _)]
            simp [Nat.mul_comm]
          · simp only [if_neg hy0, Nat.zero_mul, Nat.add_zero]
            by_cases hyk : dag.size - k ≤ y
            · rw [if_pos (by omega), if_pos hyk, hw y (by omega)]
            · rw [if_neg (by omega), if_neg hyk]
        rw [List.map_congr_left hpt, sum_map_add', sum_ind_range (by omega)]
      refine ⟨h3, h4, fun t ht => ⟨?_, ?_⟩⟩
      · rw [h1, (hv t ht).1, hsum (fun y => edgeAll (Prep.ofDag dag) y t)]
        omega
      · rw [h2, (hv t ht).2, hsum (fun y => edgeMult (Prep.ofDag dag) y t false)]
        omega
  obtain ⟨_, _, hfin⟩ := hinv dag.size (Nat.le_refl _)
  rw [hdef]
  obtain ⟨e1, e2⟩ := hfin t ht
  refine ⟨?_, ?_⟩
  · rw [e1]
    congr 2
    apply List.map_congr_left
    intro y _
    rw [if_pos (by omega)]
  · rw [e2]
    congr 2
    apply List.map_congr_left
    intro y _
    rw [if_pos (by omega)]

/-! ## The gain algebra with occurrence lower bounds -/

/-- `max(x - w, 0)` as an integer. -/
theorem pos_part_cases (x w : Nat) :
    (w ≤ x ∧ (((if w ≤ x then x - w else 0 : Nat)) : _root_.Int) = (x : _root_.Int) - w) ∨
      (x < w ∧ (((if w ≤ x then x - w else 0 : Nat)) : _root_.Int) = 0) := by
  by_cases h : w ≤ x
  · left; rw [if_pos h]; exact ⟨h, by omega⟩
  · right; rw [if_neg h]; exact ⟨by omega, rfl⟩

theorem int_mul_le_mul_right' {a b c : _root_.Int} (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := _root_.Int.mul_le_mul_of_nonneg_right hab hc

theorem int_mul_le_mul_left' {a b c : _root_.Int} (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := _root_.Int.mul_le_mul_of_nonneg_left hab hc

/-- Non-telescope: `(d-1)·i⁻ - d·w ≤ H·max(I-w, 0) - I` when `1 ≤ d ≤ H`,
`i⁻ ≤ I`. -/
theorem gain_alg_node (d H I iLB w Ah : _root_.Int) (hd1 : 1 ≤ d) (hdH : d ≤ H) (hiLB : iLB ≤ I)
    (hw : 0 ≤ w) (hA : (w ≤ I ∧ Ah = I - w) ∨ (I < w ∧ Ah = 0)) :
    (d - 1) * iLB - d * w ≤ H * Ah - I := by
  have e1 := int_mul_le_mul_left' hiLB (show (0 : _root_.Int) ≤ d - 1 by omega)
  rcases hA with ⟨hwI, rfl⟩ | ⟨hIw, rfl⟩
  · have e2 := int_mul_le_mul_right' hdH (show (0 : _root_.Int) ≤ I - w by omega)
    simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul] at e1 e2 ⊢
    omega
  · have e2 := int_mul_le_mul_left' (show I ≤ w by omega) (show (0 : _root_.Int) ≤ d - 1 by omega)
    simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul,
      _root_.Int.mul_zero] at e1 e2 ⊢
    omega

/-- Telescope with a head occurrence:
`(d-1)·b + (h-1) - d·w ≤ H·max(I-w, 0) + C·max(M-w, 0) - I` when
`1 ≤ h ≤ H`, `h ≤ d ≤ H + C`, `b ≤ M`, `1 + M ≤ I`. -/
theorem gain_alg_head (d h H C I M mLB w Ah Ac : _root_.Int) (hh1 : 1 ≤ h) (hhd : h ≤ d)
    (hhH : h ≤ H) (hdHC : d ≤ H + C) (hC0 : 0 ≤ C) (hmLB : mLB ≤ M) (hMI : 1 + M ≤ I)
    (hw : 0 ≤ w) (hAh : (w ≤ I ∧ Ah = I - w) ∨ (I < w ∧ Ah = 0))
    (hAc : (w ≤ M ∧ Ac = M - w) ∨ (M < w ∧ Ac = 0)) :
    (d - 1) * mLB + (h - 1) - d * w ≤ H * Ah + C * Ac - I := by
  have e1 := int_mul_le_mul_left' hmLB (show (0 : _root_.Int) ≤ d - 1 by omega)
  rcases hAc with ⟨hwM, rfl⟩ | ⟨hMw, rfl⟩
  · rcases hAh with ⟨_, rfl⟩ | ⟨hIw, _⟩
    · -- H(I-w) = H(I-M-1) + H(M-w) + H ≥ (I-M-1) + H(M-w) + h
      have e2 := int_mul_le_mul_right' (show (1 : _root_.Int) ≤ H by omega)
        (show (0 : _root_.Int) ≤ I - M - 1 by omega)
      have e3 := int_mul_le_mul_right' hdHC (show (0 : _root_.Int) ≤ M - w by omega)
      simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.add_mul,
        _root_.Int.mul_one] at e1 e2 e3 ⊢
      omega
    · omega
  · have e2 := int_mul_le_mul_left' (show mLB ≤ w - 1 by omega) (show (0 : _root_.Int) ≤ d - 1 by omega)
    rcases hAh with ⟨hwI, rfl⟩ | ⟨hIw, rfl⟩
    · have e3 := int_mul_le_mul_right' (show (1 : _root_.Int) ≤ H by omega)
        (show (0 : _root_.Int) ≤ I - w by omega)
      simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.mul_one,
        _root_.Int.mul_zero] at e1 e2 e3 ⊢
      omega
    · simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.mul_one,
        _root_.Int.mul_zero] at e1 e2 ⊢
      omega

/-- Telescope without head occurrences:
`(d-1)·b - T - d·w ≤ H·max(I-w, 0) + C·max(M-w, 0) - I` when
`1 ≤ d ≤ H + C`, `b ≤ M`, `1 + M ≤ I ≤ T + M`. -/
theorem gain_alg_cont (d H C I M mLB T w Ah Ac : _root_.Int) (hd1 : 1 ≤ d) (hdHC : d ≤ H + C)
    (hH0 : 0 ≤ H) (hC0 : 0 ≤ C) (hmLB : mLB ≤ M) (hMI : 1 + M ≤ I) (hIT : I ≤ T + M)
    (hw : 0 ≤ w) (hAh : (w ≤ I ∧ Ah = I - w) ∨ (I < w ∧ Ah = 0))
    (hAc : (w ≤ M ∧ Ac = M - w) ∨ (M < w ∧ Ac = 0)) :
    (d - 1) * mLB - T - d * w ≤ H * Ah + C * Ac - I := by
  have e1 := int_mul_le_mul_left' hmLB (show (0 : _root_.Int) ≤ d - 1 by omega)
  rcases hAc with ⟨hwM, rfl⟩ | ⟨hMw, rfl⟩
  · rcases hAh with ⟨_, rfl⟩ | ⟨hIw, _⟩
    · have e2 := int_mul_le_mul_left' (show M - w ≤ I - w by omega) hH0
      have e3 := int_mul_le_mul_right' hdHC (show (0 : _root_.Int) ≤ M - w by omega)
      simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.add_mul,
        _root_.Int.mul_one] at e1 e2 e3 ⊢
      omega
    · omega
  · have e2 := int_mul_le_mul_left' (show mLB ≤ w - 1 by omega) (show (0 : _root_.Int) ≤ d - 1 by omega)
    have e3 : 0 ≤ H * Ah := by
      rcases hAh with ⟨hwI, rfl⟩ | ⟨_, rfl⟩
      · exact _root_.Int.mul_nonneg hH0 (by omega)
      · simp
    simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.mul_one,
      _root_.Int.mul_zero] at e1 e2 ⊢
    omega

/-- **Visible counts.** `visibleCounts dag roots ms` gives every term `t` its
root occurrences plus, per edge from `y`, the weight of `y`: 1 if `ms[y]`,
else the (capped) count of `y`. -/
theorem visibleCounts_spec {dag : Dag} (h : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (ms : Array Bool) {t : Nat}
    (ht : t < dag.size) :
    (visibleCounts dag roots ms).1[t]! = roots.toList.count t +
        ((List.range dag.size).map fun y => edgeAll (Prep.ofDag dag) y t *
          visWeight ms (visibleCounts dag roots ms).1 y).sum ∧
      (visibleCounts dag roots ms).2[t]! = roots.toList.count t +
        ((List.range dag.size).map fun y => edgeMult (Prep.ofDag dag) y t false *
          visWeight ms (visibleCounts dag roots ms).1 y).sum :=
  propagateCounts_spec h roots hroots _ ht

/-- **Occurrences.** `occurrences dag roots` counts every root occurrence
plus, per edge from `y`, the occurrences of `y`. -/
theorem occurrences_spec {dag : Dag} (h : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) {t : Nat} (ht : t < dag.size) :
    (occurrences dag roots)[t]! = roots.toList.count t +
      ((List.range dag.size).map fun y => edgeAll (Prep.ofDag dag) y t *
        (occurrences dag roots)[y]!).sum :=
  (propagateCounts_spec h roots hroots (fun _ c => c) ht).1

/-! ## Writes of an encoding and the visible counts -/

open Ix.Compile.Verify.SharingExact (Desc)

theorem le_sum_map_of_mem {α : Type} (f : α → Nat) {l : List α} {a : α} (h : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem PrepWF.refs_zero {p : Prep} (hp : PrepWF p) {S : List Nat} {E : Nat → WTree}
    {roots : List Nat} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size) {t : Nat}
    (htS : t ∉ S) : encRefs S E R t = 0 := by
  have hz : ∀ {x : Nat} {T : WTree}, Valid p (fun y => decide (y ∈ S)) x T → x < p.dag.size →
      T.shares.count t = 0 := by
    intro x T hv hx
    rw [List.count_eq_zero]
    intro hs
    have := (hp.shares_lt hv hx t hs).1
    simp only [decide_eq_true_eq] at this
    exact htS this
  unfold encRefs
  rw [sum_map_eq_zero (fun s hs => hz (hEnc.1 s hs).1 (hSin s hs)),
    sum_map_eq_zero (fun T hT => by
      obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
      exact hz hr (hroots r hrm))]

theorem PrepWF.writes_pos {p : Prep} (hp : PrepWF p) {S : List Nat} {E : Nat → WTree}
    {roots : List Nat} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size)
    (hreach : ∀ y, y < p.dag.size → ∃ r ∈ roots, Desc p.dag r y) :
    ∀ y, y < p.dag.size → 1 ≤ encWrites p S E R y := by
  intro y hy
  have hc := hp.encoding_covers hEnc hSin hroots hreach y hy
  unfold encWrites
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hc
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hl
    have h1 : 1 ≤ (T.written p).count y := List.count_pos_iff.mpr hyl
    have := le_sum_map_of_mem (fun T => (T.written p).count y) hT
    omega
  · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    have h1 : 1 ≤ ((E s).written p).count y := List.count_pos_iff.mpr hyl
    have := le_sum_map_of_mem (fun s => ((E s).written p).count y) hs
    omega

theorem PrepWF.writes_unstored {p : Prep} (hp : PrepWF p) {S : List Nat} {E : Nat → WTree}
    {roots : List Nat} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size) {y : Nat}
    (hy : y < p.dag.size) (hyS : y ∉ S) :
    encWrites p S E R y = roots.count y +
      ((List.range p.dag.size).map fun z => encWrites p S E R z * edgeAll p z y).sum := by
  have := hp.enc_slots hEnc hSin hroots hy
  rw [hp.refs_zero hEnc hSin hroots hyS, List.count_eq_zero_of_not_mem hyS] at this
  omega

theorem edgeAll_zero_of_le {p : Prep} (hp : PrepWF p) {z y : Nat} (h : z ≤ y) :
    edgeAll p z y = 0 := by
  unfold edgeAll
  rw [edgeMult_zero_of_le hp h, edgeMult_zero_of_le hp h]

/-- **Visible counts are lower bounds.** In an encoding of `S ⊆ ms`, every
term gets at least its weight in writes, and every `t ∉ S` at least its
visible count. -/
theorem writes_ge_visible {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (ms : Array Bool) {S : List Nat} (hSin : ∀ s ∈ S, s < dag.size)
    (hSms : ∀ s ∈ S, ms[s]! = true) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF (Prep.ofDag dag) (fun y => decide (y ∈ S)) S E roots.toList R) :
    ∀ y, y < dag.size →
      visWeight ms (visibleCounts dag roots ms).1 y ≤ encWrites (Prep.ofDag dag) S E R y ∧
        (y ∉ S → (visibleCounts dag roots ms).1[y]! ≤ encWrites (Prep.ofDag dag) S E R y) := by
  have hp := prepWF_ofDag hwf
  have hpos := hp.writes_pos hEnc hSin hroots hreach
  have key : ∀ m, ∀ y, dag.size - y ≤ m → y < dag.size →
      visWeight ms (visibleCounts dag roots ms).1 y ≤ encWrites (Prep.ofDag dag) S E R y ∧
        (y ∉ S → (visibleCounts dag roots ms).1[y]! ≤ encWrites (Prep.ofDag dag) S E R y) := by
    intro m
    induction m with
    | zero => intro y hym hy; omega
    | succ m ih =>
      intro y hym hy
      have hstep : y ∉ S → (visibleCounts dag roots ms).1[y]! ≤
          encWrites (Prep.ofDag dag) S E R y := by
        intro hyS
        rw [(visibleCounts_spec hwf roots hroots ms hy).1,
          hp.writes_unstored hEnc hSin hroots hy hyS]
        apply Nat.add_le_add_left
        apply sum_le_sum_of_le
        intro z hz
        rw [List.mem_range] at hz
        by_cases hzy : y < z
        · rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right _ (ih z (by omega) hz).1
        · rw [edgeAll_zero_of_le hp (by omega)]
          simp
      refine ⟨?_, hstep⟩
      unfold visWeight
      split
      · exact hpos y hy
      · rename_i hms
        have hyS : y ∉ S := fun h => hms (hSms y h)
        exact Nat.le_trans (Nat.min_le_left _ _) (hstep hyS)
  intro y hy
  exact key (dag.size - y) y (Nat.le_refl _) hy

/-- The head occurrences of `t ∉ S` in an encoding: the root occurrences plus
one per non-continuation edge from each write. -/
theorem PrepWF.heads_eq {p : Prep} (hp : PrepWF p) {S : List Nat} {E : Nat → WTree}
    {roots : List Nat} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size) {t : Nat}
    (htn : t < p.dag.size) (htS : t ∉ S) :
    (S.map fun s => (E s).occH t).sum + (R.map (WTree.occH t)).sum = roots.count t +
      ((List.range p.dag.size).map fun y => encWrites p S E R y * edgeMult p y t false).sum := by
  have hSt : (fun y => decide (y ∈ S)) t = false := by simp [htS]
  have hone : ∀ {x : Nat} {T : WTree}, Valid p (fun y => decide (y ∈ S)) x T → x < p.dag.size →
      T.occH t = (if T.topIs t then 1 else 0) +
        ((List.range p.dag.size).map fun y => (T.written p).count y * edgeMult p y t false).sum := by
    intro x T hv hx
    rw [(hp.occ_edges hSt htn hv hx).1, sum_eq_count_range (n := p.dag.size)
      (fun y hy => by have := hp.written_le hv hx y hy; omega)]
  have eS := congrArg List.sum (List.map_congr_left fun s hs => hone (hEnc.1 s hs).1 (hSin s hs))
  have eR := congrArg List.sum (List.map_congr_left fun T hT => by
    obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
    exact hone hr (hroots r hrm))
  simp only [sum_map_add'] at eS eR
  have htopS : (S.map fun s => if (E s).topIs t then 1 else 0).sum = 0 := by
    apply sum_map_eq_zero
    intro s hs
    rw [if_neg]
    intro h
    have := (top_iff hSt (hEnc.1 s hs).1).mp h
    exact htS (this ▸ hs)
  rw [htopS, sum_comm_range] at eS
  rw [topIs_root hSt hEnc.2, sum_comm_range] at eR
  rw [eS, eR]
  unfold encWrites
  have hsplit : ((List.range p.dag.size).map fun y =>
      ((S.map fun s => ((E s).written p).count y).sum +
        (R.map fun T => (T.written p).count y).sum) * edgeMult p y t false).sum =
      ((List.range p.dag.size).map fun y =>
        (S.map fun s => ((E s).written p).count y * edgeMult p y t false).sum).sum +
      ((List.range p.dag.size).map fun y =>
        (R.map fun T => (T.written p).count y * edgeMult p y t false).sum).sum := by
    rw [← sum_map_add']
    apply congrArg
    apply List.map_congr_left
    intro y _
    rw [Nat.add_mul, sum_mul_right', sum_mul_right']
  rw [hsplit]
  omega

theorem heads_ge_visible {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (ms : Array Bool) {S : List Nat} (hSin : ∀ s ∈ S, s < dag.size)
    (hSms : ∀ s ∈ S, ms[s]! = true) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF (Prep.ofDag dag) (fun y => decide (y ∈ S)) S E roots.toList R) {t : Nat}
    (htn : t < dag.size) (htS : t ∉ S) :
    (visibleCounts dag roots ms).2[t]! ≤
      (S.map fun s => (E s).occH t).sum + (R.map (WTree.occH t)).sum := by
  have hp := prepWF_ofDag hwf
  rw [hp.heads_eq hEnc hSin hroots htn htS, (visibleCounts_spec hwf roots hroots ms htn).2]
  apply Nat.add_le_add_left
  apply sum_le_sum_of_le
  intro z hz
  rw [List.mem_range] at hz
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _
    (writes_ge_visible hwf roots hroots hreach ms hSin hSms hEnc z hz).1

/-! ## The exchange with visible counts -/

theorem PrepWF.occs_eq_writes {p : Prep} (hp : PrepWF p) {S : List Nat} {E : Nat → WTree}
    {roots : List Nat} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size) (t : Nat) :
    ((S.map fun s => (E s).occH t).sum + (R.map (WTree.occH t)).sum) +
        ((S.map fun s => (E s).occC p t).sum + (R.map (WTree.occC p t)).sum) =
      encWrites p S E R t := by
  have eS := congrArg List.sum (List.map_congr_left fun s hs =>
    hp.count_written t (hEnc.1 s hs).1 (hSin s hs))
  have eR := congrArg List.sum (List.map_congr_left fun T hT => by
    obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
    exact hp.count_written t hr (hroots r hrm))
  simp only [sum_map_add'] at eS eR
  unfold encWrites
  omega

theorem PrepWF.conts_zero {p : Prep} (hp : PrepWF p) {S : List Nat} {E : Nat → WTree}
    {roots : List Nat} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size) {t : Nat}
    (htn : t < p.dag.size) (htS : t ∉ S) (hf : p.family[t]! = .none) :
    (S.map fun s => (E s).occC p t).sum + (R.map (WTree.occC p t)).sum = 0 := by
  have hSt : (fun y => decide (y ∈ S)) t = false := by simp [htS]
  have hz : ∀ {x : Nat} {T : WTree}, Valid p (fun y => decide (y ∈ S)) x T → x < p.dag.size →
      T.occC p t = 0 := by
    intro x T hv hx
    rw [(hp.occ_edges hSt htn hv hx).2.1]
    exact sum_map_eq_zero fun y _ => edgeMult_cont_zero hp htn hf y
  rw [sum_map_eq_zero (fun s hs => hz (hEnc.1 s hs).1 (hSin s hs)),
    sum_map_eq_zero (fun T hT => by
      obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
      exact hz hr (hroots r hrm))]

/-- **The exchange, generalised.** For any maybe-stored set `ms ⊇ S` and
`t ∉ S`, any bounds `b` below `uniformBounds … ms` at `t` and any lower
bounds `h ≤ d` (with `1 ≤ d`) of the visible counts of `ms` at `t`:
adding `t` to `S` shortens the uniform length by at least the gain, up to
the growth of the count's `Tag0`:
`L(S ∪ {t}) + tag0Size |S| ≤ L(S) - storedGainC b w t d h + tag0Size (|S|+1)`. -/
theorem uniformCost_insert_le_counts {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (w : Nat) (ms : Array Bool) {S : List Nat} (hSin : ∀ s ∈ S, s < dag.size)
    (hSms : ∀ s ∈ S, ms[s]! = true) {t : Nat} (htn : t < dag.size) (htS : t ∉ S)
    {b : UBounds}
    (hbI : b.inlineLB[t]! ≤ (uniformBounds (Prep.ofDag dag) w ms).inlineLB[t]!)
    (hbM : b.mergedLB[t]! ≤ (uniformBounds (Prep.ofDag dag) w ms).mergedLB[t]!)
    {d h : Nat} (hd : d ≤ (visibleCounts dag roots ms).1[t]!)
    (hh : h ≤ (visibleCounts dag roots ms).2[t]!) (hhd : h ≤ d) (hd1 : 1 ≤ d) :
    ((uniformCost (Prep.ofDag dag) w (fun y => decide (y ∈ t :: S)) (t :: S) roots.toList : Nat) :
        _root_.Int) + (tag0Size S.length : _root_.Int) ≤
      (uniformCost (Prep.ofDag dag) w (fun y => decide (y ∈ S)) S roots.toList : _root_.Int) -
        storedGainC (Prep.ofDag dag) b w t d h + (tag0Size (S.length + 1) : _root_.Int) := by
  have hp := prepWF_ofDag hwf
  have hSin' : ∀ s ∈ S, s < (Prep.ofDag dag).dag.size := by rw [ofDag_dag]; exact hSin
  have hroots' : ∀ r ∈ roots.toList, r < (Prep.ofDag dag).dag.size := by
    rw [ofDag_dag]; exact hroots
  have htn' : t < (Prep.ofDag dag).dag.size := by rw [ofDag_dag]; exact htn
  obtain ⟨E, R, hEnc, hcost⟩ :=
    hp.uniformCost_attained w (fun y => decide (y ∈ S)) S roots.toList hSin' hroots'
  have hx := hp.exchange_counts w hSin' roots.toList hroots' htn' htS hEnc hcost
  simp only at hx
  have hHC := hp.occs_eq_writes hEnc hSin' hroots' t
  have hvis := (writes_ge_visible hwf roots hroots hreach ms hSin hSms hEnc t htn).2 htS
  have hhead := heads_ge_visible hwf roots hroots hreach ms hSin hSms hEnc htn htS
  generalize (S.map fun s => (E s).occH t).sum + (R.map (WTree.occH t)).sum = H at hx hHC hhead
  generalize hCdef : (S.map fun s => (E s).occC (Prep.ofDag dag) t).sum +
    (R.map (WTree.occC (Prep.ofDag dag) t)).sum = C at hx hHC
  have hb := hp.bounds_sound w ms (fun y => decide (y ∈ S))
    (fun y hy => hSms y (by simpa using hy)) t htn'
  have hIMb : (Prep.ofDag dag).family[t]! ≠ .none →
      1 + mergedOf (Prep.ofDag dag) w (fun y => decide (y ∈ S))
          (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t ≤
        uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t ∧
      uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t ≤
        tag4Size (Prep.ofDag dag).spineLen[t]! + mergedOf (Prep.ofDag dag) w
          (fun y => decide (y ∈ S)) (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t :=
    fun hf => inl_merged_bounds _ w _ _ hf
  have hAh := pos_part_cases (uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t) w
  have hAc := pos_part_cases (mergedOf (Prep.ofDag dag) w (fun y => decide (y ∈ S))
    (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t) w
  generalize uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t = I at hx hb hIMb hAh
  generalize mergedOf (Prep.ofDag dag) w (fun y => decide (y ∈ S))
    (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t = M at hx hb hIMb hAc
  generalize (if w ≤ I then I - w else 0) = Ah at hx hAh
  generalize (if w ≤ M then M - w else 0) = Ac at hx hAc
  have hexI := _root_.Int.ofNat_le.mpr hx
  simp only [_root_.Int.natCast_add, _root_.Int.natCast_mul] at hexI
  unfold storedGainC
  simp only [_root_.Int.ofNat_eq_natCast]
  by_cases hf : (Prep.ofDag dag).family[t]! = .none
  · have hC0 : C = 0 := by
      rw [← hCdef]
      exact hp.conts_zero hEnc hSin' hroots' htn' htS hf
    subst hC0
    have hfb : ((Prep.ofDag dag).family[t]! == Family.none) = true := by simp [hf]
    simp only [hfb, if_true]
    have e := gain_alg_node (d : _root_.Int) (H : _root_.Int) (I : _root_.Int)
      (b.inlineLB[t]! : _root_.Int) (w : _root_.Int) (Ah : _root_.Int) (by omega) (by omega)
      (by have := hb.2.1; omega) (by omega) (by rcases hAh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
    simp only [_root_.Int.natCast_zero, _root_.Int.zero_mul, _root_.Int.add_zero] at hexI
    omega
  · have hfb : ((Prep.ofDag dag).family[t]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, if_false]
    have hmLB := (hb.2.2 hf).1
    obtain ⟨hIM1, hIM2⟩ := hIMb hf
    by_cases hH1 : h ≥ 1
    · rw [if_pos hH1]
      have e := gain_alg_head (d : _root_.Int) (h : _root_.Int) (H : _root_.Int) (C : _root_.Int)
        (I : _root_.Int) (M : _root_.Int) (b.mergedLB[t]! : _root_.Int) (w : _root_.Int)
        (Ah : _root_.Int) (Ac : _root_.Int) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
        (by rcases hAh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
        (by rcases hAc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
      omega
    · rw [if_neg hH1]
      have e := gain_alg_cont (d : _root_.Int) (H : _root_.Int) (C : _root_.Int) (I : _root_.Int)
        (M : _root_.Int) (b.mergedLB[t]! : _root_.Int)
        (tag4Size (Prep.ofDag dag).spineLen[t]! : _root_.Int) (w : _root_.Int)
        (Ah : _root_.Int) (Ac : _root_.Int) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
        (by rcases hAh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
        (by rcases hAc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
      omega

/-! ## Certain-stored: every minimum stores the term -/

/-- The uniform length of a stored set. -/
def ulen (dag : Dag) (w : Nat) (roots : Array Nat) (S : List Nat) : Nat :=
  uniformCost (Prep.ofDag dag) w (fun y => decide (y ∈ S)) S roots.toList

theorem tag0Size_mono {a b : Nat} (h : a ≤ b) : tag0Size a ≤ tag0Size b := by
  have := natByteCount_mono h
  unfold tag0Size
  split <;> split <;> omega

/-- **Certain-stored, for any maybe-stored set.** If `S ⊆ ms`, `t ∉ S` would
make `S` strictly longer than `S ∪ {t}` when the gain of `t` (bounds below
`uniformBounds … ms`, counts below the visible counts of `ms`) exceeds the
growth of the count's `Tag0`; so a set no longer than `S ∪ {t}` contains `t`. -/
theorem mem_of_gain {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (w : Nat) (ms : Array Bool) {S : List Nat} (hSin : ∀ s ∈ S, s < dag.size)
    (hSms : ∀ s ∈ S, ms[s]! = true) {t : Nat} (htn : t < dag.size) {b : UBounds}
    (hbI : b.inlineLB[t]! ≤ (uniformBounds (Prep.ofDag dag) w ms).inlineLB[t]!)
    (hbM : b.mergedLB[t]! ≤ (uniformBounds (Prep.ofDag dag) w ms).mergedLB[t]!)
    {d h : Nat} (hd : d ≤ (visibleCounts dag roots ms).1[t]!)
    (hh : h ≤ (visibleCounts dag roots ms).2[t]!) (hhd : h ≤ d) (hd1 : 1 ≤ d)
    (hmin : ulen dag w roots S ≤ ulen dag w roots (t :: S))
    (hgain : (tag0Size (S.length + 1) : _root_.Int) - tag0Size S.length <
      storedGainC (Prep.ofDag dag) b w t d h) :
    t ∈ S := by
  by_cases htS : t ∈ S
  · exact htS
  · exfalso
    have := uniformCost_insert_le_counts hwf roots hroots hreach w ms hSin hSms htn htS hbI hbM
      hd hh hhd hd1
    unfold ulen at hmin
    have hm := _root_.Int.ofNat_le.mpr hmin
    omega

/-- The two thresholds: gain `≥ 2` always beats the `Tag0` growth; gain `≥ 1`
does when `S` and `S ∪ {t}` share a count bracket. -/
theorem tag0_growth_lt {n : Nat} {g : _root_.Int}
    (h : 2 ≤ g ∨ (1 ≤ g ∧ tag0Size (n + 1) = tag0Size n)) :
    (tag0Size (n + 1) : _root_.Int) - tag0Size n < g := by
  have := tag0Size_succ_le n
  rcases h with h | ⟨h1, h2⟩ <;> omega

/-- The restricted class: duplicate-free sets of terms of in-degree at least
two. -/
def InClass (dag : Dag) (roots : Array Nat) (S : List Nat) : Prop :=
  S.Nodup ∧ ∀ s ∈ S, s < dag.size ∧ 2 ≤ (graphFacts dag roots).deg[s]!

/-- `S` minimises the uniform length over the restricted class. -/
def IsMinimum (dag : Dag) (w : Nat) (roots : Array Nat) (S : List Nat) : Prop :=
  InClass dag roots S ∧ ∀ S', InClass dag roots S' → ulen dag w roots S ≤ ulen dag w roots S'

/-- **Stage 3 (certain-stored), for partial assignments.** Let `X` be a
minimum over the restricted class and `ms` any maybe-stored set containing
`X` (for a partial assignment respected by `X`: the candidates minus the
terms decided not stored). A term `t` of in-degree `≥ 2` whose gain under
`ms` (with any bounds below `uniformBounds … ms` and any counts `h ≤ d`
below the visible counts of `ms`) is `≥ 2`, or `≥ 1` when `|X|` and
`|X| + 1` share a `Tag0` bracket, is in `X`. -/
theorem stored_in_minimum {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (w : Nat) (ms : Array Bool) {X : List Nat} (hX : IsMinimum dag w roots X)
    (hXms : ∀ s ∈ X, ms[s]! = true) {t : Nat} (htn : t < dag.size)
    (hdeg : 2 ≤ (graphFacts dag roots).deg[t]!) {b : UBounds}
    (hbI : b.inlineLB[t]! ≤ (uniformBounds (Prep.ofDag dag) w ms).inlineLB[t]!)
    (hbM : b.mergedLB[t]! ≤ (uniformBounds (Prep.ofDag dag) w ms).mergedLB[t]!)
    {d h : Nat} (hd : d ≤ (visibleCounts dag roots ms).1[t]!)
    (hh : h ≤ (visibleCounts dag roots ms).2[t]!) (hhd : h ≤ d) (hd1 : 1 ≤ d)
    (hgain : 2 ≤ storedGainC (Prep.ofDag dag) b w t d h ∨
      (1 ≤ storedGainC (Prep.ofDag dag) b w t d h ∧
        tag0Size (X.length + 1) = tag0Size X.length)) :
    t ∈ X := by
  by_cases htX : t ∈ X
  · exact htX
  · have hcl : InClass dag roots (t :: X) :=
      ⟨List.nodup_cons.mpr ⟨htX, hX.1.1⟩, fun s hs => by
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨htn, hdeg⟩
        · exact hX.1.2 s hs⟩
    exact mem_of_gain hwf roots hroots hreach w ms (fun s hs => (hX.1.2 s hs).1) hXms htn hbI hbM
      hd hh hhd hd1 (hX.2 _ hcl) (tag0_growth_lt hgain)

/-- The bracket condition behind threshold 1: if every minimum contains a set
`G` and lies within a set `C` (both duplicate-free), with
`tag0Size |C| = tag0Size |G|`, then for a minimum `X` and `t ∈ C \ X`,
`|X|` and `|X| + 1` share a bracket. -/
theorem same_bracket {X G C : List Nat} (hGX : ∀ g ∈ G, g ∈ X) (hXC : ∀ x ∈ X, x ∈ C)
    (hG : G.Nodup) (hX : X.Nodup) (hC : C.Nodup) {t : Nat} (htC : t ∈ C) (htX : t ∉ X)
    (hbr : tag0Size C.length = tag0Size G.length) :
    tag0Size (X.length + 1) = tag0Size X.length := by
  have h1 : G.length ≤ X.length := List.Nodup.length_le_of_subset hG hGX
  have h2 : X.length + 1 ≤ C.length := by
    have hsub : t :: X ⊆ C := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact htC
      · exact hXC y hy
    have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨htX, hX⟩) hsub
    simpa using this
  have a := tag0Size_mono h1
  have b := tag0Size_mono (show X.length ≤ X.length + 1 by omega)
  have c := tag0Size_mono h2
  omega

/-! ## Certain-excluded: the removal exchange -/

theorem natByteCount_mul256 {m : Nat} (hm : m ≠ 0) : natByteCount (256 * m) = natByteCount m + 1 := by
  rw [Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero (by omega)]
  congr 2
  omega

theorem natByteCount_double (m : Nat) : natByteCount (2 * m) ≤ natByteCount m + 1 := by
  by_cases hm : m = 0
  · subst hm; simp
  · have := natByteCount_mono (show 2 * m ≤ 256 * m by omega)
    rw [natByteCount_mul256 hm] at this
    exact this

theorem natByteCount_small {n : Nat} (h0 : n ≠ 0) (h : n < 256) : natByteCount n = 1 := by
  rw [Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero h0, show n / 256 = 0 by omega,
    Ix.Compile.Verify.SharingExact.natByteCount_zero]

/-- Telescope headers are subadditive. -/
theorem tag4Size_add_le {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    tag4Size (a + b) ≤ tag4Size a + tag4Size b := by
  have key : ∀ a b, 1 ≤ a → a ≤ b → tag4Size (a + b) ≤ tag4Size a + tag4Size b := by
    intro a b ha hab
    unfold tag4Size
    by_cases hs : a + b < 8
    · simp only [hs, if_true]; split <;> split <;> omega
    · simp only [hs, if_false]
      have h2 := natByteCount_mono (show a + b ≤ 2 * b by omega)
      have h3 := natByteCount_double b
      by_cases hb8 : b < 8
      · have ha8 : a < 8 := by omega
        simp only [hb8, ha8, if_true]
        rw [natByteCount_small (by omega) (by omega)]
        omega
      · simp only [hb8, if_false]
        split <;> omega
  by_cases hab : a ≤ b
  · exact key a b ha hab
  · have := key b a hb (by omega)
    rw [Nat.add_comm a b]
    omega

/-- A writing stays valid when the available set keeps its Shares. -/
theorem Valid.restrict {p : Prep} {S S' : Nat → Bool} :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → (∀ s ∈ T.shares, S' s = true) → Valid p S' x T := by
  intro x T h
  induction h with
  | share _ => intro hs; exact .share (hs _ (by simp [WTree.shares]))
  | node hf hlen _ ih =>
    intro hs
    refine .node hf hlen fun i hi => ih i hi fun s hsi => hs s ?_
    simp only [WTree.shares]
    exact mem_sharess (List.getElem_mem hi) hsi
  | teleCut hf hj1 hj hlen _ hS ih =>
    intro hs
    refine .teleCut hf hj1 hj hlen (fun k hk => ih k hk fun s hsk => hs s ?_)
      (hs _ (by simp [WTree.shares]))
    simp only [WTree.shares, List.mem_append]
    exact Or.inl (mem_sharess (List.getElem_mem hk) hsk)
  | teleFull hf hlen _ _ ih iht =>
    intro hs
    refine .teleFull hf hlen (fun k hk => ih k hk fun s hsk => hs s ?_) (iht fun s hst => hs s ?_)
    · simp only [WTree.shares, List.mem_append]
      exact Or.inl (mem_sharess (List.getElem_mem hk) hsk)
    · simp only [WTree.shares, List.mem_append]
      exact Or.inr hst

theorem ownBytes_pos {h : Head} (hf : h.family = .none) : 1 ≤ h.ownBytes := by
  cases h with
  | sort i => exact tag4Size_pos _
  | var i => exact tag4Size_pos _
  | ref r us => simp only [Head.ownBytes]; have := tag4Size_pos us.size; omega
  | recur r us => simp only [Head.ownBytes]; have := tag4Size_pos us.size; omega
  | prj t f => simp only [Head.ownBytes]; have := tag4Size_pos f.toNat; omega
  | str i => exact tag4Size_pos _
  | nat i => exact tag4Size_pos _
  | letE c => simp only [Head.ownBytes]; omega
  | app => simp [Head.family] at hf
  | lam _ => simp [Head.family] at hf
  | all _ _ => simp [Head.family] at hf

/-- An inline writing costs at least one byte. -/
theorem PrepWF.cost_pos {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {w x : Nat} {T : WTree}
    (h : Valid p S x T) (hx : x < p.dag.size) (hns : T.isShare = false) : 1 ≤ T.cost p w := by
  cases h with
  | share => simp [WTree.isShare] at hns
  | node hf =>
    have hfam : (p.dag.node x).head.family = .none := by rw [← hp.family x hx]; exact hf
    have := ownBytes_pos hfam
    simp only [WTree.cost]
    omega
  | @teleCut _ j =>
    have := tag4Size_pos j
    simp only [WTree.cost]
    omega
  | teleFull =>
    have := tag4Size_pos p.spineLen[x]!
    simp only [WTree.cost]
    omega

/-- A cut telescope continued by a writing of its cut node. -/
def WTree.merge (x j : Nat) (sides : List WTree) : WTree → WTree
  | .tele _ j' sides' tail' => .tele x (j + j') (sides ++ sides') tail'
  | W => .tele x j sides W

/-- The telescope case of `unshare`: a cut at `t` is continued by `W`. -/
def unshareTele (p : Prep) (t : Nat) (W : WTree) (x j : Nat) (sides : List WTree)
    (tail tail' : WTree) : WTree :=
  match tail with
  | .share u => if u = t ∧ j < p.spineLen[x]! then WTree.merge x j sides W else .tele x j sides tail'
  | _ => .tele x j sides tail'

mutual
/-- Replace every Share of `t` by the writing `W` of `t`: at a head position by
`W` itself, at a telescope cut by continuing the telescope with `W`'s spine. -/
def WTree.unshare (p : Prep) (t : Nat) (W : WTree) : WTree → WTree
  | .share x => if x = t then W else .share x
  | .node x kids => .node x (WTree.unshares p t W kids)
  | .tele x j sides tail =>
    unshareTele p t W x j (WTree.unshares p t W sides) tail (WTree.unshare p t W tail)
def WTree.unshares (p : Prep) (t : Nat) (W : WTree) : List WTree → List WTree
  | [] => []
  | k :: ks => WTree.unshare p t W k :: WTree.unshares p t W ks
end

theorem unshares_eq (p : Prep) (t : Nat) (W : WTree) (l : List WTree) :
    WTree.unshares p t W l = l.map (WTree.unshare p t W) := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.unshares, ih]

theorem sum_ineq2 {α : Type} (f g c d : α → Nat) (A B : Nat) :
    ∀ (l : List α), (∀ a ∈ l, f a + g a * A ≤ c a + g a * B) →
      (l.map f).sum + (l.map g).sum * A ≤ (l.map c).sum + (l.map g).sum * B := by
  intro l h
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    omega


/-- An inline writing of a telescope node is a telescope. -/
theorem valid_tele_inv {p : Prep} {S : Nat → Bool} {t : Nat} {W : WTree} (h : Valid p S t W)
    (hns : W.isShare = false) (hft : p.family[t]! ≠ .none) :
    ∃ j' s' tl', W = .tele t j' s' tl' ∧ s'.length = j' ∧
      (∀ (k : Nat) (hk : k < s'.length), Valid p S (sideAt p t k) s'[k]) ∧
      ((1 ≤ j' ∧ j' < p.spineLen[t]! ∧ tl' = .share (spineAt p t j') ∧
          S (spineAt p t j') = true) ∨
        (j' = p.spineLen[t]! ∧ Valid p S p.tail[t]! tl')) := by
  cases h with
  | share => simp [WTree.isShare] at hns
  | node hf => exact absurd hf hft
  | teleCut _ hj1 hj hlen hsides hS => exact ⟨_, _, _, rfl, hlen, hsides, Or.inl ⟨hj1, hj, rfl, hS⟩⟩
  | teleFull _ hlen hsides htail => exact ⟨_, _, _, rfl, hlen, hsides, Or.inr ⟨rfl, htail⟩⟩

/-- **Unsharing.** Replacing the Shares of `t` by an inline writing `W` of
`t` gives a writing without `t` that is longer by at most `cost W - w` per
replaced Share (telescope headers are subadditive). -/
theorem PrepWF.unshare_spec {p : Prep} (hp : PrepWF p) (w : Nat) {A A' : Nat → Bool} {t : Nat}
    (htn : t < p.dag.size) (hA' : ∀ y, A' y = true ↔ (A y = true ∧ y ≠ t)) {W : WTree}
    (hW : Valid p A' t W) (hWs : W.isShare = false) :
    ∀ {x : Nat} {T : WTree}, Valid p A x T → x < p.dag.size →
      Valid p A' x (WTree.unshare p t W T) ∧
        (T.isShare = false → (WTree.unshare p t W T).isShare = false) ∧
        (WTree.unshare p t W T).cost p w + T.shares.count t * w ≤
          T.cost p w + T.shares.count t * W.cost p w := by
  intro x T h
  induction h with
  | @share x hS =>
    intro hx
    by_cases hxt : x = t
    · subst hxt
      simp only [WTree.unshare, if_true, WTree.shares, count_singleton', WTree.cost]
      refine ⟨hW, fun h => by simp [WTree.isShare] at h, by omega⟩
    · simp only [WTree.unshare, hxt, if_false, WTree.shares, count_singleton', WTree.isShare,
        WTree.label]
      refine ⟨.share ((hA' x).mpr ⟨hS, hxt⟩), fun h => by simp at h, by omega⟩
  | @node x kids hf hlen hkids ih =>
    intro hx
    have hk : ∀ (i : Nat) (hi : i < kids.length),
        Valid p A' ((p.dag.node x).child i) (WTree.unshare p t W kids[i]) ∧
          (WTree.unshare p t W kids[i]).cost p w + kids[i].shares.count t * w ≤
            kids[i].cost p w + kids[i].shares.count t * W.cost p w := by
      intro i hi
      have hc := hp.dag.childAt_lt hx (k := i) (by omega)
      obtain ⟨h1, _, h3⟩ := ih i hi (by omega)
      exact ⟨h1, h3⟩
    simp only [WTree.unshare, unshares_eq, WTree.isShare, Bool.false_and]
    refine ⟨.node hf (by simp [hlen]) fun i hi => by
      simp only [List.getElem_map]
      exact (hk i (by simpa using hi)).1, fun _ => trivial, ?_⟩
    simp only [WTree.cost, WTree.costs_eq, List.map_map, Function.comp_def, WTree.shares,
      sharess_count]
    have := sum_ineq2 (fun T => (WTree.unshare p t W T).cost p w) (fun T => T.shares.count t)
      (WTree.cost p w) (fun _ => 0) w (W.cost p w) kids (fun T hT => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        exact (hk i hi).2)
    omega
  | @teleCut x j sides hf hj1 hj hlen hsides hS ih =>
    intro hx
    have hside : ∀ (k : Nat) (hk : k < sides.length),
        Valid p A' (sideAt p x k) (WTree.unshare p t W sides[k]) ∧
          (WTree.unshare p t W sides[k]).cost p w + sides[k].shares.count t * w ≤
            sides[k].cost p w + sides[k].shares.count t * W.cost p w := by
      intro k hk
      have hsl := hp.sideAt_lt hx hf (k := k) (by omega)
      obtain ⟨h1, _, h3⟩ := ih k hk (by omega)
      exact ⟨h1, h3⟩
    have hsum := sum_ineq2 (fun T => (WTree.unshare p t W T).cost p w) (fun T => T.shares.count t)
      (WTree.cost p w) (fun _ => 0) w (W.cost p w) sides (fun T hT => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        exact (hside i hi).2)
    have hL1 : ∀ (k : Nat) (hk : k < (sides.map (WTree.unshare p t W)).length),
        Valid p A' (sideAt p x k) (sides.map (WTree.unshare p t W))[k] := by
      intro k hk
      simp only [List.getElem_map]
      exact (hside k (by simpa using hk)).1
    simp only [WTree.unshare, unshares_eq, unshareTele]
    by_cases hut : spineAt p x j = t
    · rw [if_pos ⟨hut, hj⟩]
      obtain ⟨hts, htf, htlen, httail, hspat, hsideat, hse⟩ := hp.spine_shift hx hf (k := j) hj
      rw [hut] at hts htf htlen httail hspat hsideat hse
      have hft : p.family[t]! ≠ .none := by rw [htf]; exact hf
      obtain ⟨j', s', tl', hWeq, hlen', hs', hcase⟩ := valid_tele_inv hW hWs hft
      have hj'1 : 1 ≤ j' := by
        rcases hcase with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · obtain ⟨hl1', _⟩ := hp.spine t hts hft
          omega
      have hT := tag4Size_add_le hj1 hj'1
      have hcW : W.cost p w = tag4Size j' + j' * (p.dag.node t).sideExtra +
          (s'.map (WTree.cost p w)).sum + tl'.cost p w := by
        rw [hWeq]; simp only [WTree.cost, WTree.costs_eq]
      have hmerge : WTree.merge x j (sides.map (WTree.unshare p t W)) W =
          .tele x (j + j') (sides.map (WTree.unshare p t W) ++ s') tl' := by
        rw [hWeq]; rfl
      rw [hmerge]
      have hsidesV : ∀ (k : Nat) (hk : k < ((sides.map (WTree.unshare p t W)) ++ s').length),
          Valid p A' (sideAt p x k) ((sides.map (WTree.unshare p t W)) ++ s')[k] := by
        intro k hk
        rw [List.getElem_append]
        split
        · rename_i hkj
          exact hL1 k hkj
        · rename_i hkj
          have hk' : k - (sides.map (WTree.unshare p t W)).length < s'.length := by
            simp only [List.length_append] at hk
            omega
          have := hs' _ hk'
          rw [hsideat] at this
          have e : j + (k - (sides.map (WTree.unshare p t W)).length) = k := by
            simp only [List.length_map] at hkj ⊢
            omega
          rwa [e] at this
      have hlenL : ((sides.map (WTree.unshare p t W)) ++ s').length = j + j' := by
        simp [hlen, hlen']
      have hcost : (WTree.tele x (j + j') (sides.map (WTree.unshare p t W) ++ s') tl').cost p w +
            (WTree.tele x j sides (.share (spineAt p x j))).shares.count t * w ≤
          (WTree.tele x j sides (.share (spineAt p x j))).cost p w +
            (WTree.tele x j sides (.share (spineAt p x j))).shares.count t * W.cost p w := by
        simp only [WTree.cost, WTree.costs_eq, List.map_append, List.sum_append, List.map_map,
          Function.comp_def, WTree.shares, sharess_count, List.count_append, count_singleton', hut,
          if_true]
        rw [hse] at hcW
        simp only [Nat.add_mul, Nat.one_mul] at hsum ⊢
        omega
      rcases hcase with ⟨_, hj', htl', hA'u⟩ | ⟨hj', htl'⟩
      · have hu : spineAt p t j' = spineAt p x (j + j') := hspat j'
        refine ⟨?_, fun _ => rfl, hcost⟩
        rw [htl', hu]
        exact .teleCut hf (by omega) (by rw [htlen] at hj'; omega) hlenL hsidesV
          (by rw [← hu]; exact hA'u)
      · have hlenx : j + j' = p.spineLen[x]! := by rw [hj', htlen]; omega
        refine ⟨?_, fun _ => rfl, hcost⟩
        rw [hlenx]
        exact .teleFull hf (by rw [hlenL, hlenx]) hsidesV (by rw [← httail]; exact htl')
    · rw [if_neg (fun h => hut h.1)]
      simp only [WTree.unshare, hut, if_false]
      refine ⟨.teleCut hf hj1 hj (by simp [hlen]) hL1 ((hA' _).mpr ⟨hS, hut⟩), fun _ => rfl, ?_⟩
      simp only [WTree.cost, WTree.costs_eq, List.map_map, Function.comp_def, WTree.shares,
        sharess_count, List.count_append, count_singleton', hut, if_false, Nat.add_zero]
      omega
  | @teleFull x sides tail hf hlen hsides htail ih iht =>
    intro hx
    obtain ⟨hl1, _, _, htl, _⟩ := hp.spine x hx hf
    have hside : ∀ (k : Nat) (hk : k < sides.length),
        Valid p A' (sideAt p x k) (WTree.unshare p t W sides[k]) ∧
          (WTree.unshare p t W sides[k]).cost p w + sides[k].shares.count t * w ≤
            sides[k].cost p w + sides[k].shares.count t * W.cost p w := by
      intro k hk
      have hsl := hp.sideAt_lt hx hf (k := k) (by omega)
      obtain ⟨h1, _, h3⟩ := ih k hk (by omega)
      exact ⟨h1, h3⟩
    have hsum := sum_ineq2 (fun T => (WTree.unshare p t W T).cost p w) (fun T => T.shares.count t)
      (WTree.cost p w) (fun _ => 0) w (W.cost p w) sides (fun T hT => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        exact (hside i hi).2)
    have hL1 : ∀ (k : Nat) (hk : k < (sides.map (WTree.unshare p t W)).length),
        Valid p A' (sideAt p x k) (sides.map (WTree.unshare p t W))[k] := by
      intro k hk
      simp only [List.getElem_map]
      exact (hside k (by simpa using hk)).1
    obtain ⟨ht1, _, ht3⟩ := iht (by omega)
    have hU : unshareTele p t W x p.spineLen[x]! (sides.map (WTree.unshare p t W)) tail
        (WTree.unshare p t W tail) =
        .tele x p.spineLen[x]! (sides.map (WTree.unshare p t W)) (WTree.unshare p t W tail) := by
      unfold unshareTele
      split
      · rw [if_neg (fun h => Nat.lt_irrefl _ h.2)]
      · rfl
    simp only [WTree.unshare, unshares_eq]
    rw [hU]
    refine ⟨.teleFull hf (by simp [hlen]) hL1 ht1, fun _ => rfl, ?_⟩
    simp only [WTree.cost, WTree.costs_eq, List.map_map, Function.comp_def, WTree.shares,
      sharess_count, List.count_append]
    simp only [Nat.add_mul] at ht3 ⊢
    omega

theorem sum_erase {S : List Nat} {t : Nat} (h : t ∈ S) (f : Nat → Nat) :
    (S.map f).sum = f t + ((S.erase t).map f).sum := by
  have hperm := List.perm_cons_erase h
  rw [(hperm.map f).sum_nat, List.map_cons, List.sum_cons]

theorem forall₂_map_of {R R' : Nat → WTree → Prop} (g : WTree → WTree) :
    ∀ {xs : List Nat} {ys : List WTree}, List.Forall₂ R xs ys →
      (∀ x ∈ xs, ∀ y, R x y → R' x (g y)) → List.Forall₂ R' xs (ys.map g)
  | _, _, .nil, _ => .nil
  | _, _, .cons h hs, hg =>
    .cons (hg _ List.mem_cons_self _ h)
      (forall₂_map_of g hs fun x hx y hxy => hg x (List.mem_cons_of_mem _ hx) y hxy)

/-- **Removal.** Dropping a stored `t` and writing its entry `W` at each of its
`R` Shares (continuing telescopes through it at cuts) costs at most
`R · (cost W - w) - cost W`: `L(S \ {t}) + cost W + R·w ≤ cost(E) + R·cost W`. -/
theorem PrepWF.removal {p : Prep} (hp : PrepWF p) (w : Nat) {S : List Nat} (hSnd : S.Nodup)
    (hSin : ∀ s ∈ S, s < p.dag.size) {roots : List Nat} (hroots : ∀ r ∈ roots, r < p.dag.size)
    {t : Nat} (htS : t ∈ S) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R) :
    uniformCost p w (fun y => decide (y ∈ S.erase t)) (S.erase t) roots + (E t).cost p w +
        encRefs S E R t * w ≤
      encodingCost p w S E R + encRefs S E R t * (E t).cost p w := by
  have hA' : ∀ y, decide (y ∈ S.erase t) = true ↔ (decide (y ∈ S) = true ∧ y ≠ t) := by
    intro y
    simp only [decide_eq_true_eq, hSnd.mem_erase_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have htn := hSin t htS
  obtain ⟨hWv, hWs⟩ := hEnc.1 t htS
  have hW' : Valid p (fun y => decide (y ∈ S.erase t)) t (E t) := Valid.restrict hWv fun s hs => by
    obtain ⟨h1, _, h3⟩ := hp.shares_lt hWv htn s hs
    have := h3 hWs
    exact (hA' s).mpr ⟨h1, by omega⟩
  have hcnt0 : (E t).shares.count t = 0 := hp.shares_count_zero hWv htn hWs t (Nat.le_refl _)
  have hU : ∀ {x : Nat} {T : WTree}, Valid p (fun y => decide (y ∈ S)) x T → x < p.dag.size →
      Valid p (fun y => decide (y ∈ S.erase t)) x (WTree.unshare p t (E t) T) ∧
        (T.isShare = false → (WTree.unshare p t (E t) T).isShare = false) ∧
        (WTree.unshare p t (E t) T).cost p w + T.shares.count t * w ≤
          T.cost p w + T.shares.count t * (E t).cost p w :=
    fun hv hx => hp.unshare_spec w htn hA' hW' hWs hv hx
  have hEnc' : EncodingWF p (fun y => decide (y ∈ S.erase t)) (S.erase t)
      (fun s => WTree.unshare p t (E t) (E s)) roots (R.map (WTree.unshare p t (E t))) := by
    refine ⟨fun s hs => ?_, forall₂_map_of _ hEnc.2 fun r hr T hT => (hU hT (hroots r hr)).1⟩
    have hsS := (hSnd.mem_erase_iff.mp hs).2
    obtain ⟨h1, h2, _⟩ := hU (hEnc.1 s hsS).1 (hSin s hsS)
    exact ⟨h1, h2 (hEnc.1 s hsS).2⟩
  have hle := hp.uniformCost_le w _ (fun s hs => hSin s (List.mem_of_mem_erase hs)) hroots hEnc'
  unfold encodingCost at hle ⊢
  have hsumS := sum_ineq2 (fun s => (WTree.unshare p t (E t) (E s)).cost p w)
    (fun s => (E s).shares.count t) (fun s => (E s).cost p w) (fun _ => 0) w ((E t).cost p w)
    (S.erase t) (fun s hs => by
      have hsS := (hSnd.mem_erase_iff.mp hs).2
      exact (hU (hEnc.1 s hsS).1 (hSin s hsS)).2.2)
  have hsumR := sum_ineq2 (fun T => (WTree.unshare p t (E t) T).cost p w)
    (fun T => T.shares.count t) (WTree.cost p w) (fun _ => 0) w ((E t).cost p w) R
    (fun T hT => by
      obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
      exact (hU hr (hroots r hrm)).2.2)
  have hcS := sum_erase htS (fun s => (E s).cost p w)
  have hrS := sum_erase htS (fun s => (E s).shares.count t)
  simp only [hcnt0, Nat.zero_add] at hrS
  have htag := tag0Size_mono (show (S.erase t).length ≤ S.length by
    rw [List.length_erase_of_mem htS]; omega)
  unfold encRefs
  simp only [List.map_map, Function.comp_def] at hle
  simp only [Nat.add_mul] at hsumS hsumR ⊢
  rw [hrS]
  omega

theorem count_zero_of_sum_zero {α : Type} {f : α → Nat} {l : List α} (h : (l.map f).sum = 0)
    {a : α} (ha : a ∈ l) : f a = 0 := by
  have := le_sum_map_of_mem f ha
  omega

theorem forall₂_imp_mem2 {α β : Type} {R R' : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ x ∈ xs, ∀ y ∈ ys, R x y → R' x y) → List.Forall₂ R' xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons hr hs, h =>
    .cons (h _ List.mem_cons_self _ List.mem_cons_self hr)
      (forall₂_imp_mem2 hs fun x hx y hy hxy =>
        h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)

/-- **Unreferenced entries.** An entry that no writing shares can be dropped,
saving its at least one byte. -/
theorem PrepWF.unreferenced {p : Prep} (hp : PrepWF p) (w : Nat) {S : List Nat} (hSnd : S.Nodup)
    (hSin : ∀ s ∈ S, s < p.dag.size) {roots : List Nat} (hroots : ∀ r ∈ roots, r < p.dag.size)
    {s : Nat} (hsS : s ∈ S) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R) (hrefs : encRefs S E R s = 0) :
    uniformCost p w (fun y => decide (y ∈ S.erase s)) (S.erase s) roots + 1 ≤
      encodingCost p w S E R := by
  unfold encRefs at hrefs
  have hS0 : (S.map fun s' => (E s').shares.count s).sum = 0 := by omega
  have hR0 : (R.map fun T => T.shares.count s).sum = 0 := by omega
  have hres : ∀ {x : Nat} {T : WTree}, Valid p (fun y => decide (y ∈ S)) x T → x < p.dag.size →
      T.shares.count s = 0 → Valid p (fun y => decide (y ∈ S.erase s)) x T := by
    intro x T hv hx h0
    apply Valid.restrict hv
    intro s' hs'
    have h1 := (hp.shares_lt hv hx s' hs').1
    simp only [decide_eq_true_eq] at h1 ⊢
    rw [hSnd.mem_erase_iff]
    refine ⟨fun h => ?_, h1⟩
    subst h
    rw [List.count_eq_zero] at h0
    exact h0 hs'
  have hEnc' : EncodingWF p (fun y => decide (y ∈ S.erase s)) (S.erase s) E roots R := by
    refine ⟨fun s' hs' => ?_, forall₂_imp_mem2 hEnc.2 fun r hr T hT hv =>
      hres hv (hroots r hr) (count_zero_of_sum_zero hR0 hT)⟩
    have hs'S := (hSnd.mem_erase_iff.mp hs').2
    exact ⟨hres (hEnc.1 s' hs'S).1 (hSin s' hs'S) (count_zero_of_sum_zero hS0 hs'S),
      (hEnc.1 s' hs'S).2⟩
  have hle := hp.uniformCost_le w _ (fun s hs => hSin s (List.mem_of_mem_erase hs)) hroots hEnc'
  have hpos := hp.cost_pos (w := w) (hEnc.1 s hsS).1 (hSin s hsS) (hEnc.1 s hsS).2
  have hcS := sum_erase hsS (fun s => (E s).cost p w)
  have htag := tag0Size_mono (show (S.erase s).length ≤ S.length by
    rw [List.length_erase_of_mem hsS]; omega)
  unfold encodingCost at hle ⊢
  omega

/-- In an attaining encoding every entry attains its inline optimum. -/
theorem PrepWF.entries_attain {p : Prep} (hp : PrepWF p) (w : Nat) {A : Nat → Bool}
    {S roots : List Nat} {E : Nat → WTree} {R : List WTree}
    (hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size)
    (hEnc : EncodingWF p A S E roots R)
    (hcost : encodingCost p w S E R = uniformCost p w A S roots) :
    ∀ s ∈ S, (E s).cost p w = uInl p w A s := by
  have he : ∀ s ∈ S, uInl p w A s ≤ (E s).cost p w :=
    fun s hs => (hp.valid_cost w A (hEnc.1 s hs).1 (hSin s hs)).2 (hEnc.1 s hs).2
  have hr : (roots.map (uCost p w A)).sum ≤ (R.map (WTree.cost p w)).sum :=
    forall₂_sum_le hEnc.2 fun r hr T hT => (hp.valid_cost w A hT (hroots r hr)).1
  have hsum : (S.map (uInl p w A)).sum ≤ (S.map fun s => (E s).cost p w).sum :=
    sum_le_sum_of_le S he
  unfold encodingCost uniformCost at hcost
  have heq : (S.map fun s => (E s).cost p w).sum = (S.map (uInl p w A)).sum := by omega
  intro s hs
  have key : ∀ (l : List Nat), (∀ s ∈ l, uInl p w A s ≤ (E s).cost p w) →
      (l.map fun s => (E s).cost p w).sum = (l.map (uInl p w A)).sum →
      ∀ s ∈ l, (E s).cost p w = uInl p w A s := by
    intro l
    induction l with
    | nil => intro _ _ s hs; cases hs
    | cons x xs ih =>
      intro hle hsum s hs
      simp only [List.map_cons, List.sum_cons] at hsum
      have h1 := hle x List.mem_cons_self
      have h2 := sum_le_sum_of_le xs fun s hs => hle s (List.mem_cons_of_mem _ hs)
      rcases List.mem_cons.mp hs with rfl | hs
      · omega
      · exact ih (fun s hs => hle s (List.mem_cons_of_mem _ hs)) (by omega) s hs
  exact key S he heq s hs

/-- An inline writing of `x` writes `x`. -/
theorem PrepWF.written_self {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {x : Nat} {T : WTree}
    (h : Valid p S x T) (hx : x < p.dag.size) (hns : T.isShare = false) : x ∈ T.written p := by
  cases h with
  | share => simp [WTree.isShare] at hns
  | node => simp [WTree.written]
  | teleCut _ hj1 =>
    simp only [WTree.written, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl ⟨0, by omega, rfl⟩)
  | teleFull hf hlen =>
    have hl1 := (hp.spine x hx hf).1
    simp only [WTree.written, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl ⟨0, by omega, rfl⟩)

/-! ## Certain-excluded: no minimum stores the term -/

theorem inClass_erase {dag : Dag} {roots : Array Nat} {X : List Nat} (hX : InClass dag roots X)
    (t : Nat) : InClass dag roots (X.erase t) :=
  ⟨hX.1.erase t, fun s hs => hX.2 s (List.mem_of_mem_erase hs)⟩

/-- In a minimum, every entry is shared somewhere. -/
theorem refs_pos_of_minimum {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {X : List Nat}
    (hX : IsMinimum dag w roots X) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF (Prep.ofDag dag) (fun y => decide (y ∈ X)) X E roots.toList R)
    (hcost : encodingCost (Prep.ofDag dag) w X E R = ulen dag w roots X) :
    ∀ s ∈ X, 1 ≤ encRefs X E R s := by
  intro s hs
  have hp := prepWF_ofDag hwf
  by_cases h0 : encRefs X E R s = 0
  · exfalso
    have hu := hp.unreferenced w hX.1.1 (fun s hs => by rw [ofDag_dag]; exact (hX.1.2 s hs).1)
      (by rw [ofDag_dag]; exact hroots) hs hEnc h0
    have hm := hX.2 _ (inClass_erase hX.1 s)
    unfold ulen at hm hcost
    omega
  · omega

/-- In a minimum, every term is written at most its occurrence count times. -/
theorem writes_le_occ {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {X : List Nat}
    (hX : IsMinimum dag w roots X) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF (Prep.ofDag dag) (fun y => decide (y ∈ X)) X E roots.toList R)
    (hcost : encodingCost (Prep.ofDag dag) w X E R = ulen dag w roots X) :
    ∀ y, y < dag.size → encWrites (Prep.ofDag dag) X E R y ≤ (occurrences dag roots)[y]! := by
  have hp := prepWF_ofDag hwf
  have hXin : ∀ s ∈ X, s < (Prep.ofDag dag).dag.size := fun s hs => by
    rw [ofDag_dag]; exact (hX.1.2 s hs).1
  have hroots' : ∀ r ∈ roots.toList, r < (Prep.ofDag dag).dag.size := by
    rw [ofDag_dag]; exact hroots
  have hrefs := refs_pos_of_minimum hwf roots hroots w hX hEnc hcost
  have key : ∀ m, ∀ y, dag.size - y ≤ m → y < dag.size →
      encWrites (Prep.ofDag dag) X E R y ≤ (occurrences dag roots)[y]! := by
    intro m
    induction m with
    | zero => intro y hym hy; omega
    | succ m ih =>
      intro y hym hy
      have hsl := hp.enc_slots hEnc hXin hroots' (t := y) (by rw [ofDag_dag]; exact hy)
      rw [ofDag_dag] at hsl
      have hcnt : X.count y ≤ encRefs X E R y := by
        rw [hX.1.1.count]
        split
        · rename_i hyX; exact hrefs y hyX
        · omega
      have hsum : ((List.range dag.size).map fun z =>
          encWrites (Prep.ofDag dag) X E R z * edgeAll (Prep.ofDag dag) z y).sum ≤
          ((List.range dag.size).map fun z =>
            edgeAll (Prep.ofDag dag) z y * (occurrences dag roots)[z]!).sum := by
        apply sum_le_sum_of_le
        intro z hz
        rw [List.mem_range] at hz
        by_cases hzy : y < z
        · rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left _ (ih z (by omega) hz)
        · rw [edgeAll_zero_of_le hp (by omega)]
          simp
      rw [occurrences_spec hwf roots hroots hy]
      omega
  intro y hy
  exact key (dag.size - y) y (Nat.le_refl _) hy

/-- In a minimum, a stored term is shared at most its occurrence count times. -/
theorem refs_le_occ {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {X : List Nat}
    (hX : IsMinimum dag w roots X) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF (Prep.ofDag dag) (fun y => decide (y ∈ X)) X E roots.toList R)
    (hcost : encodingCost (Prep.ofDag dag) w X E R = ulen dag w roots X) {t : Nat}
    (htX : t ∈ X) : encRefs X E R t ≤ (occurrences dag roots)[t]! := by
  have hp := prepWF_ofDag hwf
  have hXin : ∀ s ∈ X, s < (Prep.ofDag dag).dag.size := fun s hs => by
    rw [ofDag_dag]; exact (hX.1.2 s hs).1
  have hroots' : ∀ r ∈ roots.toList, r < (Prep.ofDag dag).dag.size := by
    rw [ofDag_dag]; exact hroots
  have htn := (hX.1.2 t htX).1
  have hwr := writes_le_occ hwf roots hroots w hX hEnc hcost
  have hsl := hp.enc_slots hEnc hXin hroots' (t := t) (by rw [ofDag_dag]; exact htn)
  rw [ofDag_dag] at hsl
  have hcnt : X.count t = 1 := by rw [hX.1.1.count, if_pos htX]
  have hw1 : 1 ≤ encWrites (Prep.ofDag dag) X E R t := by
    have h1 : 1 ≤ ((E t).written (Prep.ofDag dag)).count t :=
      List.count_pos_iff.mpr (hp.written_self (hEnc.1 t htX).1 (hXin t htX) (hEnc.1 t htX).2)
    have := le_sum_map_of_mem (fun s => ((E s).written (Prep.ofDag dag)).count t) htX
    unfold encWrites
    omega
  have hsum : ((List.range dag.size).map fun z =>
      encWrites (Prep.ofDag dag) X E R z * edgeAll (Prep.ofDag dag) z t).sum ≤
      ((List.range dag.size).map fun z =>
        edgeAll (Prep.ofDag dag) z t * (occurrences dag roots)[z]!).sum := by
    apply sum_le_sum_of_le
    intro z hz
    rw [List.mem_range] at hz
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (hwr z hz)
  rw [occurrences_spec hwf roots hroots htn]
  omega

/-- `C_∅`, the unshared standalone length, is the inline cost with nothing
available. -/
theorem base_eq_uInl {dag : Dag} (hwf : DagWF dag) (w : Nat) {t : Nat} (ht : t < dag.size) :
    (Prep.ofDag dag).base[t]! = uInl (Prep.ofDag dag) w (fun _ => false) t := by
  have hp := prepWF_ofDag hwf
  have hrow := hp.evalFrom_spec (w := w) (avail := fun _ => false)
    (Array.replicate dag.size none)
    (fun u => by
      simp only [widthOf, Array.getElem?_replicate, Bool.false_eq_true, if_false]
      split <;> rfl)
    { cost := Array.replicate dag.size 0, sides := Array.replicate dag.size 0,
      below := Array.replicate dag.size none }
    (by simp [ofDag_dag]) (Array.replicate dag.size true)
    (fun t ht => by
      rw [ofDag_dag] at ht
      simp [getElem!_def, Array.getElem?_replicate, ht])
    t (by rw [ofDag_dag]; exact ht)
  have hb : (Prep.ofDag dag).base = (evalFrom (Prep.ofDag dag).dag (Prep.ofDag dag).family
      (Prep.ofDag dag).spineLen (Prep.ofDag dag).tail
      { cost := Array.replicate dag.size 0, sides := Array.replicate dag.size 0,
        below := Array.replicate dag.size none }
      (Array.replicate dag.size none) (Array.replicate dag.size true)).cost := rfl
  rw [hb, hrow.1, hp.uCost_eq w _ t (by rw [ofDag_dag]; exact ht)]
  unfold costOf
  simp only [Bool.false_eq_true, if_false]
  rfl

/-- Inline costs only drop when terms become available. -/
theorem PrepWF.uInl_le_empty {p : Prep} (hp : PrepWF p) (w : Nat) (A : Nat → Bool) {t : Nat}
    (ht : t < p.dag.size) : uInl p w A t ≤ uInl p w (fun _ => false) t := by
  obtain ⟨T, hT, hTs, hTc⟩ := (hp.exists_opt w (fun _ => false) t ht).2
  have hT' : Valid p A t T := Valid.mono (fun y h => by simp at h) hT
  have := (hp.valid_cost w A hT' ht).2 hTs
  omega

/-- **Stage 3 (certain-excluded).** A term with `(occ - 1)·size < occ·w`
(`size` the unshared length `C_∅`) is in no minimum over the restricted
class: removing it from a minimum would be strictly shorter. -/
theorem excluded_of_minimum {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {X : List Nat}
    (hX : IsMinimum dag w roots X) {t : Nat} (htn : t < dag.size)
    (hce : ((occurrences dag roots)[t]! - 1) * (Prep.ofDag dag).base[t]! <
      (occurrences dag roots)[t]! * w) : t ∉ X := by
  intro htX
  have hp := prepWF_ofDag hwf
  have hXin : ∀ s ∈ X, s < (Prep.ofDag dag).dag.size := fun s hs => by
    rw [ofDag_dag]; exact (hX.1.2 s hs).1
  have hroots' : ∀ r ∈ roots.toList, r < (Prep.ofDag dag).dag.size := by
    rw [ofDag_dag]; exact hroots
  obtain ⟨E, R, hEnc, hcost⟩ :=
    hp.uniformCost_attained w (fun y => decide (y ∈ X)) X roots.toList hXin hroots'
  have hI := hp.entries_attain w hXin hroots' hEnc hcost t htX
  have hrem := hp.removal w hX.1.1 hXin hroots' htX hEnc
  have hmin := hX.2 _ (inClass_erase hX.1 t)
  have hRocc := refs_le_occ hwf roots hroots w hX hEnc hcost htX
  have hI1 := hp.cost_pos (w := w) (hEnc.1 t htX).1 (hXin t htX) (hEnc.1 t htX).2
  have hIb : (E t).cost (Prep.ofDag dag) w ≤ (Prep.ofDag dag).base[t]! := by
    rw [hI, base_eq_uInl hwf w htn]
    exact hp.uInl_le_empty w _ (by rw [ofDag_dag]; exact htn)
  unfold ulen at hmin
  rw [hcost] at hrem
  generalize (E t).cost (Prep.ofDag dag) w = I at hrem hI1 hIb
  generalize encRefs X E R t = Rf at hrem hRocc
  generalize (occurrences dag roots)[t]! = o at hRocc hce
  generalize (Prep.ofDag dag).base[t]! = B at hIb hce
  have h1 : I + Rf * w ≤ Rf * I := by omega
  have hRf : 1 ≤ Rf := by
    rcases Nat.eq_zero_or_pos Rf with h | h
    · subst h; simp at h1; omega
    · exact h
  have hIw : w < I := by
    have : Rf * w < Rf * I := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  -- (o-1)·B - o·w = (Rf-1)·B - Rf·w + (o-Rf)·(B-w) ≥ (Rf-1)·I - Rf·w ≥ 0
  have e1 := int_mul_le_mul_left' (show (I : _root_.Int) ≤ B by omega)
    (show (0 : _root_.Int) ≤ (Rf : _root_.Int) - 1 by omega)
  have e2 := _root_.Int.mul_nonneg (show (0 : _root_.Int) ≤ (o : _root_.Int) - Rf by omega)
    (show (0 : _root_.Int) ≤ (B : _root_.Int) - w by omega)
  have h1' : ((I + Rf * w : Nat) : _root_.Int) ≤ ((Rf * I : Nat) : _root_.Int) :=
    _root_.Int.ofNat_le.mpr h1
  have hce' : (((o - 1) * B : Nat) : _root_.Int) < ((o * w : Nat) : _root_.Int) :=
    _root_.Int.ofNat_lt.mpr hce
  simp only [_root_.Int.natCast_add, _root_.Int.natCast_mul] at h1'
  rw [_root_.Int.natCast_mul, _root_.Int.natCast_mul, _root_.Int.ofNat_sub (by omega)] at hce'
  simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.mul_one,
    _root_.Int.natCast_one] at e1 e2 hce'
  rw [_root_.Int.mul_comm (Rf : _root_.Int) (I : _root_.Int)] at e1 h1'
  omega

/-! ## The executable classification -/

theorem vis_head_le {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (ms : Array Bool) {t : Nat} (ht : t < dag.size) :
    (visibleCounts dag roots ms).2[t]! ≤ (visibleCounts dag roots ms).1[t]! := by
  obtain ⟨e1, e2⟩ := visibleCounts_spec hwf roots hroots ms ht
  rw [e1, e2]
  apply Nat.add_le_add_left
  apply sum_le_sum_of_le
  intro y _
  unfold edgeAll
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem gain_d_pos {p : Prep} {b : UBounds} {w t d h : Nat} (hhd : h ≤ d)
    (hg : 1 ≤ storedGainC p b w t d h) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0
    have hh0 : h = 0 := by omega
    subst hh0
    unfold storedGainC at hg
    simp only [_root_.Int.ofNat_eq_natCast, _root_.Int.natCast_zero, _root_.Int.zero_sub,
      _root_.Int.zero_mul, _root_.Int.sub_zero] at hg
    split at hg
    · have := _root_.Int.natCast_nonneg (b.inlineLB[t]!); omega
    · split at hg
      · omega
      · have := _root_.Int.natCast_nonneg (b.mergedLB[t]!)
        have := _root_.Int.natCast_nonneg (tag4Size p.spineLen[t]!)
        omega
  · exact h0

theorem getElem!_range_map {α : Type} [Inhabited α] (f : Nat → α) {n t : Nat} (ht : t < n) :
    ((Array.range n).map f)[t]! = f t := by
  simp [getElem!_def, ht]

/-- Every minimum stores only search candidates. -/
theorem minimum_in_candidates {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {X : List Nat}
    (hX : IsMinimum dag w roots X) :
    ∀ s ∈ X, (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)[s]! = true := by
  intro s hs
  have hsn := (hX.1.2 s hs).1
  unfold searchCandidates
  rw [getElem!_range_map _ (by rw [ofDag_dag]; exact hsn)]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  refine ⟨?_, (hX.1.2 s hs).2⟩
  cases hce : certainExcludedTest (Prep.ofDag dag) (graphFacts dag roots) w s
  · rfl
  · exfalso
    unfold certainExcludedTest at hce
    simp only [decide_eq_true_eq] at hce
    exact excluded_of_minimum hwf roots hroots w hX hsn hce hs

/-- **Stage 3, the executable classes.** With the root-level candidates,
bounds and visible counts (as `uniformChoose` computes them): a
certain-excluded term is in no minimum, and a term classified certain-stored
at threshold 2 (or at threshold 1 when `|X|` and `|X| + 1` share a `Tag0`
bracket) is in every minimum `X`. -/
theorem classify_sound {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (w : Nat) {X : List Nat} (hX : IsMinimum dag w roots X) {t : Nat} (htn : t < dag.size)
    (θ : _root_.Int)
    (hθ : θ = 2 ∨ (θ = 1 ∧ tag0Size (X.length + 1) = tag0Size X.length)) :
    let p := Prep.ofDag dag
    let f := graphFacts dag roots
    let cand := searchCandidates p f w
    let cls := classifyWith p f w (uniformBounds p w cand) (visibleCounts dag roots cand) θ
    (cls[t]! = .certainExcluded → t ∉ X) ∧ (cls[t]! = .certainStored → t ∈ X) := by
  intro p f cand cls
  have hcls : cls[t]! = (if certainExcludedTest p f w t then .certainExcluded
      else if f.deg[t]! < 2 then .lowDegree
      else if storedGainC p (uniformBounds p w cand) w t (visibleCounts dag roots cand).1[t]!
          (visibleCounts dag roots cand).2[t]! ≥ θ then .certainStored
      else .uncertain) := by
    simp only [cls, classifyWith]
    rw [getElem!_range_map _ (by simp only [p]; rw [ofDag_dag]; exact htn)]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcls] at h
    split at h
    · rename_i hce
      unfold certainExcludedTest at hce
      simp only [decide_eq_true_eq] at hce
      exact excluded_of_minimum hwf roots hroots w hX htn hce
    · split at h <;> (try split at h) <;> cases h
  · rw [hcls] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i _ hdeg hg
          have hhd := vis_head_le hwf roots hroots cand htn
          have hg1 : 1 ≤ storedGainC p (uniformBounds p w cand) w t
              (visibleCounts dag roots cand).1[t]! (visibleCounts dag roots cand).2[t]! := by
            rcases hθ with rfl | ⟨rfl, _⟩ <;> omega
          exact stored_in_minimum hwf roots hroots hreach w cand hX
            (minimum_in_candidates hwf roots hroots w hX) htn (Nat.le_of_not_lt hdeg) (Nat.le_refl _)
            (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hhd (gain_d_pos hhd hg1)
            (by rcases hθ with rfl | ⟨rfl, hb⟩
                · exact Or.inl hg
                · exact Or.inr ⟨hg, hb⟩)
        · cases h

theorem filter_size_range_map {α : Type} [Inhabited α] (n : Nat) (F : Nat → α) (P : α → Bool) :
    (((Array.range n).map F).filter P).size =
      ((List.range n).filter fun t => P ((Array.range n).map F)[t]!).length := by
  rw [Array.size_eq_length_toList, Array.toList_filter, Array.toList_map, Array.toList_range,
    List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro t ht
  rw [List.mem_range] at ht
  simp only [Function.comp_def, getElem!_range_map F ht]

/-- **The threshold-1 test of `uniformChoose`.** If the candidates and the
gain-2 terms fill the same `Tag0` bracket, then for every minimum `X` and
candidate `t ∉ X`, `|X|` and `|X| + 1` share a bracket (so threshold 1 is
sound in `classify_sound` and `stored_in_minimum`). -/
theorem threshold_one_sound {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    (w : Nat) {X : List Nat} (hX : IsMinimum dag w roots X) {t : Nat} (htn : t < dag.size) :
    let p := Prep.ofDag dag
    let f := graphFacts dag roots
    let cand := searchCandidates p f w
    let cls2 := classifyWith p f w (uniformBounds p w cand) (visibleCounts dag roots cand) 2
    tag0Size (cand.filter id).size = tag0Size (cls2.filter (· == .certainStored)).size →
    cand[t]! = true → t ∉ X → tag0Size (X.length + 1) = tag0Size X.length := by
  intro p f cand cls2 hbr htc htX
  have hn : (Prep.ofDag dag).dag.size = dag.size := by rw [ofDag_dag]
  let G := (List.range dag.size).filter fun s => cls2[s]! == .certainStored
  let C := (List.range dag.size).filter fun s => cand[s]!
  have hG : (cls2.filter (· == .certainStored)).size = G.length := by
    simp only [cls2, classifyWith, G]
    rw [filter_size_range_map, hn]
  have hC : (cand.filter id).size = C.length := by
    simp only [cand, searchCandidates, C]
    rw [filter_size_range_map, hn]
    rfl
  rw [hG, hC] at hbr
  refine same_bracket (G := G) (C := C) ?_ ?_ (List.nodup_range.filter _) hX.1.1
    (List.nodup_range.filter _) ?_ htX hbr
  · intro g hg
    simp only [G, List.mem_filter, List.mem_range] at hg
    have hcs : cls2[g]! = .certainStored := by
      have h2 := hg.2
      revert h2
      cases cls2[g]! <;> intro h <;> first | rfl | (exact absurd h (by decide))
    exact (classify_sound hwf roots hroots hreach w hX hg.1 2 (Or.inl rfl)).2 hcs
  · intro x hx
    simp only [C, List.mem_filter, List.mem_range]
    exact ⟨(hX.1.2 x hx).1, minimum_in_candidates hwf roots hroots w hX x hx⟩
  · simp only [C, List.mem_filter, List.mem_range]
    exact ⟨htn, htc⟩

end Ix.Compile.Verify.UniformModel
