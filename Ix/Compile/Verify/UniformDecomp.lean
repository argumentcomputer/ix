import Ix.Compile.Verify.UniformClasses

/-!
# Stage 4 (part): additive decomposition of the uniform cost

With an *opaque* set `O` of available terms that cost exactly `w` wherever
they occur and end every telescope running into them (`OpaqueAt`; the
certain-stored terms are opaque in every candidate set containing them,
`certainStored_opaque`):

* **Domination** (`teleFrom_dom`): a telescope's cheapest ending is decided
  at or before its first opaque spine node.
* **Locality** (`PrepWF.uCost_local`): the costs of a term depend only on the
  availability of the terms reachable from it along DAG paths whose
  intermediate terms are not opaque (`NReach`).
* **Modularity** (`PrepWF.uCost_modular`, `uniformCost_modular`): if no
  available non-opaque term reaches both of two added sets `Z₁`, `Z₂`,
  adding both changes every cost, and the uniform length up to the count's
  TagN, by the sum of adding each.
* **Components** (`components_modular`): with `cs` the certain-stored terms
  and a labeling of the uncertain terms that is constant along non-opaque
  paths, the uniform length without the TagN is modular across labels.
* **Search bound** (`lower_bound_sound`): the cost with every undecided term
  available and only the decided entries paid is at most the length of
  every completion.

The rest of Stage 4 builds on these facts in other modules: that the
uncertain components are such a labeling (`componentsChecked_spec`,
`UniformChecks`), the invariants of the component search
(`UniformSearchSpec`), and the final theorems, a successful run stores a
minimum (`optimizeUniform_minimum`) and the `setPrec`-least one
(`optimizeUniform_least`, both in `UniformOptimality`).
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact

/-! ## Paths that avoid opaque terms -/

/-- `v` is reachable from `y` along DAG edges whose intermediate terms are not
opaque (the endpoints may be). -/
inductive NReach (p : Prep) (O : Nat → Bool) (y : Nat) : Nat → Prop
  | refl : NReach p O y y
  | tail {u v : Nat} : NReach p O y u → (u = y ∨ O u = false) →
      (∃ k, k < (p.dag.node u).head.arity ∧ (p.dag.node u).child k = v) → NReach p O y v

theorem NReach.edge {p : Prep} {O : Nat → Bool} {y k : Nat}
    (hk : k < (p.dag.node y).head.arity) : NReach p O y ((p.dag.node y).child k) :=
  .tail .refl (Or.inl rfl) ⟨k, hk, rfl⟩

/-- A path from a non-opaque child extends to its parent. -/
theorem NReach.of_child {p : Prep} {O : Nat → Bool} {y c : Nat} (hc : O c = false)
    (hyc : ∃ k, k < (p.dag.node y).head.arity ∧ (p.dag.node y).child k = c) :
    ∀ {v : Nat}, NReach p O c v → NReach p O y v := by
  intro v h
  induction h with
  | refl => exact .tail .refl (Or.inl rfl) hyc
  | tail _ hu he ih =>
    refine .tail ih (Or.inr ?_) he
    rcases hu with rfl | hu
    · exact hc
    · exact hu

/-- A path extends through a non-opaque intermediate term. -/
theorem NReach.trans {p : Prep} {O : Nat → Bool} {y u : Nat} (h1 : NReach p O y u)
    (hu : u = y ∨ O u = false) : ∀ {v : Nat}, NReach p O u v → NReach p O y v := by
  intro v h
  induction h with
  | refl => exact h1
  | tail _ hw he ih =>
    refine .tail ih ?_ he
    rcases hw with rfl | hw
    · exact hu
    · exact Or.inr hw

theorem PrepWF.snext_edge {p : Prep} (hp : PrepWF p) {t : Nat} (ht : t < p.dag.size)
    (hf : p.family[t]! ≠ .none) :
    ∃ k, k < (p.dag.node t).head.arity ∧ (p.dag.node t).child k = snext p t := by
  have hft : (p.dag.node t).head.family ≠ .none := by rw [← hp.family t ht]; exact hf
  unfold snext Node.spineNext
  cases hh : (p.dag.node t).head <;> simp only [hh, Head.family, ne_eq, not_true_eq_false] at hft
  · exact ⟨0, by simp [Head.arity], rfl⟩
  · exact ⟨1, by simp [Head.arity], rfl⟩
  · exact ⟨1, by simp [Head.arity], rfl⟩

theorem PrepWF.side_edge {p : Prep} (hp : PrepWF p) {t : Nat} (ht : t < p.dag.size)
    (hf : p.family[t]! ≠ .none) :
    ∃ k, k < (p.dag.node t).head.arity ∧ (p.dag.node t).child k = (p.dag.node t).sideChild := by
  have hft : (p.dag.node t).head.family ≠ .none := by rw [← hp.family t ht]; exact hf
  unfold Node.sideChild
  cases hh : (p.dag.node t).head <;> simp only [hh, Head.family, ne_eq, not_true_eq_false] at hft
  · exact ⟨1, by simp [Head.arity], rfl⟩
  · exact ⟨0, by simp [Head.arity], rfl⟩
  · exact ⟨0, by simp [Head.arity], rfl⟩

/-- Along a telescope spine whose nodes `k, …, j-1` after `k` are not opaque,
the spine node `j` is reachable from the spine node `k`. -/
theorem PrepWF.spine_nreach {p : Prep} (hp : PrepWF p) {O : Nat → Bool} {y : Nat}
    (hy : y < p.dag.size) (hf : p.family[y]! ≠ .none) {k : Nat} :
    ∀ j, k ≤ j → j < p.spineLen[y]! → (∀ i, k < i → i < j → O (spineAt p y i) = false) →
      NReach p O (spineAt p y k) (spineAt p y j) := by
  intro j
  induction j with
  | zero => intro hkj _ _; rw [show k = 0 by omega]; exact .refl
  | succ j ih =>
    intro hkj hjl hO
    by_cases hkj' : k = j + 1
    · subst hkj'; exact .refl
    · have h1 := ih (by omega) (by omega) (fun i hi1 hi2 => hO i hi1 (by omega))
      obtain ⟨hts, htf, _⟩ := hp.spine_shift hy hf (k := j) (by omega)
      have hf' : p.family[spineAt p y j]! ≠ .none := by rw [htf]; exact hf
      refine .tail h1 ?_ ?_
      · by_cases hjk : j = k
        · exact Or.inl (by rw [hjk])
        · exact Or.inr (hO j (by omega) (by omega))
      · obtain ⟨m, hm, he⟩ := hp.snext_edge hts hf'
        exact ⟨m, hm, by rw [he, snext_spineAt]⟩

/-! ## Opaque terms -/

/-- `t` is available, its inline writing costs at least `w`, and (for a
telescope node) every continuation through it costs at least `w`. -/
def OpaqueAt (p : Prep) (w : Nat) (A : Nat → Bool) (t : Nat) : Prop :=
  A t = true ∧ (p.family[t]! = .none → w ≤ uInl p w A t) ∧
    (p.family[t]! ≠ .none → w ≤ mergedOf p w A (uCost p w A) t)

/-- An opaque term costs exactly `w`. -/
theorem PrepWF.opaque_cost {p : Prep} (hp : PrepWF p) {w : Nat} {A : Nat → Bool} {t : Nat}
    (ht : t < p.dag.size) (h : OpaqueAt p w A t) : uCost p w A t = w := by
  rw [hp.uCost_eq w A t ht]
  unfold costOf
  rw [ite_eq_left h.1]
  have hinl : w ≤ inlOf p w A (uCost p w A) t := by
    by_cases hf : p.family[t]! = .none
    · exact h.2.1 hf
    · have := (inl_merged_bounds p w A (uCost p w A) hf).1
      have := h.2.2 hf
      unfold uInl at *
      omega
  exact Nat.min_eq_right hinl

/-! ## Telescopes from a spine position -/

/-- The available cuts of `y` at spine positions `k ≤ j < K`, headers counted
from `y`, side bytes from position `k`. -/
def cutsRange (p : Prep) (w : Nat) (A : Nat → Bool) (cost : Nat → Nat) (y k K : Nat) :
    List Nat :=
  (List.range' k (K - k)).filterMap fun j =>
    if A (spineAt p y j) then some (tag4Size j + prefixSides p cost (spineAt p y k) (j - k) + w)
    else none

/-- The natural ending of `y`'s telescope, side bytes from position `k`. -/
def natFrom (p : Prep) (cost : Nat → Nat) (y k : Nat) : Nat :=
  tag4Size p.spineLen[y]! + prefixSides p cost (spineAt p y k) (p.spineLen[y]! - k) +
    cost p.tail[y]!

/-- The cheapest ending of `y`'s telescope from spine position `k` on. -/
def teleFrom (p : Prep) (w : Nat) (A : Nat → Bool) (cost : Nat → Nat) (y k : Nat) : Nat :=
  (cutsRange p w A cost y k p.spineLen[y]!).foldl min (natFrom p cost y k)

theorem prefixSides_local (p : Prep) {f g : Nat → Nat} :
    ∀ (j t : Nat), (∀ i, i < j → f (sideAt p t i) = g (sideAt p t i)) →
      prefixSides p f t j = prefixSides p g t j := by
  intro j
  induction j with
  | zero => intro _ _; rfl
  | succ j ih =>
    intro t h
    simp only [prefixSides, sideCost]
    have h0 := h 0 (by omega)
    simp only [sideAt, spineAt] at h0
    rw [h0, ih (snext p t) (fun i hi => by
      have := h (i + 1) (by omega)
      simp only [sideAt, spineAt] at this ⊢
      exact this)]

theorem foldl_min_add (a : Nat) : ∀ (l : List Nat) (x : Nat),
    (l.map (a + ·)).foldl min (a + x) = a + l.foldl min x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons y ys ih =>
    intro x
    simp only [List.map_cons, List.foldl_cons]
    rw [show min (a + x) (a + y) = a + min x y by omega, ih]

/-- With no available cut before position `k ≥ 1`, the inline cost of a
telescope is its first `k` sides plus its cheapest ending from `k`. -/
theorem PrepWF.inl_split {p : Prep} (_hp : PrepWF p) (w : Nat) (A : Nat → Bool)
    (cost : Nat → Nat) {y k : Nat} (hf : p.family[y]! ≠ .none) (hk1 : 1 ≤ k)
    (hkl : k ≤ p.spineLen[y]!) (hnone : ∀ j, 1 ≤ j → j < k → A (spineAt p y j) = false) :
    inlOf p w A cost y = prefixSides p cost y k + teleFrom p w A cost y k := by
  unfold inlOf teleFrom
  rw [ite_eq_right hf]
  have hcuts : cutCosts p w A cost y =
      (cutsRange p w A cost y k p.spineLen[y]!).map (prefixSides p cost y k + ·) := by
    unfold cutCosts cutsRange
    have hsplit : List.range' 1 (p.spineLen[y]! - 1) =
        List.range' 1 (k - 1) ++ List.range' k (p.spineLen[y]! - k) := by
      have := List.range'_append_1 (s := 1) (m := k - 1) (n := p.spineLen[y]! - k)
      rw [show 1 + (k - 1) = k by omega, show k - 1 + (p.spineLen[y]! - k) = p.spineLen[y]! - 1 by omega] at this
      exact this.symm
    rw [hsplit, List.filterMap_append]
    have h1 : (List.range' 1 (k - 1)).filterMap (fun j =>
        if A (spineAt p y j) then some (tag4Size j + prefixSides p cost y j + w) else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro j hj
      rw [List.mem_range'_1] at hj
      rw [hnone j hj.1 (by omega)]
      rfl
    rw [h1, List.nil_append, List.map_filterMap]
    apply filterMap_congr'
    intro j hj
    rw [List.mem_range'_1] at hj
    split
    · simp only [Option.map_some]
      congr 1
      rw [show j = k + (j - k) by omega, prefixSides_add p cost k (j - k) y]
      have : k + (j - k) - k = j - k := by omega
      rw [this]
      omega
    · rfl
  rw [hcuts]
  have hnat : naturalCost p cost y = prefixSides p cost y k + natFrom p cost y k := by
    unfold naturalCost natFrom
    rw [show p.spineLen[y]! = k + (p.spineLen[y]! - k) by omega]
    rw [prefixSides_add p cost k (p.spineLen[y]! - k) y]
    rw [show k + (p.spineLen[y]! - k) - k = p.spineLen[y]! - k by omega]
    omega
  rw [hnat, foldl_min_add]

theorem mem_cutsRange {p : Prep} {w : Nat} {A : Nat → Bool} {cost : Nat → Nat} {y k K e : Nat} :
    e ∈ cutsRange p w A cost y k K ↔ ∃ j, k ≤ j ∧ j < K ∧ A (spineAt p y j) = true ∧
      e = tag4Size j + prefixSides p cost (spineAt p y k) (j - k) + w := by
  unfold cutsRange
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, he⟩
    rw [List.mem_range'_1] at hj
    split at he
    · rename_i hA
      exact ⟨j, hj.1, by omega, hA, (Option.some.inj he).symm⟩
    · cases he
  · rintro ⟨j, h1, h2, hA, rfl⟩
    exact ⟨j, List.mem_range'_1.mpr ⟨h1, by omega⟩, by rw [ite_eq_left hA]⟩

theorem prefixSides_mono (p : Prep) (cost : Nat → Nat) (t : Nat) {a b : Nat} (h : a ≤ b) :
    prefixSides p cost t a ≤ prefixSides p cost t b := by
  rw [show b = a + (b - a) by omega, prefixSides_add p cost a (b - a) t]
  omega

/-- **Domination at an opaque spine node.** When the spine node at position
`K ≥ k` is opaque, no ending at or beyond it is cheaper than the cut there. -/
theorem PrepWF.teleFrom_dom {p : Prep} (hp : PrepWF p) {w : Nat} {A : Nat → Bool} {y k K : Nat}
    (hy : y < p.dag.size) (hf : p.family[y]! ≠ .none) (hkK : k ≤ K) (hK : K < p.spineLen[y]!)
    (hop : OpaqueAt p w A (spineAt p y K)) :
    teleFrom p w A (uCost p w A) y k =
      (cutsRange p w A (uCost p w A) y k K).foldl min
        (tag4Size K + prefixSides p (uCost p w A) (spineAt p y k) (K - k) + w) := by
  have hsp : spineAt p (spineAt p y k) (K - k) = spineAt p y K := by
    rw [← spineAt_add]; congr 1; omega
  have hge : ∀ j, K ≤ j → tag4Size K + prefixSides p (uCost p w A) (spineAt p y k) (K - k) + w ≤
      tag4Size j + prefixSides p (uCost p w A) (spineAt p y k) (j - k) + w := by
    intro j hj
    have := tag4Size_mono hj
    have := prefixSides_mono p (uCost p w A) (spineAt p y k) (show K - k ≤ j - k by omega)
    omega
  unfold teleFrom
  apply foldl_min_unique
  · -- the right side is one of the options
    rcases List.mem_cons.mp (foldl_min_mem (cutsRange p w A (uCost p w A) y k K)
      (tag4Size K + prefixSides p (uCost p w A) (spineAt p y k) (K - k) + w)) with h | h
    · rw [h]
      exact List.mem_cons_of_mem _ (mem_cutsRange.mpr ⟨K, hkK, hK, hop.1, rfl⟩)
    · obtain ⟨j, h1, h2, hA, he⟩ := mem_cutsRange.mp h
      exact List.mem_cons_of_mem _ (mem_cutsRange.mpr ⟨j, h1, by omega, hA, he⟩)
  · intro e he
    have hle := foldl_min_le (cutsRange p w A (uCost p w A) y k K)
      (tag4Size K + prefixSides p (uCost p w A) (spineAt p y k) (K - k) + w) _
      List.mem_cons_self
    rcases List.mem_cons.mp he with rfl | he
    · -- the natural ending costs at least the cut
      obtain ⟨hts, htf, htlen, httail, _, _, _⟩ := hp.spine_shift hy hf (k := K) hK
      have hfK : p.family[spineAt p y K]! ≠ .none := by rw [htf]; exact hf
      have hm := hop.2.2 hfK
      have hmle := foldl_min_le (mergedCuts p w A (uCost p w A) (spineAt p y K))
        (prefixSides p (uCost p w A) (spineAt p y K) p.spineLen[spineAt p y K]! +
          uCost p w A p.tail[spineAt p y K]!) _ List.mem_cons_self
      unfold mergedOf at hm
      rw [htlen, httail] at hm hmle
      have hsplit : prefixSides p (uCost p w A) (spineAt p y k) (p.spineLen[y]! - k) =
          prefixSides p (uCost p w A) (spineAt p y k) (K - k) +
            prefixSides p (uCost p w A) (spineAt p y K) (p.spineLen[y]! - K) := by
        rw [show p.spineLen[y]! - k = (K - k) + (p.spineLen[y]! - K) by omega,
          prefixSides_add, hsp]
      have := tag4Size_mono (show K ≤ p.spineLen[y]! by omega)
      unfold natFrom
      omega
    · obtain ⟨j, h1, h2, hA, rfl⟩ := mem_cutsRange.mp he
      by_cases hjK : j < K
      · exact foldl_min_le _ _ _ (List.mem_cons_of_mem _ (mem_cutsRange.mpr ⟨j, h1, hjK, hA, rfl⟩))
      · exact Nat.le_trans hle (hge j (by omega))

/-! ## Locality -/

/-- Every opaque term is opaque under `A`. -/
def OpaqueOn (p : Prep) (w : Nat) (O A : Nat → Bool) : Prop :=
  ∀ t, t < p.dag.size → O t = true → OpaqueAt p w A t

/-- The cost of a term below `y` agrees under `A` and `B` when it is opaque or
when `A` and `B` agree on everything it reaches. -/
def CostAgree (p : Prep) (w : Nat) (O A B : Nat → Bool) (y : Nat) : Prop :=
  ∀ c, c < y → (∀ v, NReach p O c v → A v = B v) → uCost p w A c = uCost p w B c

theorem PrepWF.cost_agree_of {p : Prep} (hp : PrepWF p) {w : Nat} {O A B : Nat → Bool} {y : Nat}
    (hy : y < p.dag.size) (hA : OpaqueOn p w O A) (hB : OpaqueOn p w O B)
    (hc : CostAgree p w O A B y) {u c : Nat} (hcy : c < y)
    (hu : ∃ k, k < (p.dag.node u).head.arity ∧ (p.dag.node u).child k = c) {z : Nat}
    (hzu : NReach p O z u) (hzu' : u = z ∨ O u = false)
    (hagree : ∀ v, NReach p O z v → A v = B v) : uCost p w A c = uCost p w B c := by
  by_cases hO : O c = true
  · rw [hp.opaque_cost (by omega) (hA c (by omega) hO), hp.opaque_cost (by omega) (hB c (by omega) hO)]
  · have hO' : O c = false := by simpa using hO
    exact hc c hcy fun v hv => hagree v (hzu.trans hzu' (NReach.of_child hO' hu hv))

theorem exists_min_nat (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hm : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hpm⟩ := hm
      exact ih m hmn hpm
    · exact ⟨n, hn, fun m hmn hpm => hm ⟨m, hmn, hpm⟩⟩

/-- **Locality of a telescope ending.** The cheapest ending of `y`'s telescope
from position `k ≥ 1` is the same under `A` and `B` when the spine node there
is opaque, or when `A` and `B` agree on everything it reaches. -/
theorem PrepWF.teleFrom_local_lt {p : Prep} (hp : PrepWF p) (w : Nat) (O : Nat → Bool) {y k : Nat}
    (hy : y < p.dag.size) (hf : p.family[y]! ≠ .none) (hkl : k < p.spineLen[y]!)
    {A B : Nat → Bool} (hA : OpaqueOn p w O A) (hB : OpaqueOn p w O B)
    (hc : CostAgree p w O A B y)
    (hagree : O (spineAt p y k) = false → ∀ v, NReach p O (spineAt p y k) v → A v = B v) :
    teleFrom p w A (uCost p w A) y k = teleFrom p w B (uCost p w B) y k := by
  classical
  have hsk : ∀ j, j < p.spineLen[y]! → spineAt p y j < p.dag.size ∧
      p.family[spineAt p y j]! ≠ .none := by
    intro j hj
    obtain ⟨hts, htf, _⟩ := hp.spine_shift hy hf (k := j) hj
    exact ⟨hts, by rw [htf]; exact hf⟩
  -- agreement on the spine prefix `[k, J)` free of opaque nodes after `k`
  have hside : ∀ J, J ≤ p.spineLen[y]! → O (spineAt p y k) = false →
      (∀ i, k < i → i < J → O (spineAt p y i) = false) →
      (∀ j, k ≤ j → j < J → A (spineAt p y j) = B (spineAt p y j)) ∧
      (∀ m, k + m ≤ J → prefixSides p (uCost p w A) (spineAt p y k) m =
        prefixSides p (uCost p w B) (spineAt p y k) m) := by
    intro J hJ hOk hO
    have hreach : ∀ j, k ≤ j → j < J → NReach p O (spineAt p y k) (spineAt p y j) :=
      fun j h1 h2 => hp.spine_nreach hy hf j h1 (by omega) (fun i hi1 hi2 => hO i hi1 (by omega))
    have hnO : ∀ j, k ≤ j → j < J → (spineAt p y j = spineAt p y k ∨ O (spineAt p y j) = false) := by
      intro j h1 h2
      by_cases hjk : j = k
      · exact Or.inl (by rw [hjk])
      · exact Or.inr (hO j (by omega) h2)
    refine ⟨fun j h1 h2 => hagree hOk _ (hreach j h1 h2), fun m hm => ?_⟩
    apply prefixSides_local
    intro i hi
    have hsa : sideAt p (spineAt p y k) i = sideAt p y (k + i) := by
      unfold sideAt; rw [spineAt_add]
    rw [hsa]
    obtain ⟨hts, hfs⟩ := hsk (k + i) (by omega)
    have hlt := hp.sideAt_lt hy hf (k := k + i) (by omega)
    exact hp.cost_agree_of hy hA hB hc hlt (hp.side_edge hts hfs) (hreach (k + i) (by omega) (by omega))
      (hnO (k + i) (by omega) (by omega)) (hagree hOk)
  by_cases hex : ∃ K, k ≤ K ∧ K < p.spineLen[y]! ∧ O (spineAt p y K) = true
  · obtain ⟨K, ⟨hK1, hK2, hK3⟩, hKmin⟩ := exists_min_nat _ hex
    have hmin : ∀ i, k ≤ i → i < K → O (spineAt p y i) = false := by
      intro i h1 h2
      cases hOi : O (spineAt p y i)
      · rfl
      · exact absurd ⟨h1, by omega, hOi⟩ (hKmin i h2)
    obtain ⟨hts, _⟩ := hsk K hK2
    rw [hp.teleFrom_dom hy hf hK1 hK2 (hA _ hts hK3), hp.teleFrom_dom hy hf hK1 hK2 (hB _ hts hK3)]
    by_cases hKk : K = k
    · have : (cutsRange p w A (uCost p w A) y k K) = [] := by
        unfold cutsRange; rw [hKk]; simp
      have h2 : (cutsRange p w B (uCost p w B) y k K) = [] := by
        unfold cutsRange; rw [hKk]; simp
      rw [this, h2, hKk]
      simp [prefixSides]
    · have hOk : O (spineAt p y k) = false := hmin k (Nat.le_refl _) (by omega)
      obtain ⟨hav, hps⟩ := hside K (by omega) hOk (fun i h1 h2 => hmin i (by omega) h2)
      have hlist : cutsRange p w A (uCost p w A) y k K = cutsRange p w B (uCost p w B) y k K := by
        unfold cutsRange
        apply filterMap_congr'
        intro j hj
        rw [List.mem_range'_1] at hj
        rw [hav j hj.1 (by omega), hps (j - k) (by omega)]
      rw [hlist, hps (K - k) (by omega)]
  · have hnoO : ∀ i, k ≤ i → i < p.spineLen[y]! → O (spineAt p y i) = false := by
      intro i h1 h2
      cases hOi : O (spineAt p y i)
      · rfl
      · exact absurd ⟨i, h1, h2, hOi⟩ hex
    have hOk := hnoO k (Nat.le_refl _) hkl
    obtain ⟨hav, hps⟩ := hside p.spineLen[y]! (Nat.le_refl _) hOk
      (fun i h1 h2 => hnoO i (by omega) h2)
    have hlist : cutsRange p w A (uCost p w A) y k p.spineLen[y]! =
        cutsRange p w B (uCost p w B) y k p.spineLen[y]! := by
      unfold cutsRange
      apply filterMap_congr'
      intro j hj
      rw [List.mem_range'_1] at hj
      rw [hav j hj.1 (by omega), hps (j - k) (by omega)]
    -- the tail
    obtain ⟨hl1, _, hend, htl, _⟩ := hp.spine y hy hf
    have hlast := hsk (p.spineLen[y]! - 1) (by omega)
    have htail : uCost p w A p.tail[y]! = uCost p w B p.tail[y]! := by
      have hedge := hp.snext_edge hlast.1 hlast.2
      rw [snext_spineAt, show p.spineLen[y]! - 1 + 1 = p.spineLen[y]! by omega, hend] at hedge
      refine hp.cost_agree_of hy hA hB hc htl hedge
        (hp.spine_nreach hy hf (p.spineLen[y]! - 1) (by omega) (by omega)
          (fun i h1 h2 => hnoO i (by omega) (by omega))) ?_ (hagree hOk)
      by_cases hlk : p.spineLen[y]! - 1 = k
      · exact Or.inl (by rw [hlk])
      · exact Or.inr (hnoO _ (by omega) (by omega))
    unfold teleFrom natFrom
    rw [hlist, hps (p.spineLen[y]! - k) (by omega), htail]

theorem PrepWF.teleFrom_local {p : Prep} (hp : PrepWF p) (w : Nat) (O : Nat → Bool) {y k : Nat}
    (hy : y < p.dag.size) (hf : p.family[y]! ≠ .none) (hkl : k ≤ p.spineLen[y]!)
    {A B : Nat → Bool} (hA : OpaqueOn p w O A) (hB : OpaqueOn p w O B)
    (hc : CostAgree p w O A B y)
    (hagree : O (spineAt p y k) = false → ∀ v, NReach p O (spineAt p y k) v → A v = B v) :
    teleFrom p w A (uCost p w A) y k = teleFrom p w B (uCost p w B) y k := by
  by_cases hkl' : k = p.spineLen[y]!
  · obtain ⟨hl1, _, hend, htl, _⟩ := hp.spine y hy hf
    have hcuts : ∀ (C : Nat → Bool) (cost : Nat → Nat),
        cutsRange p w C cost y k p.spineLen[y]! = [] := by
      intro C cost; unfold cutsRange; rw [hkl']; simp
    have htail : uCost p w A p.tail[y]! = uCost p w B p.tail[y]! := by
      by_cases hO : O p.tail[y]! = true
      · rw [hp.opaque_cost (by omega) (hA _ (by omega) hO),
          hp.opaque_cost (by omega) (hB _ (by omega) hO)]
      · rw [hkl', hend] at hagree
        exact hc _ htl (hagree (by simpa using hO))
    unfold teleFrom natFrom
    rw [hcuts, hcuts, htail, hkl', Nat.sub_self]
    rfl
  · exact hp.teleFrom_local_lt w O hy hf (by omega) hA hB hc hagree

/-- **Locality.** The costs of `y` are the same under two availabilities
(both making every opaque term opaque) that agree on every term reachable
from `y` along paths whose intermediate terms are not opaque. -/
theorem PrepWF.uCost_local {p : Prep} (hp : PrepWF p) (w : Nat) (O : Nat → Bool) :
    ∀ y, y < p.dag.size → ∀ (A B : Nat → Bool), OpaqueOn p w O A → OpaqueOn p w O B →
      (∀ v, NReach p O y v → A v = B v) →
      uCost p w A y = uCost p w B y ∧ uInl p w A y = uInl p w B y := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro hy A B hA hB hagree
    have hc : CostAgree p w O A B y := fun c hcy hcag => (ih c hcy (by omega) A B hA hB hcag).1
    have hinl : uInl p w A y = uInl p w B y := by
      unfold uInl
      by_cases hf : p.family[y]! = .none
      · unfold inlOf
        rw [ite_eq_left hf, ite_eq_left hf]
        apply foldl_add_congr
        intro c hcm
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hcm
        have har := hp.dag.arity y hy
        rw [← dag_node_eq hy] at har
        have hci : (p.dag.node y).child i = (p.dag.node y).children[i] :=
          Ix.Compile.Verify.SharingExact.child_eq_getElem _ i hi
        rw [← hci]
        have hlt := hp.dag.childAt_lt hy (k := i) (by omega)
        exact hp.cost_agree_of hy hA hB hc hlt ⟨i, by omega, rfl⟩ .refl (Or.inl rfl) hagree
      · rw [hp.inl_split w A _ hf (Nat.le_refl _) ((hp.spine y hy hf).1) (fun j h1 h2 => by omega),
          hp.inl_split w B _ hf (Nat.le_refl _) ((hp.spine y hy hf).1) (fun j h1 h2 => by omega)]
        have hside : prefixSides p (uCost p w A) y 1 = prefixSides p (uCost p w B) y 1 := by
          simp only [prefixSides, sideCost]
          have hlt := hp.sideChild_lt (t := y) hy hf
          rw [hp.cost_agree_of hy hA hB hc hlt (hp.side_edge hy hf) .refl (Or.inl rfl) hagree]
        have hs1 : spineAt p y 1 = snext p y := rfl
        rw [hside, hp.teleFrom_local w O (k := 1) hy hf ((hp.spine y hy hf).1) hA hB hc
          (fun hO1 v hv => by
            rw [hs1] at hO1 hv
            exact hagree v (NReach.trans (.tail .refl (Or.inl rfl) (hp.snext_edge hy hf))
              (Or.inr hO1) hv))]
    refine ⟨?_, hinl⟩
    rw [hp.uCost_eq w A y hy, hp.uCost_eq w B y hy]
    unfold costOf
    rw [hagree y .refl]
    unfold uInl at hinl
    rw [hinl]

/-! ## Modularity -/

theorem arr_foldl_add_eq_sum (f : Nat → Nat) (a : Nat) (arr : Array Nat) :
    arr.foldl (fun acc c => acc + f c) a = a + (arr.toList.map f).sum := by
  rw [← Array.foldl_toList]
  generalize arr.toList = l
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

theorem prefixSides_modular (p : Prep) {f12 f0 f1 f2 : Nat → Nat} :
    ∀ (j t : Nat), (∀ i, i < j → f12 (sideAt p t i) + f0 (sideAt p t i) =
        f1 (sideAt p t i) + f2 (sideAt p t i)) →
      prefixSides p f12 t j + prefixSides p f0 t j = prefixSides p f1 t j + prefixSides p f2 t j := by
  intro j
  induction j with
  | zero => intro _ _; rfl
  | succ j ih =>
    intro t h
    simp only [prefixSides, sideCost]
    have h0 := h 0 (by omega)
    simp only [sideAt, spineAt] at h0
    have hr := ih (snext p t) (fun i hi => by
      have := h (i + 1) (by omega)
      simp only [sideAt, spineAt] at this ⊢
      exact this)
    omega

/-- Adding `Z₁`, `Z₂` to a base availability `A₀`. -/
def addAvail (A Z : Nat → Bool) : Nat → Bool := fun v => A v || Z v

/-- No term reachable from `x` (along non-opaque paths) is in `Z`. -/
def Unreached (p : Prep) (O Z : Nat → Bool) (x : Nat) : Prop :=
  ∀ v, NReach p O x v → Z v = false

theorem agree_of_unreached {p : Prep} {O A Z : Nat → Bool} {x : Nat} (h : Unreached p O Z x) :
    ∀ v, NReach p O x v → addAvail A Z v = A v := by
  intro v hv
  simp [addAvail, h v hv]

/-- **Modularity.** Let every opaque term be opaque under the base `A₀` and
under each of `A₀ ∪ Z₁`, `A₀ ∪ Z₂`, `A₀ ∪ Z₁ ∪ Z₂`, and let no available
non-opaque term reach both `Z₁` and `Z₂` (along non-opaque paths). Then
adding both changes every cost by the sum of adding each:
`C₁₂ + C₀ = C₁ + C₂` for `uCost` and for `uInl`. -/
theorem PrepWF.uCost_modular {p : Prep} (hp : PrepWF p) (w : Nat) (O A0 Z1 Z2 : Nat → Bool)
    (h0 : OpaqueOn p w O A0) (h1 : OpaqueOn p w O (addAvail A0 Z1))
    (h2 : OpaqueOn p w O (addAvail A0 Z2))
    (h12 : OpaqueOn p w O (addAvail (addAvail A0 Z1) Z2))
    (hsep : ∀ v, v < p.dag.size → addAvail (addAvail A0 Z1) Z2 v = true → O v = false →
      Unreached p O Z1 v ∨ Unreached p O Z2 v) :
    ∀ y, y < p.dag.size →
      uCost p w (addAvail (addAvail A0 Z1) Z2) y + uCost p w A0 y =
          uCost p w (addAvail A0 Z1) y + uCost p w (addAvail A0 Z2) y ∧
        uInl p w (addAvail (addAvail A0 Z1) Z2) y + uInl p w A0 y =
          uInl p w (addAvail A0 Z1) y + uInl p w (addAvail A0 Z2) y := by
  -- shorthands
  have hA12_1 : ∀ x, Unreached p O Z2 x → ∀ v, NReach p O x v →
      addAvail (addAvail A0 Z1) Z2 v = addAvail A0 Z1 v :=
    fun x hx => agree_of_unreached hx
  have hA2_0 : ∀ x, Unreached p O Z2 x → ∀ v, NReach p O x v → addAvail A0 Z2 v = A0 v :=
    fun x hx => agree_of_unreached hx
  have hA12_2 : ∀ x, Unreached p O Z1 x → ∀ v, NReach p O x v →
      addAvail (addAvail A0 Z1) Z2 v = addAvail A0 Z2 v := by
    intro x hx v hv
    simp [addAvail, hx v hv]
  have hA1_0 : ∀ x, Unreached p O Z1 x → ∀ v, NReach p O x v → addAvail A0 Z1 v = A0 v :=
    fun x hx => agree_of_unreached hx
  have hcostAgree : ∀ (A B : Nat → Bool), OpaqueOn p w O A → OpaqueOn p w O B → ∀ y,
      y < p.dag.size → CostAgree p w O A B y :=
    fun A B hA hB y hy c hcy hag => (hp.uCost_local w O c (by omega) A B hA hB hag).1
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro hy
    -- a side that one of the sets does not reach
    have hlocal : Unreached p O Z1 y ∨ Unreached p O Z2 y →
        uCost p w (addAvail (addAvail A0 Z1) Z2) y + uCost p w A0 y =
            uCost p w (addAvail A0 Z1) y + uCost p w (addAvail A0 Z2) y ∧
          uInl p w (addAvail (addAvail A0 Z1) Z2) y + uInl p w A0 y =
            uInl p w (addAvail A0 Z1) y + uInl p w (addAvail A0 Z2) y := by
      rintro (hu | hu)
      · obtain ⟨a1, a2⟩ := hp.uCost_local w O y hy _ _ h12 h2 (hA12_2 y hu)
        obtain ⟨b1, b2⟩ := hp.uCost_local w O y hy _ _ h1 h0 (hA1_0 y hu)
        omega
      · obtain ⟨a1, a2⟩ := hp.uCost_local w O y hy _ _ h12 h1 (hA12_1 y hu)
        obtain ⟨b1, b2⟩ := hp.uCost_local w O y hy _ _ h2 h0 (hA2_0 y hu)
        omega
    -- the inline costs are modular in every case
    have hinl : uInl p w (addAvail (addAvail A0 Z1) Z2) y + uInl p w A0 y =
        uInl p w (addAvail A0 Z1) y + uInl p w (addAvail A0 Z2) y := by
      unfold uInl
      by_cases hf : p.family[y]! = .none
      · unfold inlOf
        simp only [ite_eq_left hf]
        rw [arr_foldl_add_eq_sum, arr_foldl_add_eq_sum, arr_foldl_add_eq_sum,
          arr_foldl_add_eq_sum]
        have hch : ∀ c ∈ (p.dag.node y).children.toList,
            uCost p w (addAvail (addAvail A0 Z1) Z2) c + uCost p w A0 c =
              uCost p w (addAvail A0 Z1) c + uCost p w (addAvail A0 Z2) c := by
          intro c hc
          have hlt := hp.dag.child_lt hy (Array.mem_toList_iff.mp hc)
          exact (ih c hlt (by omega)).1
        have e := congrArg List.sum (List.map_congr_left hch)
        simp only [sum_map_add'] at e
        omega
      · have hl1 := (hp.spine y hy hf).1
        have hsub : ∀ (X : Nat → Bool), (X = A0 ∨ X = addAvail A0 Z1 ∨ X = addAvail A0 Z2 ∨
            X = addAvail (addAvail A0 Z1) Z2) → ∀ v, X v = true →
              addAvail (addAvail A0 Z1) Z2 v = true := by
          intro X hX v hv
          rcases hX with h | h | h | h <;> rw [h] at hv <;>
            (simp only [addAvail] at hv ⊢; revert hv; cases A0 v <;> cases Z1 v <;> cases Z2 v <;> decide)
        have hsides : ∀ j, j ≤ p.spineLen[y]! →
            prefixSides p (uCost p w (addAvail (addAvail A0 Z1) Z2)) y j +
                prefixSides p (uCost p w A0) y j =
              prefixSides p (uCost p w (addAvail A0 Z1)) y j +
                prefixSides p (uCost p w (addAvail A0 Z2)) y j := by
          intro j hj
          apply prefixSides_modular
          intro i hi
          exact (ih _ (hp.sideAt_lt hy hf (k := i) (by omega)) (by
            have := hp.sideAt_lt hy hf (k := i) (by omega); omega)).1
        by_cases hex : ∃ k, 1 ≤ k ∧ k < p.spineLen[y]! ∧
            addAvail (addAvail A0 Z1) Z2 (spineAt p y k) = true
        · obtain ⟨K1, ⟨hK1a, hK1b, hK1c⟩, hKmin⟩ := exists_min_nat _ hex
          have hnone : ∀ (X : Nat → Bool), (∀ v, X v = true →
              addAvail (addAvail A0 Z1) Z2 v = true) →
              ∀ j, 1 ≤ j → j < K1 → X (spineAt p y j) = false := by
            intro X hX j h1 h2
            cases hXj : X (spineAt p y j)
            · rfl
            · exact absurd ⟨h1, by omega, hX _ hXj⟩ (hKmin j h2)
          rw [hp.inl_split w _ _ hf hK1a (by omega) (hnone _ (hsub _ (Or.inr (Or.inr (Or.inr rfl))))),
            hp.inl_split w _ _ hf hK1a (by omega) (hnone _ (hsub _ (Or.inl rfl))),
            hp.inl_split w _ _ hf hK1a (by omega) (hnone _ (hsub _ (Or.inr (Or.inl rfl)))),
            hp.inl_split w _ _ hf hK1a (by omega) (hnone _ (hsub _ (Or.inr (Or.inr (Or.inl rfl)))))]
          have hpre := hsides K1 (by omega)
          obtain ⟨hts, _⟩ := hp.spine_shift hy hf (k := K1) hK1b
          have htele : teleFrom p w (addAvail (addAvail A0 Z1) Z2)
                (uCost p w (addAvail (addAvail A0 Z1) Z2)) y K1 +
              teleFrom p w A0 (uCost p w A0) y K1 =
              teleFrom p w (addAvail A0 Z1) (uCost p w (addAvail A0 Z1)) y K1 +
                teleFrom p w (addAvail A0 Z2) (uCost p w (addAvail A0 Z2)) y K1 := by
            by_cases hOK : O (spineAt p y K1) = true
            · rw [hp.teleFrom_dom hy hf (Nat.le_refl _) hK1b (h12 _ hts hOK),
                hp.teleFrom_dom hy hf (Nat.le_refl _) hK1b (h0 _ hts hOK),
                hp.teleFrom_dom hy hf (Nat.le_refl _) hK1b (h1 _ hts hOK),
                hp.teleFrom_dom hy hf (Nat.le_refl _) hK1b (h2 _ hts hOK)]
              simp [cutsRange, prefixSides]
            · have hOK' : O (spineAt p y K1) = false := by simpa using hOK
              rcases hsep _ hts hK1c hOK' with hu | hu
              · rw [hp.teleFrom_local w O hy hf (by omega) h12 h2 (hcostAgree _ _ h12 h2 y hy)
                  (fun _ => hA12_2 _ hu),
                  hp.teleFrom_local w O hy hf (by omega) h1 h0 (hcostAgree _ _ h1 h0 y hy)
                  (fun _ => hA1_0 _ hu)]
                omega
              · rw [hp.teleFrom_local w O hy hf (by omega) h12 h1 (hcostAgree _ _ h12 h1 y hy)
                  (fun _ => hA12_1 _ hu),
                  hp.teleFrom_local w O hy hf (by omega) h2 h0 (hcostAgree _ _ h2 h0 y hy)
                  (fun _ => hA2_0 _ hu)]
          omega
        · have hnone : ∀ (X : Nat → Bool), (∀ v, X v = true →
              addAvail (addAvail A0 Z1) Z2 v = true) →
              ∀ j, 1 ≤ j → j < p.spineLen[y]! → X (spineAt p y j) = false := by
            intro X hX j h1 h2
            cases hXj : X (spineAt p y j)
            · rfl
            · exact absurd ⟨j, h1, h2, hX _ hXj⟩ hex
          rw [hp.inl_split w _ _ hf hl1 (Nat.le_refl _) (hnone _ (hsub _ (Or.inr (Or.inr (Or.inr rfl))))),
            hp.inl_split w _ _ hf hl1 (Nat.le_refl _) (hnone _ (hsub _ (Or.inl rfl))),
            hp.inl_split w _ _ hf hl1 (Nat.le_refl _) (hnone _ (hsub _ (Or.inr (Or.inl rfl)))),
            hp.inl_split w _ _ hf hl1 (Nat.le_refl _) (hnone _ (hsub _ (Or.inr (Or.inr (Or.inl rfl)))))]
          have hpre := hsides p.spineLen[y]! (Nat.le_refl _)
          obtain ⟨_, _, _, htl, _⟩ := hp.spine y hy hf
          have htail := (ih p.tail[y]! htl (by omega)).1
          simp only [teleFrom, natFrom, cutsRange, Nat.sub_self, List.range'_zero,
            List.filterMap_nil, List.foldl_nil, prefixSides]
          omega
    by_cases hreach : Unreached p O Z1 y ∨ Unreached p O Z2 y
    · exact hlocal hreach
    · refine ⟨?_, hinl⟩
      by_cases hO : O y = true
      · rw [hp.opaque_cost hy (h12 y hy hO), hp.opaque_cost hy (h0 y hy hO),
          hp.opaque_cost hy (h1 y hy hO), hp.opaque_cost hy (h2 y hy hO)]
      · have hO' : O y = false := by simpa using hO
        have hA : addAvail (addAvail A0 Z1) Z2 y = false := by
          cases hav : addAvail (addAvail A0 Z1) Z2 y
          · rfl
          · exact absurd (hsep y hy hav hO') hreach
        have hA0 : A0 y = false := by simp [addAvail] at hA; exact hA.1.1
        have hA1 : addAvail A0 Z1 y = false := by simp [addAvail] at hA ⊢; exact hA.1
        have hA2 : addAvail A0 Z2 y = false := by simp [addAvail] at hA ⊢; exact ⟨hA.1.1, hA.2⟩
        rw [hp.uCost_eq w _ y hy, hp.uCost_eq w A0 y hy, hp.uCost_eq w (addAvail A0 Z1) y hy,
          hp.uCost_eq w (addAvail A0 Z2) y hy]
        unfold costOf
        rw [hA, hA0, hA1, hA2]
        simp only [Bool.false_eq_true, ite_false]
        unfold uInl at hinl
        exact hinl

/-! ## The uniform length -/

theorem mem_append_avail (a b : List Nat) (y : Nat) :
    decide (y ∈ a ++ b) = (decide (y ∈ a) || decide (y ∈ b)) := by
  by_cases ha : y ∈ a <;> by_cases hb : y ∈ b <;> simp [ha, hb]

/-- **Modularity of the uniform length.** For stored lists `cs`, `z₁`, `z₂`
with every term of `cs` opaque (in the base and the three extensions), no term
of `z₁`, `z₂` opaque, and no available non-opaque term reaching both `z₁`
and `z₂` along non-opaque paths:
`L(cs ++ z₁ ++ z₂) + L(cs) = L(cs ++ z₁) + L(cs ++ z₂)` up to the count's
TagN (each side carries the other side's TagN terms). -/
theorem uniformCost_modular {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {cs z1 z2 : List Nat}
    (hin : ∀ t ∈ cs ++ z1 ++ z2, t < dag.size)
    (hop : ∀ (A : List Nat), (A = cs ∨ A = cs ++ z1 ∨ A = cs ++ z2 ∨ A = cs ++ z1 ++ z2) →
      OpaqueOn (Prep.ofDag dag) w (fun y => decide (y ∈ cs)) (fun y => decide (y ∈ A)))
    (_hz : ∀ t ∈ z1 ++ z2, t ∉ cs)
    (hsep : ∀ v, v < dag.size → v ∈ z1 ++ z2 →
      Unreached (Prep.ofDag dag) (fun y => decide (y ∈ cs)) (fun y => decide (y ∈ z1)) v ∨
        Unreached (Prep.ofDag dag) (fun y => decide (y ∈ cs)) (fun y => decide (y ∈ z2)) v) :
    ulen dag w roots (cs ++ z1 ++ z2) + ulen dag w roots cs +
        tag0Size (cs ++ z1).length + tag0Size (cs ++ z2).length =
      ulen dag w roots (cs ++ z1) + ulen dag w roots (cs ++ z2) +
        tag0Size (cs ++ z1 ++ z2).length + tag0Size cs.length := by
  have hp := prepWF_ofDag hwf
  let O : Nat → Bool := fun y => decide (y ∈ cs)
  let A0 : Nat → Bool := fun y => decide (y ∈ cs)
  let Z1 : Nat → Bool := fun y => decide (y ∈ z1)
  let Z2 : Nat → Bool := fun y => decide (y ∈ z2)
  have e1 : (fun y => decide (y ∈ cs ++ z1)) = addAvail A0 Z1 := by
    funext y; simp only [addAvail, A0, Z1]; exact mem_append_avail cs z1 y
  have e2 : (fun y => decide (y ∈ cs ++ z2)) = addAvail A0 Z2 := by
    funext y; simp only [addAvail, A0, Z2]; exact mem_append_avail cs z2 y
  have e12 : (fun y => decide (y ∈ cs ++ z1 ++ z2)) = addAvail (addAvail A0 Z1) Z2 := by
    funext y; simp only [addAvail, A0, Z1, Z2]
    rw [mem_append_avail (cs ++ z1) z2 y, mem_append_avail cs z1 y]
  have h0 := hop cs (Or.inl rfl)
  have h1 : OpaqueOn (Prep.ofDag dag) w O (addAvail A0 Z1) := by
    rw [← e1]; exact hop _ (Or.inr (Or.inl rfl))
  have h2 : OpaqueOn (Prep.ofDag dag) w O (addAvail A0 Z2) := by
    rw [← e2]; exact hop _ (Or.inr (Or.inr (Or.inl rfl)))
  have h12 : OpaqueOn (Prep.ofDag dag) w O (addAvail (addAvail A0 Z1) Z2) := by
    rw [← e12]; exact hop _ (Or.inr (Or.inr (Or.inr rfl)))
  have hsep' : ∀ v, v < (Prep.ofDag dag).dag.size → addAvail (addAvail A0 Z1) Z2 v = true →
      O v = false → Unreached (Prep.ofDag dag) O Z1 v ∨ Unreached (Prep.ofDag dag) O Z2 v := by
    intro v hv hav hO
    rw [ofDag_dag] at hv
    have : v ∈ z1 ++ z2 := by
      simp only [addAvail, A0, Z1, Z2, O, Bool.or_eq_true, decide_eq_true_eq,
        decide_eq_false_iff_not] at hav hO
      rw [List.mem_append]
      rcases hav with (h | h) | h
      · exact absurd h hO
      · exact Or.inl h
      · exact Or.inr h
    exact hsep v hv this
  have hmod := hp.uCost_modular w O A0 Z1 Z2 h0 h1 h2 h12 hsep'
  have hloc1 : ∀ t ∈ z1, uInl (Prep.ofDag dag) w (addAvail (addAvail A0 Z1) Z2) t =
      uInl (Prep.ofDag dag) w (addAvail A0 Z1) t := by
    intro t ht
    have htn := hin t (by simp [ht])
    rcases hsep t htn (by simp [ht]) with hu | hu
    · exact absurd (hu t .refl) (by simp [ht])
    · exact (hp.uCost_local w O t (by rw [ofDag_dag]; exact htn) _ _ h12 h1
        (agree_of_unreached hu)).2
  have hloc2 : ∀ t ∈ z2, uInl (Prep.ofDag dag) w (addAvail (addAvail A0 Z1) Z2) t =
      uInl (Prep.ofDag dag) w (addAvail A0 Z2) t := by
    intro t ht
    have htn := hin t (by simp [ht])
    rcases hsep t htn (by simp [ht]) with hu | hu
    · have hagree : ∀ v, NReach (Prep.ofDag dag) O t v →
          addAvail (addAvail A0 Z1) Z2 v = addAvail A0 Z2 v := by
        intro v hv
        have := hu v hv
        simp only [addAvail, Z1] at this ⊢
        rw [this]
        simp
      exact (hp.uCost_local w O t (by rw [ofDag_dag]; exact htn) _ _ h12 h2 hagree).2
    · exact absurd (hu t .refl) (by simp [ht])
  simp only [ulen, uniformCost]
  rw [e1, e2, e12]
  simp only [List.map_append, List.sum_append]
  have hcs := congrArg List.sum (List.map_congr_left (l := cs) fun t ht =>
    (hmod t (by rw [ofDag_dag]; exact hin t (by simp [ht]))).2)
  have hr := congrArg List.sum (List.map_congr_left (l := roots.toList) fun r hr =>
    (hmod r (by rw [ofDag_dag]; exact hroots r hr)).1)
  simp only [sum_map_add'] at hcs hr
  rw [List.map_congr_left hloc1, List.map_congr_left hloc2]
  simp only [A0] at hcs hr ⊢
  omega

/-! ## Certain-stored terms are opaque; components are separated -/

/-- A gain of at least 1 puts the bounds above the reference width. -/
theorem gain_opaque_bounds {p : Prep} {b : UBounds} {w t d h : Nat} (hhd : h ≤ d)
    (hg : 1 ≤ storedGainWith p b w t d h) :
    (p.family[t]! = .none → w < b.inlineLB[t]!) ∧
      (p.family[t]! ≠ .none → w ≤ b.mergedLB[t]!) := by
  have hd1 := gain_d_pos hhd hg
  unfold storedGainWith at hg
  simp only [_root_.Int.ofNat_eq_natCast] at hg
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have hfb : (p.family[t]! == Family.none) = true := by simp [hf]
    rw [ite_eq_left hfb] at hg
    by_cases hlt : w < b.inlineLB[t]!
    · exact hlt
    · exfalso
      have e := int_mul_le_mul_left' (show ((b.inlineLB[t]! : Nat) : _root_.Int) ≤ (w : _root_.Int) by omega)
        (show (0 : _root_.Int) ≤ (d : _root_.Int) - 1 by omega)
      simp only [_root_.Int.sub_mul, _root_.Int.one_mul] at e hg
      omega
  · have hfb : (p.family[t]! == Family.none) = false := by simpa using hf
    rw [ite_eq_right (by simp [hfb])] at hg
    by_cases hle : w ≤ b.mergedLB[t]!
    · exact hle
    · exfalso
      have e := int_mul_le_mul_left' (show ((b.mergedLB[t]! : Nat) : _root_.Int) ≤ (w : _root_.Int) - 1 by omega)
        (show (0 : _root_.Int) ≤ (d : _root_.Int) - 1 by omega)
      have hT := tag4Size_pos p.spineLen[t]!
      split at hg
      · simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.mul_one] at e hg
        omega
      · simp only [_root_.Int.sub_mul, _root_.Int.mul_sub, _root_.Int.one_mul, _root_.Int.mul_one] at e hg
        omega

/-- **Certain-stored terms are opaque** in every available set within the
candidates that contains them. -/
theorem certainStored_opaque {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) (θ : _root_.Int) (hθ : 1 ≤ θ)
    {t : Nat} (htn : t < dag.size)
    (hcls : (classifyWith (Prep.ofDag dag) (graphFacts dag roots) w
      (uniformBounds (Prep.ofDag dag) w (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w))
      (visibleCounts dag roots (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)) θ)[t]! =
        .certainStored)
    {A : Nat → Bool} (hAt : A t = true)
    (hA : ∀ v, A v = true →
      (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)[v]! = true) :
    OpaqueAt (Prep.ofDag dag) w A t := by
  have hp := prepWF_ofDag hwf
  let cand := searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w
  have hg : θ ≤ storedGainWith (Prep.ofDag dag) (uniformBounds (Prep.ofDag dag) w cand) w t
      (visibleCounts dag roots cand).1[t]! (visibleCounts dag roots cand).2[t]! := by
    simp only [classifyWith] at hcls
    rw [getElem!_range_map _ (by rw [ofDag_dag]; exact htn)] at hcls
    split at hcls
    · cases hcls
    · split at hcls
      · cases hcls
      · split at hcls
        · rename_i hg; exact hg
        · cases hcls
  have hhd := vis_head_le hwf roots hroots cand htn
  have hg1 : 1 ≤ storedGainWith (Prep.ofDag dag) (uniformBounds (Prep.ofDag dag) w cand) w t
      (visibleCounts dag roots cand).1[t]! (visibleCounts dag roots cand).2[t]! := by omega
  obtain ⟨hb1, hb2⟩ := gain_opaque_bounds hhd hg1
  have hbs := hp.bounds_sound w cand A hA t (by rw [ofDag_dag]; exact htn)
  refine ⟨hAt, fun hf => ?_, fun hf => ?_⟩
  · have := hb1 hf; have := hbs.2.1; omega
  · have := hb2 hf; have := (hbs.2.2 hf).1; omega

/-- **Decomposition over components (Stage 4).** Let `cs` list the
certain-stored terms (threshold `θ ≥ 1`), and `z₁`, `z₂` uncertain terms
from different components of a labeling that is constant along non-opaque
paths between uncertain terms. Then the uniform length is modular:
`L(cs ∪ z₁ ∪ z₂) + L(cs) = L(cs ∪ z₁) + L(cs ∪ z₂)` up to the count's
TagN; by induction, the length without the TagN is a sum over
components. -/
theorem components_modular {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) (θ : _root_.Int) (hθ : 1 ≤ θ)
    {cs z1 z2 : List Nat}
    (hcs : ∀ t ∈ cs, t < dag.size ∧
      (classifyWith (Prep.ofDag dag) (graphFacts dag roots) w
        (uniformBounds (Prep.ofDag dag) w
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w))
        (visibleCounts dag roots
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)) θ)[t]! = .certainStored)
    (hz : ∀ t ∈ z1 ++ z2, t < dag.size ∧
      (classifyWith (Prep.ofDag dag) (graphFacts dag roots) w
        (uniformBounds (Prep.ofDag dag) w
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w))
        (visibleCounts dag roots
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)) θ)[t]! = .uncertain)
    (comp : Nat → Nat)
    (hcomp : ∀ a b, a ∈ z1 ++ z2 → b ∈ z1 ++ z2 →
      NReach (Prep.ofDag dag) (fun y => decide (y ∈ cs)) a b → comp a = comp b)
    (hdisj : ∀ a ∈ z1, ∀ b ∈ z2, comp a ≠ comp b) :
    ulen dag w roots (cs ++ z1 ++ z2) + ulen dag w roots cs +
        tag0Size (cs ++ z1).length + tag0Size (cs ++ z2).length =
      ulen dag w roots (cs ++ z1) + ulen dag w roots (cs ++ z2) +
        tag0Size (cs ++ z1 ++ z2).length + tag0Size cs.length := by
  have hcand : ∀ t, t < dag.size → (classifyWith (Prep.ofDag dag) (graphFacts dag roots) w
        (uniformBounds (Prep.ofDag dag) w
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w))
        (visibleCounts dag roots
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)) θ)[t]! ≠ .certainExcluded →
      (classifyWith (Prep.ofDag dag) (graphFacts dag roots) w
        (uniformBounds (Prep.ofDag dag) w
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w))
        (visibleCounts dag roots
          (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)) θ)[t]! ≠ .lowDegree →
      (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)[t]! = true := by
    intro t ht h1 h2
    simp only [classifyWith] at h1 h2
    rw [getElem!_range_map _ (by rw [ofDag_dag]; exact ht)] at h1 h2
    unfold searchCandidates
    rw [getElem!_range_map _ (by rw [ofDag_dag]; exact ht)]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    by_cases hce : certainExcludedTest (Prep.ofDag dag) (graphFacts dag roots) w t = true
    · exact absurd (by rw [ite_eq_left hce]) h1
    · rw [ite_eq_right hce] at h1 h2
      by_cases hdeg : (graphFacts dag roots).deg[t]! < 2
      · exact absurd (by rw [ite_eq_left hdeg]) h2
      · exact ⟨by simpa using hce, by omega⟩
  have hin : ∀ t ∈ cs ++ z1 ++ z2, t < dag.size := by
    intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · rw [List.mem_append] at ht
      rcases ht with ht | ht
      · exact (hcs t ht).1
      · exact (hz t (by simp [ht])).1
    · exact (hz t (by simp [ht])).1
  have hinCand : ∀ t ∈ cs ++ z1 ++ z2,
      (searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w)[t]! = true := by
    intro t ht
    have htn := hin t ht
    apply hcand t htn
    · rw [List.mem_append, List.mem_append] at ht
      rcases ht with (ht | ht) | ht
      · rw [(hcs t ht).2]; exact fun h => by cases h
      · rw [(hz t (by simp [ht])).2]; exact fun h => by cases h
      · rw [(hz t (by simp [ht])).2]; exact fun h => by cases h
    · rw [List.mem_append, List.mem_append] at ht
      rcases ht with (ht | ht) | ht
      · rw [(hcs t ht).2]; exact fun h => by cases h
      · rw [(hz t (by simp [ht])).2]; exact fun h => by cases h
      · rw [(hz t (by simp [ht])).2]; exact fun h => by cases h
  apply uniformCost_modular hwf roots hroots w hin
  · intro A hA t ht hO
    simp only [decide_eq_true_eq] at hO
    have htcs := hcs t hO
    rw [ofDag_dag] at ht
    apply certainStored_opaque hwf roots hroots w θ hθ ht htcs.2
    · simp only [decide_eq_true_eq]
      rcases hA with rfl | rfl | rfl | rfl <;> simp [hO]
    · intro v hv
      simp only [decide_eq_true_eq] at hv
      apply hinCand v
      simp only [List.mem_append]
      rcases hA with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hv)
      · simp only [List.mem_append] at hv
        rcases hv with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · simp only [List.mem_append] at hv
        rcases hv with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · simp only [List.mem_append] at hv
        exact hv
  · intro t ht htcs
    have h1 := (hz t ht).2
    rw [(hcs t htcs).2] at h1
    cases h1
  · intro v hv hvz
    by_cases h1 : Unreached (Prep.ofDag dag) (fun y => decide (y ∈ cs)) (fun y => decide (y ∈ z1)) v
    · exact Or.inl h1
    · right
      intro b hb
      cases hbz : decide (b ∈ z2)
      · exact hbz
      · exfalso
        apply h1
        intro a ha
        cases haz : decide (a ∈ z1)
        · exact haz
        · exfalso
          simp only [decide_eq_true_eq] at hbz haz
          have e1 := hcomp v a hvz (by simp [haz]) ha
          have e2 := hcomp v b hvz (by simp [hbz]) hb
          exact hdisj a haz b hbz (by rw [← e1, ← e2])

/-! ## The search lower bound -/

/-- Costs only drop when more terms are available. -/
theorem PrepWF.costs_antitone {p : Prep} (hp : PrepWF p) (w : Nat) {A B : Nat → Bool}
    (hAB : ∀ v, A v = true → B v = true) {t : Nat} (ht : t < p.dag.size) :
    uCost p w B t ≤ uCost p w A t ∧ uInl p w B t ≤ uInl p w A t := by
  obtain ⟨⟨T, hT, hTc⟩, ⟨U, hU, hUs, hUc⟩⟩ := hp.exists_opt w A t ht
  have h1 := (hp.valid_cost w B (Valid.mono hAB hT) ht).1
  have h2 := (hp.valid_cost w B (Valid.mono hAB hU) ht).2 hUs
  omega

/-- A sub-list of a duplicate-free list sums to at most the whole. -/
theorem sum_le_of_subset (f : Nat → Nat) : ∀ {l X : List Nat}, l.Nodup → X.Nodup →
    (∀ t ∈ l, t ∈ X) → (l.map f).sum ≤ (X.map f).sum
  | [], _, _, _, _ => by simp
  | a :: as, X, hl, hX, hsub => by
    have haX := hsub a List.mem_cons_self
    rw [sum_erase haX f, List.map_cons, List.sum_cons]
    have hnd := List.nodup_cons.mp hl
    have := sum_le_of_subset f hnd.2 (hX.erase a) (fun t ht => by
      rw [hX.mem_erase_iff]
      exact ⟨fun h => hnd.1 (h ▸ ht), hsub t (List.mem_cons_of_mem _ ht)⟩)
    omega

/-- **The lower bound of a search node is sound.** For decided-stored `F`
and undecided `U`, the cost with `F ∪ U` available but only the entries of
`F` paid is at most the length (without the count's TagN) of every
completion `F ⊆ X ⊆ F ∪ U`. -/
theorem lower_bound_sound {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {F U X : List Nat}
    (hF : ∀ t ∈ F, t ∈ X) (hX : ∀ t ∈ X, t ∈ F ∨ t ∈ U) (hXn : ∀ t ∈ X, t < dag.size)
    (hFnd : F.Nodup) (hXnd : X.Nodup) :
    (F.map (uInl (Prep.ofDag dag) w fun y => decide (y ∈ F ∨ y ∈ U))).sum +
        (roots.toList.map (uCost (Prep.ofDag dag) w fun y => decide (y ∈ F ∨ y ∈ U))).sum ≤
      ulen dag w roots X - tag0Size X.length := by
  suffices h : (F.map (uInl (Prep.ofDag dag) w fun y => decide (y ∈ F ∨ y ∈ U))).sum +
        (roots.toList.map (uCost (Prep.ofDag dag) w fun y => decide (y ∈ F ∨ y ∈ U))).sum +
        tag0Size X.length ≤ ulen dag w roots X by omega
  have hp := prepWF_ofDag hwf
  have hsub : ∀ v, decide (v ∈ X) = true → decide (v ∈ F ∨ v ∈ U) = true := by
    intro v hv
    simp only [decide_eq_true_eq] at hv ⊢
    exact hX v hv
  have hroot : (roots.toList.map (uCost (Prep.ofDag dag) w fun y => decide (y ∈ F ∨ y ∈ U))).sum ≤
      (roots.toList.map (uCost (Prep.ofDag dag) w fun y => decide (y ∈ X))).sum :=
    sum_le_sum_of_le roots.toList fun r hr =>
      (hp.costs_antitone w hsub (by rw [ofDag_dag]; exact hroots r hr)).1
  have hent : (F.map (uInl (Prep.ofDag dag) w fun y => decide (y ∈ F ∨ y ∈ U))).sum ≤
      (F.map (uInl (Prep.ofDag dag) w fun y => decide (y ∈ X))).sum :=
    sum_le_sum_of_le F fun t ht =>
      (hp.costs_antitone w hsub (by rw [ofDag_dag]; exact hXn t (hF t ht))).2
  have hsubl : (F.map (uInl (Prep.ofDag dag) w fun y => decide (y ∈ X))).sum ≤
      (X.map (uInl (Prep.ofDag dag) w fun y => decide (y ∈ X))).sum := by
    exact sum_le_of_subset _ hFnd hXnd hF
  unfold ulen uniformCost
  omega

end Ix.Compile.Verify.UniformModel
