import Ix.Sharing.Verify.UniformOptimal

/-!
# Stage 4: the visible counts of a search node

Visible counts are positive and antitone in the maybe-stored set, and the
counts `revisible` recomputes at a search node are below the visible counts
of the node's maybe-stored set, so the node's reclassification is sound.
-/

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (Desc child_eq_getElem setBang_getElem!)

/-- A path is empty or ends in an edge. -/
theorem desc_last {dag : Dag} {r y : Nat} (h : Desc dag r y) :
    r = y ∨ ∃ z k, Desc dag r z ∧ k < (dag.node z).children.size ∧ (dag.node z).child k = y := by
  induction h with
  | refl => exact Or.inl rfl
  | @child t u k hk _ ih =>
    rcases ih with h | ⟨z, k', hz, hk', he⟩
    · exact Or.inr ⟨t, k, .refl _, hk, h⟩
    · exact Or.inr ⟨z, k', .child k hk hz, hk', he⟩

theorem edgeAll_pos {dag : Dag} {z y k : Nat} (hk : k < (dag.node z).head.arity)
    (he : (dag.node z).child k = y) : 1 ≤ edgeAll (Prep.ofDag dag) z y := by
  unfold edgeAll edgeMult
  simp only [ofDag_dag]
  have hmem : ∀ c : Bool, continuationEdge (dag.node z) k (dag.node y) = c →
      k ∈ (List.range (dag.node z).head.arity).filter (fun i => (dag.node z).child i == y &&
        continuationEdge (dag.node z) i (dag.node y) == c) := by
    intro c hc
    simp [List.mem_filter, List.mem_range, hk, he, hc]
  cases hc : continuationEdge (dag.node z) k (dag.node y)
  · have := List.length_pos_of_mem (hmem false hc); omega
  · have := List.length_pos_of_mem (hmem true hc); omega

theorem le_sum_of_mem_nat : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_sum_of_mem_nat h; simp; omega

theorem sum_range_ge (f : Nat → Nat) {n z : Nat} (hz : z < n) :
    f z ≤ ((List.range n).map f).sum := by
  have hmem : f z ∈ (List.range n).map f := List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩
  exact le_sum_of_mem_nat hmem

/-- **Visible counts are positive** on a DAG whose roots reach every term. -/
theorem vis_pos {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y) (ms : Array Bool) :
    ∀ y, y < dag.size → 1 ≤ (visibleCounts dag roots ms).1[y]! := by
  have key : ∀ m y, dag.size - y = m → y < dag.size → 1 ≤ (visibleCounts dag roots ms).1[y]! := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro y hm hy
      rw [(visibleCounts_spec hwf roots hroots ms hy).1]
      obtain ⟨r, hr, hd⟩ := hreach y hy
      rcases desc_last hd with rfl | ⟨z, k, hz, hk, he⟩
      · have := List.count_pos_iff.mpr hr
        omega
      · have hrn := hroots r hr
        have hzn : z < dag.size := Nat.lt_of_le_of_lt (Desc.le_of_wf hwf hz hrn) hrn
        have hyz : y < z := by
          rw [← he, child_eq_getElem _ k hk]
          exact hwf.child_lt hzn (Array.getElem_mem _)
        have hk' : k < (dag.node z).head.arity := by rw [← hwf.children_size hzn]; exact hk
        have he1 := edgeAll_pos hk' he
        have hw1 : 1 ≤ visWeight ms (visibleCounts dag roots ms).1 z := by
          unfold visWeight
          split
          · exact Nat.le_refl 1
          · have := ih (dag.size - z) (by omega) z rfl hzn
            unfold visibleCap; simp only [Nat.le_min]; omega
        have := sum_range_ge (fun y' => edgeAll (Prep.ofDag dag) y' y *
          visWeight ms (visibleCounts dag roots ms).1 y') hzn
        have := Nat.mul_le_mul he1 hw1
        omega
  exact fun y hy => key _ y rfl hy

/-- **Visible counts are antitone** in the maybe-stored set. -/
theorem vis_mono {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y) {ms ms' : Array Bool}
    (hms : ∀ v : Nat, ms'[v]! = true → ms[v]! = true) :
    ∀ t, t < dag.size → (visibleCounts dag roots ms).1[t]! ≤ (visibleCounts dag roots ms').1[t]! ∧
      (visibleCounts dag roots ms).2[t]! ≤ (visibleCounts dag roots ms').2[t]! := by
  have hp := prepWF_ofDag hwf
  have key : ∀ m t, dag.size - t = m → t < dag.size →
      (visibleCounts dag roots ms).1[t]! ≤ (visibleCounts dag roots ms').1[t]! ∧
        (visibleCounts dag roots ms).2[t]! ≤ (visibleCounts dag roots ms').2[t]! := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro t hm ht
      obtain ⟨a1, a2⟩ := visibleCounts_spec hwf roots hroots ms ht
      obtain ⟨b1, b2⟩ := visibleCounts_spec hwf roots hroots ms' ht
      have hw : ∀ y ∈ List.range dag.size, t < y →
          visWeight ms (visibleCounts dag roots ms).1 y ≤
            visWeight ms' (visibleCounts dag roots ms').1 y := by
        intro y hy hty
        have hyn := List.mem_range.mp hy
        unfold visWeight
        by_cases h1 : ms'[y]! = true
        · rw [if_pos h1, if_pos (hms y h1)]
          exact Nat.le_refl 1
        · rw [if_neg h1]
          by_cases h2 : ms[y]! = true
          · rw [if_pos h2]
            have := vis_pos hwf roots hroots hreach ms' y hyn
            unfold visibleCap; simp only [Nat.le_min]; omega
          · rw [if_neg h2]
            have := (ih (dag.size - y) (by omega) y rfl hyn).1
            simp only [Nat.min_def]; split <;> split <;> omega
      have hterm : ∀ (e : Nat → Nat), (∀ y, y ≤ t → e y = 0) →
          ((List.range dag.size).map fun y => e y *
            visWeight ms (visibleCounts dag roots ms).1 y).sum ≤
          ((List.range dag.size).map fun y => e y *
            visWeight ms' (visibleCounts dag roots ms').1 y).sum := by
        intro e he
        apply sum_le_sum_of_le
        intro y hy
        by_cases hty : t < y
        · exact Nat.mul_le_mul_left _ (hw y hy hty)
        · rw [he y (by omega)]; simp
      refine ⟨?_, ?_⟩
      · rw [a1, b1]
        exact Nat.add_le_add_left (hterm _ (fun y hy => edgeAll_zero_of_le hp hy)) _
      · rw [a2, b2]
        exact Nat.add_le_add_left (hterm _ (fun y hy => edgeMult_zero_of_le hp hy false)) _
  exact fun t ht => key _ t rfl ht

/-! ## The recomputed counts of a search node -/

/-- What the area tables of a component's context satisfy. -/
structure AreaWF (dag : Dag) (roots : Array Nat) (cx : SCtx) : Prop where
  rootOcc : ∀ j, j < cx.area.size → cx.rootOcc[j]! ≤ roots.toList.count cx.area[j]!
  nodup : ∀ j, j < cx.area.size → ((cx.inEdges[j]!).toList.map (·.1)).Nodup
  lt : ∀ j, j < cx.area.size → ∀ e ∈ (cx.inEdges[j]!).toList, e.1 < dag.size
  cnt : ∀ j, j < cx.area.size → ∀ e ∈ (cx.inEdges[j]!).toList,
    e.2.1 ≤ edgeAll (Prep.ofDag dag) e.1 cx.area[j]! ∧
      e.2.2 ≤ edgeMult (Prep.ofDag dag) e.1 cx.area[j]! false

theorem foldl_pair_sum (W : Nat → Nat) :
    ∀ (l : List (Nat × Nat × Nat)) (a b : Nat),
      l.foldl (fun (dh : Nat × Nat) (e : Nat × Nat × Nat) =>
          (dh.1 + e.2.1 * W e.1, dh.2 + e.2.2 * W e.1)) (a, b) =
        (a + (l.map fun e => e.2.1 * W e.1).sum, b + (l.map fun e => e.2.2 * W e.1).sum)
  | [], a, b => by simp
  | e :: l, a, b => by
    rw [List.foldl_cons, foldl_pair_sum W l]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
    omega

theorem sum_le_sum_map {α : Type} {f g : α → Nat} :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_sum_map l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have := h a List.mem_cons_self
    omega

/-- Sum over a duplicate-free list of parents, below the sum over all terms. -/
theorem sum_parents_le (f : Nat → Nat) {L : List Nat} {n : Nat} (hL : L.Nodup)
    (hlt : ∀ q ∈ L, q < n) : (L.map f).sum ≤ ((List.range n).map f).sum :=
  sum_le_of_subset f hL List.nodup_range (fun q hq => List.mem_range.mpr (hlt q hq))

/-- **The recomputed counts are below the visible counts** of the node's
maybe-stored set (within the candidates). -/
theorem revisible_le {dag : Dag} (hwf : DagWF dag) {roots : Array Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    {w : Nat} {θ : _root_.Int} {cs : List Nat} {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx)
    (ha : AreaWF dag roots cx) {ms : Array Bool}
    (hms : ∀ v : Nat, ms[v]! = true → (ucand dag roots w)[v]! = true) :
    ∀ t, t < dag.size → (cx.revisible ms).1[t]! ≤ (visibleCounts dag roots ms).1[t]! ∧
      (cx.revisible ms).2[t]! ≤ (visibleCounts dag roots ms).2[t]! := by
  let Vm := visibleCounts dag roots ms
  let Inv : Array Nat × Array Nat → Prop := fun dh =>
    ∀ t, t < dag.size → dh.1[t]! ≤ Vm.1[t]! ∧ dh.2[t]! ≤ Vm.2[t]!
  have hinit : Inv cx.vis0 := by
    intro t ht
    rw [hcx.vis0]
    exact vis_mono hwf roots hroots hreach hms t ht
  have hstep : ∀ (ds hs : Array Nat) (k : Nat), Inv (ds, hs) → k < cx.area.size →
      Inv (let j := cx.area.size - 1 - k
        let y := cx.area[j]!
        let r := cx.rootOcc[j]!
        let dh := cx.inEdges[j]!.foldl (fun (dh : Nat × Nat) (e : Nat × Nat × Nat) =>
          let wq := if ms[e.1]! then 1 else min ds[e.1]! visibleCap
          (dh.1 + e.2.1 * wq, dh.2 + e.2.2 * wq)) (r, r)
        (ds.set! y dh.1, hs.set! y dh.2)) := by
    intro ds hs k hinv hk
    simp only
    generalize hj : cx.area.size - 1 - k = j
    have hjs : j < cx.area.size := by omega
    let W : Nat → Nat := fun q => if ms[q]! then 1 else min ds[q]! visibleCap
    have hfold := foldl_pair_sum W (cx.inEdges[j]!).toList (cx.rootOcc[j]!) (cx.rootOcc[j]!)
    rw [Array.foldl_toList] at hfold
    simp only [W] at hfold
    rw [hfold]
    generalize hy : cx.area[j]! = y
    have hW : ∀ q, q < dag.size → W q ≤ visWeight ms Vm.1 q := by
      intro q hq
      simp only [W, visWeight]
      split
      · exact Nat.le_refl 1
      · have := (hinv q hq).1
        simp only at this
        simp only [Nat.min_def]; split <;> split <;> omega
    have hbound : ∀ (c : Bool), y < dag.size →
        (cx.rootOcc[j]! + ((cx.inEdges[j]!).toList.map fun e =>
          (if c then e.2.2 else e.2.1) * W e.1).sum) ≤
        roots.toList.count y + ((List.range dag.size).map fun q =>
          (if c then edgeMult (Prep.ofDag dag) q y false else edgeAll (Prep.ofDag dag) q y) *
            visWeight ms Vm.1 q).sum := by
      intro c hyn
      have h1 : cx.rootOcc[j]! ≤ roots.toList.count y := by rw [← hy]; exact ha.rootOcc j hjs
      have h2 : ((cx.inEdges[j]!).toList.map fun e => (if c then e.2.2 else e.2.1) * W e.1).sum ≤
          (((cx.inEdges[j]!).toList.map (·.1)).map fun q =>
            (if c then edgeMult (Prep.ofDag dag) q y false else edgeAll (Prep.ofDag dag) q y) *
              visWeight ms Vm.1 q).sum := by
        rw [List.map_map]
        apply sum_le_sum_map
        intro e he
        have hc := ha.cnt j hjs e he
        rw [hy] at hc
        have hq := ha.lt j hjs e he
        cases c
        · exact Nat.mul_le_mul hc.1 (hW e.1 hq)
        · exact Nat.mul_le_mul hc.2 (hW e.1 hq)
      have h3 := sum_parents_le (fun q =>
          (if c then edgeMult (Prep.ofDag dag) q y false else edgeAll (Prep.ofDag dag) q y) *
            visWeight ms Vm.1 q) (ha.nodup j hjs)
        (fun q hq => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
          exact ha.lt j hjs e he)
      omega
    intro t ht
    simp only
    rw [setBang_getElem!, setBang_getElem!]
    by_cases hyt : y = t
    · subst hyt
      have e := visibleCounts_spec hwf roots hroots ms ht
      refine ⟨?_, ?_⟩
      · by_cases hs : y < ds.size
        · rw [if_pos ⟨rfl, hs⟩]
          have := hbound false ht
          simp only [Bool.false_eq_true, if_false] at this
          rw [e.1]; exact this
        · rw [if_neg (fun h => hs h.2)]; exact (hinv y ht).1
      · by_cases hs : y < hs.size
        · rw [if_pos ⟨rfl, hs⟩]
          have := hbound true ht
          simp only [if_true] at this
          rw [e.2]; exact this
        · rw [if_neg (fun h => hs h.2)]; exact (hinv y ht).2
    · rw [if_neg (fun h => hyt h.1), if_neg (fun h => hyt h.1)]
      exact hinv t ht
  have hall : ∀ (l : List Nat) (acc : Array Nat × Array Nat), (∀ k ∈ l, k < cx.area.size) →
      Inv acc → Inv (l.foldl (fun (acc : Array Nat × Array Nat) k =>
        match acc with
        | (ds, hs) =>
          let j := cx.area.size - 1 - k
          let y := cx.area[j]!
          let r := cx.rootOcc[j]!
          let dh := cx.inEdges[j]!.foldl (fun (dh : Nat × Nat) (e : Nat × Nat × Nat) =>
            let wq := if ms[e.1]! then 1 else min ds[e.1]! visibleCap
            (dh.1 + e.2.1 * wq, dh.2 + e.2.2 * wq)) (r, r)
          (ds.set! y dh.1, hs.set! y dh.2)) acc) := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons k l ih =>
      intro acc hl h
      rw [List.foldl_cons]
      apply ih _ (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))
      obtain ⟨ds, hs⟩ := acc
      exact hstep ds hs k h (hl k List.mem_cons_self)
  intro t ht
  exact hall (List.range cx.area.size) cx.vis0 (fun k hk => List.mem_range.mp hk) hinit t ht

/-- The node's bounds are below the bounds of its maybe-stored set. -/
theorem rebound_le {dag : Dag} (hwf : DagWF dag) {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx) {ms : Array Bool}
    (hms : ∀ v : Nat, ms[v]! = true → (ucand dag roots w)[v]! = true) :
    BLe (cx.rebound ms) (uniformBounds (Prep.ofDag dag) w ms) := by
  have hp := prepWF_ofDag hwf
  unfold SCtx.rebound
  rw [hcx.prep, hcx.width, hcx.bounds0, ← Array.foldl_toList]
  exact hp.boundsFold_le w cx.area.toList _
    (uniformBounds_antitone (Prep.ofDag dag) w hms) (uniformBounds_size _ _ _)

/-- **Reclassification at a search node is sound.** A member whose gain under
the node's bounds and recomputed counts reaches the threshold (with
`1 ≤ d` and `h ≤ d`) is in every minimum that stores no decided-out term. -/
theorem forced_mem {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} {cs : List Nat}
    (hG : GlobalWF dag roots w θ cs) {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx)
    (ha : AreaWF dag roots cx) {outAll : Array Nat} {Y : List Nat}
    (hY : IsMinimum dag w roots Y) (hYo : ∀ t ∈ outAll.toList, t ∉ Y) {t : Nat}
    (htm : t ∈ cx.members.toList)
    (hd1 : 1 ≤ (cx.revisible (msOf cx.cand outAll)).1[t]!)
    (hhd : (cx.revisible (msOf cx.cand outAll)).2[t]! ≤ (cx.revisible (msOf cx.cand outAll)).1[t]!)
    (hgain : storedGainWith cx.up.prep (cx.rebound (msOf cx.cand outAll)) cx.up.w t
      (cx.revisible (msOf cx.cand outAll)).1[t]! (cx.revisible (msOf cx.cand outAll)).2[t]! ≥
        cx.theta) : t ∈ Y := by
  have hwf := hG.wf
  obtain ⟨htn, htu⟩ := hcx.mem t htm
  have htc : (ucand dag roots w)[t]! = true := ucand_of_ucls htn (Or.inr htu)
  generalize hmsd : msOf cx.cand outAll = ms at hd1 hhd hgain
  have hms : ∀ v : Nat, ms[v]! = true → (ucand dag roots w)[v]! = true := by
    intro v hv
    rw [← hmsd] at hv
    have := (msOf_spec cx.cand outAll v).mp hv
    rw [hcx.cand] at this
    exact this.1
  have hYms : ∀ s ∈ Y, ms[s]! = true := by
    intro s hs
    rw [← hmsd]
    apply (msOf_spec cx.cand outAll s).mpr
    obtain ⟨hsn, hcl⟩ := hG.min_class hY hs
    rw [hcx.cand]
    exact ⟨ucand_of_ucls hsn hcl, fun h => hYo s h hs⟩
  have hble := rebound_le hwf hcx hms
  have hvis := revisible_le hwf hG.hroots hG.reach hcx ha hms t htn
  rw [hcx.prep, hcx.width, hcx.theta] at hgain
  refine Classical.byContradiction (fun htY => ?_)
  have hθ := hG.theta_ok hY htn htc htY
  apply htY
  exact stored_in_minimum hwf roots hG.hroots hG.reach w ms hY hYms htn
    (deg_of_ucls htn (Or.inr htu)) (hble t).1 (hble t).2.1 hvis.1 hvis.2 hhd hd1
    (fun _ => minimum_length_lt hwf hG.spines roots hG.hroots w hY htn htc htY)
    (by rcases hθ with h | ⟨h, hb⟩
        · left; rw [h] at hgain; exact hgain
        · right; rw [h] at hgain; exact ⟨hgain, hb⟩)

end Ix.Sharing.Verify.UniformModel
