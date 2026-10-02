import Ix.Compile.Verify.UniformExchange

/-!
# The certain-stored gain bound

The executable facts behind `storedGain`: `graphFacts` counts in-degrees and
head in-degrees exactly as the edges `edgeMult` (`edgeCounts_spec`), and
`uniformBounds` gives lower bounds of the model values for every stored set
within the candidates (`bounds_sound`). With the exchange of
`UniformExchange` this gives the stage-2 inequality
`uniformCost (S ∪ {t}) ≤ uniformCost S - storedGain t + 1`.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact

/-! ## In-degrees -/

theorem modify_add_getElem! (acc : Array Nat) (c t : Nat) :
    (acc.modify c (· + 1))[t]! = acc[t]! + (if c = t ∧ c < acc.size then 1 else 0) := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases hct : c = t
  · subst hct
    by_cases hc : c < acc.size
    · simp [hc]
    · simp [hc]
  · simp [hct]

theorem foldl_modify_count :
    ∀ (l : List Nat) (acc : Array Nat) (t : Nat), (∀ c ∈ l, c < acc.size) →
      (l.foldl (fun acc c => acc.modify c (· + 1)) acc)[t]! = acc[t]! + l.count t ∧
        (l.foldl (fun acc c => acc.modify c (· + 1)) acc).size = acc.size := by
  intro l
  induction l with
  | nil => intro acc t _; simp
  | cons c cs ih =>
    intro acc t hl
    rw [List.foldl_cons]
    have hc := hl c List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (acc.modify c (· + 1)) t (fun c' hc' => by
      simpa using hl c' (List.mem_cons_of_mem _ hc'))
    refine ⟨?_, by rw [h2]; simp⟩
    rw [h1, modify_add_getElem!, List.count_cons]
    by_cases hct : c = t
    · subst hct; simp [hc]; omega
    · simp [hct]

theorem foldl_if_modify {α : Type} (P : α → Bool) (g : α → Nat) :
    ∀ (l : List α) (acc : Array Nat),
      l.foldl (fun acc i => if P i then acc else acc.modify (g i) (· + 1)) acc =
        ((l.filter fun i => !P i).map g).foldl (fun acc c => acc.modify c (· + 1)) acc := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons, List.filter_cons]
    cases hP : P x <;> simp [ih]

theorem count_map_filter (g : Nat → Nat) (Q : Nat → Bool) (l : List Nat) (t : Nat) :
    ((l.filter Q).map g).count t = (l.filter fun i => Q i && g i == t).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hQ : Q x <;> by_cases hg : g x = t <;> simp [hg, ih]

theorem filter_length_split {α : Type} (a b : α → Bool) (l : List α) :
    (l.filter a).length = (l.filter fun i => a i && b i == false).length +
      (l.filter fun i => a i && b i == true).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases ha : a x <;> cases hb : b x <;> simp [ih] <;> omega

/-- **In-degrees.** `edgeCounts` (`graphFacts.deg` / `.headDeg`) counts the
root occurrences plus every edge (every non-continuation edge) into `t`. -/
theorem edgeCounts_spec {dag : Dag} (h : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (headOnly : Bool) (t : Nat) :
    (edgeCounts dag roots headOnly)[t]! = roots.toList.count t +
      ((List.range dag.size).map fun y =>
        if headOnly then edgeMult (Prep.ofDag dag) y t false
        else edgeMult (Prep.ofDag dag) y t false + edgeMult (Prep.ofDag dag) y t true).sum := by
  let step := fun (acc : Array Nat) (y : Nat) =>
    (List.range (dag.node y).children.size).foldl (fun acc i =>
      if headOnly && continuationEdge (dag.node y) i (dag.node ((dag.node y).child i)) then acc
      else acc.modify ((dag.node y).child i) (· + 1)) acc
  have hstep : ∀ (acc : Array Nat) (y : Nat), acc.size = dag.size → y < dag.size →
      (step acc y)[t]! = acc[t]! + (if headOnly then edgeMult (Prep.ofDag dag) y t false
        else edgeMult (Prep.ofDag dag) y t false + edgeMult (Prep.ofDag dag) y t true) ∧
        (step acc y).size = dag.size := by
    intro acc y hs hy
    simp only [step]
    rw [foldl_if_modify (fun i => headOnly &&
      continuationEdge (dag.node y) i (dag.node ((dag.node y).child i))) (dag.node y).child]
    have hlt : ∀ c ∈ ((List.range (dag.node y).children.size).filter fun i =>
        !(headOnly && continuationEdge (dag.node y) i (dag.node ((dag.node y).child i)))).map
          (dag.node y).child, c < acc.size := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
      rw [Ix.Compile.Verify.SharingExact.child_eq_getElem _ i hi']
      have := h.child_lt hy (Array.getElem_mem hi')
      omega
    obtain ⟨h1, h2⟩ := foldl_modify_count _ acc t hlt
    refine ⟨?_, by rw [h2, hs]⟩
    rw [h1, count_map_filter]
    congr 1
    have har := h.arity y hy
    rw [← dag_node_eq hy] at har
    unfold edgeMult
    rw [ofDag_dag, ← har]
    cases headOnly with
    | true =>
      simp only [if_true]
      congr 1
      apply List.filter_congr
      intro i _
      cases hc : continuationEdge (dag.node y) i (dag.node ((dag.node y).child i)) <;>
        by_cases hct : (dag.node y).child i = t <;> simp_all
    | false =>
      simp only [Bool.false_eq_true, if_false, Bool.false_and, Bool.not_false, Bool.true_and]
      rw [filter_length_split (fun i => (dag.node y).child i == t)
        (fun i => continuationEdge (dag.node y) i (dag.node t))]
  have hinv : ∀ m, m ≤ dag.size →
      ((List.range m).foldl step
          (roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate dag.size 0)))[t]! =
        roots.toList.count t + ((List.range m).map fun y =>
          if headOnly then edgeMult (Prep.ofDag dag) y t false
          else edgeMult (Prep.ofDag dag) y t false + edgeMult (Prep.ofDag dag) y t true).sum ∧
      ((List.range m).foldl step
          (roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate dag.size 0))).size =
        dag.size := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
      rw [← Array.foldl_toList]
      obtain ⟨h1, h2⟩ := foldl_modify_count roots.toList (Array.replicate dag.size 0) t
        (fun c hc => by simpa using hroots c hc)
      refine ⟨?_, by rw [h2]; simp⟩
      rw [h1]
      have : (Array.replicate dag.size (0 : Nat))[t]! = 0 := by
        simp only [getElem!_def, Array.getElem?_replicate]
        by_cases ht : t < dag.size <;> simp [ht]
      rw [this]
      omega
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [foldl_range_succ, sum_range_succ']
      obtain ⟨h3, h4⟩ := hstep _ m h2 (by omega)
      exact ⟨by rw [h3, h1]; omega, h4⟩
  unfold edgeCounts
  rw [foldRange_zero]
  exact (hinv dag.size (Nat.le_refl _)).1

/-! ## The bounds -/

/-- The recurrence of `uniformBounds` at `t`. -/
def BoundsRow (p : Prep) (w : Nat) (ms : Array Bool) (b : UBounds) (t : Nat) : Prop :=
  (p.family[t]! = .none →
      b.inlineLB[t]! = (p.dag.node t).children.foldl (fun acc c => acc + b.headLB[c]!)
        (p.dag.node t).head.ownBytes ∧ b.mergedLB[t]! = b.inlineLB[t]!) ∧
    (p.family[t]! ≠ .none →
      b.mergedLB[t]! = (p.dag.node t).sideExtra + b.headLB[(p.dag.node t).sideChild]! +
        (if p.family[snext p t]! = p.family[t]! then b.contLB[snext p t]! else b.headLB[snext p t]!) ∧
      b.inlineLB[t]! = 1 + b.mergedLB[t]!) ∧
    b.headLB[t]! = (if ms[t]! then min w b.inlineLB[t]! else b.inlineLB[t]!) ∧
    b.contLB[t]! = (if ms[t]! then min w b.mergedLB[t]! else b.mergedLB[t]!)

theorem BoundsRow.congr {p : Prep} (hp : PrepWF p) {w : Nat} {ms : Array Bool} {b b' : UBounds}
    {t : Nat} (ht : t < p.dag.size)
    (hi : b'.inlineLB[t]! = b.inlineLB[t]!) (hm : b'.mergedLB[t]! = b.mergedLB[t]!)
    (hh : ∀ c, c ≤ t → b'.headLB[c]! = b.headLB[c]!) (hc : ∀ c, c ≤ t → b'.contLB[c]! = b.contLB[c]!)
    (hrow : BoundsRow p w ms b t) : BoundsRow p w ms b' t := by
  obtain ⟨h1, h2, h3, h4⟩ := hrow
  refine ⟨fun hf => ?_, fun hf => ?_, by rw [hh t (Nat.le_refl _), hi, h3],
    by rw [hc t (Nat.le_refl _), hm, h4]⟩
  · obtain ⟨a, b⟩ := h1 hf
    refine ⟨?_, by rw [hm, hi, b]⟩
    rw [hi, a]
    exact foldl_add_congr _ _ fun c hc' => (hh c (by
      have := hp.dag.child_lt ht hc'; omega)).symm
  · obtain ⟨a, b⟩ := h2 hf
    have hs := hp.sideChild_lt ht hf
    have hn := hp.snext_lt ht hf
    refine ⟨?_, by rw [hi, hm, b]⟩
    rw [hm, a, hh _ (by omega), hh _ (by omega), hc _ (by omega)]

theorem setBang_getElem!_ne {α : Type} [Inhabited α] (a : Array α) {i j : Nat} (v : α)
    (h : j ≠ i) : (a.set! i v)[j]! = a[j]! := by
  rw [Ix.Compile.Verify.SharingExact.setBang_getElem!, if_neg (fun h' => h h'.1.symm)]

theorem setBang_getElem!_self {α : Type} [Inhabited α] (a : Array α) {i : Nat} (v : α)
    (h : i < a.size) : (a.set! i v)[i]! = v := by
  rw [Ix.Compile.Verify.SharingExact.setBang_getElem!, if_pos ⟨rfl, h⟩]

/-- `uniformBounds` satisfies its recurrence at every term. -/
theorem PrepWF.uniformBounds_spec {p : Prep} (hp : PrepWF p) (w : Nat) (ms : Array Bool) (t : Nat)
    (ht : t < p.dag.size) : BoundsRow p w ms (uniformBounds p w ms) t := by
  let init : UBounds :=
    { inlineLB := Array.replicate p.dag.size 0, mergedLB := Array.replicate p.dag.size 0,
      headLB := Array.replicate p.dag.size 0, contLB := Array.replicate p.dag.size 0 }
  have hinv : ∀ m, m ≤ p.dag.size →
      let b := (List.range m).foldl (boundsStep p w ms) init
      (b.inlineLB.size = p.dag.size ∧ b.mergedLB.size = p.dag.size ∧
        b.headLB.size = p.dag.size ∧ b.contLB.size = p.dag.size) ∧
      ∀ t, t < m → BoundsRow p w ms b t := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simp [init], fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨⟨s1, s2, s3, s4⟩, hrows⟩ := ih (by omega)
      simp only at s1 s2 s3 s4 hrows ⊢
      rw [foldl_range_succ]
      generalize (List.range m).foldl (boundsStep p w ms) init = b at s1 s2 s3 s4 hrows
      have hmn : m < p.dag.size := by omega
      -- the new arrays agree with the old ones below `m`
      have keep : ∀ c, c < m →
          (boundsStep p w ms b m).inlineLB[c]! = b.inlineLB[c]! ∧
          (boundsStep p w ms b m).mergedLB[c]! = b.mergedLB[c]! ∧
          (boundsStep p w ms b m).headLB[c]! = b.headLB[c]! ∧
          (boundsStep p w ms b m).contLB[c]! = b.contLB[c]! := by
        intro c hc
        unfold boundsStep
        simp only
        split <;> exact ⟨setBang_getElem!_ne _ _ (by omega), setBang_getElem!_ne _ _ (by omega),
          setBang_getElem!_ne _ _ (by omega), setBang_getElem!_ne _ _ (by omega)⟩
      refine ⟨by unfold boundsStep; simp only; split <;> simp [s1, s2, s3, s4], fun t ht' => ?_⟩
      by_cases htm : t = m
      · subst htm
        unfold boundsStep
        simp only
        by_cases hf : p.family[t]! = .none
        · have hfb : (p.family[t]! == Family.none) = true := by simp [hf]
          simp only [hfb, if_true]
          refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hf h, ?_, ?_⟩
          · rw [setBang_getElem!_self _ _ (by omega)]
            exact foldl_add_congr _ _ fun c hc => (setBang_getElem!_ne _ _ (by
              have := hp.dag.child_lt hmn hc; omega)).symm
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_self _ _ (by omega)]
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_self _ _ (by omega)]
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_self _ _ (by omega)]
        · have hfb : (p.family[t]! == Family.none) = false := by simpa using hf
          simp only [hfb, Bool.false_eq_true, if_false]
          have hs := hp.sideChild_lt hmn hf
          have hn := hp.snext_lt hmn hf
          refine ⟨fun h => absurd h hf, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_ne _ _ (by omega),
              setBang_getElem!_ne (i := t) _ _ (show snext p t ≠ t by omega),
              setBang_getElem!_ne (i := t) _ _ (show snext p t ≠ t by omega)]
            unfold snext
            simp only [beq_iff_eq]
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_self _ _ (by omega)]
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_self _ _ (by omega)]
          · rw [setBang_getElem!_self _ _ (by omega), setBang_getElem!_self _ _ (by omega)]
      · obtain ⟨k1, k2, _, _⟩ := keep t (by omega)
        exact BoundsRow.congr hp (by omega) k1 k2
          (fun c hc => (keep c (by omega)).2.2.1) (fun c hc => (keep c (by omega)).2.2.2)
          (hrows t (by omega))
  unfold uniformBounds
  rw [foldRange_zero]
  exact (hinv p.dag.size (Nat.le_refl _)).2 t ht

/-- The bytes of `t` as a continuation: `min w M` if `t` is stored, else `M`. -/
def contVal (p : Prep) (w : Nat) (S : Nat → Bool) (t : Nat) : Nat :=
  if S t then min w (mergedOf p w S (uCost p w S) t) else mergedOf p w S (uCost p w S) t

theorem contVal_le (p : Prep) (w : Nat) (S : Nat → Bool) (t : Nat) :
    contVal p w S t ≤ mergedOf p w S (uCost p w S) t := by
  unfold contVal; split <;> omega

/-- `M_S(t)` is at least `t`'s own side bytes plus the continuation from the
next spine node (`contVal` if it continues the spine, its standalone cost
otherwise). -/
theorem PrepWF.merged_ge {p : Prep} (hp : PrepWF p) (w : Nat) (S : Nat → Bool) {t : Nat}
    (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) :
    sideCost p (uCost p w S) t +
        (if p.family[snext p t]! = p.family[t]! then contVal p w S (snext p t)
          else uCost p w S (snext p t)) ≤ mergedOf p w S (uCost p w S) t := by
  have hlt := hp.snext_lt ht hf
  unfold mergedOf
  rcases List.mem_cons.mp (foldl_min_mem (mergedCuts p w S (uCost p w S) t)
      (prefixSides p (uCost p w S) t p.spineLen[t]! + uCost p w S p.tail[t]!)) with h | h
  · rw [h]
    rcases hp.spine_step ht hf with ⟨hs, hl, htl⟩ | ⟨hs, hl, htl⟩
    · rw [if_pos hs, hl, htl]
      simp only [prefixSides]
      have := contVal_le p w S (snext p t)
      have := foldl_min_le (mergedCuts p w S (uCost p w S) (snext p t))
        (prefixSides p (uCost p w S) (snext p t) p.spineLen[snext p t]! +
          uCost p w S p.tail[snext p t]!) _ List.mem_cons_self
      unfold mergedOf at *
      omega
    · rw [if_neg hs, hl, htl]
      simp [prefixSides]
  · obtain ⟨j, hj1, hj, hSj, hc⟩ := mem_mergedCuts h
    rw [hc]
    rcases hp.spine_step ht hf with ⟨hs, hl, htl⟩ | ⟨hs, hl, htl⟩
    · rw [if_pos hs]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [prefixSides]
      by_cases hj' : j' = 0
      · subst hj'
        simp only [prefixSides]
        have : contVal p w S (snext p t) ≤ w := by
          unfold contVal
          simp only [spineAt] at hSj
          rw [if_pos hSj]; omega
        omega
      · have hmem := merged_mem_mergedCuts p w S (uCost p w S) (x := snext p t) (j := j')
          (by omega) (by omega) (by simpa [spineAt] using hSj)
        have := foldl_min_le (mergedCuts p w S (uCost p w S) (snext p t))
          (prefixSides p (uCost p w S) (snext p t) p.spineLen[snext p t]! +
            uCost p w S p.tail[snext p t]!) _ (List.mem_cons_of_mem _ hmem)
        have := contVal_le p w S (snext p t)
        unfold mergedOf at *
        omega
    · omega

/-- **Soundness of the bounds.** For every stored set within the
candidates, `uniformBounds` lower-bounds the standalone cost, the inline
cost and the merged continuation of every term. -/
theorem PrepWF.bounds_sound {p : Prep} (hp : PrepWF p) (w : Nat) (ms : Array Bool)
    (S : Nat → Bool) (hS : ∀ y, S y = true → ms[y]! = true) :
    ∀ t, t < p.dag.size →
      (uniformBounds p w ms).headLB[t]! ≤ uCost p w S t ∧
        (uniformBounds p w ms).inlineLB[t]! ≤ uInl p w S t ∧
        (p.family[t]! ≠ .none →
          (uniformBounds p w ms).mergedLB[t]! ≤ mergedOf p w S (uCost p w S) t ∧
            (uniformBounds p w ms).contLB[t]! ≤ contVal p w S t) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    obtain ⟨r1, r2, r3, r4⟩ := hp.uniformBounds_spec w ms t ht
    have hinl : (uniformBounds p w ms).inlineLB[t]! ≤ uInl p w S t ∧
        (p.family[t]! ≠ .none →
          (uniformBounds p w ms).mergedLB[t]! ≤ mergedOf p w S (uCost p w S) t) := by
      by_cases hf : p.family[t]! = .none
      · obtain ⟨a, _⟩ := r1 hf
        refine ⟨?_, fun h => absurd hf h⟩
        rw [a]
        unfold uInl inlOf
        rw [if_pos hf, ← Array.foldl_toList, ← Array.foldl_toList, foldl_add_eq_sum,
          foldl_add_eq_sum]
        have : ∀ c ∈ (p.dag.node t).children.toList,
            (uniformBounds p w ms).headLB[c]! ≤ uCost p w S c := by
          intro c hc
          have hct := hp.dag.child_lt ht (Array.mem_toList_iff.mp hc)
          exact (ih c hct (by omega)).1
        have := sum_le_sum_of_le' this
        omega
      · obtain ⟨a, b⟩ := r2 hf
        have hm : (uniformBounds p w ms).mergedLB[t]! ≤ mergedOf p w S (uCost p w S) t := by
          rw [a]
          have hge := hp.merged_ge w S ht hf
          have hs := hp.sideChild_lt ht hf
          have hn := hp.snext_lt ht hf
          have hside := (ih _ hs (by omega)).1
          unfold sideCost at hge
          by_cases hsame : p.family[snext p t]! = p.family[t]!
          · rw [if_pos hsame] at hge ⊢
            have := ((ih _ hn (by omega)).2.2 (by rw [hsame]; exact hf)).2
            omega
          · rw [if_neg hsame] at hge ⊢
            have := (ih _ hn (by omega)).1
            omega
        refine ⟨?_, fun _ => hm⟩
        rw [b]
        have := (inl_merged_bounds p w S (uCost p w S) hf).1
        unfold uInl
        omega
    refine ⟨?_, hinl.1, fun hf => ⟨hinl.2 hf, ?_⟩⟩
    · rw [r3, hp.uCost_eq w S t ht]
      unfold costOf
      have := hinl.1
      unfold uInl at this
      by_cases hSt : S t = true
      · rw [if_pos (hS t hSt), if_pos hSt]; omega
      · simp only [hSt, Bool.false_eq_true, if_false]
        split <;> omega
    · rw [r4]
      unfold contVal
      have := hinl.2 hf
      by_cases hSt : S t = true
      · rw [if_pos (hS t hSt), if_pos hSt]; omega
      · simp only [hSt, Bool.false_eq_true, if_false]
        split <;> omega
where
  sum_le_sum_of_le' {f g : Nat → Nat} {l : List Nat} (h : ∀ k ∈ l, f k ≤ g k) :
      (l.map f).sum ≤ (l.map g).sum := sum_le_sum_of_le l h

/-! ## Counting over a whole encoding -/

theorem sum_ge_of_covers (f : Nat → Nat) : ∀ (n : Nat) (l : List Nat), (∀ y, y < n → y ∈ l) →
    ((List.range n).map f).sum ≤ (l.map f).sum := by
  intro n
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro l hl
    rw [sum_range_succ']
    have hn := hl n (by omega)
    have hperm := List.perm_cons_erase hn
    rw [(hperm.map f).sum_nat, List.map_cons, List.sum_cons]
    have := ih (l.erase n) (fun y hy => (List.mem_erase_of_ne (by omega)).mpr (hl y (by omega)))
    omega

/-- Every term of the DAG is written somewhere in a complete encoding whose
roots reach every term. -/
theorem PrepWF.encoding_covers {p : Prep} (hp : PrepWF p) {S : List Nat} {entry : Nat → WTree}
    {roots : List Nat} {rootsW : List WTree}
    (h : EncodingWF p (fun y => decide (y ∈ S)) S entry roots rootsW)
    (_hSin : ∀ s ∈ S, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size)
    (hreach : ∀ y, y < p.dag.size → ∃ r ∈ roots, Ix.Compile.Verify.SharingExact.Desc p.dag r y) :
    ∀ y, y < p.dag.size →
      y ∈ (rootsW.map (WTree.written p)).flatten ++ (S.map fun s => (entry s).written p).flatten := by
  -- terms below a stored term are written by the entries
  have hentry : ∀ s, s < p.dag.size → s ∈ S → ∀ y, Ix.Compile.Verify.SharingExact.Desc p.dag s y →
      y ∈ (S.map fun s => (entry s).written p).flatten := by
    intro s
    induction s using Nat.strongRecOn with
    | _ s ih =>
      intro hs hsS y hd
      obtain ⟨hv, hns⟩ := h.1 s hsS
      rcases hp.cover hv hs y hd with hw | ⟨s', hs', hd'⟩
      · exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨s, hsS, rfl⟩, hw⟩
      · obtain ⟨hS', hle, hlt⟩ := hp.shares_lt hv hs s' hs'
        have hlt' := hlt hns
        exact ih s' hlt' (by omega) (by simpa using hS') y hd'
  intro y hy
  obtain ⟨r, hr, hd⟩ := hreach y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hlen := (Ix.Compile.Verify.SharingExact.forall₂_getElem h.2).1
  have hv := (Ix.Compile.Verify.SharingExact.forall₂_getElem h.2).2 i hi (by omega)
  rcases hp.cover hv (hroots _ hr) y hd with hw | ⟨s, hs, hd'⟩
  · exact List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨rootsW[i], List.getElem_mem (by omega), rfl⟩, hw⟩)
  · obtain ⟨hS, hle, _⟩ := hp.shares_lt hv (hroots _ hr) s hs
    exact List.mem_append_right _ (hentry s (by have := hroots _ hr; omega) (by simpa using hS) y hd')

theorem subst_isShare {p : Prep} {S : Nat → Bool} {t : Nat} (rh rc : Bool) {x : Nat} {T : WTree}
    (h : Valid p S x T) (hs : T.isShare = false) (hxt : x ≠ t) :
    (T.subst p t rh rc).isShare = false := by
  cases h with
  | share => simp [WTree.isShare] at hs
  | node => simp [WTree.subst, hxt, WTree.isShare]
  | teleCut =>
    simp only [WTree.subst, hxt, if_false]
    split <;> (try split) <;> rfl
  | teleFull =>
    simp only [WTree.subst, hxt, if_false]
    split <;> (try split) <;> rfl

theorem topIs_root {p : Prep} {S : Nat → Bool} {t : Nat} (hSt : S t = false) :
    ∀ {roots : List Nat} {rootsW : List WTree}, List.Forall₂ (Valid p S) roots rootsW →
      (rootsW.map fun T => if T.topIs t then 1 else 0).sum = roots.count t
  | _, _, .nil => rfl
  | r :: rs, T :: Ts, .cons hv hs => by
    simp only [List.map_cons, List.sum_cons, List.count_cons, topIs_root hSt hs]
    by_cases hrt : r = t
    · rw [if_pos ((top_iff hSt hv).mpr hrt)]; simp [hrt]; omega
    · rw [if_neg (fun h => hrt ((top_iff hSt hv).mp (by simpa using h)))]
      simp [hrt]

theorem forall₂_imp_mem {α β : Type} {R R' : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ x ∈ xs, ∀ y, R x y → R' x y) → List.Forall₂ R' xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons hr hs, h =>
    .cons (h _ List.mem_cons_self _ hr)
      (forall₂_imp_mem hs fun x hx y hxy => h x (List.mem_cons_of_mem _ hx) y hxy)

theorem forall₂_mem_right' {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil => fun _ h => by cases h
  | _, _, .cons hr hs => fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, h'⟩ := forall₂_mem_right' hs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h'⟩
/-- **Exchange with the encoding's counts.** For `t ∉ S` and an encoding
`E, R` of `S` that attains its length: adding `t` costs at most its optimal
entry plus the growth of the count's TagN, and saves `inl_S(t) - w` per
head occurrence and `M_S(t) - w` per continuation occurrence of `t` in the
encoding (when positive). -/
theorem PrepWF.exchange_counts {p : Prep} (hp : PrepWF p) (w : Nat) {S : List Nat}
    (hSin : ∀ s ∈ S, s < p.dag.size) (roots : List Nat) (hroots : ∀ r ∈ roots, r < p.dag.size)
    {t : Nat} (htn : t < p.dag.size) (htS : t ∉ S) {E : Nat → WTree} {R : List WTree}
    (hEnc : EncodingWF p (fun y => decide (y ∈ S)) S E roots R)
    (hcost : encodingCost p w S E R = uniformCost p w (fun y => decide (y ∈ S)) S roots) :
    let A := fun y => decide (y ∈ S)
    let I := uInl p w A t
    let M := mergedOf p w A (uCost p w A) t
    uniformCost p w (fun y => decide (y ∈ t :: S)) (t :: S) roots + tag0Size S.length +
        ((S.map fun s => (E s).occH t).sum + (R.map (WTree.occH t)).sum) *
          (if w ≤ I then I - w else 0) +
        ((S.map fun s => (E s).occC p t).sum + (R.map (WTree.occC p t)).sum) *
          (if w ≤ M then M - w else 0) ≤
      uniformCost p w A S roots + tag0Size (S.length + 1) + I := by
  intro A I M
  have hSt : A t = false := by simp [A, htS]
  have hA' : (fun y => decide (y ∈ t :: S)) = addT A t := by
    funext y
    simp only [A, addT, List.mem_cons]
    by_cases hy : y = t <;> by_cases hyS : y ∈ S <;> simp [hy, hyS]
  rw [hA']
  obtain ⟨Tt, hTt, hTts, hTtc⟩ := (hp.exists_opt w A t htn).2
  let rh := decide (w ≤ I)
  let rc := decide (w ≤ M)
  have hrh : rh = true → w ≤ uInl p w A t := fun h => by simpa [rh] using h
  have hrc : rc = true → w ≤ mergedOf p w A (uCost p w A) t := fun h => by simpa [rc] using h
  have hAh : (if rh then uInl p w A t - w else 0) = (if w ≤ I then I - w else 0) := by
    simp only [rh, decide_eq_true_eq]; rfl
  have hAc : (if rc then mergedOf p w A (uCost p w A) t - w else 0) =
      (if w ≤ M then M - w else 0) := by
    simp only [rc, decide_eq_true_eq]; rfl
  generalize (if w ≤ I then I - w else 0) = Ah at hAh ⊢
  generalize (if w ≤ M then M - w else 0) = Ac at hAc ⊢
  let E' : Nat → WTree := fun y => if y = t then Tt else (E y).subst p t rh rc
  let R' := R.map (WTree.subst p t rh rc)
  -- the substitution facts per writing
  have hsubE : ∀ s ∈ S, Valid p (addT A t) s ((E s).subst p t rh rc) ∧
      ((E s).subst p t rh rc).cost p w + (E s).occH t * Ah + (E s).occC p t * Ac ≤
        (E s).cost p w := by
    intro s hs
    obtain ⟨h1, h2⟩ := hp.subst_spec w hSt htn rh rc hrh hrc (hEnc.1 s hs).1 (hSin s hs)
    rw [hAh, hAc] at h2
    exact ⟨h1, h2⟩
  have hsubR : List.Forall₂ (fun r T => Valid p (addT A t) r (T.subst p t rh rc) ∧
      (T.subst p t rh rc).cost p w + T.occH t * Ah + T.occC p t * Ac ≤ T.cost p w) roots R :=
    forall₂_imp_mem hEnc.2 fun r hr T hv => by
      obtain ⟨h1, h2⟩ := hp.subst_spec w hSt htn rh rc hrh hrc hv (hroots r hr)
      rw [hAh, hAc] at h2
      exact ⟨h1, h2⟩
  -- the new encoding
  have hR' : List.Forall₂ (Valid p (addT A t)) roots R' := by
    have : ∀ {xs : List Nat} {ys : List WTree}, List.Forall₂ (fun r T =>
        Valid p (addT A t) r (T.subst p t rh rc) ∧
          (T.subst p t rh rc).cost p w + T.occH t * Ah + T.occC p t * Ac ≤ T.cost p w) xs ys →
        List.Forall₂ (Valid p (addT A t)) xs (ys.map (WTree.subst p t rh rc)) := by
      intro xs ys h
      induction h with
      | nil => exact .nil
      | cons h _ ih => exact .cons h.1 ih
    exact this hsubR
  have hEnc' : EncodingWF p (addT A t) (t :: S) E' roots R' := by
    refine ⟨fun y hy => ?_, hR'⟩
    by_cases hyt : y = t
    · subst hyt
      simp only [E', if_true]
      exact ⟨hTt.mono (addT_le A y), hTts⟩
    · have hyS : y ∈ S := by
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h hyt
        · exact h
      simp only [E', if_neg hyt]
      exact ⟨(hsubE y hyS).1, subst_isShare rh rc (hEnc.1 y hyS).1 (hEnc.1 y hyS).2 hyt⟩
  have hle := hp.uniformCost_le w (addT A t) (fun s hs => by
      rcases List.mem_cons.mp hs with rfl | h
      · exact htn
      · exact hSin s h) hroots hEnc'
  unfold encodingCost at hle hcost
  -- the new entry costs
  have hE' : ((t :: S).map fun s => (E' s).cost p w).sum =
      Tt.cost p w + (S.map fun s => ((E s).subst p t rh rc).cost p w).sum := by
    simp only [List.map_cons, List.sum_cons, E', if_true]
    congr 1
    apply congrArg
    apply List.map_congr_left
    intro s hs
    rw [if_neg (fun h => htS (by rw [← h]; exact hs))]
  have hR'c : (R'.map (WTree.cost p w)).sum = (R.map fun T => (T.subst p t rh rc).cost p w).sum := by
    simp only [R', List.map_map, Function.comp_def]
  -- the savings
  have hsumE := sum_ineq (fun s => ((E s).subst p t rh rc).cost p w) (fun s => (E s).occH t)
    (fun s => (E s).occC p t) (fun s => (E s).cost p w) Ah Ac S (fun s hs => (hsubE s hs).2)
  have hsumR := sum_ineq (fun T => (T.subst p t rh rc).cost p w) (WTree.occH t) (WTree.occC p t)
    (WTree.cost p w) Ah Ac R (fun T hT => by
      obtain ⟨r, hr⟩ := Ix.Compile.Verify.SharingExact.forall₂_mem_right hsubR T hT
      exact hr.2)
  have hI : I = uInl p w A t := rfl
  have hc' : uniformCost p w (fun y => decide (y ∈ S)) S roots = uniformCost p w A S roots := rfl
  rw [hE', hR'c, hTtc] at hle
  simp only [List.length_cons] at hle
  simp only [Nat.add_mul]
  omega


/-- **Exchange (lengths).** For `t ∉ S`, adding `t` costs at most its
`S`-optimal entry and the growth of the table count's TagN, and saves `inl_S(t) - w` per head
occurrence and `M_S(t) - w` per continuation occurrence (when positive): the
head occurrences number at least the root occurrences plus the
non-continuation edges into `t`, the continuation occurrences at least the
continuation edges into `t`. -/
theorem PrepWF.exchange {p : Prep} (hp : PrepWF p) (w : Nat) {S : List Nat}
    (hSin : ∀ s ∈ S, s < p.dag.size) (roots : List Nat) (hroots : ∀ r ∈ roots, r < p.dag.size)
    (hreach : ∀ y, y < p.dag.size → ∃ r ∈ roots, Ix.Compile.Verify.SharingExact.Desc p.dag r y)
    {t : Nat} (htn : t < p.dag.size) (htS : t ∉ S) :
    let A := fun y => decide (y ∈ S)
    let I := uInl p w A t
    let M := mergedOf p w A (uCost p w A) t
    uniformCost p w (fun y => decide (y ∈ t :: S)) (t :: S) roots +
        (roots.count t + ((List.range p.dag.size).map fun y => edgeMult p y t false).sum) *
          (if w ≤ I then I - w else 0) +
        ((List.range p.dag.size).map fun y => edgeMult p y t true).sum *
          (if w ≤ M then M - w else 0) ≤
      uniformCost p w A S roots + (tag0Size (S.length + 1) - tag0Size S.length) + I := by
  intro A I M
  have hSt : A t = false := by simp [A, htS]
  obtain ⟨E, R, hEnc, hcost⟩ := hp.uniformCost_attained w A S roots hSin hroots
  have hx := hp.exchange_counts w hSin roots hroots htn htS hEnc hcost
  simp only at hx
  -- the occurrence counts
  have hocc : ∀ (W : WTree) (x : Nat), Valid p A x W → x < p.dag.size →
      W.occH t = (if W.topIs t then 1 else 0) +
          ((W.written p).map fun y => edgeMult p y t false).sum ∧
        W.occC p t = ((W.written p).map fun y => edgeMult p y t true).sum :=
    fun W x hv hx => ⟨(hp.occ_edges hSt htn hv hx).1, (hp.occ_edges hSt htn hv hx).2.1⟩
  have hcov := hp.encoding_covers hEnc hSin hroots hreach
  have hflat : ∀ (f : Nat → Nat) (L : List (List Nat)),
      (L.flatten.map f).sum = (L.map fun l => (l.map f).sum).sum := by
    intro f L
    induction L with
    | nil => rfl
    | cons l ls ih => simp only [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
  have hcount : ∀ c : Bool,
      ((List.range p.dag.size).map fun y => edgeMult p y t c).sum ≤
        (R.map fun T => ((T.written p).map fun y => edgeMult p y t c).sum).sum +
          (S.map fun s => (((E s).written p).map fun y => edgeMult p y t c).sum).sum := by
    intro c
    have := sum_ge_of_covers (fun y => edgeMult p y t c) p.dag.size _ hcov
    rw [List.map_append, List.sum_append, hflat, hflat, List.map_map, List.map_map] at this
    simpa [Function.comp_def] using this
  have hH : roots.count t + ((List.range p.dag.size).map fun y => edgeMult p y t false).sum ≤
      (S.map fun s => (E s).occH t).sum + (R.map (WTree.occH t)).sum := by
    have hRH : (R.map (WTree.occH t)).sum = roots.count t +
        (R.map fun T => ((T.written p).map fun y => edgeMult p y t false).sum).sum := by
      rw [List.map_congr_left (fun T hT => by
        obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
        exact (hocc T r hr (hroots r hrm)).1), sum_map_add', topIs_root hSt hEnc.2]
    have hSH : (S.map fun s => (((E s).written p).map fun y => edgeMult p y t false).sum).sum ≤
        (S.map fun s => (E s).occH t).sum := by
      apply sum_le_sum_of_le
      intro s hs
      rw [(hocc (E s) s (hEnc.1 s hs).1 (hSin s hs)).1]
      omega
    have := hcount false
    omega
  have hC : ((List.range p.dag.size).map fun y => edgeMult p y t true).sum ≤
      (S.map fun s => (E s).occC p t).sum + (R.map (WTree.occC p t)).sum := by
    have hRC : (R.map (WTree.occC p t)).sum =
        (R.map fun T => ((T.written p).map fun y => edgeMult p y t true).sum).sum := by
      apply congrArg
      apply List.map_congr_left
      intro T hT
      obtain ⟨r, hrm, hr⟩ := forall₂_mem_right' hEnc.2 T hT
      exact (hocc T r hr (hroots r hrm)).2
    have hSC : (S.map fun s => (((E s).written p).map fun y => edgeMult p y t true).sum).sum =
        (S.map fun s => (E s).occC p t).sum := by
      apply congrArg
      apply List.map_congr_left
      intro s hs
      exact ((hocc (E s) s (hEnc.1 s hs).1 (hSin s hs)).2).symm
    have := hcount true
    omega
  have h0 : tag0Size S.length ≤ tag0Size (S.length + 1) := tag0Size_mono (Nat.le_succ _)
  have hHm := Nat.mul_le_mul_right (if w ≤ I then I - w else 0) hH
  have hCm := Nat.mul_le_mul_right (if w ≤ M then M - w else 0) hC
  simp only [A, I, M] at hHm hCm ⊢
  simp only [Nat.add_mul] at hHm hCm hx ⊢
  omega

/-! ## The stage-2 inequality -/

theorem prod_nonneg_expand (a b c d : _root_.Int) (h1 : b ≤ a) (h2 : d ≤ c) :
    a * d + b * c ≤ a * c + b * d := by
  have h := _root_.Int.mul_nonneg (_root_.Int.sub_nonneg.mpr h1) (_root_.Int.sub_nonneg.mpr h2)
  simp only [_root_.Int.sub_mul, _root_.Int.mul_sub] at h
  omega

theorem mul_pos_part (h a b : Nat) :
    (h : _root_.Int) * (a : _root_.Int) - (h : _root_.Int) * (b : _root_.Int) ≤ (h : _root_.Int) * ((if b ≤ a then a - b else 0 : Nat) : _root_.Int) := by
  split
  · rename_i hle
    rw [_root_.Int.ofNat_sub hle, _root_.Int.mul_sub]
    exact _root_.Int.le_refl _
  · rename_i hlt
    have : (h : _root_.Int) * (a : _root_.Int) ≤ (h : _root_.Int) * (b : _root_.Int) :=
      _root_.Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    simp only [_root_.Int.ofNat_zero, _root_.Int.mul_zero]
    omega

theorem edgeMult_cont_zero {p : Prep} (hp : PrepWF p) {t : Nat} (ht : t < p.dag.size)
    (hf : p.family[t]! = .none) (y : Nat) : edgeMult p y t true = 0 := by
  have hft : (p.dag.node t).head.family = .none := by rw [← hp.family t ht]; exact hf
  unfold edgeMult
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro i _
  have : continuationEdge (p.dag.node y) i (p.dag.node t) = false := by
    unfold continuationEdge
    cases hy : (p.dag.node y).head <;> cases htt : (p.dag.node t).head <;>
      simp_all [Head.family]
  simp [this]

/-- **Stage 2: the monotone exchange.** On a well-formed DAG whose roots
reach every term, for a stored set `S` within the candidates `ms` and a
candidate `t ∉ S` with in-degree at least one,
`uniformCost (t :: S) ≤ uniformCost S - storedGain t + (tag0Size (|S| + 1) - tag0Size |S|)`
(the growth of the table count's TagN). -/
theorem uniformCost_insert_le {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hreach : ∀ y, y < dag.size →
      ∃ r ∈ roots.toList, Ix.Compile.Verify.SharingExact.Desc dag r y)
    (w : Nat) (ms : Array Bool) {S : List Nat} (hSin : ∀ s ∈ S, s < dag.size)
    (hSms : ∀ s ∈ S, ms[s]! = true) {t : Nat} (htn : t < dag.size) (htS : t ∉ S)
    (hdeg : 1 ≤ (graphFacts dag roots).deg[t]!) :
    ((uniformCost (Prep.ofDag dag) w (fun y => decide (y ∈ t :: S)) (t :: S) roots.toList : Nat) :
        _root_.Int) ≤
      (uniformCost (Prep.ofDag dag) w (fun y => decide (y ∈ S)) S roots.toList : _root_.Int) -
        storedGain (Prep.ofDag dag) (graphFacts dag roots)
          (uniformBounds (Prep.ofDag dag) w ms) w t +
        ((tag0Size (S.length + 1) : _root_.Int) - tag0Size S.length) := by
  have hp := prepWF_ofDag hwf
  have h0 : tag0Size S.length ≤ tag0Size (S.length + 1) := tag0Size_mono (Nat.le_succ _)
  have hex := hp.exchange w hSin roots.toList hroots hreach htn htS
  simp only at hex
  -- in-degrees
  have hdegE := edgeCounts_spec hwf roots hroots false t
  have hheadE := edgeCounts_spec hwf roots hroots true t
  simp only [Bool.false_eq_true, if_false, if_true] at hdegE hheadE
  rw [sum_map_add'] at hdegE
  rw [ofDag_dag] at hex
  generalize hHc : roots.toList.count t +
    ((List.range dag.size).map fun y => edgeMult (Prep.ofDag dag) y t false).sum = Hc at hex
  generalize hCc : ((List.range dag.size).map fun y => edgeMult (Prep.ofDag dag) y t true).sum = Cc
    at hex
  have hdeg' : (graphFacts dag roots).deg[t]! = Hc + Cc := by
    simp only [graphFacts]; rw [hdegE, ← hHc, ← hCc, Nat.add_assoc]
  have hhead' : (graphFacts dag roots).headDeg[t]! = Hc := by
    simp only [graphFacts]; rw [hheadE, ← hHc]
  -- bounds
  have hb := hp.bounds_sound w ms (fun y => decide (y ∈ S))
    (fun y hy => hSms y (by simpa using hy)) t (by rw [ofDag_dag]; exact htn)
  have hIMb : (Prep.ofDag dag).family[t]! ≠ .none →
      1 + mergedOf (Prep.ofDag dag) w (fun y => decide (y ∈ S))
          (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t ≤
        uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t ∧
      uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t ≤
        tag4Size (Prep.ofDag dag).spineLen[t]! + mergedOf (Prep.ofDag dag) w
          (fun y => decide (y ∈ S)) (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t :=
    fun hf => inl_merged_bounds _ w _ _ hf
  generalize uInl (Prep.ofDag dag) w (fun y => decide (y ∈ S)) t = I at hex hb hIMb
  generalize mergedOf (Prep.ofDag dag) w (fun y => decide (y ∈ S))
    (uCost (Prep.ofDag dag) w fun y => decide (y ∈ S)) t = M at hex hb hIMb
  have hAh := mul_pos_part Hc I w
  have hAc := mul_pos_part Cc M w
  have hexI := _root_.Int.ofNat_le.mpr hex
  simp only [_root_.Int.natCast_add, _root_.Int.natCast_mul] at hexI
  unfold storedGain storedGainWith
  rw [hdeg', hhead']
  rw [hdeg'] at hdeg
  simp only [_root_.Int.ofNat_eq_natCast]
  by_cases hf : (Prep.ofDag dag).family[t]! = .none
  · -- a non-telescope has no continuation edges into it
    have hCc0 : Cc = 0 := by
      rw [← hCc]
      exact sum_map_eq_zero fun y _ => edgeMult_cont_zero hp (by rw [ofDag_dag]; exact htn) hf y
    subst hCc0
    have hfb : ((Prep.ofDag dag).family[t]! == Family.none) = true := by simp [hf]
    simp only [hfb, if_true]
    have hiLB := hb.2.1
    have e2 := prod_nonneg_expand (Hc : _root_.Int) 1 I
      (uniformBounds (Prep.ofDag dag) w ms).inlineLB[t]! (by omega) (by omega)
    simp only [_root_.Int.one_mul] at e2
    simp only [Nat.add_zero, _root_.Int.natCast_zero, _root_.Int.zero_mul, _root_.Int.add_zero,
      _root_.Int.sub_mul, _root_.Int.one_mul] at hexI hAc hdeg ⊢
    omega
  · have hfb : ((Prep.ofDag dag).family[t]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, if_false]
    have hmLB := (hb.2.2 hf).1
    obtain ⟨hIM1, hIM2⟩ := hIMb hf
    by_cases hH : Hc ≥ 1
    · rw [if_pos (by omega)]
      have f3 := prod_nonneg_expand (Hc : _root_.Int) 1 I (1 + M) (by omega) (by omega)
      have f4 := prod_nonneg_expand ((Hc + Cc : Nat) : _root_.Int) 1 M
        (uniformBounds (Prep.ofDag dag) w ms).mergedLB[t]! (by omega) (by omega)
      simp only [_root_.Int.one_mul, _root_.Int.mul_add, _root_.Int.mul_one,
        _root_.Int.natCast_add, _root_.Int.add_mul, _root_.Int.sub_mul] at f3 f4 ⊢
      omega
    · rw [if_neg (by omega)]
      have hH0 : Hc = 0 := by omega
      subst hH0
      have f5 := prod_nonneg_expand (Cc : _root_.Int) 1 M
        (uniformBounds (Prep.ofDag dag) w ms).mergedLB[t]! (by omega) (by omega)
      simp only [_root_.Int.one_mul, _root_.Int.natCast_zero, _root_.Int.zero_mul,
        Nat.zero_add, _root_.Int.sub_mul] at f5 hAh hexI hdeg ⊢
      omega

end Ix.Compile.Verify.UniformModel
