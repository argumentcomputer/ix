import Ix.Compile.Verify.UniformKnapsack

/-!
# Stage 4: the uniform optimizer returns a minimum

The stage facts of `uniformChoose` (classification, components, the search
context of every component), the component decomposition of the uniform
length, and the final theorem: a successful `optimizeUniformExpanded` (with
the default branch-and-bound search) stores a minimum of the uniform length
over the restricted class.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (Desc bind_eq_ok)

/-! ## The classification stage -/

section Stage

variable (w : Nat) (ex : Expanded)

/-- The stage of an input. -/
abbrev stg := uniformStage w ex (Prep.ofDag ex.dag)

theorem stage_cls_theta :
    (stg w ex).cls = ucls ex.dag ex.roots w (stg w ex).theta ∧
      ((stg w ex).theta = 2 ∨ ((stg w ex).theta = 1 ∧
        tag0Size ((ucand ex.dag ex.roots w).filter id).size =
          tag0Size ((ucls ex.dag ex.roots w 2).filter (· == .certainStored)).size)) := by
  simp only [stg, uniformStage]
  by_cases hc : (tag0Size ((ucand ex.dag ex.roots w).filter id).size ==
      tag0Size ((ucls ex.dag ex.roots w 2).filter (· == .certainStored)).size) = true
  · have hc' : (tag0Size ((searchCandidates (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w).filter id).size ==
        tag0Size ((classifyWith (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w
          (uniformBounds (Prep.ofDag ex.dag) w (searchCandidates (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w))
          (visibleCounts ex.dag ex.roots (searchCandidates (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w)) 2).filter
            (· == .certainStored)).size) = true := hc
    simp only [hc', if_true]
    refine ⟨by first | rfl | trivial, Or.inr ⟨by first | rfl | trivial, by simpa using hc⟩⟩
  · have hc' : ¬ (tag0Size ((searchCandidates (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w).filter id).size ==
        tag0Size ((classifyWith (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w
          (uniformBounds (Prep.ofDag ex.dag) w (searchCandidates (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w))
          (visibleCounts ex.dag ex.roots (searchCandidates (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) w)) 2).filter
            (· == .certainStored)).size) = true := hc
    simp only [hc', if_false]
    exact ⟨by first | rfl | trivial, Or.inl (by first | rfl | trivial)⟩

theorem stage_pick (c : UClass) :
    ((Array.range ex.dag.size).filter ((stg w ex).cls[·]! == c)).toList =
      (List.range ex.dag.size).filter (fun t => (stg w ex).cls[t]! == c) := by
  rw [Array.toList_filter, Array.toList_range]

theorem stage_cs : (stg w ex).cs.toList =
    (List.range ex.dag.size).filter (fun t => (ucls ex.dag ex.roots w (stg w ex).theta)[t]! ==
      .certainStored) := by
  rw [← (stage_cls_theta w ex).1]
  exact stage_pick w ex .certainStored

theorem stage_unc : (stg w ex).unc.toList = uunc ex.dag ex.roots w (stg w ex).theta := by
  rw [uunc, ← (stage_cls_theta w ex).1]
  exact stage_pick w ex .uncertain

theorem stage_cs_lt : ∀ t ∈ (stg w ex).cs.toList, t < ex.dag.size := by
  intro t ht
  rw [stage_cs, List.mem_filter, List.mem_range] at ht
  exact ht.1

theorem stage_opaq (u : Nat) : (stg w ex).opaq[u]! = decide (u ∈ (stg w ex).cs.toList) := by
  show ((stg w ex).cs.foldl (fun acc t => acc.set! t true) (Array.replicate ex.dag.size false))[u]! = _
  rw [← Array.foldl_toList, foldl_setBang_const]
  by_cases hu : u ∈ (stg w ex).cs.toList
  · have := stage_cs_lt w ex u hu
    simp [hu, this]
  · simp only [hu, false_and, if_false, decide_false]
    by_cases hn : u < ex.dag.size
    · rw [getElem!_pos _ u (by simpa using hn)]; simp
    · simp [getElem!_def, hn]

theorem stage_widthCs_size : (stg w ex).widthCs.size = ex.dag.size := by
  show ((stg w ex).cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)).size = _
  rw [← Array.foldl_toList, foldl_setBang_const_size]
  simp

theorem stage_widthCs (u : Nat) :
    widthOf (stg w ex).widthCs u = if (stg w ex).opaq[u]! then some w else none := by
  show widthOf ((stg w ex).cs.foldl (fun acc t => acc.set! t (some w))
    (Array.replicate ex.dag.size none)) u = _
  rw [← Array.foldl_toList, widthOfStored ex.dag.size w _ (stage_cs_lt w ex) u, stage_opaq]

/-- **The optimizer's global setting.** -/
theorem stage_global (hwf : DagWF ex.dag) (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y) :
    GlobalWF ex.dag ex.roots w (stg w ex).theta (stg w ex).cs.toList :=
  { wf := hwf, hroots, reach := hreach, theta := (stage_cls_theta w ex).2, cs := stage_cs w ex }

end Stage

/-! ## The search context of a component -/

theorem filter_and_length (p q : Nat → Bool) (l : List Nat) :
    (l.filter (fun i => p i && q i)).length + (l.filter (fun i => p i && !q i)).length =
      (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

theorem edgeCount_fold (dag : Dag) (q y : Nat) (node : Node) :
    ∀ (l : List Nat) (a b : Nat),
      l.foldl (fun (acc : Nat × Nat × Nat) i =>
        if node.child i == y then
          (q, acc.2.1 + 1, acc.2.2 + (if continuationEdge node i (dag.node y) then 0 else 1))
        else acc) (q, a, b) =
      (q, a + (l.filter (fun i => node.child i == y)).length,
        b + (l.filter (fun i => node.child i == y &&
          !continuationEdge node i (dag.node y))).length)
  | [], a, b => by simp
  | i :: l, a, b => by
    rw [List.foldl_cons]
    by_cases hi : (node.child i == y) = true
    · rw [if_pos hi, edgeCount_fold dag q y node l]
      cases hc : continuationEdge node i (dag.node y) <;> simp [List.filter_cons, hi, hc] <;> omega
    · rw [if_neg hi, edgeCount_fold dag q y node l]
      simp only [Bool.not_eq_true] at hi
      simp [List.filter_cons, hi]

/-- The edge counts of `edgeCount` are the model's edge multiplicities. -/
theorem edgeCount_le {dag : Dag} (hwf : DagWF dag) (q y : Nat) :
    (edgeCount dag q y).2.1 ≤ edgeAll (Prep.ofDag dag) q y ∧
      (edgeCount dag q y).2.2 ≤ edgeMult (Prep.ofDag dag) q y false := by
  unfold edgeCount
  rw [edgeCount_fold dag q y]
  simp only [Nat.zero_add]
  by_cases hq : q < dag.size
  · have har := hwf.children_size hq
    unfold edgeAll edgeMult
    simp only [ofDag_dag]
    rw [← har]
    have h := filter_and_length (fun i => (dag.node q).child i == y)
      (fun i => continuationEdge (dag.node q) i (dag.node y)) (List.range (dag.node q).children.size)
    constructor
    · have e1 : ((List.range (dag.node q).children.size).filter fun i =>
          (dag.node q).child i == y && continuationEdge (dag.node q) i (dag.node y) == false) =
          ((List.range (dag.node q).children.size).filter fun i =>
          (dag.node q).child i == y && !continuationEdge (dag.node q) i (dag.node y)) := by
        congr 1; funext i; cases continuationEdge (dag.node q) i (dag.node y) <;> simp
      have e2 : ((List.range (dag.node q).children.size).filter fun i =>
          (dag.node q).child i == y && continuationEdge (dag.node q) i (dag.node y) == true) =
          ((List.range (dag.node q).children.size).filter fun i =>
          (dag.node q).child i == y && continuationEdge (dag.node q) i (dag.node y)) := by
        congr 1; funext i; cases continuationEdge (dag.node q) i (dag.node y) <;> simp
      rw [e1, e2]
      omega
    · apply Nat.le_of_eq
      congr 1
      congr 1; funext i; cases continuationEdge (dag.node q) i (dag.node y) <;> simp
  · -- out of range: no children
    have hn : dag.node q = default := by
      simp [Dag.node, Dag.size] at hq ⊢
      simp [hq]
    rw [hn]
    have : (default : Node).children.size = 0 := rfl
    simp [this]

/-- The search context of component `j`. -/
abbrev compCx (w : Nat) (ex : Expanded) (j : Nat) : SCtx :=
  mkSCtx ex (stg w ex).f (stg w ex).up (stg w ex).cand (stg w ex).b0 (stg w ex).vis0
    (stg w ex).rootCount (stg w ex).slack (stg w ex).theta (stg w ex).baseEv (stg w ex).widthCs
    (stg w ex).allTrue (stg w ex).unc (stg w ex).comps[j]!

/-- The search environment of component `j`. -/
def compEnv (w : Nat) (ex : Expanded) (j : Nat) : Env :=
  { dag := ex.dag, roots := ex.roots, w, θ := (stg w ex).theta, cs := (stg w ex).cs.toList,
    cx := compCx w ex j,
    comp := fun t => ((componentLabels ex.dag.size (stg w ex).comps)[t]!).getD 0, i := j }

theorem map_getElem! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {i : Nat}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos a i hi, Array.getElem_map]

theorem rootCount_le (ex : Expanded) (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) (w t : Nat) :
    (stg w ex).rootCount[t]! ≤ ex.roots.toList.count t := by
  show (ex.roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate ex.dag.size 0))[t]! ≤ _
  rw [← Array.foldl_toList]
  have := (foldl_modify_count ex.roots.toList (Array.replicate ex.dag.size 0) t
    (fun c hc => by simpa using hroots c hc)).1
  rw [this]
  have : (Array.replicate ex.dag.size (0 : Nat))[t]! = 0 := by
    by_cases ht : t < ex.dag.size
    · rw [getElem!_pos _ t (by simpa using ht)]; simp
    · simp [getElem!_def, ht]
  omega

/-- **The search environment of every component is well formed.** -/
theorem compEnv_wf {w : Nat} {ex : Expanded} (hwf : DagWF ex.dag)
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true)
    {j : Nat} (hj : j < (stg w ex).comps.size)
    (hpar : areaParentsOK ex.dag.size (compCx w ex j) = true) : (compEnv w ex j).WF := by
  obtain ⟨hca, hcb, hcc, hcd⟩ := componentsChecked_spec hwf hchk
  have hcls := (stage_cls_theta w ex).1
  rw [hcls] at hca hcc hcd
  have hn := (stage_cls_theta w ex).2
  refine { G := stage_global w ex hwf hroots hreach, cx := ?_, area := ?_, comp := ?_,
           memi := ?_, slack := ?_ }
  · exact { prep := rfl, width := rfl, opaq := stage_opaq w ex, cand := rfl, bounds0 := rfl,
            vis0 := rfl, mem := fun t ht => ⟨(hca j hj t ht).1, (hca j hj t ht).2.1⟩,
            memNodup := hcb j hj, widthCs_size := stage_widthCs_size w ex,
            widthCs := stage_widthCs w ex, allTrue := rfl, baseEv := rfl, closure := rfl,
            rootsC := rfl, storedInC := rfl, theta := rfl }
  · unfold areaParentsOK at hpar
    rw [List.all_eq_true] at hpar
    refine { rootOcc := ?_, nodup := ?_, lt := ?_, cnt := ?_ }
    · intro j' hj'
      simp only [compEnv]
      show ((componentArea (stg w ex).up (stg w ex).f (stg w ex).comps[j]!).map
        ((stg w ex).rootCount[·]!))[j']! ≤ _
      have hj'' : j' < (componentArea (stg w ex).up (stg w ex).f (stg w ex).comps[j]!).size := hj'
      rw [map_getElem! _ _ hj'']
      exact rootCount_le ex hroots w _
    · intro j' hj'
      have := hpar j' (List.mem_range.mpr hj')
      simp only [Bool.and_eq_true] at this
      have hn := strictInc_nodup this.1
      rw [Array.toList_map] at hn
      exact hn
    · intro j' hj' e he
      have := hpar j' (List.mem_range.mpr hj')
      simp only [Bool.and_eq_true, Array.all_eq_true'] at this
      exact of_decide_eq_true (this.2 e (Array.mem_toList_iff.mp he))
    · intro j' hj' e he
      simp only [compEnv] at he ⊢
      have hin : (compCx w ex j).inEdges[j']! =
          ((stg w ex).f.parents[(compCx w ex j).area[j']!]!).map
            (fun q => edgeCount ex.dag q (compCx w ex j).area[j']!) := map_getElem! _ _ hj'
      rw [hin, Array.toList_map, List.mem_map] at he
      obtain ⟨q, _, rfl⟩ := he
      have := edgeCount_le hwf q (compCx w ex j).area[j']!
      have h1 : (edgeCount ex.dag q (compCx w ex j).area[j']!).1 = q := by
        unfold edgeCount; rw [edgeCount_fold]
      rw [h1]
      exact this
  · intro a b ha hua hub hab
    simp only [compEnv]
    rw [hcd a b ha hua hub hab]
  · intro t ht hut
    simp only [compEnv]
    constructor
    · intro htm
      rw [(hca j hj t htm).2.2]
      rfl
    · intro hct
      obtain ⟨i, hi, hl, htm⟩ := hcc t ht hut
      rw [hl] at hct
      simp only [Option.getD_some] at hct
      subst hct
      exact htm
  · have hs : (stg w ex).slack = tag0Size ((stg w ex).cs.size + (stg w ex).unc.size) -
        tag0Size (stg w ex).cs.size := rfl
    show (stg w ex).slack = tag0Size ((stg w ex).cs.toList.length +
      (uunc ex.dag ex.roots w (stg w ex).theta).length) - tag0Size (stg w ex).cs.toList.length
    rw [hs, ← stage_unc w ex, Array.length_toList, Array.length_toList]

end Ix.Compile.Verify.UniformModel
