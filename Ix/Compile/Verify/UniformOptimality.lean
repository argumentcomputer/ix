import Ix.Compile.Verify.UniformKnapsack

/-!
# Stage 4: the uniform optimizer returns a minimum

The stage facts of `uniformChoose` (classification, components, the search
context of every component), the component decomposition of the uniform
length, and the final theorem: a successful `optimizeUniformExpanded` (with
the default branch-and-bound search) stores a minimum of the uniform length
over the restricted class, when every telescope spine is shorter than
`teleSubaddEnd` (`SpinesFit`).
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (Desc bind_eq_ok)

/-! ## The classification stage -/

section Stage

variable (w : Nat) (ex : Expanded)

/-- The stage of an input. -/
abbrev stg := uniformStage w ex (Prep.ofDag ex.dag)

theorem tag0StepBound_pos (n : Nat) : 1 ≤ tag0StepBound n := by
  unfold tag0StepBound
  repeat' split
  all_goals omega

theorem stage_cls_theta :
    (stg w ex).cls = ucls ex.dag ex.roots w (stg w ex).theta ∧
      ((stg w ex).theta = uthetaMax ex.dag ex.roots w ∨ ((stg w ex).theta = 1 ∧
        tag0Size ((ucand ex.dag ex.roots w).filter id).size =
          tag0Size ((ucls ex.dag ex.roots w (uthetaMax ex.dag ex.roots w)).filter
            (· == .certainStored)).size)) := by
  have hmax : (uthetaMax ex.dag ex.roots w == 1) = false := by
    have := tag0StepBound_pos ((ucand ex.dag ex.roots w).filter id).size
    rw [beq_eq_false_iff_ne]
    unfold uthetaMax
    omega
  have htheta : (stg w ex).theta =
      if (tag0Size ((ucand ex.dag ex.roots w).filter id).size ==
        tag0Size ((ucls ex.dag ex.roots w (uthetaMax ex.dag ex.roots w)).filter
          (· == .certainStored)).size) then 1 else uthetaMax ex.dag ex.roots w := rfl
  have hcls : (stg w ex).cls =
      if (stg w ex).theta == 1 then ucls ex.dag ex.roots w 1
      else ucls ex.dag ex.roots w (uthetaMax ex.dag ex.roots w) := rfl
  by_cases hc : (tag0Size ((ucand ex.dag ex.roots w).filter id).size ==
      tag0Size ((ucls ex.dag ex.roots w (uthetaMax ex.dag ex.roots w)).filter
        (· == .certainStored)).size) = true
  · have ht : (stg w ex).theta = 1 := by rw [htheta, if_pos hc]
    refine ⟨?_, Or.inr ⟨ht, by simpa using hc⟩⟩
    rw [hcls, ht]
    rfl
  · have ht : (stg w ex).theta = uthetaMax ex.dag ex.roots w := by rw [htheta, if_neg hc]
    refine ⟨?_, Or.inl ht⟩
    rw [hcls, ht]
    simp only [hmax, Bool.false_eq_true, if_false]

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

/-- **The optimizer's global setting**, on a DAG whose telescope spines fit
(`SpinesFit`). -/
theorem stage_global (hwf : DagWF ex.dag) (hsp : SpinesFit (Prep.ofDag ex.dag))
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y) :
    GlobalWF ex.dag ex.roots w (stg w ex).theta (stg w ex).cs.toList :=
  { wf := hwf, spines := hsp, hroots, reach := hreach, theta := (stage_cls_theta w ex).2, cs := stage_cs w ex }

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
    (hsp : SpinesFit (Prep.ofDag ex.dag))
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
  refine { G := stage_global w ex hwf hsp hroots hreach, cx := ?_, area := ?_, comp := ?_,
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

/-! ## The component searches -/

/-- What a successful component search returns. -/
def SearchOK (cx : SCtx) (limits : Limits) (r : CompResult) : Prop :=
  areaParentsOK cx.up.prep.dag.size cx = true ∧ r.members = cx.members ∧
    ∃ (st0 : SState) (st : SState), st0.memo = {} ∧
      cx.solveP limits (8 * cx.members.size + 8) cx.members #[] #[] st0 = .ok (r.bySize, st) ∧
      CTable.best r.bySize = some r.bestDelta ∧ bestSetOf r.bySize r.bestDelta = some r.bestSet

theorem searchComponent_ok {cx : SCtx} {limits : Limits} {states costEvals : Nat}
    {r : CompResult} {s c : Nat} (h : searchComponent cx limits states costEvals = .ok (r, s, c)) :
    SearchOK cx limits r := by
  unfold searchComponent at h
  simp only at h
  split at h
  all_goals first | (cases h; done) | skip
  rename_i hpar0
  have hpar : areaParentsOK cx.up.prep.dag.size cx = true := by simpa using hpar0
  obtain ⟨⟨tb, st⟩, hs, h⟩ := bind_eq_ok h
  simp only at h
  split at h
  · rename_i bd hbd
    split at h
    · rename_i bs hbs
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨hpar, rfl, { states, costEvals }, st, rfl, hs, hbd, hbs⟩
    · cases h
  · cases h

theorem push_getElem!_lt {α : Type} [Inhabited α] (a : Array α) (x : α) {i : Nat} (hi : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos a i hi, Array.getElem_push_lt]

theorem push_getElem!_eq {α : Type} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos _ a.size (by simp), Array.getElem_push_eq]

/-- The step of `searchComponents` with the branch-and-bound search. -/
theorem searchComponents_spec {w : Nat} {limits : Limits} {ex : Expanded}
    (hsub : limits.uniformSubsetSearch = false) {results : Array CompResult} {s c : Nat}
    (h : searchComponents limits ex (stg w ex) = .ok (results, s, c)) :
    results.size = (stg w ex).comps.size ∧
      ∀ j, j < (stg w ex).comps.size → SearchOK (compCx w ex j) limits results[j]! := by
  unfold searchComponents at h
  rw [← Array.foldlM_toList] at h
  -- induction over the components, with the processed prefix
  have key : ∀ (l : List (Array Nat)) (pre : List (Array Nat)) (acc : Array CompResult × Nat × Nat),
      pre ++ l = (stg w ex).comps.toList → acc.1.size = pre.length →
      (∀ j, j < pre.length → SearchOK (compCx w ex j) limits acc.1[j]!) →
      ∀ res, l.foldlM (fun (acc : Array CompResult × Nat × Nat) members => do
          let (results, states, costEvals) := acc
          if limits.uniformSubsetSearch then
            let (r, states, costEvals) ← searchComponentRef (stg w ex).up (stg w ex).f
              (stg w ex).opaq ex.roots (stg w ex).slack limits members states costEvals
            pure (results.push r, states, costEvals)
          else
            let cx := mkSCtx ex (stg w ex).f (stg w ex).up (stg w ex).cand (stg w ex).b0
              (stg w ex).vis0 (stg w ex).rootCount (stg w ex).slack (stg w ex).theta
              (stg w ex).baseEv (stg w ex).widthCs (stg w ex).allTrue (stg w ex).unc members
            let (r, states, costEvals) ← searchComponent cx limits states costEvals
            pure (results.push r, states, costEvals)) acc = .ok res →
      res.1.size = (stg w ex).comps.size ∧
        ∀ j, j < (stg w ex).comps.size → SearchOK (compCx w ex j) limits res.1[j]! := by
    intro l
    induction l with
    | nil =>
      intro pre acc hpre hsz hall res hres
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hres
      subst hres
      have : pre.length = (stg w ex).comps.size := by
        rw [← Array.length_toList, ← hpre, List.append_nil]
      exact ⟨by rw [hsz, this], fun j hj => hall j (by omega)⟩
    | cons m l ih =>
      intro pre acc hpre hsz hall res hres
      rw [List.foldlM_cons] at hres
      obtain ⟨acc', hstep, hres⟩ := bind_eq_ok hres
      obtain ⟨results0, states0, costEvals0⟩ := acc
      simp only [hsub, Bool.false_eq_true, if_false] at hstep
      obtain ⟨⟨r, s1, c1⟩, hsc, hstep⟩ := bind_eq_ok hstep
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hmj : (stg w ex).comps[pre.length]! = m := by
        have : (stg w ex).comps.toList[pre.length]? = some m := by
          rw [← hpre]; simp
        rw [getElem!_def, ← Array.getElem?_toList, this]
      simp only at hsz hall
      refine ih (pre ++ [m]) (results0.push r, s1, c1) (by rw [← hpre]; simp)
        (by simp [hsz]) ?_ res hres
      intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < pre.length
      · simp only
        rw [push_getElem!_lt _ _ (by omega)]
        exact hall j hjl
      · have hjeq : j = pre.length := by omega
        subst hjeq
        simp only
        rw [← hsz, push_getElem!_eq]
        have := searchComponent_ok hsc
        rw [hsz]
        unfold compCx
        rw [hmj]
        exact this
  exact key (stg w ex).comps.toList [] ((#[] : Array CompResult), 0, 0) (by simp) rfl
    (fun j hj => absurd hj (Nat.not_lt_zero _)) _ h

/-! ## The uniform length of a minimum, component by component -/

theorem compCx_sctx {w : Nat} {ex : Expanded} (hwf : DagWF ex.dag)
    (hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true)
    {j : Nat} (hj : j < (stg w ex).comps.size) :
    SCtxWF ex.dag ex.roots w (stg w ex).theta (stg w ex).cs.toList (compCx w ex j) := by
  obtain ⟨hca, hcb, _, _⟩ := componentsChecked_spec hwf hchk
  rw [(stage_cls_theta w ex).1] at hca
  exact { prep := rfl, width := rfl, opaq := stage_opaq w ex, cand := rfl, bounds0 := rfl,
          vis0 := rfl, mem := fun t ht => ⟨(hca j hj t ht).1, (hca j hj t ht).2.1⟩,
          memNodup := hcb j hj, widthCs_size := stage_widthCs_size w ex,
          widthCs := stage_widthCs w ex, allTrue := rfl, baseEv := rfl, closure := rfl,
          rootsC := rfl, storedInC := rfl, theta := rfl }

/-- **The base of the model** is the length of the certain-stored terms
without the count's TagN. -/
theorem csBase_eq {w : Nat} {ex : Expanded} (hwf : DagWF ex.dag)
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) :
    csBase ex (Prep.ofDag ex.dag) (stg w ex) + tag0Size (stg w ex).cs.toList.length =
      ulen ex.dag w ex.roots (stg w ex).cs.toList := by
  have hp := prepWF_ofDag hwf
  let A : Nat → Bool := fun u => (stg w ex).opaq[u]!
  have hA : (fun y => decide (y ∈ (stg w ex).cs.toList)) = A := by
    funext y; simp only [A, stage_opaq]
  have hwid : ∀ u, widthOf (stg w ex).widthCs u = if A u then some w else none :=
    stage_widthCs w ex
  have hrows : ∀ t, t < ex.dag.size → EvalRow (Prep.ofDag ex.dag) w A (stg w ex).baseEv t := by
    intro t ht
    exact hp.evalFrom_spec (stg w ex).widthCs hwid (Prep.ofDag ex.dag).empty (ofDag_empty_size ex.dag)
      (Array.replicate ex.dag.size true) (fun t ht => replicate_getBang ht) t ht
  have hbsz := evalFrom_size (Prep.ofDag ex.dag).dag (Prep.ofDag ex.dag).family
    (Prep.ofDag ex.dag).spineLen (Prep.ofDag ex.dag).tail (Prep.ofDag ex.dag).empty
    (stg w ex).widthCs (Array.replicate ex.dag.size true)
  obtain ⟨e1, e2, e3⟩ := ofDag_empty_size ex.dag
  rw [e1, e2, e3] at hbsz
  unfold csBase ulen uniformCost
  rw [hA, arr_foldl_add_eq_sum, arr_foldl_add_eq_sum, Nat.zero_add, Nat.zero_add]
  have hr : (ex.roots.toList.map fun r => (stg w ex).baseEv.cost[r]!) =
      ex.roots.toList.map (uCost (Prep.ofDag ex.dag) w A) :=
    List.map_congr_left (fun r hr => (hrows r (hroots r hr)).1)
  have hc : ((stg w ex).cs.toList.map fun c => (evalStep (Prep.ofDag ex.dag).dag
      (Prep.ofDag ex.dag).family (Prep.ofDag ex.dag).spineLen (Prep.ofDag ex.dag).tail
      ((stg w ex).widthCs.set! c none) (stg w ex).allTrue (stg w ex).baseEv c).cost[c]!) =
      (stg w ex).cs.toList.map (uInl (Prep.ofDag ex.dag) w A) :=
    List.map_congr_left (fun c hc => entry_inl hwf (stg w ex).widthCs (stage_widthCs_size w ex)
      hwid (stg w ex).baseEv hbsz hrows (stage_cs_lt w ex c hc))
  rw [hr, hc]
  omega

/-- The parts of `Y` in the first `j` components. -/
def compParts (comps : Array (Array Nat)) (Y : List Nat) (j : Nat) : List Nat :=
  ((List.range j).map fun i => partOf Y comps[i]!.toList).flatten

theorem compParts_succ (comps : Array (Array Nat)) (Y : List Nat) (j : Nat) :
    compParts comps Y (j + 1) = compParts comps Y j ++ partOf Y comps[j]!.toList := by
  unfold compParts
  rw [List.range_succ, List.map_append, List.flatten_append]
  simp

theorem mem_compParts {comps : Array (Array Nat)} {Y : List Nat} {j t : Nat} :
    t ∈ compParts comps Y j ↔ ∃ i, i < j ∧ t ∈ comps[i]!.toList ∧ t ∈ Y := by
  unfold compParts
  simp only [List.mem_flatten, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, ⟨i, hi, rfl⟩, ht⟩
    exact ⟨i, hi, partOf_sub t ht⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨_, ⟨i, hi, rfl⟩, by simp [partOf, h1, h2]⟩

/-- **The uniform length of the certain-stored terms and the parts of `Y` in
the first `j` components**: each component adds its change of component
cost. -/
theorem ulen_compParts {w : Nat} {ex : Expanded} (hwf : DagWF ex.dag)
    (hsp : SpinesFit (Prep.ofDag ex.dag))
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true)
    (Y : List Nat) :
    ∀ j, j ≤ (stg w ex).comps.size →
      ulen ex.dag w ex.roots ((stg w ex).cs.toList ++ compParts (stg w ex).comps Y j) +
          tag0Size (stg w ex).cs.toList.length +
          ((List.range j).map fun i => scost (compCx w ex i) ex.dag []).sum =
        ulen ex.dag w ex.roots (stg w ex).cs.toList +
          tag0Size ((stg w ex).cs.toList ++ compParts (stg w ex).comps Y j).length +
          ((List.range j).map fun i =>
            scost (compCx w ex i) ex.dag (partOf Y (stg w ex).comps[i]!.toList)).sum := by
  have hG := stage_global w ex hwf hsp hroots hreach
  obtain ⟨hca, hcb, hcc, hcd⟩ := componentsChecked_spec hwf hchk
  rw [(stage_cls_theta w ex).1] at hca hcc hcd
  let comp : Nat → Nat := fun t => ((componentLabels ex.dag.size (stg w ex).comps)[t]!).getD 0
  have hθ1 : 1 ≤ (stg w ex).theta := hG.one_le_theta
  intro j
  induction j with
  | zero => intro _; simp [compParts]
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have hjs : j < (stg w ex).comps.size := by omega
    have hcx := compCx_sctx hwf hchk hjs
    -- the new component's part and the earlier parts
    have hV : ∀ t ∈ partOf Y (stg w ex).comps[j]!.toList,
        t ∈ (compCx w ex j).members.toList ∧ t < ex.dag.size ∧
          (ucls ex.dag ex.roots w (stg w ex).theta)[t]! = .uncertain ∧ comp t = j := by
      intro t ht
      have htc := (partOf_sub t ht).1
      obtain ⟨h1, h2, h3⟩ := hca j hjs t htc
      exact ⟨htc, h1, h2, by simp only [comp]; rw [h3]; rfl⟩
    have hR : ∀ t ∈ compParts (stg w ex).comps Y j, t < ex.dag.size ∧
        (ucls ex.dag ex.roots w (stg w ex).theta)[t]! = .uncertain ∧ comp t ≠ j := by
      intro t ht
      obtain ⟨i, hi, htc, _⟩ := mem_compParts.mp ht
      obtain ⟨h1, h2, h3⟩ := hca i (by omega) t htc
      exact ⟨h1, h2, by simp only [comp]; rw [h3]; simp; omega⟩
    have hsplit := ulen_split_component hwf ex.roots hroots w (stg w ex).theta hθ1
      (opaq := (compCx w ex j).up.opaq)
      (fun u => stage_opaq w ex u) hG.cs_nodup (fun t ht => (hG.mem_cs t).mp ht)
      (compCx w ex j).members comp j
      (fun a b ha hua hub hab => by simp only [comp]; rw [hcd a b ha hua hub hab])
      (V := partOf Y (stg w ex).comps[j]!.toList) (R := compParts (stg w ex).comps Y j) hV hR
    rw [← hcx.cost_eq, ← hcx.cost_eq] at hsplit
    have hperm : ((stg w ex).cs.toList ++ compParts (stg w ex).comps Y (j + 1)).Perm
        ((stg w ex).cs.toList ++ partOf Y (stg w ex).comps[j]!.toList ++
          compParts (stg w ex).comps Y j) := by
      rw [compParts_succ]
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    rw [ulen_perm hperm, hperm.length_eq, List.range_succ, List.map_append, List.map_append,
      List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    simp only [List.length_append] at hsplit ih ⊢
    omega

/-! ## The count brackets and the knapsack bound -/

/-- **A count bracket starts with its own TagN (`f = 0`) size.** -/
theorem tag0Size_bracketStart (k : Nat) : tag0Size (tag0BracketStart k) = tag0Size k := by
  have h1 : 0 < Ixon.tagNEnd1 0 := by decide
  have h12 : Ixon.tagNEnd1 0 < Ixon.tagNEnd2 0 := by decide
  have h23 : Ixon.tagNEnd2 0 < Ixon.tagNEnd3 0 := by decide
  have h34 : Ixon.tagNEnd3 0 < Ixon.tagNEnd4 0 := by decide
  unfold tag0BracketStart
  repeat' split
  all_goals
    unfold tag0Size Ixon.tagNByteWidth
    repeat' split
    all_goals omega

theorem tag0Size_ge_of_bracket {k m : Nat} (h : tag0BracketStart k ≤ m) : tag0Size k ≤ tag0Size m := by
  rw [← tag0Size_bracketStart k]
  exact tag0Size_mono h

theorem sum_map_range {α : Type} [Inhabited α] (f : α → _root_.Int) (l : List α) :
    (l.map f).sum = ((List.range l.length).map fun j => f l[j]!).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map,
      List.sum_cons, List.sum_cons, ih]
    simp [Function.comp_def]

theorem sum_map_range' (l : List _root_.Int) :
    l.sum = ((List.range l.length).map fun j => l[j]!).sum := by
  have := sum_map_range id l
  simpa using this

theorem sum_le_sum_int {f g : Nat → _root_.Int} :
    ∀ (l : List Nat), (∀ k ∈ l, f k ≤ g k) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_sum_int l (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have := h a List.mem_cons_self
    omega

/-- The sum of the bests. -/
theorem foldl_bestDelta_eq (rs : List CompResult) (a : _root_.Int) :
    rs.foldl (fun acc r => acc + r.bestDelta) a = a + (rs.map (·.bestDelta)).sum := by
  induction rs generalizing a with
  | nil => simp
  | cons r rs ih => rw [List.foldl_cons, ih]; simp; omega

theorem indexed_dp0 (cap : Nat) : Indexed (#[some (0, #[])] ++ Array.replicate cap none) := by
  intro k e he
  by_cases hk : k = 0
  · subst hk
    rw [getElem!_pos _ 0 (by rw [Array.size_append]; simp; omega)] at he
    simp at he
    rw [← he]; rfl
  · by_cases hk' : k < 1 + cap
    · rw [getElem!_pos _ k (by simp; omega), Array.getElem_append_right (by simp; omega)] at he
      simp at he
    · simp [getElem!_def, show ¬ k < 1 + cap by omega] at he

theorem indexed_fold {cap : Nat} :
    ∀ (ts : List CTable) (dp : CTable), (∀ t ∈ ts, Indexed t) → Indexed dp →
      Indexed (ts.foldl (knapStep cap) dp)
  | [], _, _, h => h
  | t :: ts, dp, ht, h => indexed_fold ts _ (fun t' h' => ht t' (List.mem_cons_of_mem _ h'))
      (knapStep_indexed h (ht t List.mem_cons_self))

/-- **The knapsack bound.** For any choice of one entry per component table
(at counts `ks`, values at most `vs`), the chosen total is at most the
choice's `Δ` plus the TagN of its count. -/
theorem uniformKnapsack_le {limits : Limits} {kCS : Nat} {results : Array CompResult}
    {cd : _root_.Int} {cx : Array Nat} {lb : Bool}
    (h : uniformKnapsack limits kCS results = .ok (cd, cx, lb))
    (ks : List Nat) (vs : List _root_.Int) (hk : ks.length = results.size)
    (hv : vs.length = results.size)
    (hhas : ∀ j, j < results.size → HasAt results[j]!.bySize ks[j]! vs[j]!)
    (hidx : ∀ j, j < results.size → Indexed results[j]!.bySize)
    (hbest : ∀ j, j < results.size → ∀ (k : Nat) (e : Entry), results[j]!.bySize[k]! = some e →
      results[j]!.bestDelta ≤ e.1) :
    cd + (tag0Size (kCS + cx.size) : _root_.Int) ≤ vs.sum + (tag0Size (kCS + ks.sum) : _root_.Int) := by
  -- the sum of the bests is below the choice
  have hbsum : (results.toList.map (·.bestDelta)).sum ≤ vs.sum := by
    rw [sum_map_range (·.bestDelta) results.toList, sum_map_range' vs]
    simp only [Array.length_toList, hv]
    apply sum_le_sum_int
    intro j hj
    have hj' := List.mem_range.mp hj
    obtain ⟨e, he, hev⟩ := hhas j hj'
    have := hbest j hj' _ e he
    rw [Array.getElem!_toList]
    omega
  have hbest_eq : results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int) =
      (results.toList.map (·.bestDelta)).sum := by
    rw [← Array.foldl_toList, foldl_bestDelta_eq]; simp
  have hts : ∀ j, j < results.size → (results.toList.map (·.bySize))[j]! = results[j]!.bySize := by
    intro j hj
    rw [getElem!_pos _ j (by simpa using hj), List.getElem_map, getElem!_pos results j hj]
    simp
  have htsl : (results.toList.map (·.bySize)).length = results.size := by simp
  unfold uniformKnapsack at h
  simp only at h
  generalize hbx : results.foldl (fun acc r => mergeSorted acc r.bestSet) #[] = bestX at h
  generalize hbd : results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int) = bestDelta at h
  have hbd' : bestDelta ≤ vs.sum := by rw [← hbd, hbest_eq]; exact hbsum
  have hbr : tag0BracketStart (kCS + bestX.size) ≤ kCS + ks.sum →
      tag0Size (kCS + bestX.size) ≤ tag0Size (kCS + ks.sum) := tag0Size_ge_of_bracket
  split at h
  · rename_i hstart
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      generalize hcap : tag0BracketStart (kCS + bestX.size) - 1 - kCS = cap at h
      have hdp : results.foldl (fun dp r => knapStep cap dp r.bySize)
          (#[some (0, #[])] ++ Array.replicate cap none) =
          (results.toList.map (·.bySize)).foldl (knapStep cap)
            (#[some (0, #[])] ++ Array.replicate cap none) := by
        rw [← Array.foldl_toList, List.foldl_map]
      rw [hdp] at h
      have hidx_dp := indexed_fold (cap := cap) (results.toList.map (·.bySize))
        (#[some (0, #[])] ++ Array.replicate cap none)
        (fun t ht => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
          obtain ⟨j, hj, hrj⟩ := List.mem_iff_getElem.mp hr
          simp only [Array.length_toList] at hj
          have := hidx j hj
          rw [getElem!_pos results j hj] at this
          simpa [← hrj] using this)
        (indexed_dp0 cap)
      obtain ⟨hc1, hc2⟩ := knapChoose_le kCS hidx_dp (bestDelta, bestX, false)
      rw [h] at hc1 hc2
      unfold knapTotal at hc1 hc2
      simp only at hc1 hc2
      by_cases hfit : ks.sum ≤ cap
      · obtain ⟨e, he, hev⟩ := knapFold_hasAt (cap := cap) (results.toList.map (·.bySize)) ks vs
          (#[some (0, #[])] ++ Array.replicate cap none) 0 0 (by rw [htsl, hk]) (by rw [htsl, hv])
          (fun j hj => by rw [hts j (by rw [← htsl]; exact hj)]; exact hhas j (by rw [← htsl]; exact hj))
          ⟨(0, #[]), by rw [getElem!_pos _ 0 (by rw [Array.size_append]; simp; omega)]; simp,
            Int.le_refl _⟩ (by omega)
        have := hc2 (0 + ks.sum) e he
        simp only [Nat.zero_add, Int.zero_add] at this hev
        omega
      · have := hbr (by omega)
        omega
  · rename_i hstart
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have := hbr (by omega)
    omega

/-! ## Minima -/

/-- **A minimum exists** (the class contains the empty set). -/
theorem minimum_exists (dag : Dag) (w : Nat) (roots : Array Nat) :
    ∃ Y, IsMinimum dag w roots Y := by
  obtain ⟨m, ⟨Y, hY, hYm⟩, hmin⟩ := exists_min_nat (fun m => ∃ Y, InClass dag roots Y ∧ ulen dag w roots Y = m)
    ⟨_, [], ⟨List.nodup_nil, fun s hs => absurd hs List.not_mem_nil⟩, rfl⟩
  refine ⟨Y, hY, fun Y' hY' => ?_⟩
  rw [hYm]
  refine Classical.byContradiction fun hlt => ?_
  exact hmin (ulen dag w roots Y') (by omega) ⟨Y', hY', rfl⟩

/-- A minimum is the certain-stored terms and its parts in the components. -/
theorem min_perm_parts {w : Nat} {ex : Expanded} (hwf : DagWF ex.dag)
    (hsp : SpinesFit (Prep.ofDag ex.dag))
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true)
    {Y : List Nat} (hY : IsMinimum ex.dag w ex.roots Y) :
    Y.Perm ((stg w ex).cs.toList ++ compParts (stg w ex).comps Y (stg w ex).comps.size) := by
  have hG := stage_global w ex hwf hsp hroots hreach
  obtain ⟨hca, hcb, hcc, _⟩ := componentsChecked_spec hwf hchk
  rw [(stage_cls_theta w ex).1] at hca hcc
  -- the parts are duplicate-free and disjoint
  have hnd : ∀ j, j ≤ (stg w ex).comps.size → (compParts (stg w ex).comps Y j).Nodup := by
    intro j
    induction j with
    | zero => intro _; simp [compParts]
    | succ j ih =>
      intro hj
      rw [compParts_succ]
      apply nodup_app (ih (by omega)) (List.Nodup.sublist List.filter_sublist (hcb j (by omega)))
      intro x hx hxV
      obtain ⟨i, hi, hxi, _⟩ := mem_compParts.mp hx
      have h1 := (hca i (by omega) x hxi).2.2
      have h2 := (hca j (by omega) x (partOf_sub x hxV).1).2.2
      rw [h1] at h2
      simp at h2
      omega
  apply (List.perm_ext_iff_of_nodup hY.1.1 (nodup_app hG.cs_nodup (hnd _ (Nat.le_refl _)) ?_)).mpr
  · intro t
    simp only [List.mem_append, mem_compParts]
    constructor
    · intro htY
      obtain ⟨htn, hcl⟩ := hG.min_class hY htY
      rcases hcl with hcl | hcl
      · exact Or.inl ((hG.mem_cs t).mpr ⟨htn, hcl⟩)
      · obtain ⟨i, hi, _, hti⟩ := hcc t htn hcl
        exact Or.inr ⟨i, hi, hti, htY⟩
    · rintro (h | ⟨_, _, _, h⟩)
      · exact hG.min_cs hY h
      · exact h
  · intro x hx hxp
    obtain ⟨i, hi, hxi, _⟩ := mem_compParts.mp hxp
    have h1 := (hca i hi x hxi).2.1
    have h2 := ((hG.mem_cs x).mp hx).2
    rw [h1] at h2
    cases h2

theorem compParts_length (comps : Array (Array Nat)) (Y : List Nat) (j : Nat) :
    (compParts comps Y j).length =
      ((List.range j).map fun i => (partOf Y comps[i]!.toList).length).sum := by
  unfold compParts
  rw [List.length_flatten, List.map_map]
  rfl

theorem sum_map_sub_int (a b : Nat → Nat) (l : List Nat) :
    (l.map fun j => ((a j : _root_.Int) - (b j : _root_.Int))).sum =
      ((l.map a).sum : _root_.Int) - ((l.map b).sum : _root_.Int) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; push_cast; rw [ih]; omega

/-! ## The model length is at most every minimum's length -/

/-- **The chosen model length is a lower bound of the minimum.** With the
branch-and-bound search, the model length `uniformChoose` reports is at most
the uniform length of every minimum. -/
theorem uniformChoose_model_le {w : Nat} {limits : Limits} {ex : Expanded}
    (hsub : limits.uniformSubsetSearch = false) (hwf : DagWF ex.dag)
    (hsp : SpinesFit (Prep.ofDag ex.dag))
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {c : UniformChoice} (h : uniformChoose w limits ex (Prep.ofDag ex.dag) = .ok c)
    {Y : List Nat} (hY : IsMinimum ex.dag w ex.roots Y) :
    c.model ≤ ulen ex.dag w ex.roots Y := by
  unfold uniformChoose at h
  simp only at h
  split at h
  all_goals first | (cases h; done) | skip
  rename_i hchk0
  have hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true := by simpa using hchk0
  obtain ⟨⟨results, s1, c1⟩, hsc, h⟩ := bind_eq_ok h
  obtain ⟨⟨cd, cx, lb⟩, hkn, h⟩ := bind_eq_ok h
  simp only at h hkn
  split at h
  · cases h
  rename_i hneg
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only
  obtain ⟨hsize, hok⟩ := searchComponents_spec hsub hsc
  let m := (stg w ex).comps.size
  let V : Nat → List Nat := fun j => partOf Y (stg w ex).comps[j]!.toList
  -- every component's table covers the minimum
  have hfacts : ∀ j, j < m →
      HasAt results[j]!.bySize (V j).length ((compEnv w ex j).delta [] (V j)) ∧
      Indexed results[j]!.bySize ∧
      (∀ (k : Nat) (e : Entry), results[j]!.bySize[k]! = some e → results[j]!.bestDelta ≤ e.1) := by
    intro j hj
    obtain ⟨hpar, _, st0, st, hm0, hsolve, hbest, _⟩ := hok j hj
    have hE := compEnv_wf hwf hsp hroots hreach hchk hj hpar
    obtain ⟨htabj, hcovj⟩ := Env.component_table (E := compEnv w ex j) hE hsolve hm0
    exact ⟨(hcovj Y hY).toHasAt, fun k e he => (htabj k e he).1, fun k e he => best_le hbest he⟩
  let ks := (List.range m).map fun j => (V j).length
  let vs := (List.range m).map fun j => (compEnv w ex j).delta [] (V j)
  have hgr : ∀ {α : Type} [Inhabited α] (f : Nat → α) {j : Nat}, j < m →
      ((List.range m).map f)[j]! = f j := by
    intro α _ f j hj
    rw [getElem!_pos _ j (by simpa using hj), List.getElem_map, List.getElem_range]
  have hkn' := uniformKnapsack_le hkn ks vs (by simp [ks, hsize, m]) (by simp [vs, hsize, m])
    (fun j hj => by
      rw [hgr _ (by simp only [m]; omega), hgr _ (by simp only [m]; omega)]
      exact (hfacts j (by simp only [m]; omega)).1)
    (fun j hj => (hfacts j (by simp only [m]; omega)).2.1)
    (fun j hj => (hfacts j (by simp only [m]; omega)).2.2)
  -- the minimum's length, component by component
  have hdec := ulen_compParts hwf hsp hroots hreach hchk Y m (Nat.le_refl _)
  have hbase := csBase_eq (w := w) hwf hroots
  have hperm := min_perm_parts hwf hsp hroots hreach hchk hY
  rw [← ulen_perm hperm] at hdec
  have hlen : ((stg w ex).cs.toList ++ compParts (stg w ex).comps Y m).length =
      (stg w ex).cs.size + ks.sum := by
    rw [List.length_append, compParts_length, Array.length_toList]
  rw [hlen] at hdec
  have hvs : vs.sum = (((List.range m).map fun j => scost (compCx w ex j) ex.dag (V j)).sum : _root_.Int) -
      (((List.range m).map fun j => scost (compCx w ex j) ex.dag []).sum : _root_.Int) := by
    rw [← sum_map_sub_int]
    rfl
  have hcs : (stg w ex).cs.toList.length = (stg w ex).cs.size := Array.length_toList
  rw [hcs] at hbase hdec
  apply Int.toNat_le.mpr
  simp only [Int.not_lt] at hneg
  push_cast
  simp only [V, m, ks, vs, stg] at hneg hkn' hdec hbase hvs ⊢
  omega

/-! ## The final theorem -/

theorem inClass_of_check {dag : Dag} {roots stored : Array Nat}
    (hin : ∀ t ∈ stored.toList, t < dag.size) (h : inClassCheck dag roots stored = true) :
    InClass dag roots stored.toList := by
  unfold inClassCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hs : strictInc stored = true := h1
  refine ⟨strictInc_nodup hs, fun s hs' => ⟨hin s hs', ?_⟩⟩
  rw [Array.all_eq_true'] at h2
  exact of_decide_eq_true (h2 s (Array.mem_toList_iff.mp hs'))

/-- **Stage 4: the uniform optimizer returns a minimum.** With the default
branch-and-bound component search (`uniformSubsetSearch = false`), the set a
successful `optimizeUniformExpanded` stores minimises the uniform length over
the restricted class (duplicate-free terms of in-degree at least 2): its
model length equals its uniform length and is at most every member's.
Hypothesis `SpinesFit`: every telescope spine is shorter than
`teleSubaddEnd` (`Ixon.tagNEnd3 4`), where the TagN telescope headers are
subadditive; the certain-excluded class relies on it. -/
theorem optimizeUniform_minimum {w : Nat} {limits : Limits} {ex : Expanded}
    {res : UniformSharingResult} (hsub : limits.uniformSubsetSearch = false)
    (hsp : SpinesFit (Prep.ofDag ex.dag))
    (h : optimizeUniformExpanded w limits ex = .ok res) :
    IsMinimum ex.dag w ex.roots res.stored.toList ∧
      res.result.modelBytes = ulen ex.dag w ex.roots res.stored.toList := by
  obtain ⟨_, hwf, hroots, _, c, hc, hfin⟩ := optimizeUniform_parts h
  have hreach := optimizeUniform_reach h
  obtain ⟨hin, hcls, hstored, _, hmodel, _⟩ := uniformFinish_spec hfin
  obtain ⟨_, hmb⟩ := optimizeUniform_modelBytes h
  have hul : res.result.modelBytes = ulen ex.dag w ex.roots res.stored.toList := hmb
  have hic : InClass ex.dag ex.roots res.stored.toList := by
    rw [hstored]; exact inClass_of_check hin hcls
  obtain ⟨Ys, hYs⟩ := minimum_exists ex.dag w ex.roots
  have hle := uniformChoose_model_le hsub hwf hsp hroots hreach hc hYs
  refine ⟨⟨hic, fun Y' hY' => ?_⟩, hul⟩
  rw [← hul, hmodel]
  exact Nat.le_trans hle (hYs.2 Y' hY')

/-! ## The tie order of the result -/

/-- The step of `bestSetOf`. -/
def bestStepSet (bd : _root_.Int) (acc : Option (Array Nat)) (o : Option Entry) : Option (Array Nat) :=
  match o with
  | some (d, s) =>
    if d == bd then
      match acc with
      | none => some s
      | some a => if setPrec s a then some s else acc
    else acc
  | none => acc

theorem bestSetOf_eq (tb : CTable) (bd : _root_.Int) :
    bestSetOf tb bd = tb.toList.foldl (bestStepSet bd) none := by
  unfold bestSetOf; rw [← Array.foldl_toList]; rfl

/-- **The best set is the earliest set of value `bd`.** -/
theorem bestSetOf_spec {tb : CTable} (hs : SortedT tb) {bd : _root_.Int} {bs : Array Nat}
    (h : bestSetOf tb bd = some bs) :
    (∃ e, some e ∈ tb.toList ∧ e.1 = bd ∧ e.2 = bs) ∧
      ∀ e, some e ∈ tb.toList → e.1 = bd → LeL bs.toList e.2.toList := by
  rw [bestSetOf_eq] at h
  have hsm : ∀ e, some e ∈ tb.toList → e.2.toList.Pairwise (· < ·) := by
    intro e he
    obtain ⟨k, hk⟩ := mem_toList_getElem! he
    exact hs k e hk
  -- invariant over the fold
  have key : ∀ (l : List (Option Entry)), (∀ o ∈ l, o ∈ tb.toList) → ∀ acc,
      (∀ a, acc = some a → (∃ e, some e ∈ tb.toList ∧ e.1 = bd ∧ e.2 = a) ∧
        a.toList.Pairwise (· < ·)) →
      ∀ r, l.foldl (bestStepSet bd) acc = some r →
        ((∃ e, some e ∈ tb.toList ∧ e.1 = bd ∧ e.2 = r) ∧ r.toList.Pairwise (· < ·)) ∧
          (∀ a, acc = some a → LeL r.toList a.toList) ∧
          ∀ e, some e ∈ l → e.1 = bd → LeL r.toList e.2.toList := by
    intro l
    induction l with
    | nil =>
      intro _ acc hacc r hr
      simp only [List.foldl_nil] at hr
      subst hr
      exact ⟨hacc r rfl, fun a ha => by cases ha; exact leL_refl _,
        fun e he => absurd he List.not_mem_nil⟩
    | cons o l ih =>
      intro hl acc hacc r hr
      rw [List.foldl_cons] at hr
      have hacc' : ∀ a, bestStepSet bd acc o = some a →
          ((∃ e, some e ∈ tb.toList ∧ e.1 = bd ∧ e.2 = a) ∧ a.toList.Pairwise (· < ·)) ∧
            (∀ a', acc = some a' → LeL a.toList a'.toList) ∧
            ∀ e, o = some e → e.1 = bd → LeL a.toList e.2.toList := by
        intro a ha
        cases o with
        | none =>
          simp only [bestStepSet] at ha
          refine ⟨hacc a ha, fun a' ha' => by rw [ha] at ha'; cases ha'; exact leL_refl _,
            fun e he => by cases he⟩
        | some e =>
          obtain ⟨d, s⟩ := e
          have hes : s.toList.Pairwise (· < ·) := hsm (d, s) (hl _ List.mem_cons_self)
          simp only [bestStepSet] at ha
          split at ha
          · rename_i hdb
            have hdb' : d = bd := by simpa using hdb
            cases acc with
            | none =>
              simp only [Option.some.injEq] at ha
              subst ha
              exact ⟨⟨⟨(d, s), hl _ List.mem_cons_self, hdb', rfl⟩, hes⟩, fun a' ha' => (by cases ha'),
                fun e he _ => (by cases he; exact leL_refl _)⟩
            | some a0 =>
              obtain ⟨_, ha0s⟩ := hacc a0 rfl
              simp only at ha
              split at ha
              · rename_i hp
                simp only [Option.some.injEq] at ha
                subst ha
                exact ⟨⟨⟨(d, s), hl _ List.mem_cons_self, hdb', rfl⟩, hes⟩,
                  fun a' ha' => by cases ha'; exact Or.inr ((setPrec_iff hes ha0s).mp hp),
                  fun e he _ => by cases he; exact leL_refl _⟩
              · rename_i hp
                simp only [Option.some.injEq] at ha
                subst ha
                refine ⟨hacc a0 rfl, fun a' ha' => by cases ha'; exact leL_refl _, fun e he _ => ?_⟩
                cases he
                rcases leL_total ha0s hes with h | h
                · exact h
                · exact absurd ((setPrec_iff hes ha0s).mpr h) (by simp [hp])
          · rename_i hdb
            refine ⟨hacc a ha, fun a' ha' => by rw [ha] at ha'; cases ha'; exact leL_refl _,
              fun e he hed => ?_⟩
            cases he
            simp at hdb
            exact absurd hed hdb
      have hstep_some : ∀ a, bestStepSet bd acc o = some a →
          (∃ e, some e ∈ tb.toList ∧ e.1 = bd ∧ e.2 = a) ∧ a.toList.Pairwise (· < ·) :=
        fun a ha => (hacc' a ha).1
      obtain ⟨r1, r2, r3⟩ := ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) _ hstep_some r hr
      refine ⟨r1, fun a ha => ?_, fun e he hed => ?_⟩
      · -- the step's result is at least as early as `a`
        cases hst : bestStepSet bd acc o with
        | none =>
          -- the step never drops a set
          exfalso
          cases o with
          | none => simp [bestStepSet, ha] at hst
          | some e =>
            obtain ⟨d, s⟩ := e
            simp only [bestStepSet, ha] at hst
            split at hst
            · split at hst <;> cases hst
            · cases hst
        | some a1 => exact leL_trans (r2 a1 hst) ((hacc' a1 hst).2.1 a ha)
      · rcases List.mem_cons.mp he with he | he
        · cases hst : bestStepSet bd acc o with
          | none =>
            exfalso
            subst he
            obtain ⟨d, s⟩ := e
            simp only at hed
            simp only [bestStepSet, hed, beq_self_eq_true, if_true] at hst
            cases acc with
            | none => cases hst
            | some a0 => simp only at hst; split at hst <;> cases hst
          | some a1 => exact leL_trans (r2 a1 hst) ((hacc' a1 hst).2.2 e he.symm hed)
        · exact r3 e he hed
  obtain ⟨⟨r1, _⟩, _, r3⟩ := key tb.toList (fun o ho => ho) none (fun a ha => by cases ha) bs h
  exact ⟨r1, fun e he hed => r3 e he hed⟩

/-- Termwise below with equal sums: termwise equal. -/
theorem sum_eq_termwise : ∀ (as bs : List _root_.Int), as.length = bs.length →
    (∀ j, j < as.length → as[j]! ≤ bs[j]!) → as.sum = bs.sum → ∀ j, j < as.length → as[j]! = bs[j]!
  | [], [], _, _, _, j, hj => absurd hj (by simp)
  | a :: as, b :: bs, hl, hle, hs, j, hj => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have h0 := hle 0 (by simp)
    simp only [List.getElem!_cons_zero] at h0
    have hrest : ∀ j, j < as.length → as[j]! ≤ bs[j]! := fun j hj => by
      simpa using hle (j + 1) (by simp; omega)
    have hsr : as.sum ≤ bs.sum := by
      rw [sum_map_range' as, sum_map_range' bs, hl]
      apply sum_le_sum_int
      intro k hk
      have := hrest k (by rw [hl]; exact List.mem_range.mp hk)
      exact this
    simp only [List.sum_cons] at hs
    cases j with
    | zero => simp; omega
    | succ j =>
      simp only [List.getElem!_cons_succ]
      exact sum_eq_termwise as bs hl hrest (by omega) j (by simp at hj; omega)
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl

/-- Merging per-universe sets keeps the tie order. -/
theorem foldl_merge_leL (Uf : Nat → Nat → Prop) (hU : ∀ i i' x, i ≠ i' → Uf i x → ¬ Uf i' x) :
    ∀ (As : List (Array Nat)) (Bs : List (List Nat)) (j0 : Nat) (acc : Array Nat) (B0 : List Nat),
      As.length = Bs.length →
      (∀ j, j < As.length → (∀ x ∈ As[j]!.toList, Uf (j0 + j) x) ∧ (∀ x ∈ Bs[j]!, Uf (j0 + j) x) ∧
        LeL As[j]!.toList Bs[j]!) →
      (∀ x ∈ acc.toList, ∃ i, i < j0 ∧ Uf i x) → (∀ x ∈ B0, ∃ i, i < j0 ∧ Uf i x) →
      LeL acc.toList B0 →
      LeL (As.foldl mergeSorted acc).toList (B0 ++ Bs.flatten)
  | [], Bs, _, acc, B0, hl, _, _, _, h => by
    have : Bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst this; simpa using h
  | A :: As, B :: Bs, j0, acc, B0, hl, hall, hacc, hB0, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
    obtain ⟨hA, hB, hAB⟩ := hall 0 (by simp)
    simp only [List.getElem!_cons_zero, Nat.add_zero] at hA hB hAB
    apply foldl_merge_leL Uf hU As Bs (j0 + 1) _ _ hl
    · intro j hj
      have := hall (j + 1) (by simp; omega)
      simp only [List.getElem!_cons_succ] at this
      rw [show j0 + 1 + j = j0 + (j + 1) by omega]
      exact this
    · intro x hx
      rcases List.mem_append.mp ((mergeSorted_perm acc A).mem_iff.mp hx) with h | h
      · obtain ⟨i, hi, hxi⟩ := hacc x h; exact ⟨i, by omega, hxi⟩
      · exact ⟨j0, by omega, hA x h⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨i, hi, hxi⟩ := hB0 x h; exact ⟨i, by omega, hxi⟩
      · exact ⟨j0, by omega, hB x h⟩
    · apply precL_union (X1 := acc.toList) (Y1 := B0) (X2 := A.toList) (Y2 := B)
      · intro a ha hb
        have ha' : ∃ i, i < j0 ∧ Uf i a := by
          rcases ha with ha | ha
          · exact hacc a ha
          · exact hB0 a ha
        have hb' : Uf j0 a := by
          rcases hb with hb | hb
          · exact hA a hb
          · exact hB a hb
        obtain ⟨i, hi, hia⟩ := ha'
        exact hU i j0 a (by omega) hia hb'
      · intro u; rw [(mergeSorted_perm acc A).mem_iff, List.mem_append]
      · intro u; rw [List.mem_append]
      · exact h
      · exact hAB
  | _ :: _, [], _, _, _, hl, _, _, _, _ => by simp at hl

theorem foldl_merge_sorted (Uf : Nat → Nat → Prop) (hU : ∀ i i' x, i ≠ i' → Uf i x → ¬ Uf i' x) :
    ∀ (As : List (Array Nat)) (j0 : Nat) (acc : Array Nat),
      (∀ j, j < As.length → As[j]!.toList.Pairwise (· < ·) ∧ ∀ x ∈ As[j]!.toList, Uf (j0 + j) x) →
      acc.toList.Pairwise (· < ·) → (∀ x ∈ acc.toList, ∃ i, i < j0 ∧ Uf i x) →
      (As.foldl mergeSorted acc).toList.Pairwise (· < ·)
  | [], _, _, _, h, _ => h
  | A :: As, j0, acc, hall, hs, hacc => by
    rw [List.foldl_cons]
    obtain ⟨hA, hAU⟩ := hall 0 (by simp)
    simp only [List.getElem!_cons_zero, Nat.add_zero] at hA hAU
    apply foldl_merge_sorted Uf hU As (j0 + 1) _ (fun j hj => by
      have := hall (j + 1) (by simp; omega)
      simp only [List.getElem!_cons_succ] at this
      rw [show j0 + 1 + j = j0 + (j + 1) by omega]
      exact this)
    · apply mergeSorted_strict hs hA
      intro x hx hx'
      obtain ⟨i, hi, hxi⟩ := hacc x hx
      exact hU i j0 x (by omega) hxi (hAU x hx')
    · intro x hx
      rcases List.mem_append.mp ((mergeSorted_perm acc A).mem_iff.mp hx) with h | h
      · obtain ⟨i, hi, hxi⟩ := hacc x h; exact ⟨i, by omega, hxi⟩
      · exact ⟨j0, by omega, hAU x h⟩

/-- **The knapsack's choice with the tie order.** -/
theorem uniformKnapsack_tie {limits : Limits} {kCS : Nat} {results : Array CompResult}
    {cd : _root_.Int} {cx : Array Nat} {lb : Bool}
    (h : uniformKnapsack limits kCS results = .ok (cd, cx, lb))
    (Uf : Nat → Nat → Prop) (hU : ∀ i i' x, i ≠ i' → Uf i x → ¬ Uf i' x)
    (ks : List Nat) (vs : List _root_.Int) (Ss : List (List Nat)) (hk : ks.length = results.size)
    (hv : vs.length = results.size) (hS : Ss.length = results.size)
    (hcj : ∀ j, j < results.size →
      SortedT results[j]!.bySize ∧ Indexed results[j]!.bySize ∧ SetsIn results[j]!.bySize (Uf j) ∧
      HasAtT results[j]!.bySize ks[j]! vs[j]! Ss[j]! ∧ (∀ x ∈ Ss[j]!, Uf j x) ∧
      (∀ (k : Nat) (e : Entry), results[j]!.bySize[k]! = some e → results[j]!.bestDelta ≤ e.1) ∧
      bestSetOf results[j]!.bySize results[j]!.bestDelta = some results[j]!.bestSet) :
    CLe (cd + (tag0Size (kCS + cx.size) : _root_.Int)) cx.toList
      (vs.sum + (tag0Size (kCS + ks.sum) : _root_.Int)) Ss.flatten := by
  -- per component: the best is below the choice, and the best set precedes it at a tie
  have hbs : ∀ j, j < results.size → results[j]!.bestDelta ≤ vs[j]! ∧
      (results[j]!.bestDelta = vs[j]! → LeL results[j]!.bestSet.toList Ss[j]!) ∧
      results[j]!.bestSet.toList.Pairwise (· < ·) ∧ ∀ x ∈ results[j]!.bestSet.toList, Uf j x := by
    intro j hjl
    obtain ⟨hsrt, _, hset, hhas, _, hle, hbset⟩ := hcj j hjl
    obtain ⟨⟨eb, heb, hebv, hebs⟩, hleast⟩ := bestSetOf_spec hsrt hbset
    obtain ⟨kb, hkb⟩ := mem_toList_getElem! heb
    obtain ⟨e, he, hev⟩ := hhas
    have hbe := hle _ e he
    refine ⟨by rcases hev with hev | ⟨hev, _⟩ <;> omega, fun heq => ?_, ?_, ?_⟩
    · rcases hev with hev | ⟨hev, hev'⟩
      · omega
      · exact leL_trans (hleast e (getElem!_mem_toList he) (by omega)) hev'
    · rw [← hebs]; exact hsrt kb eb hkb
    · intro x hx; rw [← hebs] at hx; exact hset kb eb hkb x hx
  -- the per-component bests combined
  have hbest_eq : results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int) =
      (results.toList.map (·.bestDelta)).sum := by
    rw [← Array.foldl_toList, foldl_bestDelta_eq]; simp
  have hbx_eq : results.foldl (fun acc r => mergeSorted acc r.bestSet) #[] =
      (results.toList.map (·.bestSet)).foldl mergeSorted #[] := by
    rw [← Array.foldl_toList, List.foldl_map]
  have hgetL : ∀ {α : Type} [Inhabited α] (f : CompResult → α) {j : Nat}, j < results.size →
      (results.toList.map f)[j]! = f results[j]! := by
    intro α _ f j hj
    rw [getElem!_pos _ j (by simpa using hj), List.getElem_map, getElem!_pos results j hj]
    simp
  have hbxs : ((results.toList.map (·.bestSet)).foldl mergeSorted #[]).toList.Pairwise (· < ·) :=
    foldl_merge_sorted Uf hU _ 0 #[] (fun j hj => by
      simp only [List.length_map, Array.length_toList] at hj
      rw [hgetL _ hj, Nat.zero_add]
      exact ⟨(hbs j hj).2.2.1, (hbs j hj).2.2.2⟩) (by simp) (by simp)
  have hsumle : (results.toList.map (·.bestDelta)).sum ≤ vs.sum := by
    rw [sum_map_range (·.bestDelta) results.toList, sum_map_range' vs]
    simp only [Array.length_toList, hv]
    apply sum_le_sum_int
    intro j hjr
    have hj' := List.mem_range.mp hjr
    rw [Array.getElem!_toList]
    exact (hbs j hj').1
  -- the bracket comparison against the per-component bests
  have hbracket : ∀ (bestDelta : _root_.Int) (bestX : Array Nat), bestDelta =
      (results.toList.map (·.bestDelta)).sum →
      bestX = (results.toList.map (·.bestSet)).foldl mergeSorted #[] →
      tag0Size (kCS + bestX.size) ≤ tag0Size (kCS + ks.sum) →
      CLe (bestDelta + (tag0Size (kCS + bestX.size) : _root_.Int)) bestX.toList
        (vs.sum + (tag0Size (kCS + ks.sum) : _root_.Int)) Ss.flatten := by
    intro bestDelta bestX hbd hbx ht
    by_cases hlt : bestDelta + (tag0Size (kCS + bestX.size) : _root_.Int) <
        vs.sum + (tag0Size (kCS + ks.sum) : _root_.Int)
    · exact Or.inl hlt
    · refine Or.inr ⟨by omega, ?_⟩
      have hsum : (results.toList.map (·.bestDelta)).sum = vs.sum := by omega
      have hterm := sum_eq_termwise (results.toList.map (·.bestDelta)) vs (by simp [hv])
        (fun j hj => by
          simp only [List.length_map, Array.length_toList] at hj
          rw [hgetL _ hj]; exact (hbs j hj).1) hsum
      rw [hbx]
      have := foldl_merge_leL Uf hU (results.toList.map (·.bestSet)) Ss 0 #[] [] (by simp [hS])
        (fun j hj => by
          simp only [List.length_map, Array.length_toList] at hj
          rw [hgetL _ hj, Nat.zero_add]
          refine ⟨(hbs j hj).2.2.2, (hcj j hj).2.2.2.2.1, (hbs j hj).2.1 ?_⟩
          have := hterm j (by simp; exact hj)
          rw [hgetL _ hj] at this
          exact this) (by simp) (by simp) (leL_refl _)
      simpa using this
  unfold uniformKnapsack at h
  simp only at h
  rw [hbx_eq, hbest_eq] at h
  generalize hbx : (results.toList.map (·.bestSet)).foldl mergeSorted #[] = bestX at h hbxs
  generalize hbd : (results.toList.map (·.bestDelta)).sum = bestDelta at h hsumle
  split at h
  · rename_i hstart
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      generalize hcap : tag0BracketStart (kCS + bestX.size) - 1 - kCS = cap at h
      have hdp : results.foldl (fun dp r => knapStep cap dp r.bySize)
          (#[some (0, #[])] ++ Array.replicate cap none) =
          (results.toList.map (·.bySize)).foldl (knapStep cap)
            (#[some (0, #[])] ++ Array.replicate cap none) := by
        rw [← Array.foldl_toList, List.foldl_map]
      rw [hdp] at h
      have hts : ∀ j, j < (results.toList.map (·.bySize)).length →
          (results.toList.map (·.bySize))[j]! = results[j]!.bySize := fun j hj => by
        simp only [List.length_map, Array.length_toList] at hj
        exact hgetL _ hj
      have hsorted0 : SortedT (#[some (0, #[])] ++ Array.replicate cap none) := by
        intro k e he
        by_cases hk : k = 0
        · subst hk
          rw [getElem!_pos _ 0 (by rw [Array.size_append]; simp; omega)] at he
          simp at he
          subst he
          simp
        · by_cases hk' : k < 1 + cap
          · rw [getElem!_pos _ k (by simp; omega), Array.getElem_append_right (by simp; omega)] at he
            simp at he
          · simp [getElem!_def, show ¬ k < 1 + cap by omega] at he
      have hsets0 : SetsIn (#[some (0, #[])] ++ Array.replicate cap none) (fun x => ∃ i, i < 0 ∧ Uf i x) := by
        intro k e he x hx
        by_cases hk : k = 0
        · subst hk
          rw [getElem!_pos _ 0 (by rw [Array.size_append]; simp; omega)] at he
          simp at he; rw [← he] at hx; simp at hx
        · by_cases hk' : k < 1 + cap
          · rw [getElem!_pos _ k (by simp; omega), Array.getElem_append_right (by simp; omega)] at he
            simp at he
          · simp [getElem!_def, show ¬ k < 1 + cap by omega] at he
      have hdpS := knapFold_sorted (cap := cap) Uf hU (results.toList.map (·.bySize)) 0 _
        (fun j hj => by rw [hts j hj, Nat.zero_add]
                        simp only [List.length_map, Array.length_toList] at hj
                        exact ⟨(hcj j hj).1, (hcj j hj).2.2.1⟩) hsorted0 hsets0
      have hidx_dp := indexed_fold (cap := cap) (results.toList.map (·.bySize))
        (#[some (0, #[])] ++ Array.replicate cap none)
        (fun t ht => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
          obtain ⟨j, hj', hrj⟩ := List.mem_iff_getElem.mp hr
          simp only [Array.length_toList] at hj'
          have := (hcj j hj').2.1
          rw [getElem!_pos results j hj'] at this
          simpa [← hrj] using this)
        (indexed_dp0 cap)
      obtain ⟨hc1, hc2⟩ := knapChoose_tie kCS hidx_dp hdpS (bestDelta, bestX, false) hbxs
      rw [h] at hc1 hc2
      unfold knapTotal at hc1 hc2
      simp only at hc1 hc2
      by_cases hfit : ks.sum ≤ cap
      · have hfold := knapFold_tie (cap := cap) Uf hU (results.toList.map (·.bySize)) 0 ks vs Ss
          (#[some (0, #[])] ++ Array.replicate cap none) 0 0 []
          (by simp [hk]) (by simp [hv]) (by simp [hS])
          (fun j hj => by
            rw [hts j hj, Nat.zero_add]
            simp only [List.length_map, Array.length_toList] at hj
            exact ⟨(hcj j hj).1, (hcj j hj).2.2.1, (hcj j hj).2.2.2.1, (hcj j hj).2.2.2.2.1⟩)
          hsorted0 hsets0
          ⟨(0, #[]), by rw [getElem!_pos _ 0 (by rw [Array.size_append]; simp; omega)]; simp,
            Or.inr ⟨rfl, leL_refl _⟩⟩ (by simp) (by omega) (by simp <;> omega)
        obtain ⟨e, he, hev⟩ := hfold
        have := hc2 (0 + ks.sum) e he
        simp only [Nat.zero_add, Int.zero_add, List.nil_append] at this hev
        refine cle_trans this ?_
        rcases hev with hev | ⟨hev, hev'⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, hev'⟩
      · exact cle_trans hc1 (hbracket bestDelta bestX hbd.symm hbx.symm
          (tag0Size_ge_of_bracket (by omega)))
  · rename_i hstart
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hbracket _ _ hbd.symm hbx.symm (tag0Size_ge_of_bracket (by omega))

theorem comps_disjoint {w : Nat} {ex : Expanded} (hwf : DagWF ex.dag)
    (hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true) :
    ∀ (i i' x : Nat), i ≠ i' → x ∈ (stg w ex).comps[i]!.toList → ¬ x ∈ (stg w ex).comps[i']!.toList := by
  obtain ⟨hca, _, _, _⟩ := componentsChecked_spec hwf hchk
  intro i i' x hii hx hx'
  have hi : i < (stg w ex).comps.size := Classical.byContradiction fun h => by
    rw [getElem!_neg (stg w ex).comps i h] at hx; exact absurd hx (by simp [default]; exact Array.not_mem_empty x)
  have hi' : i' < (stg w ex).comps.size := Classical.byContradiction fun h => by
    rw [getElem!_neg (stg w ex).comps i' h] at hx'; exact absurd hx' (by simp [default]; exact Array.not_mem_empty x)
  have h1 := (hca i hi x hx).2.2
  have h2 := (hca i' hi' x hx').2.2
  rw [h1] at h2
  simp at h2
  exact hii h2

/-- **The chosen set with the tie order.** The model length and the chosen
uncertain set are at least as good as every minimum's length and uncertain
part. -/
theorem uniformChoose_tie {w : Nat} {limits : Limits} {ex : Expanded}
    (hsub : limits.uniformSubsetSearch = false) (hwf : DagWF ex.dag)
    (hsp : SpinesFit (Prep.ofDag ex.dag))
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hreach : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {c : UniformChoice} (h : uniformChoose w limits ex (Prep.ofDag ex.dag) = .ok c)
    {Y : List Nat} (hY : IsMinimum ex.dag w ex.roots Y) :
    ∃ cx : Array Nat, c.stored = mergeSorted (stg w ex).cs cx ∧
      CLe (c.model : _root_.Int) cx.toList (ulen ex.dag w ex.roots Y : _root_.Int)
        (compParts (stg w ex).comps Y (stg w ex).comps.size) := by
  unfold uniformChoose at h
  simp only at h
  split at h
  all_goals first | (cases h; done) | skip
  rename_i hchk0
  have hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true := by simpa using hchk0
  obtain ⟨⟨results, s1, c1⟩, hsc, h⟩ := bind_eq_ok h
  obtain ⟨⟨cd, cx, lb⟩, hkn, h⟩ := bind_eq_ok h
  simp only at h hkn
  split at h
  · cases h
  rename_i hneg
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨cx, rfl, ?_⟩
  simp only
  obtain ⟨hsize, hok⟩ := searchComponents_spec hsub hsc
  let m := (stg w ex).comps.size
  let V : Nat → List Nat := fun j => partOf Y (stg w ex).comps[j]!.toList
  let Uf : Nat → Nat → Prop := fun j x => x ∈ (stg w ex).comps[j]!.toList
  have hU : ∀ i i' x, i ≠ i' → Uf i x → ¬ Uf i' x := comps_disjoint hwf hchk
  have hfacts : ∀ j, j < m →
      SortedT results[j]!.bySize ∧ Indexed results[j]!.bySize ∧ SetsIn results[j]!.bySize (Uf j) ∧
      HasAtT results[j]!.bySize (V j).length ((compEnv w ex j).delta [] (V j)) (V j) ∧
      (∀ x ∈ V j, Uf j x) ∧
      (∀ (k : Nat) (e : Entry), results[j]!.bySize[k]! = some e → results[j]!.bestDelta ≤ e.1) ∧
      bestSetOf results[j]!.bySize results[j]!.bestDelta = some results[j]!.bestSet := by
    intro j hj
    obtain ⟨hpar, _, st0, st, hm0, hsolve, hbest, hbset⟩ := hok j hj
    have hE := compEnv_wf hwf hsp hroots hreach hchk hj hpar
    obtain ⟨htabj, hcovj⟩ := Env.component_table (E := compEnv w ex j) hE hsolve hm0
    exact ⟨htabj.sorted, fun k e he => (htabj k e he).1, fun k e he x hx => (htabj k e he).2.2.1 x hx,
      hcovj Y hY, fun x hx => (partOf_sub x hx).1, fun k e he => best_le hbest he, hbset⟩
  let ks := (List.range m).map fun j => (V j).length
  let vs := (List.range m).map fun j => (compEnv w ex j).delta [] (V j)
  let Ss := (List.range m).map V
  have hgr : ∀ {α : Type} [Inhabited α] (f : Nat → α) {j : Nat}, j < m →
      ((List.range m).map f)[j]! = f j := by
    intro α _ f j hj
    rw [getElem!_pos _ j (by simpa using hj), List.getElem_map, List.getElem_range]
  have hkt := uniformKnapsack_tie hkn Uf hU ks vs Ss (by simp [ks, hsize, m]) (by simp [vs, hsize, m])
    (by simp [Ss, hsize, m])
    (fun j hj => by
      have hjm : j < m := by simp only [m]; omega
      rw [hgr _ hjm, hgr _ hjm, hgr _ hjm]
      exact hfacts j hjm)
  -- the minimum's length, component by component
  have hdec := ulen_compParts hwf hsp hroots hreach hchk Y m (Nat.le_refl _)
  have hbase := csBase_eq (w := w) hwf hroots
  have hperm := min_perm_parts hwf hsp hroots hreach hchk hY
  rw [← ulen_perm hperm] at hdec
  have hlen : ((stg w ex).cs.toList ++ compParts (stg w ex).comps Y m).length =
      (stg w ex).cs.size + ks.sum := by
    rw [List.length_append, compParts_length, Array.length_toList]
  rw [hlen] at hdec
  have hvs : vs.sum = (((List.range m).map fun j => scost (compCx w ex j) ex.dag (V j)).sum : _root_.Int) -
      (((List.range m).map fun j => scost (compCx w ex j) ex.dag []).sum : _root_.Int) := by
    rw [← sum_map_sub_int]
    rfl
  have hcs : (stg w ex).cs.toList.length = (stg w ex).cs.size := Array.length_toList
  rw [hcs] at hbase hdec
  have hflat : Ss.flatten = compParts (stg w ex).comps Y m := rfl
  rw [hflat] at hkt
  have hmodel : ((((csBase ex (Prep.ofDag ex.dag) (uniformStage w ex (Prep.ofDag ex.dag)) : Nat) :
      _root_.Int) + cd + (tag0Size ((uniformStage w ex (Prep.ofDag ex.dag)).cs.size + cx.size) : _root_.Int)).toNat :
        _root_.Int) = (csBase ex (Prep.ofDag ex.dag) (stg w ex) : _root_.Int) + cd +
          (tag0Size ((stg w ex).cs.size + cx.size) : _root_.Int) := by
    simp only [Int.not_lt] at hneg
    rw [Int.toNat_of_nonneg hneg]
  have hY' : (ulen ex.dag w ex.roots Y : _root_.Int) = (csBase ex (Prep.ofDag ex.dag) (stg w ex) : _root_.Int) +
      (vs.sum + (tag0Size ((stg w ex).cs.size + ks.sum) : _root_.Int)) := by
    simp only [V, m, ks, vs, stg] at hbase hdec hvs ⊢
    omega
  rw [hmodel, hY']
  simp only [stg] at hkt ⊢
  rcases hkt with hk1 | ⟨hk1, hk2⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, hk2⟩

/-- **Stage 4: the uniform optimizer returns the tie-least minimum.** With the
default branch-and-bound component search, the set a successful
`optimizeUniformExpanded` stores minimises the uniform length over the
restricted class, its `modelBytes` is that length, and it comes first in the
tie order `setPrec` (the smallest term where it differs from another minimum
belongs to the other) among all minima. Same `SpinesFit` hypothesis as
`optimizeUniform_minimum`. -/
theorem optimizeUniform_least {w : Nat} {limits : Limits} {ex : Expanded}
    {res : UniformSharingResult} (hsub : limits.uniformSubsetSearch = false)
    (hsp : SpinesFit (Prep.ofDag ex.dag))
    (h : optimizeUniformExpanded w limits ex = .ok res) :
    IsMinimum ex.dag w ex.roots res.stored.toList ∧
      res.result.modelBytes = ulen ex.dag w ex.roots res.stored.toList ∧
      ∀ Y, IsMinimum ex.dag w ex.roots Y → LeL res.stored.toList Y := by
  obtain ⟨hmin, hmb⟩ := optimizeUniform_minimum hsub hsp h
  refine ⟨hmin, hmb, fun Y hY => ?_⟩
  obtain ⟨_, hwf, hroots, _, c, hc, hfin⟩ := optimizeUniform_parts h
  have hreach := optimizeUniform_reach h
  obtain ⟨_, _, hstored, _, hmodel, _⟩ := uniformFinish_spec hfin
  obtain ⟨cx, hcs, hcle⟩ := uniformChoose_tie hsub hwf hsp hroots hreach hc hY
  -- both are minima, so their lengths agree
  have h1 := hmin.2 Y hY.1
  have h2 := hY.2 _ hmin.1
  have hX : ulen ex.dag w ex.roots res.stored.toList = c.model := by rw [← hmb, hmodel]
  have hcle' : LeL cx.toList (compParts (stg w ex).comps Y (stg w ex).comps.size) := by
    rcases hcle with hlt | ⟨_, hle⟩
    · exfalso; omega
    · exact hle
  -- the stored set is the certain-stored terms and `cx`; a minimum is them and its parts
  have hchk : componentsChecked ex.dag (stg w ex).cls (stg w ex).opaq (stg w ex).comps
      (componentLabels ex.dag.size (stg w ex).comps) = true := by
    unfold uniformChoose at hc
    simp only at hc
    split at hc
    · simpa using (by assumption : _)
    · cases hc
  have hperm := min_perm_parts hwf hsp hroots hreach hchk hY
  have hXperm : res.stored.toList.Perm ((stg w ex).cs.toList ++ cx.toList) := by
    rw [hstored, hcs]; exact mergeSorted_perm _ _
  have hXn := hmin.1.1
  have hYn := hY.1.1
  have hdisjX := (List.nodup_append.mp (hXperm.nodup_iff.mp hXn)).2.2
  have hdisjY := (List.nodup_append.mp (hperm.nodup_iff.mp hYn)).2.2
  have hu := precL_union (X1 := (stg w ex).cs.toList) (Y1 := (stg w ex).cs.toList)
    (X2 := cx.toList) (Y2 := compParts (stg w ex).comps Y (stg w ex).comps.size)
    (X := res.stored.toList) (Y := Y)
    (fun a ha hb => by
      have ha' : a ∈ (stg w ex).cs.toList := by rcases ha with ha | ha <;> exact ha
      rcases hb with hb | hb
      · exact hdisjX a ha' a hb rfl
      · exact hdisjY a ha' a hb rfl)
    (fun u => by rw [hXperm.mem_iff, List.mem_append])
    (fun u => by rw [hperm.mem_iff, List.mem_append])
    (leL_refl _) hcle'
  exact hu

end Ix.Compile.Verify.UniformModel
