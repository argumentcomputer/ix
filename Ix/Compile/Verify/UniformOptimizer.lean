import Ix.Compile.Verify.UniformModel

/-!
# The uniform-width optimizer against the model

`modelBytes` of `optimizeSharingUniform` is the model length
`uniformCost` of the stored set it returns, and the table it materializes is
a permutation of that set.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (bind_eq_ok indexOfTable_spec indexOfPairs_mem
  getElem!_of_getElem? foldl_some_mem setBang_getElem! cp_of_childrenPrecede)

/-! ## Pinned order -/

theorem toList_erase (xs : Array Nat) (a : Nat) : (xs.erase a).toList = xs.toList.erase a := by
  rcases xs with ⟨xs⟩
  simp

theorem pinnedPick_mem (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat))
    (placed : Std.HashSet Nat) (remaining : Array Nat) {pick : Nat}
    (h : pinnedPick deg deps placed remaining = some pick) : pick ∈ remaining.toList := by
  unfold pinnedPick at h
  rw [← Array.foldl_toList] at h
  rcases foldl_some_mem _ (by
      intro b o r hb
      cases b with
      | none => simp only [Option.some.injEq] at hb; exact Or.inl hb.symm
      | some b =>
        simp only at hb
        split at hb
        · simp only [Option.some.injEq] at hb; exact Or.inl hb.symm
        · exact Or.inr hb) _ _ _ h with hm | hm
  · rw [Array.toList_filter] at hm
    exact (List.mem_filter.mp hm).1
  · cases hm

/-- The pinned order places every remaining term exactly once. -/
theorem pinnedPlace_perm (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) :
    ∀ (fuel : Nat) (order remaining : Array Nat) (placed : Std.HashSet Nat),
      (pinnedPlace deg deps fuel order remaining placed).toList.Perm
        (order.toList ++ remaining.toList) := by
  intro fuel
  induction fuel with
  | zero => intro order remaining placed; simp [pinnedPlace]
  | succ fuel ih =>
    intro order remaining placed
    simp only [pinnedPlace]
    split
    · simp
    · rename_i pick hpick
      have hmem := pinnedPick_mem deg deps placed remaining hpick
      refine (ih _ _ _).trans ?_
      rw [Array.toList_push, toList_erase, List.append_assoc]
      exact List.Perm.append_left _ (List.perm_cons_erase hmem).symm

theorem pinnedOrder_perm (dag : Dag) (deg : Array Nat) (stored : Array Nat) :
    (pinnedOrder dag deg stored).toList.Perm stored.toList := by
  unfold pinnedOrder
  simpa using pinnedPlace_perm deg (pinnedDeps dag stored) stored.size #[] stored {}

/-! ## Dictionaries of a table -/

theorem getD_setBang (acc : Array (Option Nat)) (t u : Nat) (v : Option Nat) :
    (acc.set! t v)[u]?.getD none = if t = u ∧ t < acc.size then v else acc[u]?.getD none := by
  simp only [Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : t = u
  · subst h
    by_cases hs : t < acc.size <;> simp [hs]
  · simp [h]

theorem indexOfPairs_isSome :
    ∀ (pairs : List (Nat × Nat)) (acc : Array (Option Nat)) (u : Nat), u < acc.size →
      ((acc[u]?.getD none).isSome = true ∨ ∃ i, (u, i) ∈ pairs) →
      ((pairs.foldl (fun acc (t, i) => acc.set! t (some i)) acc)[u]?.getD none).isSome = true := by
  intro pairs
  induction pairs with
  | nil =>
    intro acc u _ h
    rcases h with h | ⟨_, h⟩
    · exact h
    · cases h
  | cons x xs ih =>
    intro acc u hu h
    obtain ⟨t, i⟩ := x
    rw [List.foldl_cons]
    apply ih _ u (by simp [Array.set!]; omega)
    by_cases htu : t = u
    · subst htu
      left
      rw [getD_setBang, if_pos ⟨rfl, hu⟩]
      rfl
    · rw [getD_setBang, if_neg (fun h => htu h.1)]
      rcases h with h | ⟨i', hi'⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp hi' with h | h
        · cases h; exact absurd rfl htu
        · exact Or.inr ⟨i', h⟩

theorem indexOfPairs_size :
    ∀ (pairs : List (Nat × Nat)) (acc : Array (Option Nat)),
      (pairs.foldl (fun acc (t, i) => acc.set! t (some i)) acc).size = acc.size := by
  intro pairs
  induction pairs with
  | nil => intro _; rfl
  | cons x xs ih => intro acc; rw [List.foldl_cons, ih]; simp [Array.set!]

/-- The dictionary of a table holds exactly the table's terms. -/
theorem indexOfTable_isSome (size : Nat) (table : Array Nat) (hin : ∀ t ∈ table.toList, t < size)
    (u : Nat) :
    ((indexOfPairs size table.toList.zipIdx)[u]?.getD none).isSome =
      decide (u ∈ table.toList) := by
  by_cases hu : u ∈ table.toList
  · rw [decide_eq_true hu]
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
    unfold indexOfPairs
    apply indexOfPairs_isSome _ _ u (by simp; exact hin u hu)
    exact Or.inr ⟨i, List.mem_zipIdx_iff_getElem?.mpr hi⟩
  · rw [decide_eq_false hu]
    cases hs : (indexOfPairs size table.toList.zipIdx)[u]?.getD none with
    | none => rfl
    | some i =>
      have := indexOfTable_spec size table u i hs
      exact absurd (Array.mem_toList_iff.mpr (Array.mem_of_getElem? this)) hu

theorem widthOfStored (n w : Nat) (stored : List Nat) (hin : ∀ t ∈ stored, t < n) (u : Nat) :
    widthOf (stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)) u =
      if decide (u ∈ stored) then some w else none := by
  unfold widthOf
  suffices h : ∀ (l : List Nat) (acc : Array (Option Nat)), acc.size = n →
      (∀ t ∈ l, t < n) →
      (l.foldl (fun acc t => acc.set! t (some w)) acc)[u]?.getD none =
        if u ∈ l then some w else acc[u]?.getD none by
    rw [h stored _ (by simp) hin]
    by_cases hu : u ∈ stored
    · simp [hu]
    · simp only [hu, decide_false, if_false, Bool.false_eq_true]
      simp only [Array.getElem?_replicate]
      split <;> rfl
  intro l
  induction l with
  | nil => intro acc _ _; simp
  | cons x xs ih =>
    intro acc hacc hl
    rw [List.foldl_cons, ih _ (by simp [Array.set!, hacc])
      (fun t ht => hl t (List.mem_cons_of_mem _ ht)), getD_setBang]
    have hx := hl x List.mem_cons_self
    by_cases hux : u ∈ xs
    · simp [hux]
    · by_cases hxu : x = u
      · subst hxu; simp [hacc, hx]
      · simp [hux, hxu, Ne.symm hxu]

/-! ## The materialized total -/

theorem foldl_add_eq_sum {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat), l.foldl (fun acc t => acc + f t) a = a + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; rw [List.foldl_cons, ih]; simp; omega

theorem array_foldl_add_sum {α : Type} (f : α → Nat) (arr : Array α) :
    arr.foldl (fun acc t => acc + f t) 0 = (arr.toList.map f).sum := by
  rw [← Array.foldl_toList, foldl_add_eq_sum]
  simp

theorem materializeDependent_total {p : Prep} {table roots : Array Nat}
    {width : Array (Option Nat)} {limits : Limits} {es rs : Array Ixon.Expr} {total work : Nat}
    (h : p.materializeDependent table roots width limits = .ok (es, rs, total, work)) :
    total = tag0Size table.size +
      (table.toList.map (p.inlineCost (p.evalAll width)
        (indexOfPairs p.dag.size table.toList.zipIdx) width)).sum +
      (roots.toList.map fun r => (p.evalAll width).cost[r]!).sum := by
  unfold Prep.materializeDependent at h
  split at h
  · cases h
  simp only at h
  split at h
  · cases h
  obtain ⟨es', _, h⟩ := bind_eq_ok h
  obtain ⟨rs', _, h⟩ := bind_eq_ok h
  cases h
  rw [array_foldl_add_sum, array_foldl_add_sum]

/-! ## The optimizer's last stage -/

/-- What a successful `uniformFinish` returns. -/
theorem uniformFinish_spec {w : Nat} {limits : Limits} {ex : Expanded} {p : Prep}
    {c : UniformChoice} {res : UniformSharingResult}
    (h : uniformFinish w limits ex p c = .ok res) :
    (∀ t ∈ c.stored.toList, t < ex.dag.size) ∧ inClassCheck ex.dag ex.roots c.stored = true ∧
      res.stored = c.stored ∧
      res.result.tableTerms = pinnedOrder ex.dag c.facts.deg c.stored ∧
      res.result.modelBytes = c.model ∧
      ∃ work, p.materializeDependent (pinnedOrder ex.dag c.facts.deg c.stored) ex.roots
          (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
          limits = .ok (res.result.sharing, res.result.roots, c.model, work) ∧
        res.result.variableBytes = tag0Size res.result.sharing.size +
          exprsSize res.result.sharing + exprsSize res.result.roots := by
  unfold uniformFinish at h
  simp only at h
  split at h
  · rename_i hall
    split at h
    case isFalse => cases h
    rename_i hcls
    have hcls' : inClassCheck ex.dag ex.roots c.stored = true := by simpa using hcls
    obtain ⟨⟨entries, roots, predicted, work⟩, hmat, h⟩ := bind_eq_ok h
    simp only at h
    split at h
    · rename_i hpred
      obtain ⟨⟨entryIds, rootIds, visits⟩, _, h⟩ := bind_eq_ok h
      simp only at h
      split at h
      · split at h
        · cases h
          have hpm : predicted = c.model := by simpa using hpred
          subst hpm
          refine ⟨fun t ht => ?_, hcls', rfl, rfl, rfl, work, hmat, rfl⟩
          rw [Array.all_eq_true] at hall
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
          simpa using hall i (by simpa using hi)
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## `modelBytes` soundness -/

theorem dagWF_of_checks {dag : Dag} (hcp : childrenPrecede dag.nodes = true)
    (har : dag.nodes.all (fun node => node.children.size == node.head.arity) = true) :
    DagWF dag where
  precede := cp_of_childrenPrecede hcp
  arity := by
    intro t ht
    rw [Array.all_eq_true] at har
    have := har t ht
    rw [Ix.Compile.Verify.SharingExact.getElem!_eq_getElem _ t ht]
    simpa using this

/-- The optimizer's checks and its last stage. -/
theorem optimizeUniform_parts {w : Nat} {limits : Limits} {ex : Expanded}
    {res : UniformSharingResult} (h : optimizeUniformExpanded w limits ex = .ok res) :
    w ≠ 0 ∧ DagWF ex.dag ∧ (∀ r ∈ ex.roots.toList, r < ex.dag.size) ∧
      (reachMarks ex.dag.nodes ex.roots).all id = true ∧
      ∃ c, uniformChoose w limits ex (Prep.ofDag ex.dag) = .ok c ∧
        uniformFinish w limits ex (Prep.ofDag ex.dag) c = .ok res := by
  unfold optimizeUniformExpanded at h
  cases hw : (w == 0) with
  | true => simp [hw] at h; cases h
  | false =>
    cases hcp : childrenPrecede ex.dag.nodes with
    | false => simp [hw, hcp] at h; cases h
    | true =>
      cases har : ex.dag.nodes.all (fun node => node.children.size == node.head.arity) with
      | false => simp [hw, hcp, har] at h; cases h
      | true =>
        cases hr : ex.roots.all (· < ex.dag.size) with
        | false => simp [hw, hcp, har, hr] at h; cases h
        | true =>
          cases hm : (reachMarks ex.dag.nodes ex.roots).all id with
          | false =>
            simp only [hw, hcp, har, hr, hm, Bool.false_eq_true, if_false, if_true,
              Bool.not_true, Bool.not_false, ↓reduceIte] at h
            cases h
          | true =>
            simp only [hw, hcp, har, hr, hm, Bool.false_eq_true, if_false, if_true] at h
            obtain ⟨c, hc, h⟩ := bind_eq_ok h
            refine ⟨by simpa using hw, dagWF_of_checks hcp har, fun r hrm => ?_, rfl, c, hc, h⟩
            rw [Array.all_eq_true] at hr
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrm
            simpa using hr i (by simpa using hi)

/-- **`modelBytes` soundness.** The model length reported by the uniform
optimizer is `uniformCost` of the stored set it returns (every stored term
at width `w`, each entry at its cheapest inline writing, each root at its
cheapest standalone writing), and the materialized table is a permutation
of that set. -/
theorem optimizeUniform_modelBytes {w : Nat} {limits : Limits} {ex : Expanded}
    {res : UniformSharingResult} (h : optimizeUniformExpanded w limits ex = .ok res) :
    res.result.tableTerms.toList.Perm res.stored.toList ∧
      res.result.modelBytes = uniformCost (Prep.ofDag ex.dag) w
        (fun t => decide (t ∈ res.stored.toList)) res.stored.toList ex.roots.toList := by
  obtain ⟨_, hwf, _, _, c, _, hfin⟩ := optimizeUniform_parts h
  obtain ⟨hin, _, hstored, htable, hmodel, work, hmat, _⟩ := uniformFinish_spec hfin
  have hp := prepWF_ofDag hwf
  have hempty := ofDag_empty_size ex.dag
  let p := Prep.ofDag ex.dag
  let order := pinnedOrder ex.dag c.facts.deg c.stored
  have hperm : order.toList.Perm c.stored.toList := pinnedOrder_perm _ _ _
  have hin' : ∀ t ∈ order.toList, t < p.dag.size := fun t ht => hin t (hperm.subset ht)
  have hwidth : ∀ u, widthOf (c.stored.foldl (fun acc t => acc.set! t (some w))
      (Array.replicate ex.dag.size none)) u =
      if (fun t => decide (t ∈ c.stored.toList)) u then some w else none := by
    intro u
    rw [← Array.foldl_toList]
    exact widthOfStored ex.dag.size w c.stored.toList hin u
  have hindex : ∀ u, ((indexOfPairs p.dag.size order.toList.zipIdx)[u]?.getD none).isSome =
      (fun t => decide (t ∈ c.stored.toList)) u := by
    intro u
    rw [indexOfTable_isSome _ order hin' u]
    simp only [decide_eq_decide]
    exact hperm.mem_iff
  refine ⟨by rw [htable, hstored]; exact hperm, ?_⟩
  rw [hmodel, materializeDependent_total hmat, hstored]
  unfold uniformCost
  have hlen : order.size = c.stored.toList.length := by
    rw [← Array.length_toList]; exact hperm.length_eq
  have hentries : (order.toList.map (p.inlineCost (p.evalAll
      (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)))
      (indexOfPairs p.dag.size order.toList.zipIdx)
      (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)))).sum =
      (c.stored.toList.map (uInl p w (fun t => decide (t ∈ c.stored.toList)))).sum := by
    rw [List.map_congr_left (fun t ht => hp.inlineCost_eq hempty _ _ hwidth hindex t (hin' t ht))]
    exact List.Perm.sum_nat (hperm.map _)
  have hroots : (ex.roots.toList.map fun r => (p.evalAll
      (c.stored.foldl (fun acc t => acc.set! t (some w))
        (Array.replicate ex.dag.size none))).cost[r]!).sum =
      (ex.roots.toList.map (uCost p w (fun t => decide (t ∈ c.stored.toList)))).sum := by
    rw [List.map_congr_left (fun r _ => hp.evalAll_cost hempty _ hwidth r)]
  simp only [p, order] at hentries hroots hlen
  rw [hlen, hentries, hroots]

end Ix.Compile.Verify.UniformModel
