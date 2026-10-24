import IxSharingVerify.FamilyCostDomain

/-! Ingredients for a full-endpoint output witness. Every initial component
chooses its actual full family endpoint. Their merged terms are exactly the
initial uncertain terms, so the stored set is CS union uncertain.

An omitted term of compact degree at least two has unshared semantic size
less than twice the reference width. Low compact degree is a separate case:
such a term can have many unfolded occurrences through a repeated parent.
These facts do not yet bound the residual forest, total output, payloads,
root costs or UInt64 fields. No runtime guard or canonical rule is changed. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc child_eq_getElem)

/-- Choose the full ascending set from every actual factor. -/
def fullChoices (factors : List Factor) : List (Array Nat) :=
  factors.map fun f => sorted f.members

theorem fullChoices_member (cfg : Config) {factors : List Factor}
    (valid : FactorsValid factors) : ProductMember cfg factors (fullChoices factors) := by
  induction factors with
  | nil => exact List.Forall₂.nil
  | cons f fs ih =>
    exact List.Forall₂.cons (family_full cfg f.cost (valid f List.mem_cons_self))
      (ih (fun g hg => valid g (List.mem_cons_of_mem _ hg)))

theorem fullChoices_selected_mem (factors : List Factor) (t : Nat) :
    t ∈ selectedTerms (fullChoices factors) ↔ ∃ f ∈ factors, t ∈ f.members := by
  induction factors with
  | nil => simp [fullChoices, selectedTerms]
  | cons f fs ih =>
    simpa only [fullChoices, selectedTerms, List.map_cons, List.flatten_cons,
      List.mem_append, sorted_mem, List.mem_cons, exists_eq_or_imp] using
      or_congr Iff.rfl ih

/-- This is a product member before trimming; it is not asserted to survive
slack trimming or to be the minimizing selection. -/
theorem initial_full_member (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    ProductMember cfg (initialFactors ex (stg width ex))
      (fullChoices (initialFactors ex (stg width ex))) :=
  fullChoices_member cfg (initial_factors_partition ex width wf checked).1

/-- Checked component coverage identifies the union of the full endpoints
with all initial uncertain terms, including both directions of membership. -/
theorem initial_full_selected_mem (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (t : Nat) :
    t ∈ selectedTerms (fullChoices (initialFactors ex (stg width ex))) ↔
      t ∈ (stg width ex).unc.toList := by
  rw [fullChoices_selected_mem]
  have components : (∃ f ∈ initialFactors ex (stg width ex), t ∈ f.members) ↔
      ∃ members ∈ (stg width ex).comps.toList, t ∈ members.toList := by
    constructor
    · rintro ⟨f, present, inside⟩
      unfold initialFactors at present
      obtain ⟨members, component, rfl⟩ := List.mem_map.mp present
      exact ⟨members, component, inside⟩
    · rintro ⟨members, present, inside⟩
      exact ⟨_, List.mem_map.mpr ⟨members, present, rfl⟩, inside⟩
  rw [components, stage_unc, mem_uunc, ← (stage_cls_theta width ex).1]
  obtain ⟨members, _, coverage, _⟩ := componentsChecked_spec wf checked
  constructor
  · rintro ⟨component, present, inside⟩
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp present
    have hic : i < (stg width ex).comps.size := by simpa using hi
    subst component
    have own : t ∈ (stg width ex).comps[i]!.toList := by
      simpa [getElem!_pos (stg width ex).comps i hic] using inside
    exact ⟨(members i hic t own).1, (members i hic t own).2.1⟩
  · rintro ⟨bound, uncertain⟩
    obtain ⟨i, hi, _, inside⟩ := coverage t bound uncertain
    refine ⟨(stg width ex).comps[i]!, ?_, inside⟩
    rw [getElem!_pos (stg width ex).comps i hi]
    exact List.getElem_mem (by simpa using hi)

/-- The actual sorted merge, not only a set-equivalence, recovers `unc`. -/
theorem initial_full_merge (cfg : Config) (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    (fullChoices (initialFactors ex (stg width ex))).foldl mergeSorted #[] =
      (stg width ex).unc := by
  obtain ⟨valid, separated, _⟩ := initial_factors_partition ex width wf checked
  have ascending := (initial_full_member cfg ex width wf checked).merge_sorted valid separated
  have uncAscending : (stg width ex).unc.toList.Pairwise (· < ·) := by
    rw [stage_unc]
    exact (List.pairwise_lt_range).filter _
  apply Array.toList_inj.mp
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    (ascending.imp Nat.le_of_lt) (uncAscending.imp Nat.le_of_lt)
  apply (List.perm_ext_iff_of_nodup (ascending.imp Nat.ne_of_lt)
    (uncAscending.imp Nat.ne_of_lt)).mpr
  intro t
  rw [merge_fold_mem]
  simp only [List.nil_append]
  exact initial_full_selected_mem ex width wf checked t

/-- The full endpoint stored array, in the same merge representation used
by the uniform finisher. -/
def fullStored (ex : Expanded) (width : Nat) : Array Nat :=
  mergeSorted (stg width ex).cs
    ((fullChoices (initialFactors ex (stg width ex))).foldl mergeSorted #[])

theorem initial_full_stored (cfg : Config) (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    fullStored ex width = mergeSorted (stg width ex).cs (stg width ex).unc := by
  unfold fullStored
  rw [initial_full_merge cfg ex width wf checked]

theorem initial_full_stored_mem (cfg : Config) (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (t : Nat) :
    t ∈ (fullStored ex width).toList ↔ t < ex.dag.size ∧
      ((ucls ex.dag ex.roots width (stg width ex).theta)[t]! = .certainStored ∨
        (ucls ex.dag ex.roots width (stg width ex).theta)[t]! = .uncertain) := by
  rw [initial_full_stored cfg ex width wf checked, (Exact.mergeSorted_perm _ _).mem_iff,
    List.mem_append, initial_cs_mem, stage_unc, mem_uunc]
  constructor
  · rintro (⟨bound, stored⟩ | ⟨bound, uncertain⟩)
    · exact ⟨bound, Or.inl stored⟩
    · exact ⟨bound, Or.inr uncertain⟩
  · rintro ⟨bound, stored | uncertain⟩
    · exact Or.inl ⟨bound, stored⟩
    · exact Or.inr ⟨bound, uncertain⟩

/-- Every reachable node has at least one fully unfolded occurrence. -/
theorem occurrences_positive {dag : Dag} (wf : DagWF dag) (roots : Array Nat)
    (inBounds : ∀ r ∈ roots.toList, r < dag.size)
    (reachable : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y) :
    ∀ y, y < dag.size → 1 ≤ (occurrences dag roots)[y]! := by
  have key : ∀ m y, dag.size - y = m → y < dag.size →
      1 ≤ (occurrences dag roots)[y]! := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro y distance bound
      rw [occurrences_spec wf roots inBounds bound]
      obtain ⟨r, present, desc⟩ := reachable y bound
      rcases desc_last desc with rfl | ⟨z, k, parent, hk, edge⟩
      · have := List.count_pos_iff.mpr present
        omega
      · have rootBound := inBounds r present
        have parentBound : z < dag.size :=
          Nat.lt_of_le_of_lt (Desc.le_of_wf wf parent rootBound) rootBound
        have below : y < z := by
          rw [← edge, child_eq_getElem _ k hk]
          exact wf.child_lt parentBound (Array.getElem_mem _)
        have arity : k < (dag.node z).head.arity := by
          rw [← wf.children_size parentBound]
          exact hk
        have edgePositive := edgeAll_pos arity edge
        have parentPositive := ih (dag.size - z) (by omega) z rfl parentBound
        have termBound := sum_range_ge
          (fun x => edgeAll (Prep.ofDag dag) x y * (occurrences dag roots)[x]!) parentBound
        have productPositive := Nat.mul_le_mul edgePositive parentPositive
        omega
  exact fun y bound => key _ y rfl bound

/-- Compact in-degree counts each incoming edge/root once; full unfolding
counts each such edge at least once on the reachable input DAG. -/
theorem degree_le_occurrences {dag : Dag} (wf : DagWF dag) (roots : Array Nat)
    (inBounds : ∀ r ∈ roots.toList, r < dag.size)
    (reachable : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y)
    {t : Nat} (bound : t < dag.size) :
    (graphFacts dag roots).deg[t]! ≤ (graphFacts dag roots).occ[t]! := by
  change (edgeCounts dag roots false)[t]! ≤ (occurrences dag roots)[t]!
  rw [edgeCounts_spec wf roots inBounds false t, occurrences_spec wf roots inBounds bound]
  simp only [Bool.false_eq_true, ite_false]
  apply Nat.add_le_add_left
  apply sum_le_sum_of_le
  intro y present
  have positive := occurrences_positive wf roots inBounds reachable y (List.mem_range.mp present)
  change edgeAll (Prep.ofDag dag) y t ≤
    edgeAll (Prep.ofDag dag) y t * (occurrences dag roots)[y]!
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (edgeAll (Prep.ofDag dag) y t) positive

/-- The exclusion inequality for at least two occurrences forces a cheap
unshared body. This is arithmetic, without telescope subadditivity. -/
theorem excluded_size_lt_two {occ size width : Nat} (repeated : 2 ≤ occ)
    (excluded : (occ - 1) * size < occ * width) : size < 2 * width := by
  apply Classical.byContradiction
  intro large
  have doubled : occ ≤ (occ - 1) * 2 := by omega
  have first := Nat.mul_le_mul_right width doubled
  have second := Nat.mul_le_mul_left (occ - 1) (show 2 * width ≤ size by omega)
  rw [Nat.mul_assoc] at first
  exact Nat.not_lt_of_ge (Nat.le_trans first second) excluded

/-- If a term is omitted despite repeated compact use, the actual stage's
first classification test must have excluded it. -/
theorem initial_omitted_repeated_excluded (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {t : Nat} (bound : t < ex.dag.size) (omitted : t ∉ (fullStored ex width).toList)
    (repeated : 2 ≤ (graphFacts ex.dag ex.roots).deg[t]!) :
    certainExcludedTest (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) width t = true := by
  apply Classical.byContradiction
  intro excluded
  apply omitted
  apply (initial_full_stored_mem cfg ex width wf checked t).mpr
  refine ⟨bound, ?_⟩
  rw [ucls_eq bound, ite_eq_right excluded, ite_eq_right (by omega)]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The semantic unshared standalone cost of an omitted compactly repeated
term is below 2*w. This does not bound a low-degree descendant of such a
term merely because it has repeated occurrences in the full unfolding. -/
theorem initial_omitted_repeated_small (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {t : Nat} (bound : t < ex.dag.size) (omitted : t ∉ (fullStored ex width).toList)
    (repeated : 2 ≤ (graphFacts ex.dag ex.roots).deg[t]!) :
    uInl (Prep.ofDag ex.dag) width (fun _ => false) t < 2 * width := by
  have occurrences := Nat.le_trans repeated (degree_le_occurrences wf ex.roots roots reachable bound)
  have excluded := initial_omitted_repeated_excluded cfg ex width wf checked bound omitted repeated
  simp only [certainExcludedTest, decide_eq_true_eq] at excluded
  have small := excluded_size_lt_two occurrences excluded
  rwa [base_eq_uInl wf width bound] at small

/-- The exact omitted-node split needed for later residual-forest counting:
no repeated compact fanout remains except through cheap unshared bodies. -/
theorem initial_omitted_cases (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {t : Nat} (bound : t < ex.dag.size) (omitted : t ∉ (fullStored ex width).toList) :
    (graphFacts ex.dag ex.roots).deg[t]! < 2 ∨
      uInl (Prep.ofDag ex.dag) width (fun _ => false) t < 2 * width := by
  by_cases low : (graphFacts ex.dag ex.roots).deg[t]! < 2
  · exact Or.inl low
  · exact Or.inr (initial_omitted_repeated_small cfg ex width wf roots reachable checked
      bound omitted (by omega))

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.fullChoices_member [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.fullChoices_selected_mem [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_full_member [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_full_selected_mem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_full_merge [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_full_stored [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_full_stored_mem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.occurrences_positive [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.degree_le_occurrences [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.excluded_size_lt_two [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_omitted_repeated_excluded [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_omitted_repeated_small [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_omitted_cases [propext, Classical.choice, Quot.sound]
