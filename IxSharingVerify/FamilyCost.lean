import IxSharingVerify.FamilyProducer

/-! The actual initial family objective is a uniform semantic cost.
Component parts are recovered from product membership, not an assumption
that the chosen set is an old global minimum. Finishing is separate. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc forall₂_getElem)

def selectedTerms (sets : List (Array Nat)) : List Nat := (sets.map Array.toList).flatten

theorem selectedTerms_length (sets : List (Array Nat)) :
    (selectedTerms sets).length = selectedCount sets := by
  simp only [selectedTerms, selectedCount, List.length_flatten, List.map_map,
    Function.comp_def, Array.length_toList]

/-- The intersection with each component recovers precisely its selected
set, preserving component order and allowing only a local permutation. -/
theorem ProductMember.part_perm {cfg : Config} {factors : List Factor} {sets : List (Array Nat)}
    (member : ProductMember cfg factors sets) (valid : FactorsValid factors)
    (separated : FactorsSeparated factors) (j : Nat) (hj : j < factors.length) :
    (partOf (selectedTerms sets) factors[j].members).Perm sets[j]!.toList := by
  have data := forall₂_getElem member
  have hjs : j < sets.length := by omega
  have chosen := data.2 j hj hjs
  rw [getElem!_pos sets j hjs]
  apply (List.perm_ext_iff_of_nodup
    ((valid _ (List.getElem_mem hj)).filter _)
    ((family_sorted cfg _ _ (valid _ (List.getElem_mem hj)) _ chosen).imp Nat.ne_of_lt)).mpr
  intro x
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨inComponent, inUnion⟩
    obtain ⟨terms, mapped, inside⟩ := List.mem_flatten.mp inUnion
    obtain ⟨set, present, rfl⟩ := List.mem_map.mp mapped
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp present
    rw [← same] at inside
    have hif : i < factors.length := by omega
    by_cases eq : i = j
    · subst i; exact inside
    · have ownI : FactorOwns factors i x := ⟨factors[i], List.getElem?_eq_getElem hif,
        family_members cfg _ _ _ (data.2 i hif hi) x inside⟩
      have ownJ : FactorOwns factors j x := ⟨factors[j], List.getElem?_eq_getElem hj, inComponent⟩
      exact False.elim (separated i j x eq ownI ownJ)
  · intro inside
    refine ⟨family_members cfg _ _ _ chosen x inside, ?_⟩
    exact List.mem_flatten.mpr ⟨sets[j].toList,
      List.mem_map.mpr ⟨sets[j], List.getElem_mem hjs, rfl⟩, inside⟩

theorem range_getElem! {α : Type} [Inhabited α] (xs : List α) :
    (List.range xs.length).map (fun j => xs[j]!) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range]
  exact getElem!_pos xs i hj

theorem flatten_map_perm (indices : List Nat) (a b : Nat → List Nat)
    (parts : ∀ i ∈ indices, (a i).Perm (b i)) :
    (indices.map a).flatten.Perm (indices.map b).flatten := by
  induction indices with
  | nil => exact List.Perm.nil
  | cons i indices ih =>
    exact (parts i List.mem_cons_self).append (ih (fun j hj => parts j (List.mem_cons_of_mem _ hj)))

theorem initial_parts_perm {cfg : Config} {ex : Expanded} {width : Nat} {sets : List (Array Nat)}
    (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (member : ProductMember cfg (initialFactors ex (stg width ex)) sets) :
    sets.length = (stg width ex).comps.size ∧
      ∀ j, j < (stg width ex).comps.size →
        (partOf (selectedTerms sets) (stg width ex).comps[j]!.toList).Perm sets[j]!.toList := by
  obtain ⟨valid, separated, _⟩ := initial_factors_partition ex width wf checked
  have length : sets.length = (stg width ex).comps.size := by
    simpa only [initialFactors, List.length_map, Array.length_toList] using (forall₂_getElem member).1.symm
  refine ⟨length, fun j hj => ?_⟩
  have h := member.part_perm valid separated j (by simpa [initialFactors] using hj)
  simpa [initialFactors, getElem!_pos (stg width ex).comps j hj] using h

theorem initial_compParts_perm {cfg : Config} {ex : Expanded} {width : Nat} {sets : List (Array Nat)}
    (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (member : ProductMember cfg (initialFactors ex (stg width ex)) sets) :
    (compParts (stg width ex).comps (selectedTerms sets) (stg width ex).comps.size).Perm
      (selectedTerms sets) := by
  obtain ⟨length, parts⟩ := initial_parts_perm wf checked member
  have h := flatten_map_perm (List.range (stg width ex).comps.size)
    (fun i => partOf (selectedTerms sets) (stg width ex).comps[i]!.toList)
    (fun i => sets[i]!.toList) (fun i hi => parts i (List.mem_range.mp hi))
  have rhs : ((List.range (stg width ex).comps.size).map (fun i => sets[i]!.toList)).flatten =
      selectedTerms sets := by
    rw [← length]
    have mapped := congrArg (fun xs : List (Array Nat) => (xs.map Array.toList).flatten) (range_getElem! sets)
    simpa only [List.map_map, Function.comp_def, selectedTerms] using mapped
  exact h.trans (rhs ▸ List.Perm.refl _)

theorem merge_fold_perm (sets : List (Array Nat)) (start : Array Nat) :
    (sets.foldl mergeSorted start).toList.Perm (start.toList ++ selectedTerms sets) := by
  induction sets generalizing start with
  | nil => simp [selectedTerms]
  | cons s ss ih =>
    rw [List.foldl_cons]
    exact (ih (mergeSorted start s)).trans (by
      simpa only [selectedTerms, List.map_cons, List.flatten_cons, List.append_assoc]
        using (Exact.mergeSorted_perm start s).append_right (selectedTerms ss))

theorem initial_component_delta {ex : Expanded} {width : Nat} (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {j : Nat} (hj : j < (stg width ex).comps.size) (set : Array Nat)
    (inside : ∀ x ∈ set.toList, x ∈ (stg width ex).comps[j]!.toList) :
    componentDelta (compCx width ex j) ((compCx width ex j).phiE (fun _ => false) #[]).1 set =
      (scost (compCx width ex j) ex.dag set.toList : _root_.Int) -
        (scost (compCx width ex j) ex.dag [] : _root_.Int) := by
  have context := compCx_sctx wf checked hj
  have selected := phiE_cost wf context set inside set.contains (by
    intro x
    simp only [Array.contains_eq_mem, Array.mem_toList_iff])
  have empty := phiE_cost wf context #[] (by simp) (fun _ => false) (by simp)
  unfold componentDelta
  rw [selected, empty]

/-- Every actual family delta is the semantic component change from its
empty baseline, in the initial component's original position. -/
theorem initial_deltaSum {cfg : Config} {ex : Expanded} {width : Nat} {sets : List (Array Nat)}
    (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (member : ProductMember cfg (initialFactors ex (stg width ex)) sets) :
    deltaSum (initialFactors ex (stg width ex)) sets =
      ((List.range (stg width ex).comps.size).map fun j =>
        (scost (compCx width ex j) ex.dag (partOf (selectedTerms sets) (stg width ex).comps[j]!.toList) : _root_.Int) -
          (scost (compCx width ex j) ex.dag [] : _root_.Int)).sum := by
  obtain ⟨length, parts⟩ := initial_parts_perm wf checked member
  have valueLength : (componentValues (initialFactors ex (stg width ex)) sets).length =
      (stg width ex).comps.size := by simp [componentValues, initialFactors, length]
  rw [← componentValues_sum, sum_map_range', valueLength]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have bound := List.mem_range.mp hj
  have inSets : j < sets.length := by omega
  have valueAt : (componentValues (initialFactors ex (stg width ex)) sets)[j]! =
      componentDelta (compCx width ex j) ((compCx width ex j).phiE (fun _ => false) #[]).1 sets[j]! := by
    rw [getElem!_pos _ j (by rw [valueLength]; exact bound)]
    simp only [componentValues, List.getElem_zipWith, initialFactors, List.getElem_map]
    unfold compCx
    rw [getElem!_pos (stg width ex).comps j bound, getElem!_pos sets j inSets]
    rfl
  rw [valueAt, initial_component_delta wf checked bound sets[j]! ?_, scost_perm (parts j bound)]
  intro x hx
  exact (partOf_sub x ((parts j bound).mem_iff.mpr hx)).1

/-- Signed accounting cancels the component baselines exactly. The reused
decomposition requires bounded roots, reachability and `SpinesFit`; it is
valid for arbitrary width Nat and arbitrary members of the finite families. -/
theorem initial_product_cost {cfg : Config} {ex : Expanded} {width : Nat} {sets : List (Array Nat)}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (member : ProductMember cfg (initialFactors ex (stg width ex)) sets) :
    (ulen ex.dag width ex.roots ((stg width ex).cs.toList ++ selectedTerms sets) : _root_.Int) =
      (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) +
        productObjective (stg width ex).cs.size (initialFactors ex (stg width ex)) sets := by
  have parts := initial_compParts_perm wf checked member
  have decomposition := ulen_compParts wf spines roots reachable checked (selectedTerms sets)
    (stg width ex).comps.size (Nat.le_refl _)
  have base := csBase_eq (w := width) wf roots
  rw [ulen_perm (parts.append_left (stg width ex).cs.toList), List.length_append,
    parts.length_eq, selectedTerms_length, Array.length_toList] at decomposition
  rw [Array.length_toList] at base
  have deltas := initial_deltaSum wf checked member
  rw [sum_map_sub_int] at deltas
  unfold productObjective
  omega

theorem cs_merge_perm (cs : Array Nat) (sets : List (Array Nat)) :
    (mergeSorted cs (sets.foldl mergeSorted #[])).toList.Perm (cs.toList ++ selectedTerms sets) := by
  have folded := merge_fold_perm sets #[]
  simp only [List.nil_append] at folded
  exact (Exact.mergeSorted_perm cs _).trans (folded.append_left cs.toList)

/-- The same equality for the actual ascending merged array consumed by
the uniform finisher, rather than a reordered representative. -/
theorem initial_merged_cost {cfg : Config} {ex : Expanded} {width : Nat} {sets : List (Array Nat)}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (member : ProductMember cfg (initialFactors ex (stg width ex)) sets) :
    (ulen ex.dag width ex.roots
      (mergeSorted (stg width ex).cs (sets.foldl mergeSorted #[])).toList : _root_.Int) =
      (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) +
        productObjective (stg width ex).cs.size (initialFactors ex (stg width ex)) sets := by
  rw [ulen_perm (cs_merge_perm _ sets)]
  exact initial_product_cost wf spines roots reachable checked member

/-- Family-relative objective minimization is uniform semantic cost
minimization over this same declared product, with CS held fixed. -/
theorem initial_minimum_cost {cfg : Config} {ex : Expanded} {width : Nat} {sets : List (Array Nat)}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (minimum : ProductMinimum cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) sets) :
    ∀ other, ProductMember cfg (initialFactors ex (stg width ex)) other →
      ulen ex.dag width ex.roots (mergeSorted (stg width ex).cs (sets.foldl mergeSorted #[])).toList ≤
        ulen ex.dag width ex.roots (mergeSorted (stg width ex).cs (other.foldl mergeSorted #[])).toList := by
  intro other member
  have first := initial_merged_cost wf spines roots reachable checked minimum.1
  have second := initial_merged_cost wf spines roots reachable checked member
  have bound := minimum.2 other member
  omega

/-- The model expression for an actual least selection is the semantic
cost of CS merged with that same returned array. -/
theorem selected_model_eq {cfg : Config} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {delta : _root_.Int} {set : Array Nat}
    (selected : LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set) :
    (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) + delta +
        (tag0Size ((stg width ex).cs.size + set.size) : _root_.Int) =
      (ulen ex.dag width ex.roots (mergeSorted (stg width ex).cs set).toList : _root_.Int) := by
  obtain ⟨sets, minimum, deltaEq, setEq, countEq, _⟩ := selected
  have cost := initial_merged_cost wf spines roots reachable checked minimum.1
  rw [← setEq] at cost
  unfold productObjective at cost
  rw [← deltaEq, ← countEq] at cost
  omega

/-- Signed accounting introduces neither a negative model nor a truncation
error at the `Int.toNat` boundary. Output-size budgets remain runtime checks. -/
theorem selected_model_nonnegative {cfg : Config} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {delta : _root_.Int} {set : Array Nat}
    (selected : LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set) :
    let model := (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) + delta +
      (tag0Size ((stg width ex).cs.size + set.size) : _root_.Int)
    0 ≤ model ∧ model.toNat = ulen ex.dag width ex.roots (mergeSorted (stg width ex).cs set).toList := by
  have eq := selected_model_eq wf spines roots reachable checked selected
  dsimp only
  rw [eq]
  exact ⟨Int.natCast_nonneg _, Int.toNat_natCast _⟩

/-- Actual successful family production and knapsack selection satisfy
the semantic model equality without a caller delta/table-alignment premise. -/
theorem familyComponents_model {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {results : Array CompResult} {states work : Nat}
    (produced : familyComponents cfg limits ex (stg width ex) width (parentsOf ex.dag) = .ok (results, states, work))
    {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (chosen : uniformKnapsack limits (stg width ex).cs.size results = .ok (delta, set, lowerBracket)) :
    (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) + delta +
        (tag0Size ((stg width ex).cs.size + set.size) : _root_.Int) =
      (ulen ex.dag width ex.roots (mergeSorted (stg width ex).cs set).toList : _root_.Int) :=
  selected_model_eq wf spines roots reachable checked
    (familyComponents_least cfg limits ex width wf checked produced chosen)

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.ProductMember.part_perm [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_compParts_perm [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_component_delta [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_deltaSum [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_product_cost [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_merged_cost [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_minimum_cost [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.selected_model_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.selected_model_nonnegative [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyComponents_model [propext, Classical.choice, Quot.sound]
