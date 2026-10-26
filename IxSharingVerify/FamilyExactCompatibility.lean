import IxSharingVerify.FamilyIdempotence

/-! First compatibility bridge: actual successful uniform-width selections
agree when every INITIAL component uses the exact family. The old theorem
requires uniformSubsetSearch=false, its production/default search path.
Tiered encodings and complete constant-byte compatibility follow separately. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

def ExactInitial (cfg : Config) (ex : Expanded) (width : Nat) : Prop :=
  ∀ members ∈ (stg width ex).comps.toList, members.size ≤ cfg.exactLimit

def ExactAllWidths (cfg : Config) (ex : Expanded) : Prop :=
  ∀ width ∈ [1, 2, 3], ExactInitial cfg ex width

def partsChoices (comps : Array (Array Nat)) (selected : List Nat) : List (Array Nat) :=
  comps.toList.map fun members => sorted (partOf selected members.toList)

/-- Every component intersection, including one from an old minimum, is
in the exact initial product when the gate holds at this width. -/
theorem partsChoices_member (cfg : Config) (ex : Expanded) (width : Nat) (selected : List Nat)
    (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (gate : ExactInitial cfg ex width) :
    ProductMember cfg (initialFactors ex (stg width ex)) (partsChoices (stg width ex).comps selected) := by
  have valid := (checked_components_capacity wf checked).1
  unfold ExactInitial at gate
  unfold ProductMember initialFactors partsChoices
  generalize (stg width ex).comps.toList = members at valid gate ⊢
  induction members with
  | nil => exact List.Forall₂.nil
  | cons m ms ih =>
    refine List.Forall₂.cons ?_ (ih
      (fun x hx => valid x (List.mem_cons_of_mem m hx)) (fun x hx => gate x (List.mem_cons_of_mem m hx)))
    apply (exact_family_iff cfg _ (valid m List.mem_cons_self) (by simpa using gate m List.mem_cons_self) _).mpr
    refine ⟨sorted_strict ((valid m List.mem_cons_self).filter _), ?_⟩
    intro x hx
    exact (partOf_sub x ((sorted_mem _ _).mp hx)).1

theorem partsChoices_perm (comps : Array (Array Nat)) (selected : List Nat) :
    (selectedTerms (partsChoices comps selected)).Perm (compParts comps selected comps.size) := by
  have parts : (selectedTerms (partsChoices comps selected)).Perm
      (comps.toList.map (fun m => partOf selected m.toList)).flatten := by
    unfold selectedTerms partsChoices
    generalize comps.toList = members
    induction members with
    | nil => exact List.Perm.nil
    | cons m ms ih =>
      exact (List.mergeSort_perm (partOf selected m.toList) (fun a b => decide (a ≤ b))).append ih
  have enumerated : (List.range comps.size).map (fun i => comps[i]!) = comps.toList := by
    simpa only [Array.length_toList, Array.getElem!_toList] using range_getElem! comps.toList
  have same := congrArg (fun ms : List (Array Nat) => (ms.map (fun m => partOf selected m.toList)).flatten) enumerated
  have rhs : compParts comps selected comps.size = (comps.toList.map (fun m => partOf selected m.toList)).flatten := by
    simpa only [compParts, List.map_map, Function.comp_def] using same
  rw [rhs]
  exact parts

/-- The old global uniform minimum has a genuine representative in the
declared family; no idealized or unlimited old implementation is used. -/
theorem exact_minimum_represented {cfg : Config} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (gate : ExactInitial cfg ex width) {selected : List Nat}
    (minimum : IsMinimum ex.dag width ex.roots selected) :
    ∃ sets, ProductMember cfg (initialFactors ex (stg width ex)) sets ∧
      (mergeSorted (stg width ex).cs (sets.foldl mergeSorted #[])).toList.Perm selected := by
  refine ⟨partsChoices (stg width ex).comps selected, partsChoices_member cfg ex width selected wf checked gate, ?_⟩
  exact (cs_merge_perm _ _).trans
    (((partsChoices_perm _ _).append_left (stg width ex).cs.toList).trans
      (min_perm_parts wf spines roots reachable checked minimum).symm)

theorem leL_antisymm_mem {first second : List Nat} (forward : LeL first second) (backward : LeL second first) :
    ∀ x, x ∈ first ↔ x ∈ second := by
  rcases forward with same | before
  · exact same
  · rcases backward with same | after
    · exact fun x => (same x).symm
    · exact False.elim (precL_irrefl first (precL_trans before after))

theorem merge_cs_leL (cs first second : Array Nat)
    (firstNodup : (mergeSorted cs first).toList.Nodup)
    (secondNodup : (mergeSorted cs second).toList.Nodup)
    (tie : LeL first.toList second.toList) : LeL (mergeSorted cs first).toList (mergeSorted cs second).toList := by
  have firstDisjoint := (List.nodup_append.mp ((Exact.mergeSorted_perm cs first).nodup_iff.mp firstNodup)).2.2
  have secondDisjoint := (List.nodup_append.mp ((Exact.mergeSorted_perm cs second).nodup_iff.mp secondNodup)).2.2
  apply precL_union (X1 := cs.toList) (Y1 := cs.toList) (X2 := first.toList) (Y2 := second.toList)
  · intro x base extra
    have inside : x ∈ cs.toList := by rcases base with base | base <;> exact base
    rcases extra with extra | extra
    · exact firstDisjoint x inside x extra rfl
    · exact secondDisjoint x inside x extra rfl
  · intro x; rw [(Exact.mergeSorted_perm _ _).mem_iff, List.mem_append]
  · intro x; rw [(Exact.mergeSorted_perm _ _).mem_iff, List.mem_append]
  · exact leL_refl _
  · exact tie

theorem inClassCheck_ascending {dag : Dag} {roots : Array Nat} {stored : Array Nat}
    (checked : inClassCheck dag roots stored = true) : stored.toList.Pairwise (· < ·) := by
  unfold inClassCheck at checked
  simp only [Bool.and_eq_true] at checked
  exact strictInc_spec checked.1

/-- Under the exact-initial-family gate, the ACTUAL old default search and
the ACTUAL new family run return the same ascending stored array and uniform
model length. The old success supplies its existing width/DAG/root/reach/
spine domain; no success of either algorithm is manufactured. -/
theorem familyUniform_exact_match {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    {old fresh : UniformSharingResult}
    (defaultSearch : limits.uniformSubsetSearch = false) (gate : ExactInitial cfg ex width)
    (oldRun : optimizeUniformExpanded width limits ex = .ok old)
    (freshRun : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok fresh) :
    fresh.stored = old.stored ∧ fresh.result.modelBytes = old.result.modelBytes := by
  obtain ⟨_, wf, roots, marks, spines, oldChoice, _, oldFinish⟩ := optimizeUniform_parts oldRun
  have reachable := reach_of_marks wf roots marks
  obtain ⟨_, _, _, _, _, _, checked, _, _, _, _, _⟩ := familyUniform_finish freshRun
  obtain ⟨delta, chosen, least, stored, finished⟩ := familyUniform_finished wf roots reachable freshRun
  obtain ⟨sets, minimum, _, chosenEq, _, tieLeast⟩ := least
  obtain ⟨oldMinimum, oldModel, oldLeast⟩ := optimizeUniform_least defaultSearch oldRun
  obtain ⟨oldSets, oldMember, oldRepresented⟩ :=
    exact_minimum_represented wf spines roots reachable checked gate oldMinimum
  have freshLe : ulen ex.dag width ex.roots fresh.stored.toList ≤ ulen ex.dag width ex.roots old.stored.toList := by
    have bound := initial_minimum_cost wf roots reachable checked minimum oldSets oldMember
    rw [ulen_perm oldRepresented] at bound
    rw [stored, chosenEq]
    exact bound
  have oldLe := oldMinimum.2 fresh.stored.toList finished.inClass
  have freshMinimum : IsMinimum ex.dag width ex.roots fresh.stored.toList :=
    ⟨finished.inClass, fun candidate member => Nat.le_trans freshLe (oldMinimum.2 candidate member)⟩
  have freshCost := initial_merged_cost wf roots reachable checked minimum.1
  have oldCost := initial_merged_cost wf roots reachable checked oldMember
  rw [← chosenEq, ← stored] at freshCost
  rw [ulen_perm oldRepresented] at oldCost
  have equalObjective : productObjective (stg width ex).cs.size (initialFactors ex (stg width ex)) oldSets =
      productObjective (stg width ex).cs.size (initialFactors ex (stg width ex)) sets := by omega
  have oldProductMinimum : ProductMinimum cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) oldSets :=
    ⟨oldMember, fun candidate member => by rw [equalObjective]; exact minimum.2 candidate member⟩
  obtain ⟨valid, separated, _⟩ := initial_factors_partition ex width wf checked
  have chosenSorted : chosen.toList.Pairwise (· < ·) := by
    rw [chosenEq]; exact minimum.1.merge_sorted valid separated
  have oldChoiceSorted := oldMember.merge_sorted valid separated
  have uncertainTie : LeL chosen.toList (oldSets.foldl mergeSorted #[]).toList := by
    rcases tieLeast oldSets oldProductMinimum with same | before
    · rw [same]; exact leL_refl _
    · exact Or.inr ((Ix.Sharing.Verify.UniformModel.setPrec_iff chosenSorted oldChoiceSorted).mp before)
  have fullTie := merge_cs_leL (stg width ex).cs chosen (oldSets.foldl mergeSorted #[])
    (by rw [← stored]; exact finished.inClass.1)
    (oldRepresented.nodup_iff.mpr oldMinimum.1.1) uncertainTie
  rw [← stored] at fullTie
  have freshTie : LeL fresh.stored.toList old.stored.toList :=
    leL_congr (fun _ => Iff.rfl) (fun _ => oldRepresented.mem_iff) fullTie
  have sameMembers := leL_antisymm_mem freshTie (oldLeast _ freshMinimum)
  have freshSorted : fresh.stored.toList.Pairwise (· < ·) := by
    have weak : fresh.stored.toList.Pairwise (· ≤ ·) := by rw [stored]; exact mergeSorted_sorted _ _
    exact (weak.and finished.inClass.1).imp (by intro a b h; omega)
  have oldSorted : old.stored.toList.Pairwise (· < ·) := by
    have spec := uniformFinish_spec oldFinish
    rw [spec.2.2.1]
    exact inClassCheck_ascending spec.2.1
  have same : fresh.stored = old.stored := Array.toList_inj.mp (sorted_eq_of_mem freshSorted oldSorted sameMembers)
  exact ⟨same, by rw [finished.model, same, oldModel]⟩

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.partsChoices_member [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.partsChoices_perm [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.exact_minimum_represented [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.leL_antisymm_mem [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.merge_cs_leL [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.inClassCheck_ascending [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyUniform_exact_match [propext, Classical.choice, Quot.sound]
