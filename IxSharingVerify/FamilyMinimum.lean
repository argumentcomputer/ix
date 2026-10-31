import IxSharingVerify.FamilyKnapsackOrigin

/-! Family-relative minimum and canonical tie composition for the existing
knapsack. The signed objective is internal; no `ulen` or finisher claim is made. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (forall₂_getElem)

def products (cfg : Config) : List Factor → List (List (Array Nat))
  | [] => [[]]
  | f :: fs => (family cfg f.cost f.members).flatMap fun s => (products cfg fs).map (s :: ·)

theorem products_iff (cfg : Config) (factors : List Factor) (sets : List (Array Nat)) :
    sets ∈ products cfg factors ↔ ProductMember cfg factors sets := by
  induction factors generalizing sets with
  | nil =>
    cases sets with
    | nil => exact ⟨fun _ => List.Forall₂.nil, fun _ => List.mem_cons_self⟩
    | cons s ss => exact ⟨by simp [products], fun h => by cases h⟩
  | cons f fs ih =>
    constructor
    · intro h
      obtain ⟨s, hs, mapped⟩ := List.mem_flatMap.mp h
      obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp mapped
      exact List.Forall₂.cons hs ((ih rest).mp hr)
    · intro h
      cases h with
      | cons hs rest => exact List.mem_flatMap.mpr ⟨_, hs, List.mem_map.mpr ⟨_, (ih _).mpr rest, rfl⟩⟩

theorem product_nonempty (cfg : Config) {factors : List Factor} (valid : FactorsValid factors) :
    ∃ sets, ProductMember cfg factors sets := by
  induction factors with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons f fs ih =>
    obtain ⟨sets, member⟩ := ih (fun g hg => valid g (List.mem_cons_of_mem f hg))
    exact ⟨#[] :: sets, List.Forall₂.cons (family_empty cfg f.cost (valid f List.mem_cons_self)) member⟩

theorem finite_int_minimum {α : Type} (cost : α → _root_.Int) (xs : List α) (nonempty : xs ≠ []) :
    ∃ x ∈ xs, ∀ y ∈ xs, cost x ≤ cost y := by
  induction xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs ih =>
    by_cases empty : xs = []
    · subst xs
      refine ⟨x, List.mem_cons_self, ?_⟩
      intro y hy
      obtain rfl := List.mem_singleton.mp hy
      exact Int.le_refl _
    · obtain ⟨best, inside, least⟩ := ih empty
      by_cases better : cost x ≤ cost best
      · refine ⟨x, List.mem_cons_self, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Int.le_refl _
        · exact Int.le_trans better (least y hy)
      · refine ⟨best, List.mem_cons_of_mem x inside, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact least y hy

theorem product_minimum_exists (cfg : Config) (baseCount : Nat) {factors : List Factor}
    (valid : FactorsValid factors) : ∃ sets, ProductMinimum cfg baseCount factors sets := by
  obtain ⟨sets, member⟩ := product_nonempty cfg valid
  have inside := (products_iff cfg factors sets).mpr member
  obtain ⟨best, present, least⟩ := finite_int_minimum (productObjective baseCount factors)
    (products cfg factors) (fun empty => by rw [empty] at inside; cases inside)
  exact ⟨best, (products_iff cfg factors best).mp present,
    fun other ho => least other ((products_iff cfg factors other).mpr ho)⟩

def FactorOwns (factors : List Factor) (i x : Nat) : Prop :=
  ∃ f, factors[i]? = some f ∧ x ∈ f.members

def FactorsSeparated (factors : List Factor) : Prop :=
  ∀ i j x, i ≠ j → FactorOwns factors i x → ¬ FactorOwns factors j x

def ResultRow (cfg : Config) (slack : Nat) (f : Factor) (r : CompResult) : Prop :=
  r.bySize = CTable.trim (table cfg f.cost f.members) slack ∧
    CTable.best r.bySize = some r.bestDelta ∧ bestSetOf r.bySize r.bestDelta = some r.bestSet

def FamilyResults (cfg : Config) (slack : Nat) (factors : List Factor) (results : List CompResult) : Prop :=
  List.Forall₂ (ResultRow cfg slack) factors results

theorem ResultRow.sound {cfg : Config} {slack : Nat} {f : Factor} {r : CompResult}
    (row : ResultRow cfg slack f r) :
    Entries r.bySize (fun e => e.2 ∈ family cfg f.cost f.members ∧ e.1 = f.cost e.2) := by
  rw [row.1]
  exact trim_entries (table_meaning cfg f.cost f.members).sound slack

theorem ResultRow.sorted {cfg : Config} {slack : Nat} {f : Factor} {r : CompResult}
    (row : ResultRow cfg slack f r) (valid : f.members.Nodup) : SortedT r.bySize := by
  rw [row.1]
  exact (trim_tie slack (table_ties cfg f.cost valid).1).1

theorem FamilyResults.sound {cfg : Config} {slack : Nat} {factors : List Factor} {results : List CompResult}
    (rows : FamilyResults cfg slack factors results) :
    FamilyTables cfg factors (results.map (·.bySize)) := by
  induction rows with
  | nil => exact List.Forall₂.nil
  | cons row rest ih => exact List.Forall₂.cons row.sound ih

theorem FamilyResults.coherent {cfg : Config} {slack : Nat} {factors : List Factor} {results : List CompResult}
    (rows : FamilyResults cfg slack factors results) (valid : FactorsValid factors) :
    ∀ r ∈ results, ∃ k : Nat, r.bySize[k]! = some (r.bestDelta, r.bestSet) := by
  intro r hr
  obtain ⟨f, hf, row⟩ := forall₂_mem_right' rows r hr
  exact bestSetOf_row (row.sorted (valid f hf)) row.2.2

def componentValues (factors : List Factor) (sets : List (Array Nat)) : List _root_.Int :=
  List.zipWith (fun f s => f.cost s) factors sets

theorem componentValues_sum (factors : List Factor) (sets : List (Array Nat)) :
    (componentValues factors sets).sum = deltaSum factors sets := by
  induction factors generalizing sets with
  | nil => cases sets <;> rfl
  | cons f fs ih =>
    cases sets with
    | nil => rfl
    | cons s ss =>
      change f.cost s + (componentValues fs ss).sum = f.cost s + deltaSum fs ss
      rw [ih ss]

theorem family_knapsack_minimum_compare {cfg : Config} {factors : List Factor} {baseCount upper : Nat}
    (valid : FactorsValid factors) (separated : FactorsSeparated factors)
    (high : baseCount + capacity factors ≤ upper) {results : Array CompResult}
    (rows : FamilyResults cfg (headerSlack baseCount upper) factors results.toList)
    {limits : Limits} {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (run : uniformKnapsack limits baseCount results = .ok (delta, set, lowerBracket))
    {sets : List (Array Nat)} (minimum : ProductMinimum cfg baseCount factors sets) :
    CLe (delta + (tag0Size (baseCount + set.size) : _root_.Int)) set.toList
      (productObjective baseCount factors sets) (sets.map Array.toList).flatten := by
  have rdata := forall₂_getElem rows
  have sdata := forall₂_getElem minimum.1
  have covered := forall₂_getElem (minimum_retained cfg valid minimum (Nat.le_refl _) high)
  have lengths : factors.length = results.size ∧ sets.length = results.size := by
    simpa only [Array.length_toList] using And.intro rdata.1 (sdata.1.symm.trans rdata.1)
  have mapGet {α β : Type} [Inhabited β] (f : α → β) (xs : List α) (j : Nat) (h : j < xs.length) :
      (xs.map f)[j]! = f xs[j] := by
    rw [getElem!_pos _ j (by simpa using h), List.getElem_map]
  have comparison := uniformKnapsack_tie run (FactorOwns factors) separated
    (sets.map Array.size) (componentValues factors sets) (sets.map Array.toList)
    (by simp [lengths.2]) (by simp [componentValues, lengths.1, lengths.2]) (by simp [lengths.2]) ?_
  · simpa only [componentValues_sum, productObjective, selectedCount] using comparison
  intro j hj
  have hjf : j < factors.length := by omega
  have hjs : j < sets.length := by omega
  have row : ResultRow cfg (headerSlack baseCount upper) factors[j] results[j]! := by
    rw [getElem!_pos results j hj]
    exact rdata.2 j hjf (by simpa using hj)
  have chosen := sdata.2 j hjf hjs
  have keep := covered.2 j hjf hjs
  have own : ∀ x ∈ sets[j].toList, FactorOwns factors j x := fun x hx =>
    ⟨factors[j], List.getElem?_eq_getElem hjf, family_members cfg _ _ _ chosen x hx⟩
  have valj : (componentValues factors sets)[j]! = factors[j].cost sets[j] := by
    rw [getElem!_pos _ j (by simp [componentValues]; omega)]
    exact List.getElem_zipWith
  rw [mapGet _ _ _ hjs, valj, mapGet _ _ _ hjs]
  refine ⟨row.sorted (valid _ (List.getElem_mem hjf)),
    fun k e he => (row.sound k e he).1, ?_, ?_, own,
    fun k e he => best_le row.2.1 he, row.2.2⟩
  · intro k e he x hx
    exact ⟨factors[j], List.getElem?_eq_getElem hjf,
      family_members cfg _ _ _ (row.sound k e he).2.1 x hx⟩
  · rw [row.1]
    exact keep

theorem merge_fold_mem (sets : List (Array Nat)) (start : Array Nat) (x : Nat) :
    x ∈ (sets.foldl mergeSorted start).toList ↔ x ∈ start.toList ++ (sets.map Array.toList).flatten := by
  induction sets generalizing start with
  | nil => simp
  | cons s ss ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mem_append, (Exact.mergeSorted_perm start s).mem_iff,
      List.map_cons, List.flatten_cons, List.mem_append, or_assoc]

theorem ProductMember.merge_sorted {cfg : Config} {factors : List Factor} {sets : List (Array Nat)}
    (member : ProductMember cfg factors sets) (valid : FactorsValid factors)
    (separated : FactorsSeparated factors) :
    (sets.foldl mergeSorted #[]).toList.Pairwise (· < ·) := by
  have data := forall₂_getElem member
  apply foldl_merge_sorted (FactorOwns factors) separated sets 0 #[] ?_ (by simp) (by simp)
  intro j hj
  have hjf : j < factors.length := by omega
  have chosen := data.2 j hjf hj
  rw [getElem!_pos _ j hj, Nat.zero_add]
  exact ⟨family_sorted cfg _ _ (valid _ (List.getElem_mem hjf)) _ chosen,
    fun x hx => ⟨factors[j], List.getElem?_eq_getElem hjf, family_members cfg _ _ _ chosen x hx⟩⟩

/-- The actual returned set is the least merged set among product minima.
The witnesses also retain its signed delta and exact selected count. -/
def LeastProductOutput (cfg : Config) (baseCount : Nat) (factors : List Factor)
    (delta : _root_.Int) (set : Array Nat) : Prop :=
  ∃ sets, ProductMinimum cfg baseCount factors sets ∧ delta = deltaSum factors sets ∧
    set = sets.foldl mergeSorted #[] ∧ set.size = selectedCount sets ∧
    ∀ other, ProductMinimum cfg baseCount factors other →
      set = other.foldl mergeSorted #[] ∨ setPrec set (other.foldl mergeSorted #[]) = true

theorem family_knapsack_least {cfg : Config} {factors : List Factor} {baseCount upper : Nat}
    (valid : FactorsValid factors) (separated : FactorsSeparated factors)
    (high : baseCount + capacity factors ≤ upper) {results : Array CompResult}
    (rows : FamilyResults cfg (headerSlack baseCount upper) factors results.toList)
    {limits : Limits} {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (run : uniformKnapsack limits baseCount results = .ok (delta, set, lowerBracket)) :
    LeastProductOutput cfg baseCount factors delta set := by
  obtain ⟨selected, member, hd, hs, hn, objective⟩ :=
    uniformKnapsack_family run (rows.coherent valid) rows.sound
  obtain ⟨best, minimum⟩ := product_minimum_exists cfg baseCount valid
  have first := family_knapsack_minimum_compare valid separated high rows run minimum
  rw [objective] at first
  have chosenMinimum : ProductMinimum cfg baseCount factors selected := by
    refine ⟨member, fun other inside => ?_⟩
    have below := minimum.2 other inside
    rcases first with h | ⟨h, _⟩ <;> omega
  refine ⟨selected, chosenMinimum, hd, hs, hn, ?_⟩
  intro other otherMinimum
  have comparison := family_knapsack_minimum_compare valid separated high rows run otherMinimum
  rw [objective] at comparison
  have reverse := otherMinimum.2 selected member
  rcases comparison with smaller | ⟨_, tied⟩
  · omega
  · have mergedTie : LeL set.toList (other.foldl mergeSorted #[]).toList :=
      leL_congr (fun _ => Iff.rfl)
        (fun x => by simpa using (merge_fold_mem other #[] x).symm) tied
    have sortedOutput : set.toList.Pairwise (· < ·) := by
      rw [hs]; exact member.merge_sorted valid separated
    have sortedOther := otherMinimum.1.merge_sorted valid separated
    rcases mergedTie with same | earlier
    · exact Or.inl (Array.toList_inj.mp (sorted_eq_of_mem sortedOutput sortedOther same))
    · exact Or.inr ((Ix.Sharing.Verify.UniformModel.setPrec_iff sortedOutput sortedOther).mpr earlier)

/-- The existing checked partition supplies disjoint component universes,
nonempty families and the existing stage slack's count interval. -/
theorem initial_factors_partition (ex : Expanded) (width : Nat) (hwf : DagWF ex.dag)
    (checked : let stage := uniformStage width ex (Prep.ofDag ex.dag)
      componentsChecked ex.dag stage.cls stage.opaq stage.comps
        (componentLabels ex.dag.size stage.comps) = true) :
    let stage := uniformStage width ex (Prep.ofDag ex.dag)
    FactorsValid (initialFactors ex stage) ∧ FactorsSeparated (initialFactors ex stage) ∧
      stage.cs.size + capacity (initialFactors ex stage) ≤ stage.cs.size + stage.unc.size := by
  let stage := uniformStage width ex (Prep.ofDag ex.dag)
  have partition := componentsChecked_spec hwf checked
  have capacities := checked_components_capacity hwf checked
  have ownsLabel : ∀ i x, FactorOwns (initialFactors ex stage) i x →
      (componentLabels ex.dag.size stage.comps)[x]! = some i := by
    intro i x ⟨f, atFactor, inside⟩
    obtain ⟨hi, same⟩ := List.getElem?_eq_some_iff.mp atFactor
    have hic : i < stage.comps.size := by simpa [initialFactors] using hi
    have contained : x ∈ stage.comps[i]!.toList := by
      rw [← same] at inside
      simpa [initialFactors, getElem!_pos stage.comps i hic] using inside
    exact (partition.1 i hic x contained).2.2
  refine ⟨?_, ?_, ?_⟩
  · intro f inside
    obtain ⟨members, present, rfl⟩ := List.mem_map.mp inside
    exact capacities.1 members present
  · intro i j x distinct first second
    exact distinct (Option.some.inj ((ownsLabel i x first).symm.trans (ownsLabel j x second)))
  · have bound : capacity (initialFactors ex stage) ≤ stage.unc.size := by
      rw [initial_capacity]
      exact capacities.2
    exact Nat.add_le_add_left bound _

/-- Successful knapsack selection over the actual initial family tables
is a product minimum and chooses the existing `setPrec`-least merged set.
The row adapter and checked partition remain explicit; semantic lengths and
finish/allocation/rematerialization are outside this theorem. -/
theorem initial_knapsack_least (cfg : Config) (ex : Expanded) (width : Nat) (hwf : DagWF ex.dag)
    (checked : let stage := uniformStage width ex (Prep.ofDag ex.dag)
      componentsChecked ex.dag stage.cls stage.opaq stage.comps
        (componentLabels ex.dag.size stage.comps) = true)
    (results : Array CompResult)
    (rows : let stage := uniformStage width ex (Prep.ofDag ex.dag)
      FamilyResults cfg stage.slack (initialFactors ex stage) results.toList)
    {limits : Limits} {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (run : let stage := uniformStage width ex (Prep.ofDag ex.dag)
      uniformKnapsack limits stage.cs.size results = .ok (delta, set, lowerBracket)) :
    let stage := uniformStage width ex (Prep.ofDag ex.dag)
    LeastProductOutput cfg stage.cs.size (initialFactors ex stage) delta set := by
  obtain ⟨valid, separated, bound⟩ := initial_factors_partition ex width hwf checked
  exact family_knapsack_least valid separated bound rows run

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.products_iff [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.product_minimum_exists [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.FamilyResults.coherent [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.family_knapsack_minimum_compare [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.ProductMember.merge_sorted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.family_knapsack_least [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.initial_factors_partition [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.initial_knapsack_least [propext, Classical.choice, Quot.sound]
