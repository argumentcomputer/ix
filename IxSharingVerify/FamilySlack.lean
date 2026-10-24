import IxSharingVerify.FamilyTies
import IxSharingVerify.UniformChecks

/-! Whole-component replacement in the actual finite family product.
The objective is signed component deltas plus the Tag0 count header. No
exact-search subgroup, global `IsMinimum`, or spine restriction is used. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel

structure Factor where
  members : List Nat
  cost : Cost

def ProductMember (cfg : Config) (factors : List Factor) (sets : List (Array Nat)) : Prop :=
  List.Forall₂ (fun f s => s ∈ family cfg f.cost f.members) factors sets

def FactorsValid (factors : List Factor) : Prop := ∀ f ∈ factors, f.members.Nodup

def capacity (factors : List Factor) : Nat := (factors.map (·.members.length)).sum
def selectedCount (sets : List (Array Nat)) : Nat := (sets.map Array.size).sum

def deltaSum : List Factor → List (Array Nat) → _root_.Int
  | f :: fs, s :: ss => f.cost s + deltaSum fs ss
  | _, _ => 0

def productObjective (baseCount : Nat) (factors : List Factor) (sets : List (Array Nat)) : _root_.Int :=
  deltaSum factors sets + (tag0Size (baseCount + selectedCount sets) : _root_.Int)

def ProductMinimum (cfg : Config) (baseCount : Nat) (factors : List Factor)
    (sets : List (Array Nat)) : Prop :=
  ProductMember cfg factors sets ∧ ∀ other, ProductMember cfg factors other →
    productObjective baseCount factors sets ≤ productObjective baseCount factors other

def headerSlack (lower upper : Nat) : Nat := tag0Size upper - tag0Size lower

/-- Replacement changes one whole component choice to another member of
that same family. It does not require closure under arbitrary insertion. -/
theorem ProductMember.replace {cfg : Config} {factors : List Factor} {sets : List (Array Nat)}
    (h : ProductMember cfg factors sets) (i : Nat) (replacement : Array Nat) {f : Factor}
    (atFactor : factors[i]? = some f) (inside : replacement ∈ family cfg f.cost f.members) :
    ProductMember cfg factors (sets.set i replacement) := by
  induction h generalizing i with
  | nil => simp at atFactor
  | @cons factor set factors sets here tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atFactor
      subst f
      exact List.Forall₂.cons inside tail
    | succ i =>
      exact List.Forall₂.cons here (ih i (by simpa using atFactor))

theorem family_size_le (cfg : Config) (f : Factor) (hd : f.members.Nodup)
    {set : Array Nat} (inside : set ∈ family cfg f.cost f.members) : set.size ≤ f.members.length := by
  have hn : set.toList.Nodup := (family_sorted cfg f.cost f.members hd set inside).imp Nat.ne_of_lt
  exact hn.length_le_of_subset (family_members cfg f.cost f.members set inside)

theorem ProductMember.count_le {cfg : Config} {factors : List Factor} {sets : List (Array Nat)}
    (h : ProductMember cfg factors sets) (valid : FactorsValid factors) :
    selectedCount sets ≤ capacity factors := by
  induction h with
  | nil => simp [selectedCount, capacity]
  | @cons f s fs ss here tail ih =>
    have one := family_size_le cfg f (valid f List.mem_cons_self) here
    have rest := ih (fun f hf => valid f (List.mem_cons_of_mem _ hf))
    simp only [selectedCount, capacity, List.map_cons, List.sum_cons] at *
    omega

theorem header_difference {lower upper a b : Nat} (ha : lower ≤ a) (hb : b ≤ upper) :
    (tag0Size b : _root_.Int) - (tag0Size a : _root_.Int) ≤ (headerSlack lower upper : _root_.Int) := by
  have lo := tag0Size_mono ha
  have hi := tag0Size_mono hb
  unfold headerSlack
  omega

/-- A family minimum cannot spend more than the header's whole possible
variation on any one component, relative to any attained replacement. -/
theorem minimum_replacement_bound (cfg : Config) {factors : List Factor} {sets : List (Array Nat)}
    (member : ProductMember cfg factors sets) (valid : FactorsValid factors)
    {baseCount lower upper : Nat}
    (minimal : ∀ other, ProductMember cfg factors other →
      productObjective baseCount factors sets ≤ productObjective baseCount factors other)
    (low : lower ≤ baseCount) (high : baseCount + capacity factors ≤ upper) :
    List.Forall₂ (fun f s => s ∈ family cfg f.cost f.members ∧
      ∀ replacement ∈ family cfg f.cost f.members,
        f.cost s ≤ f.cost replacement + (headerSlack lower upper : _root_.Int)) factors sets := by
  induction member generalizing baseCount with
  | nil => exact List.Forall₂.nil
  | @cons f s fs ss here tail ih =>
    have validTail : FactorsValid fs := fun f hf => valid f (List.mem_cons_of_mem _ hf)
    have one := family_size_le cfg f (valid f List.mem_cons_self) here
    have rest := ProductMember.count_le tail validTail
    have headBound : ∀ replacement ∈ family cfg f.cost f.members,
        f.cost s ≤ f.cost replacement + (headerSlack lower upper : _root_.Int) := by
      intro replacement inside
      have replacementSize := family_size_le cfg f (valid f List.mem_cons_self) inside
      have comparison := minimal (replacement :: ss) (List.Forall₂.cons inside tail)
      have headers := header_difference (lower := lower) (upper := upper)
        (a := baseCount + selectedCount (s :: ss))
        (b := baseCount + selectedCount (replacement :: ss))
        (by change lower ≤ baseCount + (s.size + selectedCount ss); omega)
        (by change baseCount + (replacement.size + selectedCount ss) ≤ upper
            have h : baseCount + (f.members.length + capacity fs) ≤ upper := high
            omega)
      simp only [productObjective, deltaSum] at comparison
      omega
    have tailMinimum : ∀ other, ProductMember cfg fs other →
        productObjective (baseCount + s.size) fs ss ≤ productObjective (baseCount + s.size) fs other := by
      intro other inside
      have comparison := minimal (s :: other) (List.Forall₂.cons here inside)
      simp only [productObjective, deltaSum, selectedCount, List.map_cons, List.sum_cons,
        Nat.add_assoc, Int.add_assoc] at comparison ⊢
      omega
    refine List.Forall₂.cons ⟨here, headBound⟩ (ih validTail tailMinimum (by omega) ?_)
    simp only [capacity, List.map_cons, List.sum_cons] at high ⊢
    omega

/-- `best` is attained by an actual member of the declared family. -/
theorem table_best_member (cfg : Config) (f : Factor) {best : _root_.Int}
    (h : (table cfg f.cost f.members).best = some best) :
    ∃ selected, selected ∈ family cfg f.cost f.members ∧ f.cost selected = best := by
  obtain ⟨k, e, row, value⟩ := best_attained h
  obtain ⟨_, inside, cost⟩ := (table_meaning cfg f.cost f.members).sound k e row
  exact ⟨e.2, inside, cost.symm.trans value⟩

theorem table_best_exists (cfg : Config) (f : Factor) (hd : f.members.Nodup) :
    ∃ best, (table cfg f.cost f.members).best = some best ∧
      (∃ selected, selected ∈ family cfg f.cost f.members ∧ f.cost selected = best) ∧
      ∀ selected ∈ family cfg f.cost f.members, best ≤ f.cost selected := by
  have meaning := table_meaning cfg f.cost f.members
  obtain ⟨e, row, _⟩ := meaning.covers #[] (family_empty cfg f.cost hd)
  obtain ⟨best, hbest⟩ := best_isSome row
  refine ⟨best, hbest, table_best_member cfg f hbest, ?_⟩
  intro selected inside
  obtain ⟨other, atCount, bound⟩ := meaning.covers selected inside
  exact Int.le_trans (best_le hbest atCount) bound

def WithinSlack (cfg : Config) (slack : Nat) (f : Factor) (selected : Array Nat) : Prop :=
  selected ∈ family cfg f.cost f.members ∧
    ∀ best, (table cfg f.cost f.members).best = some best →
      f.cost selected ≤ best + (slack : _root_.Int)

theorem minimum_within_slack (cfg : Config) {factors : List Factor} {sets : List (Array Nat)}
    (valid : FactorsValid factors) {baseCount lower upper : Nat}
    (minimum : ProductMinimum cfg baseCount factors sets)
    (low : lower ≤ baseCount) (high : baseCount + capacity factors ≤ upper) :
    List.Forall₂ (WithinSlack cfg (headerSlack lower upper)) factors sets := by
  have bounded := minimum_replacement_bound cfg minimum.1 valid minimum.2 low high
  apply Ix.Sharing.Verify.SharingExact.forall₂_imp ?_ bounded
  intro f s here
  refine ⟨here.1, ?_⟩
  intro best hbest
  obtain ⟨replacement, inside, cost⟩ := table_best_member cfg f hbest
  simpa [cost] using here.2 replacement inside

def Retained (cfg : Config) (slack : Nat) (f : Factor) (selected : Array Nat) : Prop :=
  HasAtT ((table cfg f.cost f.members).trim slack) selected.size (f.cost selected) selected.toList

/-- Equality at the slack boundary is retained, with canonical tie coverage. -/
theorem within_retained (cfg : Config) (slack : Nat) (f : Factor) (hd : f.members.Nodup)
    (selected : Array Nat) (bound : WithinSlack cfg slack f selected) : Retained cfg slack f selected :=
  (trim_tie slack (table_ties cfg f.cost hd).1).2
    (table_tie_coverage cfg f.cost hd selected bound.1) bound.2

theorem minimum_retained (cfg : Config) {factors : List Factor} {sets : List (Array Nat)}
    (valid : FactorsValid factors) {baseCount lower upper : Nat}
    (minimum : ProductMinimum cfg baseCount factors sets)
    (low : lower ≤ baseCount) (high : baseCount + capacity factors ≤ upper) :
    List.Forall₂ (Retained cfg (headerSlack lower upper)) factors sets := by
  have bounds := minimum_within_slack cfg valid minimum low high
  exact forall₂_imp_mem bounds (fun f hf s h => within_retained cfg _ f (valid f hf) s h)

/-- The factors are precisely the initial prototype component contexts,
with their signed deltas relative to their own empty-subset baselines. -/
def initialFactors (ex : Expanded) (stage : UStage) : List Factor :=
  stage.comps.toList.map fun members =>
    let cx := componentContext ex stage members
    { members := members.toList, cost := componentDelta cx (cx.phiE (fun _ => false) #[]).1 }

theorem initial_capacity (ex : Expanded) (stage : UStage) :
    capacity (initialFactors ex stage) = (stage.comps.toList.map Array.size).sum := by
  simp [capacity, initialFactors, List.map_map, Function.comp_def]

/-- Only the existing checked-partition facts are needed: distinct members
and labels make the flattened component list a subset of uncertain terms. -/
theorem checked_components_capacity {dag : Dag} (hwf : DagWF dag) {cls : Array UClass}
    {opaq : Array Bool} {comps : Array (Array Nat)} {label : Array (Option Nat)}
    (checked : componentsChecked dag cls opaq comps label = true) :
    (∀ members ∈ comps.toList, members.toList.Nodup) ∧
      (comps.toList.map Array.size).sum ≤ ((Array.range dag.size).filter (cls[·]! == .uncertain)).size := by
  obtain ⟨members, distinct, _, _⟩ := componentsChecked_spec hwf checked
  have each : ∀ component ∈ comps.toList, component.toList.Nodup := by
    intro component inside
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp inside
    have hi' : i < comps.size := by simpa using hi
    subst component
    simpa [getElem!_pos comps i hi'] using distinct i hi'
  have flat : (comps.toList.flatMap Array.toList).Nodup := by
    apply List.pairwise_flatMap.mpr
    refine ⟨each, List.pairwise_iff_getElem.mpr ?_⟩
    intro i j hi hj hij x hx y hy same
    have hi' : i < comps.size := by simpa using hi
    have hj' : j < comps.size := by simpa using hj
    have hx' : x ∈ comps[i]!.toList := by simpa [getElem!_pos comps i hi'] using hx
    have hy' : y ∈ comps[j]!.toList := by simpa [getElem!_pos comps j hj'] using hy
    subst y
    have one := (members i hi' x hx').2.2
    have two := (members j hj' x hy').2.2
    have : i = j := Option.some.inj (one.symm.trans two)
    omega
  have subset : comps.toList.flatMap Array.toList ⊆
      (((Array.range dag.size).filter (cls[·]! == .uncertain)).toList) := by
    intro x inside
    obtain ⟨component, contained, hx⟩ := List.mem_flatMap.mp inside
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp contained
    have hi' : i < comps.size := by simpa using hi
    subst component
    have hx' : x ∈ comps[i]!.toList := by simpa [getElem!_pos comps i hi'] using hx
    obtain ⟨bound, uncertain, _⟩ := members i hi' x hx'
    apply Array.mem_toList_iff.mpr
    exact Array.mem_filter.mpr ⟨Array.mem_range.mpr bound, by rw [uncertain]; rfl⟩
  refine ⟨each, ?_⟩
  simpa only [List.length_flatMap, Array.length_toList] using flat.length_le_of_subset subset

/-- A minimum over the actual initial families lies within the existing
stage slack and therefore retains tie-aware per-count witnesses after trim.
The hypotheses are the old structural partition check and canonical DAG
well-formedness; no global exact minimum or subgroup-search premise appears. -/
theorem initial_minimum_slack (cfg : Config) (ex : Expanded) (width : Nat) (sets : List (Array Nat))
    (hwf : DagWF ex.dag)
    (checked : let stage := uniformStage width ex (Prep.ofDag ex.dag)
      componentsChecked ex.dag stage.cls stage.opaq stage.comps
        (componentLabels ex.dag.size stage.comps) = true)
    (minimum : let stage := uniformStage width ex (Prep.ofDag ex.dag)
      ProductMinimum cfg stage.cs.size (initialFactors ex stage) sets) :
    let stage := uniformStage width ex (Prep.ofDag ex.dag)
    List.Forall₂ (WithinSlack cfg stage.slack) (initialFactors ex stage) sets ∧
      List.Forall₂ (Retained cfg stage.slack) (initialFactors ex stage) sets := by
  let stage := uniformStage width ex (Prep.ofDag ex.dag)
  have partition := checked_components_capacity hwf checked
  have valid : FactorsValid (initialFactors ex stage) := by
    intro f inside
    obtain ⟨members, contained, rfl⟩ := List.mem_map.mp inside
    exact partition.1 members contained
  have uncertain : stage.unc = (Array.range ex.dag.size).filter (stage.cls[·]! == .uncertain) := rfl
  have bound : capacity (initialFactors ex stage) ≤ stage.unc.size := by
    simpa only [initial_capacity, uncertain] using partition.2
  have high := Nat.add_le_add_left bound stage.cs.size
  have slack : headerSlack stage.cs.size (stage.cs.size + stage.unc.size) = stage.slack := rfl
  have within := minimum_within_slack cfg valid minimum (Nat.le_refl stage.cs.size) high
  have retained := minimum_retained cfg valid minimum (Nat.le_refl stage.cs.size) high
  simpa only [slack] using And.intro within retained

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.ProductMember.replace [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.minimum_replacement_bound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.table_best_exists [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.minimum_within_slack [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.within_retained [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.minimum_retained [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.checked_components_capacity [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_minimum_slack [propext, Classical.choice, Quot.sound]
